import { spawn, type ChildProcessWithoutNullStreams } from "node:child_process";
import { mkdtemp, realpath, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { delimiter, join, resolve, relative, isAbsolute } from "node:path";
import type { Readable } from "node:stream";
import { fileURLToPath } from "node:url";

export type Json = null | boolean | number | string | Json[] | { [key: string]: Json };
export type Operation = "find_symbols" | "find_entries" | "inspect_method" | "expand_graph" | "resolve_dispatch"
  | "trace_source" | "lookup_knowledge" | "check_connection" | "scan_target" | "read_result" | "export_scan" | "export_result";
export interface ScanProgress { stage: string; entries: number; contexts: number; steps: number; relations: number; queued: number }
export interface ScanBudgets {
  contexts: number; steps: number; depth: number; relations: number; findings: number; alternatives: number;
}
export interface ScannerOptions {
  scannerJar?: string;
  bridgeJar?: string;
  input: string;
  jdk: string;
  java?: string;
  dependencies?: string[];
  staticData?: string;
  methodInstructions?: number;
  inputLimits?: { bytes: number; entries: number; classes: number; depth: number; entryBytes: number };
  scanLimits?: ScanBudgets;
  maxResults?: number;
  resultBytes?: number;
  maxScans?: number;
  startupTimeoutMs?: number;
  cancelTimeoutMs?: number;
}
export interface ResultRef {
  inputId: string; resultRef: string; operation: Operation; elapsedMillis: number; summary: { [key: string]: Json };
}
export interface Source { operation: Operation; args: Json; resultRef: string; inputId: string; summary: Record<string, Json> }
type LiveSource = Omit<Source, "args"> & { argsJson: string };
export interface ResultPage {
  resultRef: string; path: string[]; kind: string; offset: number; next: number; data: Json;
}
export interface EvidencePage {
  resultRef: string; path: string[]; kind: "selection"; requested: number[]; missing: number[]; deferred: number[]; data: Json[];
}
export type Reply = ResultRef | ResultPage | EvidencePage | { inputId: string; released: string } | { directory: string; files: string[] } | { bytes: number };
interface Pending { id: string; resolve(value: Reply): void; reject(error: Error): void; progress?: (value: ScanProgress) => void }
interface Ready { inputId: string; scanLimits: Readonly<ScanBudgets>; scanDefaults: Readonly<ScanBudgets> }
const budgetKeys: (keyof ScanBudgets)[] = ["contexts", "steps", "depth", "relations", "findings", "alternatives"];
const MAX_REPLY_CHARS = 256_000;

function readReplies(stream: Readable, accept: (line: string) => void, onError: (error: Error) => void) {
  const decoder = new TextDecoder("utf-8", { fatal: true, ignoreBOM: true });
  const endings = /\r\n?|\n/g;
  let line = "", skipLf = false, failed = false;

  function append(part: string) {
    if (part.length > MAX_REPLY_CHARS - line.length) throw new Error("Scanner protocol reply exceeds 256K characters");
    line += part;
  }

  function receive(text: string) {
    if (!text) return;
    let start = skipLf && text[0] === "\n" ? 1 : 0;
    skipLf = text.endsWith("\r");
    endings.lastIndex = start;
    for (let ending; (ending = endings.exec(text));) {
      append(text.slice(start, ending.index));
      accept(line);
      line = "";
      start = endings.lastIndex;
    }
    append(text.slice(start));
  }

  function fail(error: unknown) {
    if (failed) return;
    failed = true;
    line = "";
    onError(error instanceof Error ? error : new Error(String(error)));
  }

  stream.on("data", (chunk: Buffer) => {
    if (failed) return;
    try { receive(decoder.decode(chunk, { stream: true })); }
    catch (error) { fail(error); }
  });
  stream.once("end", () => {
    if (failed) return;
    try {
      receive(decoder.decode());
      if (line) accept(line);
    } catch (error) { fail(error); }
    finally { line = ""; }
  });
  stream.once("error", fail);
}

/** Owns the agent bridge process and its evidence lifetime. No command, classpath or filesystem operation is model-selectable. */
export class ScannerBridge {
  readonly #process: ChildProcessWithoutNullStreams;
  readonly #directory: string;
  readonly #cancelTimeout: number;
  readonly #ready: Promise<Ready>;
  readonly #exited: Promise<void>;
  #pending?: Pending;
  #failure?: Error;
  #closing?: Promise<void>;
  #queue: Promise<void> = Promise.resolve();
  #sequence = 0;
  #stderr = "";
  #info?: Ready;
  readonly #sources = new Map<string, LiveSource>();
  get inputId(): string { return this.#info?.inputId ?? ""; }
  get scanLimits(): Readonly<ScanBudgets> {
    if (!this.#info) throw new Error("Scanner bridge is not ready");
    return this.#info.scanLimits;
  }
  get scanDefaults(): Readonly<ScanBudgets> {
    if (!this.#info) throw new Error("Scanner bridge is not ready");
    return this.#info.scanDefaults;
  }

  private constructor(process: ChildProcessWithoutNullStreams, directory: string, options: ScannerOptions) {
    this.#process = process;
    this.#directory = directory;
    this.#cancelTimeout = options.cancelTimeoutMs ?? 5000;
    process.stdin.setDefaultEncoding("utf8");
    process.stderr.setEncoding("utf8");
    this.#exited = new Promise((done) => process.once("close", done));
    this.#ready = new Promise((ready, reject) => {
      const fail = (error: Error) => {
        this.#failure ??= error;
        this.#sources.clear();
        this.#pending?.reject(error);
        this.#pending = undefined;
        reject(error);
      };
      process.once("error", fail);
      process.stdin.on("error", fail);
      process.stderr.on("data", (chunk: string) => { this.#stderr = (this.#stderr + chunk).slice(-16000).replace(/^[\uDC00-\uDFFF]/, ""); });
      process.once("close", (code, signal) => fail(new Error(`Scanner bridge stopped (${code ?? signal}): ${this.#stderr}`)));
      readReplies(process.stdout, (line) => {
        const message = JSON.parse(line) as { id: string; protocol?: number; inputId?: string; scanLimits?: ScanBudgets; scanDefaults?: ScanBudgets; progress?: ScanProgress; result?: Reply; error?: { code: string; message: string } };
        if (message.id === "ready") {
          if (message.protocol !== 1 || !message.inputId) throw new Error("Unsupported scanner protocol");
          const limits = message.scanLimits;
          if (!limits || !budgetKeys.every((key) => Number.isSafeInteger(limits[key]) && limits[key] >= 1)) throw new Error("Invalid scanner budget capabilities");
          const defaults = message.scanDefaults;
          if (!defaults || !budgetKeys.every(key => Number.isSafeInteger(defaults[key]) && defaults[key] >= 1 && defaults[key] <= limits[key])) throw new Error("Invalid scanner defaults; rebuild the paired Scanner and Bridge JARs");
          ready({ inputId: message.inputId, scanLimits: Object.freeze({ ...limits }), scanDefaults: Object.freeze({ ...defaults }) });
        } else if (this.#pending?.id === message.id) {
          const pending = this.#pending;
          if (message.progress) { pending.progress?.(message.progress); return; }
          if (message.error) pending.reject(new Error(`${message.error.code}: ${message.error.message}`));
          else if (message.result !== undefined) pending.resolve(message.result);
          else throw new Error("Scanner reply has no result or error");
          this.#pending = undefined;
        } else throw new Error(`Unexpected scanner reply: ${message.id}`);
      }, (error) => {
        fail(error);
        process.kill();
      });
    });
  }

  static async open(options: ScannerOptions, signal?: AbortSignal): Promise<ScannerBridge> {
    signal?.throwIfAborted();
    const directory = await mkdtemp(join(tmpdir(), "justsimple-tools-"));
    let scanner: ScannerBridge | undefined;
    try {
      const config = {
        input: resolve(options.input), jdk: resolve(options.jdk), dependencies: (options.dependencies ?? []).map((path) => resolve(path)),
        staticData: options.staticData ? resolve(options.staticData) : null,
        results: join(directory, "results"), methodInstructions: options.methodInstructions ?? 20000,
        maxResults: options.maxResults ?? 256, resultBytes: options.resultBytes ?? 256 * 1024 * 1024, maxScans: options.maxScans ?? 4,
        inputLimits: options.inputLimits ?? null,
        scanLimits: options.scanLimits ?? null,
      };
      const path = join(directory, "config.json");
      await writeFile(path, JSON.stringify(config), { encoding: "utf8", mode: 0o600 });
      const process = spawn(options.java ?? "java", ["-cp", bridgeClasspath(options), "io.just.agent.bridge.ToolMain", path], { stdio: "pipe", windowsHide: true, shell: false });
      scanner = new ScannerBridge(process, directory, options);
      const abort = () => { process.kill(); };
      signal?.addEventListener("abort", abort, { once: true });
      let timer: ReturnType<typeof setTimeout> | undefined;
      try {
        if (signal?.aborted) abort();
        scanner.#info = await Promise.race([scanner.#ready, new Promise<never>((_, reject) => {
          timer = setTimeout(() => reject(new Error("Scanner bridge startup timed out")), options.startupTimeoutMs ?? 180000);
        })]);
        signal?.throwIfAborted();
      } finally { clearTimeout(timer); signal?.removeEventListener("abort", abort); }
      return scanner;
    } catch (error) {
      if (scanner) await scanner.close(); else await rm(directory, { recursive: true, force: true });
      signal?.throwIfAborted();
      throw error;
    }
  }

  async call(operation: Operation, args: unknown, signal?: AbortSignal, progress?: (value: ScanProgress) => void): Promise<Reply> {
    signal?.throwIfAborted();
    const argsJson = JSON.stringify(args);
    if (argsJson === undefined) throw new TypeError("Scanner arguments must be JSON serializable");
    const task = this.#queue.then(async () => {
      signal?.throwIfAborted();
      if (this.#closing || this.#failure) throw this.#failure ?? new Error("Scanner bridge is closed");
      const id = String(++this.#sequence);
      const request = `{"id":${JSON.stringify(id)},"tool":${JSON.stringify(operation)},"args":${argsJson}}`;
      if (request.length > 1000000) throw new Error("Scanner request exceeds 1M characters");
      let timer: ReturnType<typeof setTimeout> | undefined;
      const cancel = () => {
        this.#process.stdin.write(`${JSON.stringify({ id, cancel: true })}\n`);
        timer = setTimeout(() => this.#process.kill(), this.#cancelTimeout);
      };
      try {
        const result = await new Promise<Reply>((resolveReply, reject) => {
          this.#pending = { id, resolve: resolveReply, reject, progress };
          this.#process.stdin.write(`${request}\n`);
          signal?.addEventListener("abort", cancel, { once: true });
          if (signal?.aborted) cancel();
        });
        if ("summary" in result) this.#sources.set(result.resultRef, { operation, argsJson,
          resultRef: result.resultRef, inputId: result.inputId, summary: structuredClone(result.summary) });
        else if ("released" in result) this.#sources.delete(result.released);
        return result;
      } finally { signal?.removeEventListener("abort", cancel); clearTimeout(timer); }
    });
    this.#queue = task.then(() => undefined, () => undefined);
    return task;
  }

  async exportResult(ref: string, output: string, limit: number, signal?: AbortSignal): Promise<Source> {
    const source = this.#sources.get(ref);
    if (!source) throw new Error(`Unknown or released live result: ${ref}; read durable evidence by E id or query again`);
    const result = await this.call("export_result", { resultRef: ref, output, bytes: limit }, signal);
    if (!("bytes" in result)) throw new Error("Bridge did not export evidence");
    const { argsJson, ...metadata } = source;
    return { ...structuredClone(metadata), args: JSON.parse(argsJson) as Json };
  }

  close(): Promise<void> {
    return this.#closing ??= this.#close();
  }
  async #close(): Promise<void> {
    this.#sources.clear();
    this.#process.stdin.end();
    const timer = setTimeout(() => this.#process.kill(), this.#cancelTimeout);
    try { await this.#exited; } finally {
      clearTimeout(timer);
      const base = await realpath(tmpdir());
      const directory = await realpath(this.#directory);
      const path = relative(base, directory);
      if (!path || path.startsWith("..") || isAbsolute(path)) throw new Error("Scanner temporary directory escaped its owner");
      await rm(directory, { recursive: true, force: true });
    }
  }
}

export function bridgeClasspath(options: Pick<ScannerOptions, "scannerJar" | "bridgeJar"> = {}): string {
  return [options.bridgeJar ?? fileURLToPath(new URL("../../bridge/target/justsimple-agent-bridge-0.1.0.jar", import.meta.url)),
    options.scannerJar ?? fileURLToPath(new URL("../../scanner/target/justsimple-0.1.0.jar", import.meta.url))].map(path => resolve(path)).join(delimiter);
}
