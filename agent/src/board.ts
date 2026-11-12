import { createHash, randomUUID } from "node:crypto";
import { lstat, mkdir, readFile, rm, writeFile } from "node:fs/promises";
import { join } from "node:path";
import { Type, type Static } from "typebox";
import { Value } from "typebox/value";
import type { Json, Source } from "./bridge.ts";
import { missing, readJson, writeJson } from "./files.ts";

const text = Type.String({ maxLength: 4000 });
const texts = Type.Array(text, { maxItems: 32 });
const id = Type.String({ pattern: "^Q[1-9][0-9]*$" });
const MAX_ITEM_EVIDENCE = 64;
export const statusSchema = Type.Union([Type.Literal("open"), Type.Literal("pending"), Type.Literal("dead"), Type.Literal("success")]);
const selector = Type.Object({ resultRef: Type.String({ minLength: 1, maxLength: 4096 }),
  path: Type.Optional(Type.Array(Type.String({ maxLength: 512 }), { maxItems: 32 })),
  ids: Type.Optional(Type.Array(Type.Integer({ minimum: 0 }), { maxItems: 64, uniqueItems: true, description: "Only when path points to an array of records with numeric id. Omit to capture a whole query or bytecode page; these are not Q/E IDs." })),
  role: Type.Union([Type.Literal("support"), Type.Literal("counterexample"), Type.Literal("frontier")]),
}, { additionalProperties: false });
const itemSchema = Type.Object({ id, question: text, binding: text, status: statusSchema, reason: text,
  observations: texts, assumptions: texts, unresolved: texts, next: text,
  dependsOn: Type.Array(id, { maxItems: 32, uniqueItems: true }),
  evidence: Type.Array(Type.String({ pattern: "^E[1-9][0-9]*$" }), { maxItems: MAX_ITEM_EVIDENCE, uniqueItems: true }),
}, { additionalProperties: false });
export const changeSchema = Type.Object({ ...Type.Partial(itemSchema).properties,
  id: Type.Optional(Type.String({ pattern: "^Q[1-9][0-9]*$", description: "Existing question ID only. Omit to create a new question; use the ID returned by board_update." })),
  evidence: Type.Optional(Type.Array(Type.String({ pattern: "^E[1-9][0-9]*$", description: "Previously captured E ID only. Use capture with an actual resultRef to save new evidence; never invent IDs." }), { maxItems: MAX_ITEM_EVIDENCE, uniqueItems: true })),
  capture: Type.Optional(Type.Array(selector, { maxItems: 16, description: "Capture an actual scanner resultRef as durable evidence in this update; no E IDs are needed in advance." })),
}, { additionalProperties: false });
export type Change = Static<typeof changeSchema>;
export type EvidenceSelector = Static<typeof selector>;
export interface Evidence extends EvidenceSelector { id: string; source: Source; file: string; bytes: number; sha256: string; unavailable?: string }
export type Item = Static<typeof itemSchema>;
export interface BoardSnapshot { schema: 1; scope: string; version: number; focus: string | null; items: Item[]; evidence: Evidence[] }
export type Capture = (ref: string, output: string, limit: number, signal?: AbortSignal) => Promise<Source>;
const MAX_BYTES = 256 * 1024 * 1024;
const MAX_SOURCE = 32 * 1024 * 1024;
const snapshotSchema = Type.Object({ schema: Type.Literal(1), scope: Type.String(), version: Type.Integer({ minimum: 0, maximum: Number.MAX_SAFE_INTEGER }),
  focus: Type.Union([id, Type.Null()]), items: Type.Array(itemSchema, { maxItems: 2000 }),
  evidence: Type.Array(Type.Object({ ...selector.properties, id: Type.String(), file: Type.String({ pattern: "^[a-f0-9-]+\\.json$" }),
    bytes: Type.Integer({ minimum: 0, maximum: MAX_SOURCE }), sha256: Type.String({ pattern: "^[a-f0-9]{64}$" }),
    unavailable: Type.Optional(text),
    source: Type.Object({ operation: Type.String({ minLength: 1 }), args: Type.Unknown(), resultRef: Type.String({ minLength: 1 }),
      inputId: Type.String({ minLength: 1 }), summary: Type.Record(Type.String(), Type.Unknown()) }, { additionalProperties: false }),
  }, { additionalProperties: false })),
}, { additionalProperties: false });

/** Owns task records and durable evidence. Callers receive copies, never mutable state. */
export class Board {
  private readonly directory: string;
  private data: BoardSnapshot;
  private queue: Promise<void> = Promise.resolve();
  private readonly capture: Capture;

  private constructor(directory: string, data: BoardSnapshot, capture: Capture) {
    this.directory = directory; this.data = data; this.capture = capture;
  }
  get version() { return this.data.version; }
  get scope() { return this.data.scope; }
  get focus() { return this.data.focus; }

  static async open(directory: string, scope: string, capture: Capture) {
    const evidenceDirectory = join(directory, "evidence");
    await mkdir(evidenceDirectory, { recursive: true });
    if (!(await lstat(evidenceDirectory)).isDirectory()) throw new Error(`Evidence directory must be a local directory: ${evidenceDirectory}`);
    let data: BoardSnapshot = { schema: 1, scope, version: 0, focus: null, items: [], evidence: [] };
    try {
      const { value } = await readJson(join(directory, "board.json"));
      validateSnapshot(value, scope); data = value;
    } catch (error) { if (!missing(error)) throw error; }
    const board = new Board(directory, data, capture);
    const invalid = new Map<string, string>();
    for (const refs of Map.groupBy(data.evidence, ref => ref.file).values()) {
      let content: Json;
      try { content = (await board.load(refs[0]!)).value; }
      catch (error) {
        for (const ref of refs) invalid.set(ref.id, error instanceof Error ? error.message : String(error));
        continue;
      }
      for (const ref of refs) {
        try { checkSelector(content, ref); }
        catch (error) { invalid.set(ref.id, error instanceof Error ? error.message : String(error)); }
      }
    }
    let changed = false;
    for (const ref of data.evidence) {
      const reason = invalid.get(ref.id)?.slice(0, 4000);
      if (ref.unavailable !== reason) {
        if (reason === undefined) delete ref.unavailable; else ref.unavailable = reason;
        changed = true;
      }
    }
    for (const item of data.items) {
      if (item.evidence.some(ref => invalid.has(ref))) {
        if (item.status !== "pending") { item.status = "pending"; changed = true; }
      } else if (item.status === "pending" && !item.reason.trim() && !item.unresolved.length) {
        item.status = "open"; changed = true;
      }
    }
    if (changed) {
      data.version++;
      validateSnapshot(data, scope);
      await writeJson(join(directory, "board.json"), data);
    }
    return board;
  }

  overview() {
    return { scope: this.scope, version: this.version, focus: this.focus, items: this.data.items.length,
      states: Object.fromEntries(["open", "pending", "dead", "success"].map(state => [state, this.data.items.filter(item => item.status === state).length])),
      evidence: this.data.evidence.length, unavailableEvidence: this.data.evidence.filter(ref => ref.unavailable).length, evidenceBytes: evidenceBytes(this.data.evidence) };
  }
  snapshot(): BoardSnapshot { return structuredClone(this.data); }
  async flush() { await this.queue; }

  update(changes: readonly Change[], focus?: string | null, signal?: AbortSignal) {
    const owned = structuredClone(changes);
    const task = this.queue.then(() => this.commit(owned, focus, signal));
    this.queue = task.then(() => {}, () => {});
    return task;
  }
  private async commit(changes: readonly Change[], focus: string | null | undefined, signal?: AbortSignal) {
    if (changes.length > 32 || !changes.every(change => Value.Check(changeSchema, change))) throw new Error("Invalid blackboard changes; at most 32 per update");
    const next = structuredClone(this.data);
    const created: string[] = [];
    const changed: string[] = [];
    const captures = new Set<Evidence>();
    try {
      for (const change of changes) {
        signal?.throwIfAborted();
        let item = change.id ? next.items.find(item => item.id === change.id) : undefined;
        if (change.id && !item) throw new Error(`Unknown board item: ${change.id}. To create a question, omit id and provide question and binding; use the ID returned in changed for later updates.`);
        if (!item) {
          if (next.items.length >= 2000) throw new Error("Blackboard capacity reached (2000 items); existing records were retained");
          if (!change.question?.trim() || !change.binding?.trim()) throw new Error("New items require a question and explicit binding/path scope");
          item = { id: `Q${next.items.length + 1}`, question: change.question, binding: change.binding, status: "open", reason: "",
            observations: [], assumptions: [], unresolved: [], next: "", dependsOn: [], evidence: [] };
          next.items.push(item);
        }
        const { capture, id: _id, ...fields } = change;
        Object.assign(item, fields);
        for (const request of capture ?? []) {
          let evidence = next.evidence.find(ref => ref.resultRef === request.resultRef && ref.role === request.role
            && JSON.stringify(ref.path ?? []) === JSON.stringify(request.path ?? []) && JSON.stringify(ref.ids ?? []) === JSON.stringify(request.ids ?? []));
          const linked = evidence && item.evidence.includes(evidence.id);
          if (!linked && item.evidence.length >= MAX_ITEM_EVIDENCE) throw new Error(`Item ${item.id} exceeds ${MAX_ITEM_EVIDENCE} evidence references`);
          if (!evidence) {
            const retained = next.evidence.find(ref => ref.resultRef === request.resultRef);
            const file = retained?.file ?? `${randomUUID()}.json`;
            const output = join(this.directory, "evidence", file);
            let source: Source, bytes: number, sha256: string, content: Json;
            if (retained) {
              ({ source, bytes, sha256 } = retained);
              content = (await this.load(retained, signal)).value;
            }
            else {
              created.push(output);
              const available = MAX_BYTES - evidenceBytes(next.evidence);
              if (available < 1) throw new Error("Durable evidence byte capacity reached");
              source = await this.capture(request.resultRef, output, Math.min(MAX_SOURCE, available), signal);
              const raw = await readFile(output, { signal }); bytes = raw.length;
              if (bytes > Math.min(MAX_SOURCE, available)) throw new Error("Durable evidence byte capacity exceeded");
              sha256 = createHash("sha256").update(raw).digest("hex");
              content = parseEvidence(raw);
            }
            evidence = { ...request, id: `E${next.evidence.length + 1}`, file, source: structuredClone(source), bytes, sha256 };
            // Verify selector existence before committing a durable reference.
            checkSelector(content, request);
            next.evidence.push(evidence);
          }
          if (!linked) item.evidence.push(evidence.id);
          captures.add(evidence);
        }
        checkItem(item, next.evidence);
        if (JSON.stringify(item).length > 16000) throw new Error(`Item ${item.id} exceeds 16000 characters; narrow the question or reference evidence`);
        changed.push(item.id);
      }
      for (const item of next.items) for (const dependency of item.dependsOn) {
        if (dependency === item.id || !next.items.some(other => other.id === dependency)) throw new Error(`Invalid dependency ${item.id} → ${dependency}`);
      }
      if (focus !== undefined) {
        if (focus !== null && !next.items.some(item => item.id === focus)) throw new Error(`Unknown focus: ${focus}`);
        next.focus = focus;
      }
      next.version++;
      await writeJson(join(this.directory, "board.json"), next, signal);
      this.data = next;
      return { ...this.overview(), changed, captures: [...captures].map(({ id, resultRef }) => ({ id, resultRef })) };
    } catch (error) {
      const failures = [error];
      for (const file of created) {
        try { await rm(file, { force: true }); }
        catch (cleanup) { failures.push(cleanup); }
      }
      if (failures.length > 1) throw new AggregateError(failures,
        `Blackboard update failed: ${String(error)}\nEvidence cleanup failed: ${failures.slice(1).map(String).join("; ")}`, { cause: error });
      throw error;
    }
  }

  async read(options: { view?: "overview" | "item" | "graph" | "evidence"; id?: string; status?: string; query?: string; part?: "data" | "source"; path?: string[]; offset?: number; limit?: number; characters?: number } = {}) {
    const { view = "overview", offset = 0, limit = 20, characters = 6000 } = options;
    if (!Number.isSafeInteger(offset) || offset < 0 || !Number.isSafeInteger(limit) || limit < 1 || limit > 100
      || !Number.isSafeInteger(characters) || characters < 256 || characters > 16000) throw new Error("Invalid board page budget");
    if (view === "evidence") {
      const evidence = this.data.evidence.find(ref => ref.id === options.id);
      if (!evidence) throw new Error(`Unknown durable evidence: ${options.id}`);
      const source = options.part === "source";
      const value = source ? evidence.source : (await this.load(evidence)).value;
      return { scope: this.scope, version: this.version, snapshot: true,
        evidence: { id: evidence.id, operation: evidence.source.operation, role: evidence.role, bytes: evidence.bytes, sha256: evidence.sha256,
          ...(evidence.unavailable ? { unavailable: evidence.unavailable } : {}) },
        page: page(value, options.path ?? [], offset, limit, characters,
          source || options.path?.length ? undefined : evidence.ids, source ? [] : evidence.path ?? []) };
    }
    const selectedId = options.id ?? (view === "graph" ? this.focus : undefined);
    const selected = selectedId ? this.data.items.find(item => item.id === selectedId) : undefined;
    if (selectedId && !selected) throw new Error(`Unknown board item: ${selectedId}`);
    if (view === "item") {
      if (!selected) throw new Error("Item view requires an id");
      return { scope: this.scope, version: this.version, page: page(selected, options.path ?? [], offset, limit, characters) };
    }
    const query = options.query?.toLowerCase();
    const items = this.data.items.filter(item => (!options.status || item.status === options.status)
      && (!query || `${item.question}\n${item.binding}\n${item.next}`.toLowerCase().includes(query))
      && (view !== "overview" || !selected || item.id === selected.id)
      && (view !== "graph" || !selected || item.id === selected.id || selected.dependsOn.includes(item.id) || item.dependsOn.includes(selected.id)));
    return { ...this.overview(), page: page(items.map(item => ({ id: item.id, question: item.question.slice(0, 180), binding: item.binding.slice(0, 250), status: item.status,
      dependsOn: item.dependsOn, evidence: item.evidence, unresolved: item.unresolved.length, next: item.next.slice(0, 180) })), [], offset, limit, characters) };
  }
  async validateEvidence(snapshot: BoardSnapshot, ids: ReadonlySet<string>, signal?: AbortSignal) {
    for (const refs of Map.groupBy(snapshot.evidence.filter(ref => ids.has(ref.id)), ref => ref.file).values()) {
      const { value } = await this.load(refs[0]!, signal);
      for (const ref of refs) checkSelector(value, ref);
    }
  }
  async exportEvidence(snapshot: BoardSnapshot, ids: ReadonlySet<string>, destination: string, signal?: AbortSignal) {
    const selected = snapshot.evidence.filter(ref => ids.has(ref.id));
    await mkdir(destination, { recursive: true });
    for (const refs of Map.groupBy(selected, ref => ref.file).values()) {
      const { bytes, value } = await this.load(refs[0]!, signal);
      for (const ref of refs) checkSelector(value, ref);
      await writeFile(join(destination, refs[0]!.file), bytes, { signal, flag: "wx" });
    }
    return selected;
  }
  private async load(evidence: Evidence, signal?: AbortSignal) {
    signal?.throwIfAborted();
    if (!/^[a-f0-9-]+\.json$/.test(evidence.file)) throw new Error("Invalid durable evidence filename");
    const file = join(this.directory, "evidence", evidence.file);
    const info = await lstat(file);
    if (!info.isFile()) throw new Error(`Evidence must be a regular file: ${evidence.id}`);
    if (info.size !== evidence.bytes || evidence.bytes > MAX_SOURCE) throw new Error(`Evidence size changed: ${evidence.id}`);
    const bytes = await readFile(file, { signal });
    if (createHash("sha256").update(bytes).digest("hex") !== evidence.sha256) throw new Error(`Evidence content changed: ${evidence.id}`);
    return { bytes, value: parseEvidence(bytes) };
  }
}

function evidenceBytes(evidence: readonly Evidence[]) {
  return [...new Map(evidence.map(ref => [ref.file, ref.bytes])).values()].reduce((sum, bytes) => sum + bytes, 0);
}

function parseEvidence(bytes: Uint8Array): Json {
  return JSON.parse(new TextDecoder("utf-8", { fatal: true }).decode(bytes)) as Json;
}

function checkItem(item: Item, evidence: Evidence[]) {
  if (!item.question.trim() || !item.binding.trim()) throw new Error("Items require a question and binding/path scope");
  const refs = item.evidence.map(id => { const ref = evidence.find(ref => ref.id === id); if (!ref) throw new Error(`Unknown evidence ${id}`); return ref; });
  if (item.status === "pending" && !item.reason.trim() && !item.unresolved.length && !refs.some(ref => ref.unavailable)) throw new Error("Pending items require a reason or unresolved condition");
  if (item.status === "success" || item.status === "dead") {
    const role = item.status === "success" ? "support" : "counterexample";
    const supported = refs.some(ref => {
      if (ref.role !== role || ref.unavailable) return false;
      if (ref.source.operation === "inspect_method") return ["instructions", "actions"].some(key => {
        const count = ref.source.summary[key]; return typeof count === "number" && count > 0;
      });
      return ref.source.operation === "check_connection" && ref.source.summary.state === (item.status === "success" ? "CLOSED" : "CONTRADICTED");
    });
    if (!item.reason.trim() || !supported) {
      throw new Error(`${item.status} requires scoped reasoning and ${role} bytecode or connection evidence; search counts alone are insufficient`);
    }
  }
}

function validateSnapshot(value: unknown, scope: string): asserts value is BoardSnapshot {
  if (!Value.Check(snapshotSchema, value)) throw new Error("Invalid blackboard record schema");
  const data = value as BoardSnapshot;
  if (data.scope !== scope) throw new Error("Blackboard input scope mismatch");
  const ids = new Set(data.items.map(item => item.id));
  const files = new Map<string, Evidence>();
  for (const [index, ref] of data.evidence.entries()) {
    if (ref.id !== `E${index + 1}` || ref.source.resultRef !== ref.resultRef || !Object.hasOwn(ref.source, "args")) throw new Error("Invalid evidence identity or provenance");
    const previous = files.get(ref.file);
    if (previous && (previous.bytes !== ref.bytes || previous.sha256 !== ref.sha256 || previous.resultRef !== ref.resultRef)) throw new Error("Inconsistent evidence file ownership");
    files.set(ref.file, ref);
  }
  if (evidenceBytes(data.evidence) > MAX_BYTES) throw new Error("Blackboard evidence byte capacity exceeded");
  for (const [index, item] of data.items.entries()) {
    if (item.id !== `Q${index + 1}` || JSON.stringify(item).length > 16000) throw new Error("Invalid blackboard item identity or size");
    for (const dependency of item.dependsOn) if (dependency === item.id || !ids.has(dependency)) throw new Error(`Invalid blackboard dependency: ${item.id} → ${dependency}`);
    checkItem(item, data.evidence);
  }
  if (data.focus !== null && !ids.has(data.focus)) throw new Error("Invalid blackboard focus");
}

function atPath(root: unknown, path: readonly string[]) {
  let value = root;
  for (const key of path) {
    if (!value || typeof value !== "object" || !Object.hasOwn(value, key)
      || Array.isArray(value) && !/^(0|[1-9][0-9]*)$/.test(key)) throw new Error(`Unknown evidence path: ${path.join("/")}`);
    value = (value as Record<string, unknown>)[key];
  }
  return value;
}

function checkSelector(root: Json, selector: EvidenceSelector) {
  const value = atPath(root, selector.path ?? []);
  if (!selector.ids) return;
  if (!Array.isArray(value)) throw new Error("Evidence IDs require an array path");
  const available = new Set(value.map(row => row && typeof row === "object" ? row.id : undefined));
  const missing = selector.ids.filter(id => !available.has(id));
  if (missing.length) throw new Error(`Unknown evidence IDs: ${missing.join(", ")}`);
}

/** Paths and continuation pointers are relative to the captured base; IDs are never array positions. */
function page(root: unknown, path: readonly string[], offset: number, limit: number, characters: number, ids?: readonly number[], base: readonly string[] = []): unknown {
  const value = atPath(root, [...base, ...path]);
  if (ids && !Array.isArray(value)) throw new Error("Evidence IDs require an array path");
  if (Array.isArray(value)) {
    const available = ids ? value.filter(row => row && typeof row === "object" && ids.includes(row.id)) : value;
    if (offset > available.length) throw new Error("Array offset exceeds length");
    const data: unknown[] = []; let used = 2, index = offset;
    for (; index < available.length && data.length < limit; index++) {
      const row = available[index]; const length = JSON.stringify(row).length + (data.length ? 1 : 0);
      if (used + length > characters) {
        if (!data.length) { data.push({ path: [...path, String(ids ? value.indexOf(row) : index)], id: row?.id, requiresNarrowerPath: true }); index++; }
        break;
      }
      data.push(structuredClone(row)); used += length;
    }
    return { path, offset, next: index < available.length ? index : -1, total: available.length, data,
      ...(ids ? { missing: ids.filter(id => !available.some(row => row.id === id)) } : {}) };
  }
  if (typeof value === "string") {
    if (offset > value.length || offset > 0 && /[\uDC00-\uDFFF]/.test(value[offset]!)) throw new Error("Invalid string offset");
    let end = Math.min(value.length, offset + characters);
    if (end < value.length && /[\uDC00-\uDFFF]/.test(value[end]!)) end--;
    return { path, offset, next: end < value.length ? end : -1, data: value.slice(offset, end) };
  }
  if (value && typeof value === "object" && (offset > 0 || JSON.stringify(value).length > characters)) {
    const keys = Object.keys(value);
    if (offset > keys.length) throw new Error("Object key offset exceeds length");
    const selected: string[] = []; let used = 2, index = offset;
    for (; index < keys.length && selected.length < limit; index++) {
      const key = keys[index]!, length = JSON.stringify(key).length + (selected.length ? 1 : 0);
      if (used + length > characters) {
        if (!selected.length) throw new Error("Object key exceeds characters budget");
        break;
      }
      selected.push(key); used += length;
    }
    return { path, kind: "object-keys", offset, next: index < keys.length ? index : -1, total: keys.length, keys: selected, requiresNarrowerPath: true };
  }
  if (offset !== 0) throw new Error("Offset requires an array, string or object key page");
  return { path, data: structuredClone(value), next: -1 };
}
