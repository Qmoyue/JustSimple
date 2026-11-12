import { after, before, test } from "node:test";
import assert from "node:assert/strict";
import { execFile } from "node:child_process";
import { promisify } from "node:util";
import { writeFile, readFile, mkdir, cp } from "node:fs/promises";
import { join } from "node:path";
import type { ExtensionToolContext } from "@earendil-works/pi-coding-agent";
import { createScannerTools } from "../src/tools.ts";
import type { EvidencePage, ResultPage, ResultRef } from "../src/bridge.ts";
import { fileURLToPath } from "node:url";
import { cleanup, temporary } from "./work.ts";

const run = promisify(execFile);
let directory: string;
let tools: Awaited<ReturnType<typeof createScannerTools>>;
let classes: string;
const entry = { owner: "Sample", name: "flow", descriptor: "(Ljava/lang/Object;)Ljava/lang/Object;" };
const sink = { ...entry, name: "sink" };
const scannerJar = fileURLToPath(new URL("../../scanner/target/justsimple-0.1.0.jar", import.meta.url));
const bridgeJar = fileURLToPath(new URL("../../bridge/target/justsimple-agent-bridge-0.1.0.jar", import.meta.url));
const javaHome = process.env.JAVA_HOME;
assert.ok(javaHome, "JAVA_HOME is required to compile and statically read fixtures");

before(async () => {
  directory = await temporary("tool-fixture-");
  classes = join(directory, "classes"); await mkdir(classes);
  const source = `
    public class Sample {
      static { if (System.nanoTime() != 0) throw new AssertionError("Target must never execute"); }
      public interface Task { Object run(Object value); }
      public static class Stored implements java.io.Serializable { private transient String reset; private String command; }
      public static class Worker implements Task { public Object run(Object value) { return sink(value); } }
      public interface Grounded { // Static interface members require no superclass initialization.
        public static Object ground(Object value) { return sink(value); }
        public static Object sink(Object value) { return value; }
      }
      public static Object flow(Object value) { return sink(value); }
      public static Object sink(Object value) { return value; }
      public static Object dispatch(Task task, Object value) { return task.run(value); }
      public static native Object nativeTarget(Object value);
      public static Runnable lambda() { return () -> sink("reference"); }
      public static String large() { return "${"x".repeat(12000)}"; }
      public static String unicode() { return "字节码☃"; }
      public static String pagedUnicode() { return "${"a".repeat(255)}😀${"尾".repeat(100)}"; }
      public static double specialNumber() { return Double.NaN; }
      public static void fanout() { ${Array.from({length: 2000}, (_, n) => `sink("${n}");`).join(" ")} }
    }`;
  const file = join(directory, "Sample.java"); await writeFile(file, source, "utf8");
  await run(join(javaHome, "bin", "javac"), ["-encoding", "UTF-8", "-g", "-parameters", "-d", classes, file]);
  tools = await createScannerTools({ scannerJar, input: classes, jdk: javaHome, maxResults: 100 });
});
after(async () => {
  try { await tools?.close(); }
  finally { if (directory) await cleanup(directory); }
});

async function call(name: string, args: object, signal?: AbortSignal) {
  const tool = tools.tools.find((tool) => tool.name === `scanner_${name}`);
  assert.ok(tool, name);
  return tool.execute("test", args as never, signal, undefined, {} as ExtensionToolContext);
}
async function page(ref: string, path: string[], options: object = {}): Promise<ResultPage> {
  return (await call("read_result", { resultRef: ref, path, ...options })).details as unknown as ResultPage;
}
const reference = (result: Awaited<ReturnType<typeof call>>) => result.details as unknown as ResultRef;

test("scanner remains an independent CLI and the agent bridge contains no analysis implementation", async () => {
  const scanner = (await run(join(javaHome, "bin", "jar"), ["tf", scannerJar])).stdout.split(/\r?\n/);
  const bridge = (await run(join(javaHome, "bin", "jar"), ["tf", bridgeJar])).stdout.split(/\r?\n/);
  assert.ok(scanner.includes("io/just/app/Main.class"));
  assert.ok(scanner.includes("io/just/analysis/Analyzer.class"));
  assert.ok(scanner.includes("META-INF/JustSimple/LICENSE"));
  assert.ok(scanner.includes("META-INF/JustSimple/THIRD_PARTY_NOTICES.md"));
  assert.ok(scanner.includes("META-INF/JustSimple/licenses/ASM-BSD-3-Clause.txt"));
  assert.ok(scanner.every((entry) => !entry.startsWith("io/just/tools/") && !entry.startsWith("io/just/agent/")));
  assert.ok(bridge.includes("io/just/agent/bridge/ToolMain.class"));
  assert.ok(bridge.includes("META-INF/JustSimple-Agent/LICENSE"));
  assert.ok(bridge.every((entry) => !entry.startsWith("io/just/analysis/") && !entry.startsWith("io/just/program/")
    && !entry.startsWith("org/objectweb/") && !entry.startsWith("com/google/")));
});

test("Pi definitions expose only domain tools and reject invalid arguments before analysis", async () => {
  assert.equal(tools.tools.length, 10);
  assert.ok(tools.tools.every((tool) => tool.executionMode === "sequential"));
  assert.ok(tools.tools.every((tool) => !["bash", "read", "write", "edit"].includes(tool.name)));
  await assert.rejects(call("expand_graph", { scope: [], command: "ignored" }), /Invalid/);
  await assert.rejects(call("scan_target", { budgets: { steps: 2147483648 } }), /budgets\/steps/);
  const symbols = reference(await call("find_symbols", { query: "Sample#flow" }));
  assert.equal(symbols.summary.methods, 1);
  assert.ok(symbols.resultRef.startsWith(`${tools.bridge.inputId}/`));
});

test("actual bytecode and lowered sources share location identities without running target code", async () => {
  const symbols = reference(await call("find_symbols", { owner: "Sample$Stored" }));
  const definitions = (await page(symbols.resultRef, ["value", "classes"])).data as {
    parent: string; interfaces: string[]; loader: number; fields: { id: { name: string; descriptor: string }; access: number }[];
  }[];
  const stored = definitions[0]!;
  assert.equal(stored.parent, "java/lang/Object"); assert.equal(stored.loader, 0);
  assert.ok(stored.interfaces.includes("java/io/Serializable"));
  assert.equal(stored.fields.find(field => field.id.name === "command")?.id.descriptor, "Ljava/lang/String;");
  assert.ok((stored.fields.find(field => field.id.name === "reset")!.access & 0x80) !== 0, "actual transient state is exposed without guessing from a callback name");
  const code = reference(await call("inspect_method", { method: entry, limit: 100 }));
  const instructions = (await page(code.resultRef, ["value", "value", "instructions"])).data as { opcode: number; mnemonic: string; site: {instruction: number} }[];
  const invoke = instructions.find((instruction) => instruction.mnemonic === "INVOKESTATIC");
  assert.ok(invoke); assert.equal(invoke.opcode, 184);
  const facts = reference(await call("inspect_method", { method: entry, view: "facts" }));
  const actions = (await page(facts.resultRef, ["value", "facts", "actions"])).data as { kind: string; site: {instruction: number} }[];
  assert.ok(actions.some((action) => action.kind === "Call" && action.site.instruction === invoke.site.instruction));
  const trace = reference(await call("trace_source", { method: entry, origin: { kind: "Parameter", slot: 0 }, budget: 1 }));
  assert.equal(trace.summary.visited, 1);
  const missing = reference(await call("inspect_method", { method: { ...entry, owner: "Missing" } }));
  assert.ok((missing.summary.pending as unknown[]).length > 0);
  const absent = reference(await call("inspect_method", { method: { ...entry, name: "notDeclared" } }));
  assert.deepEqual(absent.summary.pending, []);
  const unicode = reference(await call("inspect_method", { method: {owner: "Sample", name: "unicode", descriptor: "()Ljava/lang/String;"} }));
  const constants = (await page(unicode.resultRef, ["value", "value", "instructions"])).data as {operands: {constant?: {value: string}}}[];
  assert.ok(constants.some((instruction) => instruction.operands.constant?.value === "字节码☃"));
});

test("symbol search reports its scope without treating unsearched platform classes as absent", async () => {
  const target = reference(await call("find_symbols", { query: "StringBuilder#append" }));
  assert.equal(target.summary.scope, "target");
  assert.equal(target.summary.methods, 0);
  const platform = reference(await call("find_symbols", { owner: "java/lang/StringBuilder", query: "append" }));
  assert.equal(platform.summary.scope, "java/lang/StringBuilder");
  assert.equal(platform.summary.classes, 1);
  assert.ok((platform.summary.methods as number) > 0);
});

test("method slices and stored result pages retain separate continuation offsets", async () => {
  const method = { owner: "Sample", name: "fanout", descriptor: "()V" };
  const code = reference(await call("inspect_method", { method, offset: 10, limit: 3 }));
  assert.equal(code.summary.offset, 10);
  assert.equal(code.summary.instructions, 3);
  assert.equal(code.summary.next, 13);
  const first = await page(code.resultRef, ["value", "value", "instructions"], { limit: 1 });
  assert.equal(first.next, 1);
  assert.equal((first.data as { site: { instruction: number } }[])[0]!.site.instruction, 10);
  const rest = await page(code.resultRef, ["value", "value", "instructions"], { offset: first.next });
  assert.equal(rest.next, -1);
  assert.deepEqual((rest.data as { site: { instruction: number } }[]).map(row => row.site.instruction), [11, 12]);
});

test("the bridge rejects invalid scalar and semantic arguments while retaining valid absence", async () => {
  await assert.rejects(tools.bridge.call("inspect_method", { method: entry, offset: 0.5 }), /INVALID_ARGUMENT.*offset/);
  await assert.rejects(tools.bridge.call("inspect_method", { method: entry, limit: "2" }), /INVALID_ARGUMENT.*limit/);
  await assert.rejects(tools.bridge.call("find_symbols", { query: 17 }), /INVALID_ARGUMENT.*query/);
  await assert.rejects(tools.bridge.call("scan_target", { entries: [entry], demandGuidance: "false" }), /INVALID_ARGUMENT.*demandGuidance/);
  await assert.rejects(tools.bridge.call("expand_graph", { scope: [{ method: entry, offset: 0.5 }] }), /INVALID_ARGUMENT.*offset/);
  await assert.rejects(tools.bridge.call("resolve_dispatch", { method: entry, upper: "Sample", receivers: [{ name: "Sample", loader: 0.5 }] }), /INVALID_ARGUMENT.*loader/);
  await assert.rejects(tools.bridge.call("find_symbols", { scope: "typo" }), /INVALID_ARGUMENT.*scope/);
  await assert.rejects(tools.bridge.call("find_symbols", { owner: "Sample", scope: "typo" }), /INVALID_ARGUMENT.*scope/);
  await assert.rejects(tools.bridge.call("inspect_method", { method: { ...entry, descriptor: "()Vextra" } }), /INVALID_ARGUMENT.*descriptor/);
  await assert.rejects(tools.bridge.call("scan_target", { knowledge: "selected" }), /INVALID_ARGUMENT.*knowledgeIds/);
  for (const knowledge of ["none", "all"]) {
    await assert.rejects(tools.bridge.call("scan_target", { knowledge, knowledgeIds: ["ignored"] }), /INVALID_ARGUMENT.*knowledgeIds/);
  }
  const symbols = reference(await call("find_symbols", { query: "Sample#flow" }));
  assert.equal(symbols.summary.methods, 1);
  await assert.rejects(tools.bridge.call("read_result", { resultRef: symbols.resultRef, action: "typo" }), /INVALID_ARGUMENT.*action/);
  assert.equal((await page(symbols.resultRef, ["value", "methods"])).data.length, 1, "invalid action does not consume the reference");
  const empty = reference(await call("find_symbols", { query: "Sample#notDeclared" }));
  assert.equal(empty.summary.methods, 0); assert.deepEqual(empty.summary.pending, []);
});

test("bytecode retains special floating-point constants as valid JSON", async () => {
  const code = reference(await call("inspect_method", { method: { owner: "Sample", name: "specialNumber", descriptor: "()D" } }));
  const instructions = (await page(code.resultRef, ["value", "value", "instructions"])).data as { operands: { constant?: { value: unknown } } }[];
  const constant = instructions.find((instruction) => instruction.operands.constant)?.operands.constant?.value;
  assert.deepEqual(constant, { type: "Double", value: "NaN" });
});

test("graph fanout is batched, paged and resumable without losing the rest of a method", async () => {
  const method = { owner: "Sample", name: "fanout", descriptor: "()V" };
  const first = reference(await call("expand_graph", { scope: [{ method }], methods: 1, edges: 7 }));
  assert.equal(first.summary.edges, 7);
  const frontier = (await page(first.resultRef, ["value", "frontier"])).data as {method: typeof method; depth: number; offset: number}[];
  const remainder = frontier.find((cursor) => cursor.method.name === "fanout");
  assert.equal(remainder?.offset, 7);
  const next = reference(await call("expand_graph", { scope: [remainder], methods: 1, edges: 2000 }));
  assert.equal(next.summary.edges, 1993);
  const firstPage = await page(next.resultRef, ["value", "edges"], { limit: 3 });
  assert.equal((firstPage.data as unknown[]).length, 3); assert.equal(firstPage.next, 3);
  const incoming = reference(await call("expand_graph", { scope: [{ method: sink }], direction: "INCOMING", methods: 1, edges: 100 }));
  assert.ok((incoming.summary.edges as number) >= 80);
});

test("dispatch keeps explicit scope, native metadata and budget frontiers", async () => {
  const method = { owner: "Sample$Task", name: "run", descriptor: entry.descriptor };
  const dispatch = reference(await call("resolve_dispatch", { method, upper: "Sample$Task", receivers: [{ name: "Sample$Worker" }, {name: "Missing"}], receiverBudget: 1 }));
  assert.equal(dispatch.summary.targets, 1); assert.equal(dispatch.summary.frontier, 1);
  const native = reference(await call("inspect_method", { method: { ...entry, name: "nativeTarget" } }));
  assert.equal(native.summary.hasBody, false);
  const nativeGraph = reference(await call("expand_graph", { scope: [{method: {...entry, name: "nativeTarget"}}] }));
  assert.ok((nativeGraph.summary.limitations as unknown[]).length > 0);
});

test("complete scan retains evidence and connection checks use result-scoped support choices", async () => {
  const scan = reference(await call("scan_target", { entries: [entry], sinks: [sink], knowledge: "none" }));
  assert.equal(scan.summary.execution, "FINISHED"); assert.ok((scan.summary.findings as number) > 0);
  assert.ok(JSON.stringify(scan).length < 3000, "scan result must remain a summary");
  const cli = join(directory, "cli");
  await run(join(javaHome, "bin", "java"), ["-jar", scannerJar, "--input", classes, "--jdk-home", javaHome,
    "--output", cli, "--mode", "component", "--entry", "Sample#flow(Ljava/lang/Object;)Ljava/lang/Object;",
    "--sink", "Sample#sink(Ljava/lang/Object;)Ljava/lang/Object;", "--no-guidance"]);
  const report = JSON.parse(await readFile(join(cli, "report.json"), "utf8"));
  const removeTiming = (value: unknown): unknown => JSON.parse(JSON.stringify(value, (key, value) => key === "elapsedMillis" ? 0 : value));
  for (const key of ["entries", "relations", "findings", "breakpoints", "statistics", "analysisBudgets", "missingClasses", "limitations"]) {
    const fromTool = await page(scan.resultRef, [key], { characters: 16000, limit: 100 });
    assert.equal(fromTool.next, -1, `${key} fixture must fit one comparison page`);
    assert.deepEqual(removeTiming(fromTool.data), removeTiming(report[key]), `CLI and scan tool ${key}`);
  }
  const findings = (await page(scan.resultRef, ["findings"], { limit: 1 })).data as {path: number[]; proof: {relation: number; support: number}[]}[];
  const scoped = reference(await call("inspect_method", { scanRef: scan.resultRef, method: entry }));
  assert.equal(scoped.summary.scanRef, scan.resultRef);
  await assert.rejects(call("inspect_method", { method: {...entry, loader: 9999} }), /unknown loader/);
  const finding = findings[0]; assert.ok(finding);
  await assert.rejects(tools.bridge.call("check_connection", { resultRef: scan.resultRef, relations: [finding.path.at(-1)! + 0.5] }), /INVALID_ARGUMENT.*relation/);
  await assert.rejects(tools.bridge.call("check_connection", { resultRef: scan.resultRef, relations: [finding.path.at(-1)], supports: [{ ...finding.proof[0], support: 0.5 }] }), /INVALID_ARGUMENT.*support/);
  const ids = [...new Set(finding.proof.map((use) => use.relation))].slice(0, 2);
  assert.equal(ids.length, 2);
  const selected = (await call("read_result", { resultRef: scan.resultRef, path: ["relations"], ids: [...ids, 999999], characters: 16000 })).details as unknown as EvidencePage;
  assert.deepEqual(selected.missing, [999999]); assert.deepEqual(selected.deferred, []);
  assert.deepEqual(selected.data.map((row) => (row as {id: number}).id).sort((a, b) => a - b), ids.toSorted((a, b) => a - b));
  const deferred = (await call("read_result", { resultRef: scan.resultRef, path: ["relations"], ids, limit: 1 })).details as unknown as EvidencePage;
  assert.equal(deferred.data.length, 1); assert.equal(deferred.deferred.length, 1); assert.deepEqual(deferred.missing, []);
  await assert.rejects(call("read_result", { resultRef: scan.resultRef, path: ["breakpoints"], ids }), /supports relations/);
  const checked = reference(await call("check_connection", { resultRef: scan.resultRef, relations: [finding.path.at(-1)], supports: finding.proof }));
  assert.equal(checked.summary.state, "PENDING");
  assert.equal(checked.summary.frontier, 0); assert.equal(checked.summary.pendingCount, 0); assert.equal(checked.summary.gaps, 1);
  const gaps = (await page(checked.resultRef, ["value", "gaps"])).data as { kind: string; site: { method: { owner: string; name: string } } }[];
  assert.deepEqual(gaps.map(gap => ({ kind: gap.kind, method: `${gap.site.method.owner}#${gap.site.method.name}` })),
    [{ kind: "CONTROL_CONDITION", method: "Sample#<clinit>" }]);
  const groundedEntry = { ...entry, owner: "Sample$Grounded", name: "ground" };
  const grounded = reference(await call("scan_target", { entries: [groundedEntry], sinks: [{ ...groundedEntry, name: "sink" }], knowledge: "none" }));
  const closedFinding = ((await page(grounded.resultRef, ["findings"], { limit: 1 })).data as typeof findings)[0]; assert.ok(closedFinding);
  const closed = reference(await call("check_connection", { resultRef: grounded.resultRef, relations: [closedFinding.path.at(-1)], supports: closedFinding.proof }));
  assert.equal(closed.summary.state, "CLOSED", JSON.stringify((await page(closed.resultRef, ["value"])).data));
  assert.equal(closed.summary.gaps, 0); assert.equal(closed.summary.frontier, 0); assert.equal(closed.summary.pendingCount, 0);
  await call("read_result", { resultRef: grounded.resultRef, action: "release" });
  const limited = reference(await call("scan_target", { entries: [entry], sinks: [sink], budgets: { steps: 1 }, knowledge: "none" }));
  assert.equal(limited.summary.execution, "TRUNCATED");
  const reasons = (await page(limited.resultRef, ["limitations"], { limit: 1 })).data;
  assert.ok(Array.isArray(reasons) && typeof reasons[0] === "string");
  assert.equal(limited.summary.firstLimitation, reasons[0]);
  await call("read_result", { resultRef: limited.resultRef, action: "release" });
  await assert.rejects(page(limited.resultRef, []), /released/);
  await assert.rejects(call("check_connection", { resultRef: `${tools.bridge.inputId}/foreign`, relations: [0] }), /unreleased/);
  await call("read_result", { resultRef: scan.resultRef, action: "release" });
});

test("large constants remain readable through bounded pages and references cannot escape into files", async () => {
  const code = reference(await call("inspect_method", { method: {owner: "Sample", name: "large", descriptor: "()Ljava/lang/String;"} }));
  const instructions = await page(code.resultRef, ["value", "value", "instructions"], { characters: 3000, limit: 10 });
  const pointer = (instructions.data as {requiresNarrowerPath?: boolean; path?: string[]}[]).find((item) => item.requiresNarrowerPath);
  assert.ok(pointer?.path);
  const unicode = reference(await call("inspect_method", { method: {owner: "Sample", name: "pagedUnicode", descriptor: "()Ljava/lang/String;"} }));
  const body = (await page(unicode.resultRef, ["value", "value", "instructions"])).data as {operands: {constant?: {value: unknown}}}[];
  const position = body.findIndex((instruction) => typeof instruction.operands.constant?.value === "string"); assert.ok(position >= 0);
  const path = ["value", "value", "instructions", String(position), "operands", "constant", "value"];
  const first = await page(unicode.resultRef, path, {characters: 256}); assert.equal(first.next, 255);
  const second = await page(unicode.resultRef, path, {offset: first.next, characters: 256});
  assert.equal(String(first.data) + String(second.data), "a".repeat(255) + "😀" + "尾".repeat(100));
  await assert.rejects(page(unicode.resultRef, path, {offset: 256}), /surrogate pair/);
  const text = await page(code.resultRef, [...pointer.path, "operands", "constant", "value"], { characters: 300 });
  assert.equal(text.kind, "string"); assert.equal((text.data as string).length, 300); assert.equal(text.next, 300);
  assert.equal((await page(code.resultRef, [...pointer.path, "operands", "constant", "value"], {offset: 11900, characters: 300})).next, -1);
  await assert.rejects(page("../../LICENSE", []), /unknown/);
  await assert.rejects(page(code.resultRef, ["not-a-field"]), /unknown/);
});

test("UTF-8 host configuration retains Unicode input paths through the real bridge", async () => {
  const input = join(directory, "中文输入😀"); await cp(classes, input, {recursive: true});
  const scanner = await createScannerTools({input, jdk: javaHome});
  try {
    const scan = scanner.tools.find((tool) => tool.name === "scanner_scan_target"); assert.ok(scan);
    const result = reference(await scan.execute("utf8", {entries: [entry], sinks: [sink], knowledge: "none"} as never, undefined, undefined, {} as ExtensionToolContext));
    assert.equal(result.summary.execution, "FINISHED");
    const inspect = scanner.tools.find((tool) => tool.name === "scanner_inspect_method"); assert.ok(inspect);
    const code = reference(await inspect.execute("utf8-code", {method: entry} as never, undefined, undefined, {} as ExtensionToolContext));
    const source = await scanner.bridge.call("read_result", {resultRef: code.resultRef, path: ["value", "value", "instructions", "0", "site", "source"]}) as ResultPage;
    assert.ok(String(source.data).includes("中文输入😀"), JSON.stringify(source));
  } finally { await scanner.close(); }
});

test("knowledge is built in, calls serialize and pre-cancellation keeps the scanner available", async () => {
  const knowledge = reference(await call("lookup_knowledge", {}));
  assert.ok((knowledge.summary.references as number) > 0);
  const abort = new AbortController(); abort.abort();
  await assert.rejects(call("find_symbols", {}, abort.signal), { name: "AbortError" });
  const [a, b] = await Promise.all([call("find_symbols", {query: "flow"}), call("find_symbols", {query: "nativeTarget"})]);
  assert.equal(reference(a).summary.methods, 1); assert.equal(reference(b).summary.methods, 1);
});

test("host startup errors are explicit and close is idempotent", async () => {
  await assert.rejects(createScannerTools({scannerJar, input: join(directory, "missing"), jdk: javaHome}), /bridge stopped/);
  const disposable = await createScannerTools({ scannerJar, input: classes, jdk: javaHome });
  await disposable.close(); await disposable.close();
  await assert.rejects(disposable.bridge.call("find_symbols", {}), /closed|stopped/);
});

test("default scan work can be increased and explicit host ceilings still apply on both sides", async () => {
  const defaults = tools.bridge.scanDefaults;
  const args = { entries: [entry], sinks: [sink], knowledge: "none" };
  const initial = reference(await call("scan_target", args));
  assert.deepEqual(initial.summary.budgets, defaults);
  const budgets = Object.fromEntries(Object.entries(defaults).map(([key, value]) => [key, value + 1]));
  const deeper = reference(await call("scan_target", { ...args, budgets }));
  assert.deepEqual(deeper.summary.budgets, budgets);
  assert.ok((deeper.summary.findings as number) > 0, "larger budgets still produce actual scanner candidates");
  const graph = reference(await call("expand_graph", { scope: [{ method: entry }], depth: 101, methods: 10001, edges: 20001 }));
  assert.ok((graph.summary.edges as number) > 0);
  const trace = reference(await call("trace_source", { method: entry, origin: { kind: "Parameter", slot: 0 }, budget: 10001 }));
  assert.ok((trace.summary.visited as number) > 0);
  await call("read_result", { resultRef: initial.resultRef, action: "release" });
  await call("read_result", { resultRef: deeper.resultRef, action: "release" });
  const limited = await createScannerTools({ input: classes, jdk: javaHome, scanLimits: {...tools.bridge.scanLimits, steps: 5} });
  try {
    const scan = limited.tools.find((tool) => tool.name === "scanner_scan_target"); assert.ok(scan);
    await assert.rejects(scan.execute("limit", { budgets: {steps: 6} } as never, undefined, undefined, {} as ExtensionToolContext), /\/budgets\/steps.*5/);
    await assert.rejects(limited.bridge.call("scan_target", { budgets: { steps: 6 } }), /INVALID_ARGUMENT.*steps/);
    const bounded = await limited.bridge.call("scan_target", args);
    assert.ok("summary" in bounded); assert.equal((bounded.summary.budgets as { steps: number }).steps, 5);
  } finally { await limited.close(); }
});
