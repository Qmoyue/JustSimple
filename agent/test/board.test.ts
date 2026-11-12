import { test } from "node:test";
import assert from "node:assert/strict";
import { mkdir, readFile, readdir, unlink, writeFile } from "node:fs/promises";
import { join } from "node:path";
import { Board, type BoardSnapshot, type Capture } from "../src/board.ts";
import type { Source } from "../src/bridge.ts";
import { cleanup, temporary } from "./work.ts";

test("restoring a board marks a non-file evidence entry unavailable", async t => {
  const directory = await temporary("board-file-type-"); t.after(() => cleanup(directory));
  const capture: Capture = async (ref, output) => {
    await writeFile(output, '{"value":"fixture"}', "utf8");
    return { operation: "read_result", args: {}, resultRef: ref, inputId: "fixture", summary: {} };
  };
  const board = await Board.open(directory, "scope", capture);
  await board.update([{ question: "Check local record", binding: "fixture", capture: [{ resultRef: "fixture/1", role: "frontier" }] }]);
  const file = join(directory, "evidence", board.snapshot().evidence[0]!.file);
  await unlink(file); await mkdir(file);

  const restored = await Board.open(directory, "scope", capture);
  assert.match(restored.snapshot().evidence[0]!.unavailable!, /Evidence must be a regular file/);
  assert.equal(restored.snapshot().items[0]!.status, "pending");
});

test("high fanout remains in immutable evidence and bounded pages survive a fresh board instance", async t => {
  const directory = await temporary("board-fanout-"); t.after(() => cleanup(directory));
  const graph = { edges: Array.from({ length: 10000 }, (_, n) => ({ id: n * 7 + 3, target: `T${n}`, binding: n % 2 ? "receiver-A" : "receiver-B" })),
    frontier: [{ method: "Sample#fanout()V", depth: 1, offset: 10000 }], text: `${"x".repeat(255)}😀${"尾".repeat(300)}` };
  let captures = 0;
  const source: Source = { operation: "expand_graph", args: { edges: 10000, receivers: Array.from({ length: 10000 }, (_, n) => `query-receiver-${n}`) }, resultRef: "run/1", inputId: "run", summary: { edges: 10000, frontier: 1 } };
  const capture: Capture = async (_ref, output) => { captures++; await writeFile(output, JSON.stringify(graph), "utf8"); return source; };
  const board = await Board.open(directory, "input-hash", capture);
  await board.update([{ question: "Which receiver bindings reach the target?", binding: "entry E; keep receiver A/B distinct",
    capture: [{ resultRef: "run/1", role: "frontier" }], unresolved: ["Other receivers remain"], next: "Expand the remaining cursor" }], "Q1");
  assert.equal(board.overview().items, 1);
  assert.equal(captures, 1);
  const overview = await board.read({ characters: 1000 });
  assert.ok(JSON.stringify(overview).length < 1600);
  assert.ok(!JSON.stringify(overview).includes("T9999"));
  const first = await board.read({ view: "evidence", id: "E1", path: ["edges"], limit: 3, characters: 1000 }) as any;
  assert.ok(JSON.stringify(first).length < 2000, "large query metadata is not repeated in the evidence envelope");
  assert.equal(first.page.data[0].id, 3); assert.equal(first.page.next, 3);
  const fresh = await Board.open(directory, "input-hash", async () => { throw new Error("No live bridge after restore"); });
  const last = await fresh.read({ view: "evidence", id: "E1", path: ["edges"], offset: 9999 }) as any;
  assert.equal(last.page.data[0].target, "T9999"); assert.equal(last.page.next, -1);
  const frontier = await fresh.read({ view: "evidence", id: "E1", path: ["frontier"] }) as any;
  assert.equal(frontier.page.data[0].offset, 10000);
  const provenance = await fresh.read({ view: "evidence", id: "E1", part: "source", path: ["args", "receivers"], offset: 9999 }) as any;
  assert.equal(provenance.page.data[0], "query-receiver-9999");
  const string = await fresh.read({ view: "evidence", id: "E1", path: ["text"], characters: 256 }) as any;
  assert.equal(string.page.next, 255);
  const next = await fresh.read({ view: "evidence", id: "E1", path: ["text"], offset: 255, characters: 256 }) as any;
  assert.ok(next.page.data.startsWith("😀"));
  await assert.rejects(fresh.read({ view: "evidence", id: "E1", path: ["text"], offset: 256 }), /offset/);
  assert.equal(captures, 1);
});

test("explicit variants and alternative dependencies keep independent states; failed batches are atomic", async t => {
  const directory = await temporary("board-variants-"); t.after(() => cleanup(directory));
  const board = await Board.open(directory, "scope-A", async (ref, output) => {
    await writeFile(output, JSON.stringify({ instructions: [{ instruction: 7, opcode: "IFNULL" }], refs: [17, 83] }), "utf8");
    return { operation: ref === "empty" ? "find_symbols" : "inspect_method", args: { method: { owner: "Sample", name: "entry", descriptor: "()V" } },
      resultRef: ref, inputId: "input-A", summary: { instructions: 1 } };
  });
  await board.update([{ question: "Path with receiver A", binding: "object A; path x", capture: [{ resultRef: "code", role: "support" }] },
    { question: "Path with receiver B", binding: "object B; path !x", capture: [{ resultRef: "code", role: "support" }] },
    { question: "Alternative paths", binding: "A or B, not a merged object", dependsOn: ["Q1", "Q2"] }]);
  assert.equal((await readdir(join(directory, "evidence"))).length, 1, "shared immutable source is written once");
  assert.equal(board.overview().evidenceBytes, (await readFile(join(directory, "evidence", board.snapshot().evidence[0]!.file))).length);
  const update = await board.update([{ id: "Q1", status: "dead", reason: "This receiver is excluded at IFNULL", capture: [{ resultRef: "code", role: "counterexample" }] },
    { id: "Q2", status: "success", reason: "The alternative binding reaches the selected call" },
    { id: "Q3", capture: [{ resultRef: "code", role: "support" }] }]);
  assert.deepEqual(update.captures, [{ id: "E2", resultRef: "code" }, { id: "E1", resultRef: "code" }]);
  assert.deepEqual(board.snapshot().items.map(item => item.status), ["dead", "success", "open"]);
  assert.deepEqual(board.snapshot().items.map(item => item.binding), ["object A; path x", "object B; path !x", "A or B, not a merged object"]);
  const filtered = await board.read({ query: "object B" }) as { page: { data: { id: string }[] } };
  assert.deepEqual(filtered.page.data.map(item => item.id), ["Q2"]);
  const version = board.version;
  await assert.rejects(board.update([{ question: "Transient", binding: "new scope", capture: [{ resultRef: "new-code", role: "support" }] },
    { id: "Q999", status: "dead" }]), /Unknown board item/);
  assert.equal(board.version, version); assert.equal(board.overview().items, 3);
  assert.equal((await readdir(join(directory, "evidence"))).length, 1);
  await assert.rejects(board.update([{ id: "Q3", status: "dead", reason: "An empty search is not a refutation", capture: [{ resultRef: "empty", role: "counterexample" }] }]), /requires scoped reasoning/);
  await assert.rejects(Board.open(directory, "scope-B", async () => { throw new Error("unused"); }), /scope mismatch/);
  const a = board.update([{ id: "Q1", status: "open" }]);
  const b = board.update([], "Q2"); await Promise.all([a, b]);
  assert.equal(board.version, version + 2); assert.equal(board.focus, "Q2");
});

test("cancelled captures keep records intact and modified durable evidence restores as pending", async t => {
  const directory = await temporary("board-recovery-"); t.after(() => cleanup(directory));
  let controller: AbortController | undefined;
  const board = await Board.open(directory, "scope", async (ref, output, _limit, signal) => {
    await writeFile(output, '{"instructions":[{"instruction":4,"opcode":"INVOKESTATIC"}]}', "utf8");
    if (ref === "cancel") controller!.abort();
    signal?.throwIfAborted();
    return { operation: "inspect_method", args: {}, resultRef: ref, inputId: "input", summary: { instructions: 1 } };
  });
  controller = new AbortController();
  await assert.rejects(board.update([{ question: "Cancelled", binding: "receiver A", capture: [{ resultRef: "cancel", role: "support" }] }], undefined, controller.signal), { name: "AbortError" });
  assert.equal(board.version, 0); assert.deepEqual(await readdir(join(directory, "evidence")), []);
  await board.update([{ question: "Call connection", binding: "receiver A; path x", status: "success", reason: "Observed call at instruction 4", capture: [{ resultRef: "code", role: "support" }] }]);
  const evidence = board.snapshot().evidence[0]!;
  const original = await readFile(join(directory, "evidence", evidence.file), "utf8");
  const changed = original.replace('"instruction":4', '"instruction":5');
  assert.notEqual(original, changed); assert.equal(Buffer.byteLength(changed), evidence.bytes);
  await writeFile(join(directory, "evidence", evidence.file), changed, "utf8");
  const restored = await Board.open(directory, "scope", async () => { throw new Error("No live evidence"); });
  assert.equal(restored.snapshot().items[0]!.status, "pending");
  assert.match(restored.snapshot().evidence[0]!.unavailable!, /content changed: E1/);
  assert.equal(restored.snapshot().items[0]!.reason, "Observed call at instruction 4");
  await assert.rejects(restored.update([{ id: "Q1", status: "success" }]), /requires scoped reasoning/);
  await assert.rejects(restored.read({ view: "evidence", id: "E1" }), /content changed/);
  assert.equal((JSON.parse(await readFile(join(directory, "board.json"), "utf8"))).version, 2);
  const again = await Board.open(directory, "scope", async () => { throw new Error("No live evidence"); });
  assert.equal(again.version, 2, "unchanged missing evidence must not create another board revision");
});

test("restoring a malformed board rejects incomplete records, ambiguous identities and broken provenance", async t => {
  const directory = await temporary("board-invalid-"); t.after(() => cleanup(directory));
  const capture: Capture = async (ref, output) => {
    await writeFile(output, '{"instructions":[{"instruction":1}]}', "utf8");
    return { operation: "inspect_method", args: {}, resultRef: ref, inputId: "input", summary: { instructions: 1 } };
  };
  const board = await Board.open(directory, "scope", capture);
  await board.update([{ question: "Stored question", binding: "object A", capture: [{ resultRef: "code", role: "support" }] }]);
  const invalid: [string, (data: BoardSnapshot) => void][] = [
    ["missing required field", data => { delete (data.items[0] as Partial<typeof data.items[0]>)!.reason; }],
    ["non-contiguous question identity", data => { data.items[0]!.id = "Q2"; }],
    ["duplicate evidence identity", data => { data.evidence.push(structuredClone(data.evidence[0]!)); }],
    ["unknown question dependency", data => { data.items[0]!.dependsOn = ["Q999"]; }],
    ["source and selection disagree", data => { data.evidence[0]!.source.resultRef = "another-result"; }],
  ];
  for (const [name, corrupt] of invalid) await t.test(name, async () => {
    const data = board.snapshot(); corrupt(data);
    const content = JSON.stringify(data);
    await writeFile(join(directory, "board.json"), content, "utf8");
    await assert.rejects(Board.open(directory, "scope", capture), /blackboard|evidence|dependency/i);
    assert.equal(await readFile(join(directory, "board.json"), "utf8"), content);
  });
  await t.test("a selection that no longer exists is restored as pending", async () => {
    const data = board.snapshot();
    data.items[0]!.status = "success"; data.items[0]!.reason = "Previously checked instruction";
    data.evidence[0]!.path = ["missing-instructions"];
    await writeFile(join(directory, "board.json"), JSON.stringify(data), "utf8");
    const restored = await Board.open(directory, "scope", capture);
    assert.equal(restored.snapshot().items[0]!.status, "pending");
    assert.match(restored.snapshot().evidence[0]!.unavailable!, /path/);
  });
});

test("durable object keys have bounded continuation and invalid selectors cannot silently change scope", async t => {
  const directory = await temporary("board-keys-"); t.after(() => cleanup(directory));
  const wide = Object.fromEntries(Array.from({ length: 300 }, (_, n) => [`${"字段".repeat(20)}${n}`, n]));
  const board = await Board.open(directory, "scope", async (ref, output) => {
    await writeFile(output, JSON.stringify({ wide, rows: [{ id: 7, detail: "x".repeat(1000) }] }), "utf8");
    return { operation: "expand_graph", args: {}, resultRef: ref, inputId: "input", summary: {} };
  });
  await board.update([{ question: "Wide evidence", binding: "scope", capture: [{ resultRef: "wide", role: "frontier" }] }]);
  await t.test("keys remain addressable across character-limited pages", async () => {
    const keys: string[] = []; let offset = 0;
    do {
      const result = await board.read({ view: "evidence", id: "E1", path: ["wide"], offset, characters: 256 }) as any;
      assert.equal(result.page.kind, "object-keys");
      assert.ok(JSON.stringify(result.page.keys).length <= 256);
      keys.push(...result.page.keys);
      assert.ok(result.page.next === -1 || result.page.next > offset);
      offset = result.page.next;
    } while (offset !== -1);
    assert.deepEqual(keys, Object.keys(wide));
  });
  await t.test("selectors and offsets are validated against their actual value", async () => {
    await assert.rejects(board.read({ view: "evidence", id: "E1", path: ["rows"], offset: 2 }), /offset/);
    await assert.rejects(board.update([{ id: "Q1", capture: [{ resultRef: "wide", role: "frontier", path: ["wide"], ids: [7] }] }]), /array|IDs/);
    assert.equal(board.version, 1);
  });
  await t.test("continuation pointers are relative to the captured selection", async () => {
    await board.update([{ id: "Q1", capture: [{ resultRef: "wide", role: "frontier", path: ["rows"], ids: [7] }] }]);
    const result = await board.read({ view: "evidence", id: "E2", characters: 256 }) as any;
    assert.equal(result.page.data[0].requiresNarrowerPath, true);
    const detail = await board.read({ view: "evidence", id: "E2", path: [...result.page.data[0].path, "detail"], characters: 256 }) as any;
    assert.equal(detail.page.data.length, 256);
    assert.equal(detail.page.next, 256);
  });
});

test("blackboard state stays owned when callers mutate update inputs and read projections", async t => {
  const directory = await temporary("board-ownership-"); t.after(() => cleanup(directory));
  const board = await Board.open(directory, "scope", async () => { throw new Error("No capture requested"); });
  const observations = ["Original observation"];
  await board.update([{ question: "Owned state", binding: "object A", observations }]);
  await t.test("update inputs are borrowed", () => {
    observations.push("Caller mutation");
    assert.deepEqual(board.snapshot().items[0]!.observations, ["Original observation"]);
  });
  await t.test("read projections are copies", async () => {
    const result = await board.read({ view: "item", id: "Q1" }) as any;
    result.page.data.question = "Caller changed a projection";
    assert.equal(board.snapshot().items[0]!.question, "Owned state");
    const overview = await board.read() as any;
    overview.page.data[0].evidence.push("E999");
    assert.deepEqual(board.snapshot().items[0]!.evidence, []);
    const restored = await Board.open(directory, "scope", async () => { throw new Error("unused"); });
    assert.equal(restored.snapshot().items[0]!.question, board.snapshot().items[0]!.question);
  });
});

test("adding evidence stops at the same capacity the saved board can restore", async t => {
  const directory = await temporary("board-evidence-capacity-"); t.after(() => cleanup(directory));
  const capture: Capture = async (ref, output) => {
    await writeFile(output, JSON.stringify(Array.from({ length: 64 }, (_, index) => index)), "utf8");
    return { operation: "read_result", args: {}, resultRef: ref, inputId: "fixture", summary: {} };
  };
  const board = await Board.open(directory, "scope", capture);
  const selectors = Array.from({ length: 64 }, (_, index) => ({ resultRef: "values", path: [String(index)], role: "frontier" as const }));
  await board.update([{ question: "Local record", binding: "fixture", capture: selectors.slice(0, 16) }]);
  for (let start = 16; start < selectors.length; start += 16) {
    await board.update([{ id: "Q1", capture: selectors.slice(start, start + 16) }]);
  }
  const saved = board.snapshot();
  await assert.rejects(board.update([{ id: "Q1", capture: [{ resultRef: "extra", role: "frontier" }] }]), /64 evidence/);
  assert.deepEqual((await Board.open(directory, "scope", capture)).snapshot(), saved);
  assert.equal((await readdir(join(directory, "evidence"))).length, 1);
});

test("a cleanup failure preserves the update error and does not leave later files", async t => {
  const directory = await temporary("board-cleanup-failure-"); t.after(() => cleanup(directory));
  let first = "";
  const capture: Capture = async (ref, output) => {
    await writeFile(output, "{}", "utf8");
    if (first) { await unlink(first); await mkdir(first); }
    else first = output;
    return { operation: "read_result", args: {}, resultRef: ref, inputId: "fixture", summary: {} };
  };
  const board = await Board.open(directory, "scope", capture);
  await assert.rejects(board.update([{ question: "Local record", binding: "fixture", capture: [
    { resultRef: "first", role: "frontier" }, { resultRef: "second", role: "frontier" },
  ] }, { id: "Q99" }]), (error: unknown) => {
    assert.ok(error instanceof AggregateError);
    assert.match(String(error.cause), /Unknown board item: Q99/);
    assert.equal(error.errors.length, 2);
    return true;
  });
  assert.equal(board.version, 0);
  const files = await readdir(join(directory, "evidence"), { withFileTypes: true });
  assert.equal(files.length, 1);
  assert.equal(files[0]!.isDirectory(), true);
});

test("evidence recovery preserves every user condition and keeps availability separate from reasoning", async t => {
  const directory = await temporary("board-conditions-"); t.after(() => cleanup(directory));
  const capture: Capture = async (ref, output) => {
    await writeFile(output, '{"edges":[{"id":7}]}', "utf8");
    return { operation: "expand_graph", args: {}, resultRef: ref, inputId: "input", summary: { edges: 1 } };
  };
  const conditions = Array.from({ length: 32 }, (_, n) => `User condition ${n}`);
  const board = await Board.open(directory, "scope", capture);
  await board.update([{ question: "Scoped question", binding: "object A", reason: "Keep the receiver assumptions",
    unresolved: conditions, capture: [{ resultRef: "graph", role: "frontier" }] },
    { question: "Evidence-only frontier", binding: "object B", capture: [{ resultRef: "graph", role: "frontier" }] }]);
  const evidence = board.snapshot().evidence[0]!;
  const file = join(directory, "evidence", evidence.file), content = await readFile(file);
  await unlink(file);
  const restored = await Board.open(directory, "scope", capture);
  assert.equal(restored.snapshot().items[0]!.status, "pending");
  assert.deepEqual(restored.snapshot().items[0]!.unresolved, conditions);
  assert.equal(restored.snapshot().items[0]!.reason, "Keep the receiver assumptions");
  const source = await restored.read({ view: "evidence", id: "E1", part: "source" }) as any;
  assert.match(source.evidence.unavailable, /ENOENT/);
  const again = await Board.open(directory, "scope", capture);
  assert.equal(again.version, restored.version);
  await writeFile(file, content);
  const repaired = await Board.open(directory, "scope", capture);
  const available = await repaired.read({ view: "evidence", id: "E1", part: "source" }) as any;
  assert.equal(available.evidence.unavailable, undefined);
  assert.equal(repaired.snapshot().items[0]!.status, "pending", "evidence recovery does not choose a conclusion");
  assert.deepEqual(repaired.snapshot().items[0]!.unresolved, conditions);
  assert.equal(repaired.snapshot().items[1]!.status, "open", "an evidence-only pause can resume exploration when its sole cause is repaired");
});
