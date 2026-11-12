import { test } from "node:test";
import assert from "node:assert/strict";
import { readFile, readdir, unlink, writeFile } from "node:fs/promises";
import { join } from "node:path";
import { Audit, type Report } from "../src/audit.ts";
import { ScannerBridge } from "../src/bridge.ts";
import { createScannerTools } from "../src/tools.ts";
import { auditTools } from "../src/audit-tools.ts";
import { cleanup } from "./work.ts";
import { fixture, javaHome } from "./runtime-fixture.ts";

test("reports reject pre-cancellation and changed evidence, clean up failed publication and preserve prior revisions", { timeout: 30000 }, async t => {
  const { directory, classes } = await fixture();
  t.after(() => cleanup(directory));
  const input = { input: classes, jdk: javaHome };
  const bridge = await ScannerBridge.open(input);
  try {
    const audit = await Audit.open(directory, "session", "input-identity", bridge, input, () => {});
    const skill = auditTools(audit).find(tool => tool.name === "skill_read")!;
    for (const page of ["index", "scan", "explore", "verify", "board"]) {
      const result = await skill.execute("load", { page });
      const chapter = result.details as { page: string; content: string };
      assert.equal(chapter.page, page); assert.ok(chapter.content.trim().length > 0, `Missing runtime chapter ${page}`);
    }
    await assert.rejects(skill.execute("phase", { page: "report" }), /audit_phase.*report/);
    await assert.rejects(audit.skill("../../AGENTS"), /Unknown built-in skill/);
    const args = { method: { owner: "Sample", name: "entry", descriptor: "(Ljava/lang/Object;)Ljava/lang/Object;" } };
    const source = await bridge.call("inspect_method", args); assert.ok("summary" in source);
    const total = await bridge.call("read_result", { resultRef: source.resultRef, path: ["value", "value", "total"] });
    assert.ok("data" in total);
    const emptyArgs = { ...args, offset: total.data, limit: 1 };
    const empty = await bridge.call("inspect_method", emptyArgs); assert.ok("summary" in empty);
    await assert.rejects(audit.update([{ question: "Empty page", binding: "entry", status: "success", reason: "No actual instructions were returned",
      capture: [{ resultRef: empty.resultRef, role: "support" }] }]), /requires scoped reasoning/);
    assert.equal(empty.summary.instructions, 0);
    assert.equal(empty.summary.totalInstructions, total.data);
    await audit.update([{ question: "Parameter forwarding", binding: "entry argument 0; loader 0; path unchanged", status: "success",
      reason: "Actual static call passes the entry parameter", capture: [{ resultRef: source.resultRef, role: "support" }] }]);
    await bridge.call("read_result", { resultRef: source.resultRef, action: "release" });
    await bridge.call("read_result", { resultRef: empty.resultRef, action: "release" });
    await assert.rejects(audit.update([{ id: "Q1", capture: [{ resultRef: empty.resultRef, role: "frontier" }] }]), /Unknown or released live result/);
    const report: Report = { summary: "Static fixture audit", scope: "Explicit fixture entry and sink", unexplored: "Deployment requirements remain outside this fixture.",
      findings: [{ itemIds: ["Q1"], title: "Forwarded parameter", impact: "Selected input reaches selected call", chain: "entry → sink",
        conditions: "Fixture-only static connection", remediation: "Review the boundary" }] };
    await assert.rejects(audit.writeReport(report), /report-phase snapshot/);
    await audit.transition("report", "Selected connection checked; deployment scope remains explicit");
    const reportSkill = auditTools(audit).find(tool => tool.name === "skill_read")!;
    const reportChapter = (await reportSkill.execute("report", { page: "report" })).details as { page: string; content: string };
    assert.equal(reportChapter.page, "report"); assert.ok(reportChapter.content.trim().length > 0);
    assert.equal(audit.allowed("board_update"), false); assert.equal(audit.allowed("write_report"), true);
    await assert.rejects(audit.update([{ id: "Q1", status: "open" }]), /exploration phase/);
    await assert.rejects(audit.writeReport(report, AbortSignal.abort()), { name: "AbortError" });
    await assert.rejects(readdir(join(audit.directory, "reports")), { code: "ENOENT" });
    const board = JSON.parse(await readFile(join(audit.directory, "board.json"), "utf8"));
    const evidenceFile = join(audit.directory, "evidence", board.evidence[0].file);
    const originalEvidence = await readFile(evidenceFile, "utf8");
    await writeFile(evidenceFile, originalEvidence.replace("INVOKESTATIC", "invokestatic"), "utf8");
    await assert.rejects(audit.writeReport(report), /content changed/);
    assert.deepEqual(await readdir(join(audit.directory, "reports")), []);
    await writeFile(evidenceFile, originalEvidence, "utf8");
    const first = await audit.writeReport(report);
    const original = await readFile(first.report, "utf8");
    assert.match(original, /Q1@1/); assert.ok(original.includes(classes)); assert.ok(original.includes(javaHome));
    const evidence = JSON.parse(await readFile(join(first.output, "evidence.json"), "utf8"));
    assert.equal(await readFile(join(first.output, "evidence", evidence.evidence[0].file), "utf8"), originalEvidence);
    await unlink(evidenceFile);
    await assert.rejects(audit.writeReport(report), /Report revision already exists/);
    await writeFile(evidenceFile, originalEvidence, "utf8");
    assert.equal(await readFile(first.report, "utf8"), original);
    assert.deepEqual(await readdir(join(audit.directory, "reports")), ["revision-1"]);
    await audit.transition("explore", "Consider another binding");
    assert.equal(audit.allowed("write_report"), false);
    const followUp = await bridge.call("inspect_method", { method: { ...args.method, name: "sink" } });
    assert.ok("summary" in followUp);
    await audit.update([{ question: "Another binding", binding: "receiver B; incompatible path", status: "pending", unresolved: ["Receiver source unknown"],
      capture: [{ resultRef: followUp.resultRef, role: "frontier" }] }]);
    await audit.transition("report", "Additional scope is explicitly unresolved");
    const second = await audit.writeReport(report);
    assert.match(await readFile(second.report, "utf8"), /Receiver source unknown/);
    const secondIndex = JSON.parse(await readFile(join(second.output, "evidence.json"), "utf8"));
    const frontier = secondIndex.evidence.find((ref: { id: string }) => ref.id === "E2");
    assert.ok(frontier, "The pending question retains its distinct captured evidence in the report");
    assert.deepEqual(await readFile(join(second.output, "evidence", frontier.file)), await readFile(join(audit.directory, "evidence", frontier.file)));
    assert.equal(await readFile(first.report, "utf8"), original);
    await unlink(evidenceFile);
    const restored = await Audit.open(directory, "session", "input-identity", bridge, input, () => {});
    await restored.transition("report", "Unavailable evidence remains an explicit gap");
    const recovery = await restored.writeReport({ ...report, findings: [] });
    const recovered = await readFile(recovery.report, "utf8");
    assert.match(recovered, /证据不可用：E1:.*ENOENT/);
    assert.match(recovered, /Actual static call passes the entry parameter/);
    const recoveryIndex = JSON.parse(await readFile(join(recovery.output, "evidence.json"), "utf8"));
    assert.deepEqual(recoveryIndex.evidence.map((ref: { id: string }) => ref.id), ["E2"]);
  } finally { await bridge.close(); }
});

test("captured query provenance keeps the sent arguments when progress callbacks mutate their input", async t => {
  const { directory, classes } = await fixture();
  t.after(() => cleanup(directory));
  const input = { input: classes, jdk: javaHome };
  const scanner = await createScannerTools(input);
  try {
    const audit = await Audit.open(directory, "provenance", "input-identity", scanner.bridge, input, () => {});
    const entry = { owner: "Sample", name: "entry", descriptor: "(Ljava/lang/Object;)Ljava/lang/Object;" };
    const args = { mode: "COMPONENT", entries: [entry], sinks: [{ ...entry, name: "sink" }], knowledge: "none" };
    const tool = scanner.tools.find(tool => tool.name === "scanner_scan_target")!;
    let changed = false;
    const result = await tool.execute("provenance", args, undefined, progress => {
      if ((progress.details as { stage?: string })?.stage && !changed) { changed = true; args.knowledge = "all"; }
    });
    assert.equal(changed, true, "the mutation occurs after the actual scan request starts");
    const ref = (result.details as { resultRef: string }).resultRef;
    const hints = await scanner.bridge.call("read_result", { resultRef: ref, path: ["hints"] });
    assert.ok("data" in hints); assert.deepEqual(hints.data, [], "the actual request used no guidance");
    await audit.update([{ question: "Original query", binding: "entry argument 0", capture: [{ resultRef: ref, role: "frontier" }] }]);
    const source = await audit.read({ view: "evidence", id: "E1", part: "source", path: ["args", "knowledge"] }) as { page: { data: string } };
    assert.equal(source.page.data, "none");
  } finally { await scanner.close(); }
});
