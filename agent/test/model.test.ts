import { test } from "node:test";
import assert from "node:assert/strict";
import { createServer } from "node:http";
import { once } from "node:events";
import { readFile, writeFile } from "node:fs/promises";
import { join } from "node:path";
import { InteractiveMode } from "@earendil-works/pi-coding-agent";
import { createScannerRuntime } from "../src/session.ts";
import { cleanup } from "./work.ts";
import { fixture, javaHome, modelConfig, TestTerminal, waitFor } from "./runtime-fixture.ts";

test("native Pi handles steering, bytecode/graph evidence, blackboard persistence and staged reports", { timeout: 90000 }, async t => {
  process.env.PI_OFFLINE = "1";
  const { directory, classes } = await fixture();
  t.after(() => cleanup(directory));
  const agentDir = join(directory, "agent");
  let requests = 0, compactions = 0, failure: unknown, reportDirectory = "";
  let releaseFirst!: () => void;
  const firstGate = new Promise<void>(resolve => { releaseFirst = resolve; });
  const method = { owner: "Sample", name: "entry", descriptor: "(Ljava/lang/Object;)Ljava/lang/Object;" };
  const text = (content: string | { type: string; text?: string }[] | null | undefined) => typeof content === "string" ? content : (content ?? []).filter(part => part.type === "text").map(part => part.text ?? "").join("\n");
  const report = { summary: "Static connection review", scope: "Sample.entry to Sample.sink; fixture input only", unexplored: "Deployment and real application controllability were not assessed.",
    findings: [{ itemIds: ["Q1"], title: "Selected local call connection", impact: "The selected static entry passes its parameter to the selected sink.",
      chain: "Sample.entry → Sample.sink", conditions: "Explicit fixture entry and sink; argument originates at the entry parameter.", remediation: "Review the real sink's input validation." }] };
  const server = createServer(async (request, response) => {
    try {
      if (request.url === "/health") { response.end("ok"); return; }
      let body = ""; for await (const chunk of request) body += chunk;
      const data = JSON.parse(body);
      const send = (delta: object, finish: string) => {
        response.writeHead(200, { "content-type": "text/event-stream" });
        const chunk = (delta: object, finish_reason: string | null) => ({ id: "fixture", object: "chat.completion.chunk", created: 0,
          model: "fixture-model", choices: [{ index: 0, delta, finish_reason }] });
        response.end(`data: ${JSON.stringify(chunk(delta, null))}\n\ndata: ${JSON.stringify(chunk({}, finish))}\n\ndata: [DONE]\n\n`);
      };
      if (!data.tools?.length) {
        compactions++;
        send({ role: "assistant", content: "## Goal\nAudit the selected static connection.\n## Progress\nQ1 and durable evidence E1 are recorded. A report is saved; exploration is available.\n## Next\nRead board_read to recover scope, assumptions and source references." }, "stop");
        return;
      }
      const turn = requests++;
      assert.equal(data.stream, true); assert.equal(request.url, "/v1/chat/completions");
      const names = data.tools.map((tool: { function: { name: string } }) => tool.function.name) as string[];
      assert.ok(!names.includes("bash") && !names.includes("read") && !names.includes("write"));
      const reply = (id: string) => {
        const message = data.messages.findLast((message: { role: string; tool_call_id?: string }) => message.role === "tool" && message.tool_call_id === id);
        assert.ok(message, `Missing tool result ${id}`); return text(message.content);
      };
      const call = (id: string, name: string, args: unknown) => ({ id, type: "function", function: { name, arguments: JSON.stringify(args) } });
      let calls: ReturnType<typeof call>[] = [];
      if (turn < 3 || turn >= 6) assert.ok(!names.includes("write_report"), "report declarations are hidden in exploration");
      if (turn === 0) {
        assert.equal(names.length, 14);
        const prompt = data.messages.filter((message: { role: string }) => message.role === "system").map((message: { content: string }) => text(message.content)).join("\n");
        assert.ok(!prompt.includes("模块与构件"), "repository developer AGENTS is not audit context");
        assert.ok(!prompt.includes("JustSimple 审计报告"), "report format is not preloaded");
        await firstGate;
        calls = [call("guide", "skill_read", { page: "index" }), call("code", "scanner_inspect_method", { method }),
          call("graph", "scanner_expand_graph", { scope: [{ method }], depth: 1, methods: 4, edges: 8 }),
          call("shell", "bash", { command: "this-must-never-run" }), call("early-format", "skill_read", { page: "report" })];
      } else if (turn === 1) {
        assert.ok(data.messages.some((message: { content: string }) => text(message.content).includes("Keep the original receiver binding")), "native steering reaches the next model request");
        assert.match(reply("code"), /INVOKESTATIC/); assert.match(reply("graph"), /sink/);
        assert.match(reply("shell"), /not found|not available|unknown|only/i);
        assert.match(reply("early-format"), /audit_phase.*report/);
        const code = JSON.parse(reply("code"));
        calls = [call("note", "board_update", { changes: [{ question: "Does this entry pass its argument to the selected sink?",
          binding: "Sample.entry argument 0, original loader and path", status: "success", reason: "Actual INVOKESTATIC forwards the entry parameter to Sample.sink.",
          assumptions: ["The fixture sink represents a user-selected boundary, not a demonstrated production vulnerability."],
          capture: [{ resultRef: code.resultRef, role: "support" }] }], focus: "Q1" }), call("early-report", "write_report", report)];
      } else if (turn === 2) {
        const note = JSON.parse(reply("note")); assert.equal(note.states.success, 1); assert.equal(note.captures[0].id, "E1");
        assert.match(reply("early-report"), /not found|not available|unknown|only/i);
        calls = [call("finish", "audit_phase", { phase: "report", reason: "The selected local connection is evidenced; remaining deployment scope is explicit." })];
      } else if (turn === 3) {
        assert.ok(names.includes("write_report")); assert.ok(!names.includes("board_update") && !names.includes("scanner_expand_graph"));
        const transition = JSON.parse(reply("finish"));
        assert.equal(transition.phase, "report");
        assert.deepEqual(new Set(transition.available), new Set(names));
        calls = [call("format", "skill_read", { page: "report" }), call("late-update", "board_update", { changes: [{ id: "Q1", status: "open" }] })];
      } else if (turn === 4) {
        assert.match(reply("format"), /证据索引/);
        assert.match(reply("late-update"), /not found|not available|unknown|only|unavailable/i);
        calls = [call("report", "write_report", report)];
      } else if (turn === 5) {
        const output = JSON.parse(reply("report")); reportDirectory = output.output;
        assert.equal(output.findings, 1); assert.equal(output.evidence, 1);
        calls = [call("resume", "audit_phase", { phase: "explore", reason: "Continue a separate receiver question after preserving the report." })];
      } else if (turn === 6) {
        assert.ok(names.includes("scanner_inspect_method"));
        assert.deepEqual(new Set(JSON.parse(reply("resume")).available), new Set(names));
        calls = [call("retracted-report", "write_report", report), call("recheck", "scanner_inspect_method", { method })];
      } else {
        assert.match(reply("retracted-report"), /not found|not available|unknown|only|unavailable/i);
        assert.match(reply("recheck"), /INVOKESTATIC/);
      }
      const delta = calls.length ? { role: "assistant", tool_calls: calls.map((entry, index) => ({ index, ...entry })) }
        : { role: "assistant", content: "Static evidence and the scoped report are saved; exploration is available again." };
      send(delta, calls.length ? "tool_calls" : "stop");
    } catch (error) { failure = error; response.writeHead(500); response.end("Fixture assertion failed"); }
  });
  let runtime: Awaited<ReturnType<typeof createScannerRuntime>> | undefined, tui: InteractiveMode | undefined;
  try {
    server.listen(0, "127.0.0.1"); await once(server, "listening"); server.unref();
    const address = server.address(); assert.ok(address && typeof address === "object");
    const endpoint = `http://127.0.0.1:${address.port}`;
    assert.equal(await (await fetch(`${endpoint}/health`)).text(), "ok");
    await modelConfig(agentDir, `${endpoint}/v1`);
    const settingsFile = join(agentDir, "settings.json");
    const settings = JSON.parse(await readFile(settingsFile, "utf8"));
    settings.compaction = { enabled: true, reserveTokens: 1024, keepRecentTokens: 128 };
    await writeFile(settingsFile, JSON.stringify(settings), "utf8");
    runtime = await createScannerRuntime({ cwd: directory, jdk: javaHome, agentDir });
    const terminal = new TestTerminal();
    tui = new InteractiveMode(runtime, { terminal }); await tui.init();
    await runtime.session.prompt(`/target "${classes}"`); assert.equal(requests, 0);
    await runtime.session.prompt("/agent"); assert.equal(requests, 0);
    assert.equal(runtime.session.getActiveToolNames().length, 14);
    const working = runtime.session.prompt("Inspect the entry bytecode and graph, preserve evidence and write the scoped audit report.");
    await waitFor(() => requests === 1, "Native model request did not start", 15000);
    await runtime.session.prompt("Keep the original receiver binding and state deployment assumptions.", { streamingBehavior: "steer" });
    releaseFirst(); await working;
    if (failure) throw failure;
    const answer = runtime.session.messages.findLast(message => message.role === "assistant");
    assert.ok(answer?.role === "assistant" && answer.stopReason !== "error", answer?.role === "assistant" ? answer.errorMessage : "No assistant response");
    assert.equal(requests, 8);
    const reportText = await readFile(join(reportDirectory, "report.md"), "utf8");
    assert.match(reportText, /Q1@1/); assert.match(reportText, /Sample\.entry/); assert.match(reportText, /SHA-256/);
    const manifest = JSON.parse(await readFile(join(reportDirectory, "evidence.json"), "utf8"));
    assert.equal(manifest.evidence[0].source.args.method.owner, "Sample");
    const raw = await readFile(join(reportDirectory, "evidence", manifest.evidence[0].file), "utf8"); assert.match(raw, /INVOKESTATIC/);
    await runtime.session.compact();
    if (failure) throw failure;
    assert.ok(compactions > 0, "compaction follows Pi's native model path; split turns may require separate history and prefix summaries");
    assert.ok(runtime.session.sessionManager.getEntries().some(entry => entry.type === "compaction"));
    assert.ok(runtime.session.messages.some(message => message.role === "custom" && message.customType === "audit-index"));
    const file = runtime.session.sessionFile!;
    await runtime.session.prompt("/home"); assert.deepEqual(runtime.session.getActiveToolNames(), []);
    await runtime.newSession(); await runtime.switchSession(file); await runtime.session.prompt("/agent");
    const read = runtime.session.agent.state.tools.find(tool => tool.name === "board_read")!;
    const restored = await read.execute("restored", {}, new AbortController().signal);
    assert.equal((restored.details as { states: { success: number } }).states.success, 1);
    const evidence = await read.execute("durable", { view: "evidence", id: "E1", path: ["value", "value", "instructions"] }, new AbortController().signal);
    assert.match(JSON.stringify(evidence.details), /INVOKESTATIC/);
    terminal.output = "";
    const browsing = runtime.session.prompt("/board");
    await waitFor(() => terminal.output.includes("审计黑板"), "Blackboard list did not open");
    terminal.input?.("\r");
    await waitFor(() => terminal.output.includes('"binding":'), "Read-only question detail did not open");
    terminal.output = "";
    terminal.input?.("\u001b");
    await waitFor(() => terminal.output.includes("返回交互"), "Blackboard list did not resume");
    terminal.input?.("\u001b"); await browsing;
    assert.equal(requests, 8, "commands and restore do not make model calls");
  } finally {
    releaseFirst();
    try { tui?.stop(); }
    finally {
      try { await runtime?.dispose(); }
      finally {
        server.closeAllConnections();
        if (server.listening) await new Promise<void>((resolve, reject) => server.close(error => error ? reject(error) : resolve()));
      }
    }
  }
});
