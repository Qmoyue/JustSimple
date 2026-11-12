import { test } from "node:test";
import assert from "node:assert/strict";
import { mkdir, readFile, readdir, realpath, rename, writeFile } from "node:fs/promises";
import { join } from "node:path";
import { InteractiveMode } from "@earendil-works/pi-coding-agent";
import { getKeybindings, Text, TuiAltScreen, TuiMainScreen, visibleWidth } from "@earendil-works/pi-tui";
import { JustSimpleEditor } from "../src/interface.ts";
import { createScannerRuntime } from "../src/session.ts";
import { ScannerSettings } from "../src/settings.ts";
import { cleanup, temporary } from "./work.ts";
import { modelConfig, TestTerminal, waitFor } from "./runtime-fixture.ts";

test("a cancelled or failed workspace switch keeps the current workspace and leaves no new session file", async t => {
  process.env.PI_OFFLINE = "1";
  const directory = await temporary("workspace-cancel-"); t.after(() => cleanup(directory));
  const current = await realpath(directory);
  const next = join(current, "next"), agentDir = join(current, "agent");
  await mkdir(next);
  await modelConfig(agentDir);
  const runtime = await createScannerRuntime({ cwd: current, agentDir });
  try {
    const switchSession = t.mock.method(runtime, "switchSession", async () => ({ cancelled: true }));
    await runtime.session.prompt(`/workspace "${next}"`);
    assert.equal(switchSession.mock.callCount(), 1);
    assert.equal(runtime.cwd, current);
    const settings = await ScannerSettings.load(agentDir);
    const sessions = join(agentDir, "sessions");
    assert.equal(settings.value.workspace, undefined);
    assert.deepEqual(await readdir(sessions), []);

    // A directory in place of scanner.json makes the atomic settings replacement fail.
    await rename(settings.file, `${settings.file}.saved`);
    await mkdir(settings.file);
    await runtime.session.prompt(`/workspace "${next}"`);
    assert.equal(switchSession.mock.callCount(), 1, "a settings write failure must stop the switch");
    assert.equal(runtime.cwd, current);
    assert.deepEqual(await readdir(sessions), []);
  } finally { await runtime.dispose(); }
});

test("fullscreen selection copies only on explicit Ctrl+C or right-click before editor actions", async () => {
  const terminal = new TestTerminal(); terminal.columns = 50; terminal.rows = 12;
  const copied: string[] = [], editorKeys: string[] = [];
  const tui = new TuiAltScreen(terminal, false, undefined, { copyOnSelect: false, copySelection: async text => { copied.push(text); return true; } });
  const text = new Text("selected evidence", 0, 0);
  tui.addChild(text); tui.setFocus({ render: () => [], invalidate() {}, handleInput: data => editorKeys.push(data) });
  try {
    tui.start(); tui.renderNow();
    terminal.input?.("\x1b[<0;1;1M"); terminal.input?.("\x1b[<32;8;1M"); terminal.input?.("\x1b[<0;8;1m");
    assert.equal(tui.hasActiveSelection(), true);
    assert.deepEqual(copied, [], "releasing the mouse must leave the clipboard alone");
    terminal.input?.("\x03");
    await waitFor(() => copied.length === 1, "Ctrl+C did not copy the selection", 1000);
    assert.deepEqual(copied, ["selected"]); assert.deepEqual(editorKeys, []);
    terminal.input?.("\x1b[<2;8;1M"); terminal.input?.("\x1b[<2;8;1m");
    await waitFor(() => copied.length === 2, "Right-click did not copy the selection", 1000);
    assert.deepEqual(copied, ["selected", "selected"]);
    tui.resetTextSelection(); terminal.input?.("\x03");
    assert.deepEqual(editorKeys, ["\x03"], "without a selection Ctrl+C retains the editor action");
  } finally { tui.stop(); }
});

test("submitted commands are gated after paste expansion without replacing native text editing", () => {
  const terminal = new TestTerminal(), tui = new TuiMainScreen(terminal);
  const plain = (text: string) => text;
  const editor = new JustSimpleEditor(tui, { borderColor: plain,
    selectList: { selectedPrefix: plain, selectedText: plain, description: plain, scrollInfo: plain, noMatch: plain } },
  getKeybindings() as ConstructorParameters<typeof JustSimpleEditor>[2]);
  const sent: string[] = [], blocked: string[] = [];
  editor.onSubmit = text => sent.push(text); editor.notify = text => blocked.push(text);
  editor.setText("/settings"); editor.handleInput("\r");
  editor.setText("/hotkeys"); editor.handleInput("\r");
  editor.setText("/share"); editor.handleInput("\r");
  editor.handleInput("\x1b[200~/bug data must stay local\x1b[201~"); editor.handleInput("\r");
  editor.setText("!echo must-not-run"); editor.handleInput("\r");
  editor.setText("/model provider/model"); editor.handleInput("\r");
  editor.setText("保持原有对象绑定"); editor.handleInput("\r");
  assert.deepEqual(sent, ["/config", "/help", "/model provider/model", "保持原有对象绑定"]);
  assert.equal(blocked.length, 3);
  editor.setText("窄终端中文输入😀");
  assert.ok(editor.render(24).every(line => visibleWidth(line) <= 24));
  tui.stop();
});

test("scan parameter overlays scroll through their real viewport in both terminal modes", { timeout: 30000 }, async t => {
  process.env.PI_OFFLINE = "1";
  const directory = await temporary("parameter-reader-"); t.after(() => cleanup(directory));
  for (const mode of ["regular", "fullscreen"] as const) {
    const agentDir = join(directory, mode); await modelConfig(agentDir);
    const file = join(agentDir, "settings.json"), saved = JSON.parse(await readFile(file, "utf8"));
    saved.tuiMode = mode; await writeFile(file, JSON.stringify(saved), "utf8");
    const terminal = new TestTerminal(); terminal.columns = 120; terminal.rows = 24;
    const runtime = await createScannerRuntime({ cwd: directory, agentDir });
    const tui = new InteractiveMode(runtime, { terminal, manageTools: false, showResumeHint: false });
    try {
      await tui.init(); terminal.output = "";
      const configuring = runtime.session.prompt("/config");
      await waitFor(() => terminal.output.includes("JustSimple · 审计设置"), "Settings did not open");
      terminal.output = "";
      for (let n = 0; n < 3; n++) terminal.input?.("\x1b[B");
      terminal.input?.("\r");
      await waitFor(() => terminal.output.includes("JustSimple · 扫描参数"), "Parameter reader did not open");
      assert.match(terminal.output, /1–\d+\/\d+/);
      terminal.output = ""; terminal.input?.("\x1b[B");
      await waitFor(() => /2–\d+\/\d+/.test(terminal.output), `Down did not scroll in ${mode}`);
      terminal.output = ""; terminal.input?.("\x1b[A");
      await waitFor(() => /1–\d+\/\d+/.test(terminal.output), `Up did not scroll in ${mode}`);
      terminal.output = ""; terminal.input?.("\x1b[6~");
      await waitFor(() => terminal.output.includes("已有结果保留"), "PageDown did not expose the final parameter explanation");
      terminal.output = ""; terminal.input?.("\x1b[5~");
      await waitFor(() => /1–\d+\/\d+/.test(terminal.output), "PageUp did not return to the beginning");
      terminal.output = ""; terminal.input?.("\x1b[F");
      await waitFor(() => terminal.output.includes("已有结果保留"), "End did not reach the final explanation");
      terminal.output = ""; terminal.input?.("\x1b[H");
      await waitFor(() => /1–\d+\/\d+/.test(terminal.output), "Home did not return to the beginning");
      terminal.output = ""; terminal.input?.("\x1b");
      await waitFor(() => terminal.output.includes("JustSimple · 审计设置"), "Esc did not return to settings");
      terminal.input?.("\x1b"); await configuring;
      terminal.rows = 48; terminal.output = "";
      const tall = runtime.session.prompt("/config");
      await waitFor(() => terminal.output.includes("JustSimple · 审计设置"), "Tall settings did not open");
      terminal.output = "";
      for (let n = 0; n < 3; n++) terminal.input?.("\x1b[B");
      terminal.input?.("\r");
      await waitFor(() => terminal.output.includes("JustSimple · 扫描参数"), "Tall reader did not open");
      assert.ok(terminal.output.includes("已有结果保留") && terminal.output.includes("Esc 返回"));
      assert.doesNotMatch(terminal.output, /\d+–\d+\/\d+/, "a fully visible document must not imply hidden pages");
      terminal.output = ""; terminal.input?.("\x1b");
      await waitFor(() => terminal.output.includes("JustSimple · 审计设置"), "Tall reader did not close");
      terminal.input?.("\x1b"); await tall;
    } finally { terminal.input?.("\x1b"); tui.stop(); await runtime.dispose(); }
  }
});

test("first startup, command suggestions and curated settings use product UI and retain Pi-owned preferences", { timeout: 30000 }, async t => {
  process.env.PI_OFFLINE = "1";
  const directory = await temporary("product-interface-"); t.after(() => cleanup(directory));
  const agentDir = join(directory, "agent"); await modelConfig(agentDir);
  const modelFile = join(agentDir, "models.json"), settingsFile = join(agentDir, "settings.json");
  const models = JSON.parse(await readFile(modelFile, "utf8")); models.providers.fixture.models[0].reasoning = true;
  await writeFile(modelFile, JSON.stringify(models), "utf8");
  const settings = JSON.parse(await readFile(settingsFile, "utf8"));
  settings.quietStartup = false; settings.defaultThinkingLevel = "high"; settings.lastChangelogVersion = "0.0.0";
  await writeFile(settingsFile, JSON.stringify(settings), "utf8");
  const terminal = new TestTerminal(); terminal.columns = 64; terminal.rows = 24;
  const runtime = await createScannerRuntime({ cwd: directory, agentDir });
  const tui = new InteractiveMode(runtime, { terminal, manageTools: false, showResumeHint: false });
  const dialog = (text: string) => waitFor(() => terminal.output.includes(`JustSimple · ${text}`), `Missing product dialog: ${text}`);
  try {
    await tui.init();
    assert.equal(runtime.services.settingsManager.getQuietStartup(), true);
    assert.equal(runtime.services.settingsManager.getFullscreenCopyOnSelect(), false);
    assert.equal(runtime.services.settingsManager.getDefaultThinkingLevel(), "high");
    assert.match(terminal.output, /JustSimple/); assert.match(terminal.output, /默认扫描/);
    assert.doesNotMatch(terminal.output, /Pi v|to run bash|\[Context\]|\[Extensions\]|What's New|Updated to v|not found|skipping download/);
    terminal.output = ""; terminal.input?.("/s");
    await waitFor(() => terminal.output.includes("静态扫描并导出报告"), "Product command completion did not render");
    assert.doesNotMatch(terminal.output, /Share session|Open settings|scoped-models|Show session info/);
    terminal.input?.("\x03");
    terminal.output = "";
    const configuring = runtime.session.prompt("/config"); await dialog("审计设置");
    terminal.output = ""; terminal.input?.("\r"); await dialog("思考强度");
    terminal.output = ""; terminal.input?.("\x1b[A"); terminal.input?.("\r");
    await dialog("审计设置");
    assert.equal(runtime.services.settingsManager.getModelThinkingLevel("fixture", "fixture-model"), "medium");
    assert.equal(runtime.session.thinkingLevel, "medium");
    terminal.output = ""; terminal.input?.("\x1b[B"); terminal.input?.("\r");
    await waitFor(() => terminal.output.includes("自动整理上下文 · 关闭"), "Compaction choice did not update");
    assert.equal(runtime.session.autoCompactionEnabled, false);
    terminal.output = ""; terminal.input?.("\x1b[B"); terminal.input?.("\x1b[B"); terminal.input?.("\r");
    await waitFor(() => terminal.output.includes("工具结果 · 展开"), "Tool detail choice did not update");
    terminal.input?.("\x1b"); await configuring;
    assert.ok(!runtime.session.messages.some(message => message.role === "user" || message.role === "assistant"));
    const saved = JSON.parse(await readFile(settingsFile, "utf8"));
    assert.equal(saved.compaction.enabled, false); assert.equal(saved.defaultThinkingLevel, "high");
    await runtime.newSession();
    assert.equal(runtime.session.thinkingLevel, "medium"); assert.equal(runtime.session.autoCompactionEnabled, false);
    assert.deepEqual(runtime.session.getActiveToolNames(), []);
    terminal.output = "";
    const help = runtime.session.prompt("/help"); await dialog("使用帮助");
    assert.match(terminal.output, /JustSimple 用法与参数说明|扫描与审计参数|Java 静态分析/);
    terminal.input?.("\x1b"); await help;
  } finally { terminal.input?.("\x1b"); tui.stop(); await runtime.dispose(); }
});
