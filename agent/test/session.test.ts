import { after, before, test } from "node:test";
import assert from "node:assert/strict";
import { execFile } from "node:child_process";
import { promisify } from "node:util";
import { existsSync } from "node:fs";
import { mkdir, writeFile, readFile, realpath, readdir } from "node:fs/promises";
import { join, resolve } from "node:path";
import { fileURLToPath } from "node:url";
import { InteractiveMode, SessionManager } from "@earendil-works/pi-coding-agent";
import { parseScannerArgs, restoreSetup } from "../src/scan-args.ts";
import { createScannerRuntime } from "../src/session.ts";
import { ScannerBridge } from "../src/bridge.ts";
import { ScannerSettings } from "../src/settings.ts";
import { fixture, javaHome, modelConfig, TestTerminal, waitFor } from "./runtime-fixture.ts";
import { cleanup } from "./work.ts";

let directory: string, classes: string;
before(async () => {
  process.env.PI_OFFLINE = "1";
  ({ directory, classes } = await fixture());
});
after(async () => { if (directory) await cleanup(directory); });

test("configuration gates prompts while offline scan exports real evidence and preserves native settings", { timeout: 60000 }, async () => {
  const terminal = new TestTerminal(), agentDir = join(directory, "offline-agent");
  const originalFetch = globalThis.fetch; let fetches = 0;
  globalThis.fetch = async () => { fetches++; throw new Error("Offline scan must not access the network"); };
  const runtime = await createScannerRuntime({ cwd: directory, jdk: javaHome, agentDir });
  const tui = new InteractiveMode(runtime, { terminal });
  try {
    await tui.init();
    assert.equal(runtime.services.settingsManager.getCompactionEnabled(), true);
    runtime.services.settingsManager.setDefaultThinkingLevel("high"); await runtime.services.settingsManager.flush();
    await runtime.session.prompt("ordinary text before /agent must stay local");
    assert.ok(!runtime.session.messages.some(message => message.role === "user"));
    await runtime.session.prompt(`/target "${classes}"`);
    assert.deepEqual(runtime.session.getActiveToolNames(), []);
    assert.match(terminal.output, /JustSimple/);
    await runtime.session.prompt("/agent");
    assert.deepEqual(runtime.session.getActiveToolNames(), [], "authentication is required only for Agent mode");
    terminal.output = "";
    const cancelled = runtime.session.prompt("/scan-only --mode component");
    await waitFor(() => terminal.output.includes("静态扫描"), "Scan view was not shown");
    await runtime.session.prompt("/config");
    await waitFor(() => terminal.output.includes("正在读取或扫描"), "Settings command did not respect the active scanner job");
    assert.doesNotMatch(terminal.output, /JustSimple · 审计设置/);
    terminal.input?.("\u001b");
    await cancelled;
    assert.ok(!runtime.session.messages.some(message => message.role === "custom" && message.customType === "scanner-result"));
    const output = join(directory, "扫描结果");
    await runtime.session.prompt(`/scan-only --mode component --knowledge none --steps 1000 --output "${output}"
      --entry 'Sample#entry(Ljava/lang/Object;)Ljava/lang/Object;' --sink 'Sample#sink(Ljava/lang/Object;)Ljava/lang/Object;'`);
    const result = JSON.parse(await readFile(join(output, "report.json"), "utf8"));
    assert.ok(result.findings.length > 0); assert.equal(result.analysisBudgets.steps, 1000);
    assert.ok((await readFile(join(output, "report.md"), "utf8")).includes("Sample"));
    assert.ok((await readdir(output)).includes("input-requirements.json"));
    const message = runtime.session.messages.find(message => message.role === "custom" && message.customType === "scanner-result");
    assert.ok(message?.role === "custom");
    const file = runtime.session.sessionFile!;
    assert.ok((await readFile(file, "utf8")).includes("scanner-target"));
    assert.equal(fetches, 0); assert.deepEqual(runtime.session.getActiveToolNames(), []);
    await runtime.newSession(); assert.equal(runtime.services.settingsManager.getDefaultThinkingLevel(), "high");
    await runtime.switchSession(file);
    assert.equal((await ScannerSettings.load(agentDir)).value.target, await realpath(classes));
    assert.deepEqual(runtime.session.getActiveToolNames(), []);
    assert.ok(terminal.output.includes("\\.静态") || terminal.output.includes("/.静态"), "Windows dot-prefixed paths render literally");
  } finally { globalThis.fetch = originalFetch; tui.stop(); await runtime.dispose(); }
});

test("project target picker and optional scan dialogs use defaults without invoking a model", { timeout: 45000 }, async () => {
  const terminal = new TestTerminal(), agentDir = join(directory, "wizard-agent");
  const runtime = await createScannerRuntime({ cwd: classes, jdk: javaHome, agentDir });
  const tui = new InteractiveMode(runtime, { terminal });
  const shown = (text: string) => waitFor(() => terminal.output.includes(text), `Missing native dialog: ${text}`);
  try {
    await tui.init();
    const choosing = runtime.session.prompt("/target"); await shown("JustSimple · 选择目标 ·");
    terminal.input?.("\r"); await choosing;
    assert.equal((await ScannerSettings.load(agentDir)).value.target, await realpath(join(classes, "Sample.class")));
    assert.deepEqual(runtime.session.getActiveToolNames(), []);
    const scan = runtime.session.prompt("/scan-only"); await shown("扫描模式"); terminal.input?.("\r");
    await shown("可选参数"); terminal.input?.("\r");
    await shown("输出目录"); terminal.input?.("\r"); await scan;
    const outputRoot = join(classes, ".local", "scans");
    const outputs = await readdir(outputRoot); assert.equal(outputs.length, 1);
    assert.ok((await readdir(join(outputRoot, outputs[0]!))).includes("report.json"));
    await runtime.session.prompt("/scan-only --mode component --steps 9");
    terminal.output = "";
    const repeated = runtime.session.prompt("/scan-only");
    await shown("扫描模式"); terminal.input?.("\r");
    await shown("可选参数"); terminal.input?.("-"); terminal.input?.("-"); terminal.input?.("\r");
    await shown("输出目录");
    const outputName = "review's reports";
    for (const char of outputName) terminal.input?.(char);
    terminal.input?.("\r"); await repeated;
    const result = JSON.parse(await readFile(join(classes, outputName, "report.json"), "utf8"));
    assert.equal(result.mode, "COMPONENT"); assert.equal(result.analysisBudgets.steps, 9);
    assert.ok(!runtime.session.messages.some(message => message.role === "assistant"));
  } finally { tui.stop(); await runtime.dispose(); }
});

test("offline scanning checks the chosen output and uses the JDK supplied for this run", { timeout: 30000 }, async () => {
  const agentDir = join(directory, "overrides-agent");
  const settings = await ScannerSettings.load(agentDir);
  const missingJdk = join(directory, "missing-platform");
  await settings.save({ target: classes, jdk: missingJdk });
  const existing = join(directory, "existing-report"), output = join(directory, "jdk-override-report");
  await mkdir(existing);
  await writeFile(join(existing, "keep.txt"), "keep");
  const terminal = new TestTerminal();
  const runtime = await createScannerRuntime({ cwd: directory, agentDir });
  const tui = new InteractiveMode(runtime, { terminal, manageTools: false, showResumeHint: false });
  try {
    await tui.init(); terminal.output = "";
    const args = `--jdk-home "${javaHome}" --mode component --knowledge none --steps 9`;
    await runtime.session.prompt(`/scan-only ${args} --output "${existing}"`);
    await waitFor(() => terminal.output.includes("Report directory already exists"), "Expected the existing-output error before target setup");
    assert.equal(await readFile(join(existing, "keep.txt"), "utf8"), "keep");
    assert.deepEqual(await readdir(existing), ["keep.txt"]);

    await runtime.session.prompt(`/scan-only ${args} --output "${output}"`);
    const report = JSON.parse(await readFile(join(output, "report.json"), "utf8"));
    assert.equal(report.analysisBudgets.steps, 9);
    assert.ok(report.input.jdkFeature >= 17);
    assert.equal((await ScannerSettings.load(agentDir)).value.jdk, missingJdk);
  } finally { tui.stop(); await runtime.dispose(); }
});

test("CLI help and version work without a terminal, credentials or SDK initialization", async () => {
  const cli = fileURLToPath(new URL("../dist/cli.js", import.meta.url));
  const { stdout } = await promisify(execFile)(process.execPath, [cli, "--help"], { env: { ...process.env, JAVA_HOME: "" } });
  assert.match(stdout, /\/scan-only/); assert.match(stdout, /\/agent/); assert.ok(!stdout.includes("/scanner"));
  assert.match((await promisify(execFile)(process.execPath, [cli, "--version"])).stdout, /^JustSimple \d+\.\d+\.\d+/);
});

test("scanner arguments preserve quoted paths, Windows backslashes, repeated inputs and exact method signatures", () => {
  const request = parseScannerArgs(`"C:\\审计 目录\\app.jar" --dependency "lib one.jar" --dependency lib2.jar --facts facts.json
    --mode component --entry 'demo.Sample#entry(Ljava/lang/Object;)Ljava/lang/Object;' --sink 'demo/Sample#sink(Ljava/lang/Object;)Ljava/lang/Object;'
    --steps 1000 --knowledge selected --knowledge-id reference`, process.cwd(), javaHome);
  assert.ok(request);
  assert.equal(request.options.input, resolve("C:\\审计 目录\\app.jar"));
  assert.deepEqual(request.options.dependencies, [resolve("lib one.jar"), resolve("lib2.jar")]);
  assert.equal(request.scan.entries[0]?.owner, "demo/Sample");
  assert.equal(request.scan.entries[0]?.descriptor, "(Ljava/lang/Object;)Ljava/lang/Object;");
  assert.equal(request.scan.mode, "COMPONENT");
  assert.deepEqual(request.scan.budgets, { steps: 1000 });
  assert.deepEqual(request.scan.knowledgeIds, ["reference"]);
  for (const args of ["file --steps 0", "file --steps 1.5", "file --steps 999999999999", "file --mode typo", "file --knowledge selected",
    "file --knowledge none --knowledge-id x", "file --unknown", "file another", "'unclosed", "file --entry bad", 'file --dependency ""', 'file --facts ""', 'file --output ""']) {
    assert.throws(() => parseScannerArgs(args, process.cwd(), javaHome), args);
  }
  assert.throws(() => parseScannerArgs("file", process.cwd()), /jdk-home/);
  assert.equal(parseScannerArgs("--help", process.cwd()), undefined);
  const original = parseScannerArgs("local.class --mode component --dependency existing.jar --facts input.json", process.cwd(), javaHome)!;
  const same = parseScannerArgs("", process.cwd(), javaHome, { previous: original });
  assert.equal(same?.options.staticData, resolve("input.json"));
  const different = parseScannerArgs("--jdk-home alternate-jdk", process.cwd(), javaHome, { previous: original });
  assert.equal(different?.options.input, original.options.input);
  assert.equal(different?.options.jdk, resolve("alternate-jdk"));
  assert.deepEqual(different?.options.dependencies, []);
  assert.equal(different?.options.staticData, undefined);
  assert.equal(different?.scan.mode, "APPLICATION");
});


test("workspace, JDK and Maven commands persist scanner preferences and rebuild the native cwd", { timeout: 30000 }, async () => {
  process.env.PI_OFFLINE = "1";
  const agentDir = join(directory, "preferences-agent");
  const workspace = join(directory, "新工作目录");
  const repository = join(directory, "maven repository");
  await mkdir(workspace); await mkdir(repository);
  const libraryClasses = join(directory, "library classes");
  const libraryJar = join(repository, "example", "library", "1.2.3", "library-1.2.3.jar");
  await mkdir(libraryClasses); await mkdir(join(repository, "example", "library", "1.2.3"), { recursive: true });
  const source = join(directory, "Library.java");
  await writeFile(source, 'public class Library { static { if (System.nanoTime() != 0) throw new AssertionError("Never execute"); } public static Object value(Object input) { return input; } }', "utf8");
  await promisify(execFile)(join(javaHome, "bin", "javac"), ["-encoding", "UTF-8", "-d", libraryClasses, source]);
  await promisify(execFile)(join(javaHome, "bin", "jar"), ["cf", libraryJar, "-C", libraryClasses, "."]);
  await modelConfig(agentDir);
  const runtime = await createScannerRuntime({ cwd: directory, jdk: javaHome, agentDir });
  const tui = new InteractiveMode(runtime, { terminal: new TestTerminal() });
  try {
    await tui.init();
    await runtime.session.prompt(`/maven-home "${repository}"`);
    await runtime.session.prompt(`/jdk-home "${javaHome}"`);
    await runtime.session.prompt(`/maven-home "${join(directory, 'missing-repository')}"`);
    await runtime.session.prompt(`/jdk-home "${join(directory, 'missing-jdk')}"`);
    const commandErrors: string[] = [];
    const stopErrors = runtime.session.extensionRunner.onError(error => commandErrors.push(error.error));
    try { await runtime.session.prompt(`/workspace "${workspace}"`); }
    finally { stopErrors(); }
    assert.deepEqual(commandErrors, [], "workspace replacement must not use the previous command context");
    assert.equal(runtime.cwd, await realpath(workspace));
    assert.deepEqual(runtime.session.getActiveToolNames(), []);
    const settings = await ScannerSettings.load(agentDir);
    assert.equal(settings.value.mavenRepository, repository);
    assert.equal(settings.value.workspace, runtime.cwd);
    assert.ok(settings.value.jdk);
    assert.ok(settings.value.jdks.includes(settings.value.jdk));
    const parsed = parseScannerArgs(`"${classes}" --dependency example:library:1.2.3`, runtime.cwd, settings.value.jdk,
      { mavenRepository: settings.value.mavenRepository });
    assert.equal(parsed?.options.dependencies?.[0], join(repository, "example", "library", "1.2.3", "library-1.2.3.jar"));
    await runtime.session.prompt(`/target "${classes}"`);
    await runtime.session.prompt("/scan-only --mode component --knowledge none --steps 9 --output workspace-results");
    assert.ok((await readdir(join(workspace, "workspace-results"))).includes("report.json"));
    await runtime.session.prompt(`/agent --dependency example:library:1.2.3`);
    const find = runtime.session.agent.state.tools.find(tool => tool.name === "scanner_find_symbols");
    assert.ok(find);
    const symbols = await find.execute("cache", { query: "Library#value", scope: "candidates" }, new AbortController().signal);
    assert.equal((symbols.details as { summary: { methods: number } }).summary.methods, 1);
    assert.throws(() => parseScannerArgs(`"${classes}" --dependency '..:library:1.0'`, runtime.cwd, javaHome, { mavenRepository: repository }), /Invalid Maven/);
  } finally { tui.stop(); await runtime.dispose(); }
  const reopened = await createScannerRuntime({ agentDir });
  try { assert.equal(reopened.cwd, workspace); }
  finally { await reopened.dispose(); }
});


test("scanner settings preserve concurrent changes and reject malformed persisted input", async () => {
  const agentDir = join(directory, "validation-agent");
  const settings = await ScannerSettings.load(agentDir);
  await Promise.all([settings.save({ workspace: directory }), settings.save({ mavenRepository: classes })]);
  const saved = await ScannerSettings.load(agentDir);
  assert.equal(saved.value.workspace, directory);
  assert.equal(saved.value.mavenRepository, classes);
  await assert.rejects(settings.save({ jdk: "relative/path" }), /absolute path/);
  await settings.save({ jdk: javaHome });
  const setup = parseScannerArgs(`"${classes}"`, directory, javaHome)!;
  assert.throws(() => restoreSetup({ ...setup, options: { ...setup.options, java: "other-program" } }), /Invalid saved/);
  assert.throws(() => restoreSetup({ ...setup, options: { ...setup.options, input: "relative" } }), /Invalid saved/);
  await writeFile(settings.file, Buffer.from([0xff]));
  await assert.rejects(ScannerSettings.load(agentDir), /Reading/);
});


test("cancellation stops a bridge that has not announced readiness", { timeout: 15000 }, async () => {
  const protocol = join(directory, "protocol"); await mkdir(protocol);
  const host = join(directory, "ToolMain.java"), started = join(directory, "host-started");
  await writeFile(host, `
    package io.just.agent.bridge;
    public class ToolMain {
      public static void main(String[] args) throws Exception {
        java.nio.file.Files.createFile(java.nio.file.Path.of(${JSON.stringify(started)}));
        System.in.read();
      }
    }`, "utf8");
  await promisify(execFile)(join(javaHome, "bin", "javac"), ["-encoding", "UTF-8", "-d", protocol, host]);
  const controller = new AbortController();
  const opening = ScannerBridge.open({ input: classes, jdk: javaHome, bridgeJar: protocol, startupTimeoutMs: 10000 }, controller.signal);
  try {
    await Promise.all([
      assert.rejects(opening, { name: "AbortError" }),
      waitFor(() => existsSync(started), "Bridge process did not start", 5000).then(() => controller.abort()),
    ]);
  } finally { controller.abort(); }
});
