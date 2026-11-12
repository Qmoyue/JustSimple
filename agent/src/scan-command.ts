import { lstat, realpath, stat } from "node:fs/promises";
import { basename, join } from "node:path";
import { randomUUID } from "node:crypto";
import type { ExtensionCommandContext, ExtensionContext, ExtensionFactory, SessionManager, SettingsManager } from "@earendil-works/pi-coding-agent";
import { matchesKey, Text } from "@earendil-works/pi-tui";
import type { TSchema } from "typebox";
import type { Json } from "./bridge.ts";
import { parseScannerArgs, restoreSetup, scannerUsage, type ScanSetup } from "./scan-args.ts";
import type { ScannerSettings } from "./settings.ts";
import { choosePath, commandPath, input, select, showDocument } from "./ui.ts";
import { createScannerTools } from "./tools.ts";
import { checkJdk, inspectTarget, inputIdentity } from "./environment.ts";
import { showScreen, type ScreenState } from "./screen.ts";
import { Audit } from "./audit.ts";
import { auditTools } from "./audit-tools.ts";
import { commands, installInterface, type Command } from "./interface.ts";
import { missing } from "./files.ts";

type Scanner = Awaited<ReturnType<typeof createScannerTools>>;

/** Owns configured input and running jobs; analysis, blackboard and Pi keep their own state. */
export function scannerCommands(settings: ScannerSettings, sessionManager: SessionManager,
  switchWorkspace: (cwd: string) => Promise<boolean>, agentDir: string, nativeSettings: SettingsManager): ExtensionFactory {
  return pi => {
    const screen: ScreenState = { page: "home" };
    let current: { scanner: Scanner; audit: Audit } | undefined;
    let setup: ScanSetup | undefined;
    let running: { controller: AbortController; task: Promise<void> } | undefined;
    let ui: ExtensionContext | undefined;
    let registeredPhase: string | undefined;
    installInterface(pi, nativeSettings, command);

    pi.registerMessageRenderer("scanner-result", message => new Text(typeof message.content === "string" ? message.content : "", 1, 0));
    function refresh(ctx = ui) {
      if (!ctx) return;
      ui = ctx;
      if (screen.page === "agent" && current) {
        const phase = current.audit.phase;
        if (registeredPhase !== phase) {
          for (const tool of auditTools(current.audit)) pi.registerTool<TSchema, Json>(tool);
          registeredPhase = phase;
        }
        pi.setActiveTools(current.audit.toolNames);
        const board = current.audit.overview();
        ctx.ui.setStatus("audit", `${phase === "report" ? "报告" : "探索"} · ${board.items} 个问题 · 焦点 ${board.focus ?? "无"}`);
      } else { pi.setActiveTools([]); ctx.ui.setStatus("audit", undefined); }
      showScreen(ctx, settings.value, screen, configuredSetup()?.scan);
    }
    async function closeInput() {
      const previous = current; current = undefined; registeredPhase = undefined;
      if (previous) await previous.scanner.close();
    }
    async function job(ctx: ExtensionContext, activity: string, action: (signal: AbortSignal) => Promise<void>) {
      if (running) throw new Error("A scanner job is already active; Esc cancels it");
      const controller = new AbortController();
      const unsubscribe = ctx.hasUI ? ctx.ui.onTerminalInput(data => {
        if (matchesKey(data, "escape")) { controller.abort(); return { consume: true }; }
        return undefined;
      }) : undefined;
      screen.activity = activity; refresh(ctx);
      const task = Promise.resolve().then(() => action(controller.signal));
      running = { controller, task };
      try { await task; return true; }
      catch (error) {
        if (controller.signal.aborted) { ctx.ui.notify("已取消，保留已有配置和结果。", "info"); return false; }
        throw error;
      } finally { unsubscribe?.(); running = undefined; screen.activity = undefined; refresh(ctx); }
    }
    function configuredSetup() {
      return setup && setup.options.input === settings.value.target && setup.options.jdk === settings.value.jdk ? setup : undefined;
    }
    function request(args: string, ctx: ExtensionContext) {
      const { target, jdk, mavenRepository } = settings.value;
      if (!target) throw new Error("先使用 /target 选择目标。");
      const previous = configuredSetup();
      const result = parseScannerArgs(args, ctx.cwd, jdk, { previous, input: previous ? undefined : target, mavenRepository });
      if (!result) throw new Error(scannerUsage);
      return result;
    }
    async function ready(ctx: ExtensionContext, options: ScanSetup["options"], signal: AbortSignal) {
      signal.throwIfAborted();
      const target = screen.target?.path === options.input ? screen.target : await inspectTarget(options.input, signal);
      const jdk = await checkJdk(options.jdk);
      signal.throwIfAborted();
      if (options.input === settings.value.target) screen.target = target;
      if (options.jdk === settings.value.jdk) screen.jdkVersion = jdk;
      const version = Number(/^1\.(\d+)|^(\d+)/.exec(jdk)?.slice(1).find(Boolean));
      if (target.minimumJdk && version < target.minimumJdk) ctx.ui.notify(`目标含 JDK ${target.minimumJdk} 字节码，当前类库 ${jdk}。按所选 JDK 静态分析，运行时与依赖要求需核对；/jdk-home 可切换。`, "warning");
      refresh(ctx);
    }
    pi.on("session_start", async (_event, ctx) => {
      ui = ctx; refresh(ctx);
      const saved = [...ctx.sessionManager.getBranch()].reverse().find(entry => entry.type === "custom" && entry.customType === "scanner-target");
      try {
        if (saved?.type === "custom") {
          setup = restoreSetup(saved.data);
          await settings.save({ target: setup.options.input, jdk: setup.options.jdk });
        }
        const jdk = settings.value.jdk ?? process.env.JAVA_HOME;
        if (jdk) {
          const path = await realpath(jdk); screen.jdkVersion = await checkJdk(path);
          if (settings.value.jdk !== path) await settings.save({ jdk: path, jdks: [...settings.value.jdks, path] });
        }
        if (settings.value.target) await job(ctx, "核对目标", async signal => { screen.target = await inspectTarget(settings.value.target!, signal); });
      } catch (error) { ctx.ui.notify(`配置需要核对：${error instanceof Error ? error.message : error}`, "warning"); }
      refresh(ctx);
    });
    pi.on("input", (_event, ctx) => {
      if (screen.page !== "agent") { ctx.ui.notify("先完成配置，使用 /scan-only 扫描或 /agent 进入交互。", "info"); refresh(ctx); return { action: "handled" }; }
      if (!current || !ctx.model || !ctx.modelRegistry.hasConfiguredAuth(ctx.model)) {
        ctx.ui.notify("交互审计需要目标、JDK 和可用模型；/login 认证，/model 选择。", "warning"); return { action: "handled" };
      }
      return { action: "continue" };
    });
    pi.on("before_agent_start", (_event, ctx) => {
      refresh(ctx);
      return { message: { customType: "audit-index", display: false,
        content: `JustSimple task: ${JSON.stringify(current?.audit.overview())}. Read skill_read(index) when starting; inspect board_read after resuming. Old live evidence references expire when input is rebuilt.` } };
    });
    pi.on("model_select", (_event, ctx) => refresh(ctx));
    pi.on("session_compact", (_event, ctx) => {
      if (current) pi.sendMessage({ customType: "audit-index", display: false,
        content: `Task continues: ${JSON.stringify(current.audit.overview())}. Read board_read for durable evidence and unresolved conditions.` }, { triggerTurn: false });
      refresh(ctx);
    });
    pi.on("tool_call", event => {
      if (screen.page !== "agent" || !current?.audit.allowed(event.toolName)) return { block: true, reason: "Only current task tools allowed in the current audit phase are available." };
      return undefined;
    });
    pi.on("user_bash", () => ({ result: { output: "Shell execution is disabled in JustSimple", exitCode: 1, cancelled: false, truncated: false } }));
    pi.on("session_shutdown", async () => {
      running?.controller.abort();
      try { await running?.task; } catch { /* The command owns and reports its failure. */ }
      await closeInput();
    });

    function command(name: Command, handler: (args: string, ctx: ExtensionCommandContext) => Promise<void | "replaced">) {
      pi.registerCommand(name, { description: commands[name], async handler(args, ctx) {
        if (running) { ctx.ui.notify("正在读取或扫描，Esc 可取消。", "warning"); return; }
        let replaced = false;
        try { await ctx.waitForIdle(); replaced = await handler(args, ctx) === "replaced"; }
        catch (error) { ctx.ui.notify(error instanceof Error ? error.message : String(error), "error"); }
        finally { if (!replaced) refresh(ctx); }
      } });
    }
    command("home", async (_args, ctx) => {
      await closeInput(); screen.page = "home"; refresh(ctx);
    });
    command("workspace", async (args, ctx) => {
      const path = args.trim() ? commandPath(args, ctx.cwd) : await choosePath(ctx, "工作目录", "directory");
      if (!path) return;
      const directory = await realpath(path);
      if (!(await stat(directory)).isDirectory()) throw new Error(`Not a directory: ${directory}`);
      if (directory !== ctx.cwd && await switchWorkspace(directory)) return "replaced";
    });
    command("target", async (args, ctx) => {
      const path = args.trim() ? commandPath(args, ctx.cwd) : await choosePath(ctx, "选择目标", "target");
      if (!path) return;
      await job(ctx, "读取 classfile 版本", async signal => {
        const target = await inspectTarget(path, signal); signal.throwIfAborted();
        await settings.save({ target: target.path }); await closeInput();
        setup = undefined; screen.target = target; screen.page = "home";
        ctx.ui.notify(`目标已选择 · 字节码要求 JDK ${target.minimumJdk || "未知"}${target.partial ? "（部分检查，依赖要求需另行核对）" : "+"}；/jdk-home 选择运行时类库。`, "info");
      });
    });
    command("jdk-home", async (args, ctx) => {
      let path = args.trim() ? commandPath(args, ctx.cwd) : undefined;
      if (!path) {
        const known = [...new Set([settings.value.jdk, ...settings.value.jdks, process.env.JAVA_HOME].filter((path): path is string => !!path))];
        const choice = await select(ctx, "目标 JDK · 静态分析使用其类库", [...known, "新增 JDK…"]);
        if (!choice) return;
        path = choice === "新增 JDK…" ? await choosePath(ctx, "JDK 安装目录", "directory") : choice;
      }
      if (!path) return;
      path = await realpath(path); const version = await checkJdk(path);
      await settings.save({ jdk: path, jdks: [...settings.value.jdks, path] }); await closeInput();
      setup = undefined; screen.jdkVersion = version; screen.page = "home";
    });
    command("maven-home", async (args, ctx) => {
      const path = args.trim() ? commandPath(args, ctx.cwd) : await choosePath(ctx, "Maven 本地仓库", "directory");
      if (!path) return;
      const repository = await realpath(path);
      if (!(await stat(repository)).isDirectory()) throw new Error(`Not a directory: ${repository}`);
      await settings.save({ mavenRepository: repository });
    });
    command("scan-only", async (args, ctx) => {
      if (args.trim() === "--help") { ctx.ui.notify(scannerUsage, "info"); return; }
      let selectedOutput: string | undefined;
      if (!args.trim()) {
        if (!settings.value.target) throw new Error("先使用 /target 选择目标。");
        const modes = ["应用入口 · 查找已支持的应用边界（默认）", "组件能力 · 以公共方法为边界"];
        const mode = await select(ctx, "扫描模式 · 沿用当前目标的选择，可按 Enter 确认", modes, configuredSetup()?.scan.mode === "COMPONENT" ? 1 : 0);
        if (mode === undefined) return;
        const extra = await input(ctx, "可选参数（留空沿用当前目标设置）", "如 --dependency lib.jar --steps 100000；完整说明见 /help");
        if (extra === undefined) return;
        const output = await input(ctx, "输出目录（留空保存到当前工作目录）", ".local/scans/scan-<ID>");
        if (output === undefined) return;
        args = `--mode ${mode === modes[1] ? "component" : "application"} ${extra}`;
        if (output.trim()) selectedOutput = commandPath(output, ctx.cwd);
      }
      const scan = request(args, ctx);
      if (selectedOutput !== undefined) scan.output = selectedOutput;
      const output = scan.output ?? join(ctx.cwd, ".local", "scans", `scan-${randomUUID()}`);
      if (scan.output) {
        const existing = await lstat(output).catch(error => {
          if (missing(error)) return undefined;
          throw error;
        });
        if (existing) throw new Error(`Report directory already exists: ${output}`);
      }
      screen.page = "scan"; screen.scan = { state: "准备扫描", target: scan.options.input, output };
      let scanner: Scanner | undefined;
      try {
        const finished = await job(ctx, "静态扫描", async signal => {
          await ready(ctx, scan.options, signal);
          await closeInput();
          scanner = await createScannerTools(scan.options, signal);
          const result = await scanner.bridge.call("scan_target", scan.scan, signal, progress => { screen.scan!.progress = progress; refresh(ctx); });
          if (!("summary" in result)) throw new Error("Scanner returned no summary");
          screen.scan!.state = "写入报告"; refresh(ctx);
          await scanner.bridge.call("export_scan", { resultRef: result.resultRef, output }, signal);
          screen.scan!.state = `${result.summary.execution === "TRUNCATED" ? "预算或范围受限" : "已完成"} · ${result.summary.outcome === "FINDINGS" ? "存在候选" : "未发现候选"}`;
          screen.scan!.summary = `候选 ${result.summary.findings} · 关系 ${result.summary.relations} · 断点 ${result.summary.breakpoints}\nreport.json · report.md · input-requirements.json`;
          sessionManager.appendMessage({ role: "user", content: [{ type: "text", text: `/scan-only ${scan.options.input}` }], timestamp: Date.now() });
          pi.appendEntry("scanner-target", scan); setup = scan;
          pi.sendMessage({ customType: "scanner-result", display: false, content: `${screen.scan!.state}\n输出 ${output}`, details: result }, { triggerTurn: false });
        });
        if (!finished) screen.scan.state = "已取消";
      } catch (error) { screen.scan.state = "失败"; screen.scan.error = error instanceof Error ? error.message : String(error); throw error; }
      finally { await scanner?.close(); refresh(ctx); }
    });
    command("agent", async (args, ctx) => {
      if (!ctx.model || !ctx.modelRegistry.hasConfiguredAuth(ctx.model)) throw new Error("先用 /login 完成认证，再用 /model 选择审计模型；/config 调整思考设置。");
      if (current && !args.trim()) { screen.page = "agent"; refresh(ctx); return; }
      const analysis = request(args, ctx);
      await job(ctx, "准备审计工具与任务记录", async signal => {
        let scanner: Scanner | undefined;
        try {
          await ready(ctx, analysis.options, signal);
          const scope = await inputIdentity(analysis.options, signal);
          scanner = await createScannerTools(analysis.options, signal);
          const audit = await Audit.open(agentDir, sessionManager.getSessionId(), scope, scanner.bridge, analysis.options, () => refresh());
          signal.throwIfAborted();
          await closeInput();
          current = { scanner, audit }; scanner = undefined;
          for (const tool of current.scanner.tools) pi.registerTool<TSchema, Json>(tool);
          setup = analysis; pi.appendEntry("scanner-target", analysis);
          registeredPhase = undefined; screen.page = "agent";
          ctx.ui.notify(`审计就绪 · ${basename(analysis.options.input)} · 输入提示词开始；/board 查看黑板，/home 返回配置。`, "info");
        } finally { await scanner?.close(); }
      });
    });
    command("board", async (args, ctx) => {
      if (!current) throw new Error("先使用 /agent 打开审计任务。");
      if (args.trim()) {
        const result = await current.audit.read({ view: args.trim().startsWith("E") ? "evidence" : "graph", id: args.trim(), limit: 20 });
        await showDocument(ctx, `审计黑板 · ${args.trim()}`, JSON.stringify(result, null, 2)); return;
      }
      let offset = 0;
      while (true) {
        const result = await current.audit.read({ view: "overview", offset, limit: 20 });
        const index = result as { version: number; items: number; page: { next: number; data: { id: string; question: string; status: string }[] } };
        const labels = index.page.data.map(item => `${item.id} · ${item.status} · ${item.question}`);
        const choice = await select(ctx, `审计黑板 · 版本 ${index.version} · ${index.items} 个问题`,
          [...labels, ...(offset ? ["上一页"] : []), ...(index.page.next !== -1 ? ["下一页"] : []), "返回交互"]);
        if (choice === undefined || choice === "返回交互") return;
        if (choice === "上一页") { offset = Math.max(0, offset - 20); continue; }
        if (choice === "下一页") { offset = index.page.next; continue; }
        const item = index.page.data[labels.indexOf(choice)];
        if (!item) throw new Error("The selected board item is no longer available");
        const detail = await current.audit.read({ view: "item", id: item.id, characters: 16000 });
        const graph = await current.audit.read({ view: "graph", id: item.id });
        await showDocument(ctx, `${item.id} · ${item.question}`, `${JSON.stringify(detail, null, 2)}\n\n局部依赖（dependsOn 为问题依赖）\n${JSON.stringify(graph, null, 2)}`);
      }
    });
  };
}
