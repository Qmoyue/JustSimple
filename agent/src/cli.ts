#!/usr/bin/env node
import { resolve, join } from "node:path";
import { parseArgs } from "node:util";
import { VERSION } from "./version.ts";

process.stdout.setDefaultEncoding("utf8");
process.stderr.setDefaultEncoding("utf8");

try {
  const { values } = parseArgs({ options: { help: { type: "boolean", short: "h" }, version: { type: "boolean" }, cwd: { type: "string" }, "jdk-home": { type: "string" }, "agent-dir": { type: "string" } } });
  if (values.version) process.stdout.write(`JustSimple ${VERSION}\n`);
  else if (values.help) {
    process.stdout.write(`JustSimple ${VERSION} · Java 静态分析\n\npnpm agent [--cwd <目录>] [--jdk-home <JDK>] [--agent-dir <状态目录>]\n\n/target        选择 JAR、WAR、class 或类目录\n/scan-only     完整静态扫描，无需模型\n/agent         进入交互审计\n/board [Q/E编号] 查看问题与持久证据\n/config        审计与展示设置\n/login /model  模型认证与选择\n/new /resume   新建或恢复会话\n/workspace /jdk-home /maven-home  环境配置\n/home /help /quit  首页、参数帮助与退出\n\n路径相对工作目录。Esc 中断当前任务。\n`);
  } else {
    if (!process.stdin.isTTY || !process.stdout.isTTY) throw new Error("JustSimple TUI requires an interactive terminal");
    const agentDir = resolve(values["agent-dir"] ?? join(process.cwd(), ".local", "agent"));
    process.env.PI_CODING_AGENT_DIR = agentDir;
    // The embedded SDK is updated with this product, without standalone SDK update prompts.
    process.env.PI_OFFLINE = "1";
    const [{ InteractiveMode }, { createScannerRuntime }, { ProcessTerminal }] = await Promise.all([
      import("@earendil-works/pi-coding-agent"), import("./session.ts"), import("@earendil-works/pi-tui"),
    ]);
    const runtime = await createScannerRuntime({ cwd: values.cwd, agentDir, jdk: values["jdk-home"] });
    class ProductTerminal extends ProcessTerminal {
      override setTitle() { super.setTitle(`JustSimple ${VERSION}`); }
    }
    const tui = new InteractiveMode(runtime, { terminal: new ProductTerminal(), manageTools: false, showResumeHint: false });
    try { await tui.run(); } finally { tui.stop(); await runtime.dispose(); }
  }
} catch (error) {
  process.stderr.write(`JustSimple: ${error instanceof Error ? error.message : String(error)}\n`);
  process.exitCode = 1;
}
