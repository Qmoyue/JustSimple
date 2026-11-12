import { readFile, realpath, rm, stat } from "node:fs/promises";
import { resolve, join } from "node:path";
import { fileURLToPath } from "node:url";
import {
  createAgentSessionRuntime, createAgentSessionServices, createAgentSessionFromServices,
  SessionManager, SettingsManager, type AgentSessionRuntime, type CreateAgentSessionRuntimeFactory,
} from "@earendil-works/pi-coding-agent";
import { scannerCommands } from "./scan-command.ts";
import { ScannerSettings } from "./settings.ts";
import { checkJdk } from "./environment.ts";
import { resource } from "./audit.ts";

export async function createScannerRuntime(options: { cwd?: string; jdk?: string; agentDir?: string; sessionManager?: SessionManager } = {}) {
  const agentDir = resolve(options.agentDir ?? join(options.cwd ?? process.cwd(), ".local", "agent"));
  const settings = await ScannerSettings.load(agentDir);
  const cwd = resolve(options.cwd ?? settings.value.workspace ?? process.cwd());
  if (!(await stat(cwd)).isDirectory()) throw new Error(`Workspace is not a directory: ${cwd}`);
  if (options.jdk) {
    const jdk = await realpath(resolve(cwd, options.jdk));
    await checkJdk(jdk);
    await settings.save({ jdk, jdks: [...settings.value.jdks, jdk] });
  }
  let runtime: AgentSessionRuntime;
  async function switchWorkspace(next: string) {
    const manager = SessionManager.create(next, join(agentDir, "sessions"));
    const file = manager.getSessionFile()!;
    const { workspace, target } = settings.value;
    await settings.save({ workspace: next, target: undefined });

    async function restore(cause?: unknown) {
      const restored = await Promise.allSettled([settings.save({ workspace, target }), rm(file, { force: true })]);
      const failures: unknown[] = restored.flatMap(result => result.status === "rejected" ? [result.reason] : []);
      if (failures.length) {
        if (cause !== undefined) failures.unshift(cause);
        throw new AggregateError(failures, `恢复工作目录失败\n${failures.map(String).join("\n")}`);
      }
    }

    try {
      // Pi persists the new session when its first user command is appended.
      manager.appendMessage({ role: "user", content: [{ type: "text", text: `/workspace ${next}` }], timestamp: Date.now() });
      if (!(await runtime.switchSession(file)).cancelled) return true;
    } catch (error) {
      // The SDK may already have installed the new session before UI rebinding fails.
      if (runtime.session.sessionFile !== file) await restore(error);
      throw error;
    }
    await restore();
    return false;
  }
  const instructions = await readFile(resource("AGENTS.md"), "utf8");
  const sdkPackage = new URL("../package.json", import.meta.resolve("@earendil-works/pi-coding-agent"));
  const { version: sdkVersion } = JSON.parse(await readFile(sdkPackage, "utf8")) as { version: string };
  const create: CreateAgentSessionRuntimeFactory = async ({ cwd, agentDir, sessionManager, sessionStartEvent }) => {
    const nativeSettings = SettingsManager.create(cwd, agentDir);
    // The host owns startup presentation; SDK release notices belong to product upgrades.
    if (nativeSettings.getQuietStartup() !== true) nativeSettings.setQuietStartup(true);
    if (nativeSettings.getLastChangelogVersion() !== sdkVersion) nativeSettings.setLastChangelogVersion(sdkVersion);
    if (nativeSettings.getDoubleEscapeAction() !== "none") nativeSettings.setDoubleEscapeAction("none");
    if (nativeSettings.getFullscreenCopyOnSelect()) nativeSettings.setFullscreenCopyOnSelect(false);
    if (nativeSettings.getSettings().hideThinkingBlock === undefined) nativeSettings.setHideThinkingBlock(true);
    if (nativeSettings.getEnableInstallTelemetry()) nativeSettings.setEnableInstallTelemetry(false);
    if (nativeSettings.getEnableAnalytics()) nativeSettings.setEnableAnalytics(false);
    await nativeSettings.flush();
    const services = await createAgentSessionServices({ cwd, agentDir, settingsManager: nativeSettings,
      resourceLoaderOptions: { noExtensions: true, noContextFiles: true, noSkills: true, noPromptTemplates: true,
        agentsFilesOverride: () => ({ agentsFiles: [{ path: fileURLToPath(resource("AGENTS.md")), content: instructions }] }),
        extensionFactories: [scannerCommands(settings, sessionManager, switchWorkspace, agentDir, nativeSettings)] },
    });
    const result = await createAgentSessionFromServices({ services, sessionManager, sessionStartEvent,
      tools: ["scanner_*", "board_read", "board_update", "skill_read", "audit_phase", "write_report"], noTools: "builtin" });
    return { ...result, services, diagnostics: services.diagnostics };
  };
  runtime = await createAgentSessionRuntime(create, { cwd, agentDir,
    sessionManager: options.sessionManager ?? SessionManager.create(cwd, join(agentDir, "sessions")) });
  return runtime;
}
