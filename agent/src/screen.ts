import type { ExtensionContext } from "@earendil-works/pi-coding-agent";
import { Text, truncateToWidth, visibleWidth } from "@earendil-works/pi-tui";
import { basename } from "node:path";
import type { ScannerSettings } from "./settings.ts";
import type { TargetInfo } from "./environment.ts";
import type { ScanProgress } from "./bridge.ts";
import { thinkingLabel } from "./interface.ts";
import type { ScanRequest } from "./scan-args.ts";

export interface ScreenState {
  page: "home" | "scan" | "agent";
  target?: TargetInfo;
  jdkVersion?: string;
  activity?: string;
  scan?: { state: string; target: string; output: string; progress?: ScanProgress; summary?: string; error?: string };
}

/** Derives terminal views; input, scan and audit state remain with their services. */
export function showScreen(ctx: ExtensionContext, preferences: ScannerSettings["value"], state: ScreenState, scanDefaults?: ScanRequest) {
  ctx.ui.setFooter((_tui, theme, data) => ({
    invalidate() {},
    render(width) {
      const usage = state.page === "agent" ? ctx.getContextUsage() : undefined;
      const status = state.page === "agent" ? [data.getExtensionStatuses().get("audit"),
        usage?.percent == null ? undefined : `上下文 ${Math.round(usage.percent)}%`, "Esc 中断 · /home 首页"]
        : [state.activity ? "Esc 取消当前任务" : "输入 / 选择操作", "/help 帮助 · Ctrl+D 退出"];
      return new Text(theme.fg("dim", status.filter(Boolean).join(" · ")), 1, 0).render(width);
    },
  }));
  if (state.page === "agent") { ctx.ui.setWidget("justsimple", undefined); return; }
  ctx.ui.setWidget("justsimple", (_tui, theme) => ({
    invalidate() {},
    render(width: number) {
      const room = Math.max(1, width - 14);
      const fit = (value: string, available = room) => truncateToWidth(value, Math.max(1, available), "…");
      const path = (value: string) => {
        if (room < 4 || visibleWidth(value) <= room) return fit(value);
        const tail = fit(basename(value), Math.floor(room * 0.6));
        return `${truncateToWidth(value, room - visibleWidth(tail) - 1, "")}…${tail}`;
      };
      let lines: string[];
      if (state.page === "scan" && state.scan) {
        const scan = state.scan, progress = scan.progress;
        const stages: Record<string, string> = { READ: "读取输入", ENTRIES: "发现入口", KNOWLEDGE: "匹配知识", ANALYSIS: "分析传播", RECOVERY: "汇总证据", WRITE: "写入报告" };
        lines = ["", `静态扫描 · ${scan.state}`, path(scan.target), "",
          ...(progress ? [`阶段 ${stages[progress.stage] ?? progress.stage}`, `入口 ${progress.entries} · 分析上下文 ${progress.contexts}`, `步骤 ${progress.steps} · 关系 ${progress.relations} · 待处理 ${progress.queued}`] : ["读取输入与建立分析范围"]),
          "", `输出 ${path(scan.output)}`, ...(scan.summary ? ["", scan.summary] : []), ...(scan.error ? ["", theme.fg("error", scan.error)] : []),
          "", state.activity ? "" : "/home 返回首页 · /agent 进入审计"];
      } else {
        const target = state.target?.path === preferences.target ? state.target : undefined;
        const model = ctx.model?.provider === "unknown" ? undefined : ctx.model;
        const knowledge = scanDefaults?.knowledge === "none" ? "无参考知识" : scanDefaults?.knowledge === "selected" ? "所选知识" : "知识引导";
        const budgets = Object.entries(scanDefaults?.budgets ?? {}).map(([key, value]) => `${key}=${value}`).join(" · ") || "扫描器预算";
        const auth = model && ctx.modelRegistry.hasConfiguredAuth(model) ? "已认证" : "/login 认证";
        lines = ["", "Java 静态分析", "",
          `目标   ${preferences.target ? path(preferences.target) : "待选择 · /target"}`,
          ...(target ? [`       ${target.classes} 个 class · 至少 JDK ${target.minimumJdk || "未知"}${target.partial ? " · 部分检查" : ""}${target.multiReleaseMax ? ` · 多版本最高 ${target.multiReleaseMax}` : ""}`] : []),
          `JDK    ${state.jdkVersion && preferences.jdk ? `${state.jdkVersion} · ${path(preferences.jdk)}` : "待选择 · /jdk-home"}`,
          `目录   ${path(ctx.cwd)}`,
          `依赖库 ${path(preferences.mavenRepository)}`,
          model ? `模型   ${fit(`${model.provider}/${model.id}`, width - visibleWidth(auth) - 12)} · ${auth}` : "模型   未配置 · /login /model",
          `思考   ${thinkingLabel(model ? ctx.thinkingLevel : undefined)} · /config 设置`, "",
          `${scanDefaults ? "当前" : "默认"}扫描 · ${scanDefaults?.mode === "COMPONENT" ? "组件能力" : "应用入口"} · ${knowledge}`,
          fit(budgets),
          "", target && state.jdkVersion ? "/scan-only 扫描 · /agent 审计" : "/target 目标 · /jdk-home 类库",
          ...(state.activity ? ["", state.activity] : [])];
      }
      return new Text(lines.join("\n"), 1, 0).render(width);
    },
  }));
}
