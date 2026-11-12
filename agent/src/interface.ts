import { CustomEditor, type ExtensionAPI, type ExtensionCommandContext, type SettingsManager } from "@earendil-works/pi-coding-agent";
import { Text, type AutocompleteProvider } from "@earendil-works/pi-tui";
import { scannerUsage } from "./scan-args.ts";
import { select, showDocument } from "./ui.ts";
import { VERSION } from "./version.ts";

export const commands = {
  target: "选择 JAR、WAR、class 或类目录", "scan-only": "静态扫描并导出报告，无需模型", agent: "进入交互审计", board: "查看问题与持久证据",
  home: "返回首页并释放分析进程", workspace: "选择工作目录", "jdk-home": "选择目标 JDK 类库", "maven-home": "设置本地依赖仓库",
  config: "思考、上下文与工具展示设置", help: "JustSimple 用法与参数说明",
  login: "配置模型服务认证", logout: "移除模型服务认证", model: "选择审计模型",
  new: "新建审计会话", resume: "恢复已有会话", compact: "整理当前会话上下文", quit: "退出 JustSimple",
} as const;
export type Command = keyof typeof commands;

const levels = { off: "关闭", minimal: "极简", low: "轻量", medium: "标准", high: "深入", xhigh: "更深入" } as const;
export function thinkingLabel(level: string | undefined) { return level ? levels[level as keyof typeof levels] ?? level : "随模型"; }
export const interfaceHelp = `JustSimple · Java 静态分析

开始：/target 选择目标，/jdk-home 选择类库，然后 /scan-only 扫描或 /agent 交互审计。
首页输入普通文本不会调用模型。审计中直接输入问题；生成期间可继续输入纠偏，Esc 中断当前任务。

${Object.entries(commands).map(([name, description]) => `/${name}  ${description}`).join("\n")}

模型认证、模型选择与会话使用内置流程。/config 只展示本项目需要的设置；/settings 也会打开该页。
路径相对工作目录。↑↓ 翻阅，Enter 确定，Esc 返回；Ctrl+O 展开工具结果，Ctrl+D 在空输入时退出。
`;

/** Keeps the SDK's argument/file completion while owning the product's command list and descriptions. */
function completions(current: AutocompleteProvider): AutocompleteProvider {
  return {
    triggerCharacters: current.triggerCharacters,
    async getSuggestions(lines, row, column, options) {
      const result = await current.getSuggestions(lines, row, column, options);
      if (!result || row !== 0 || !/^\/[^\s]*$/.test(lines[0]?.slice(0, column) ?? "")) return result;
      const items = result.items.flatMap(item => {
        const name = item.value.replace(/^\//, "") as Command;
        return Object.hasOwn(commands, name) ? [{ ...item, description: commands[name] }] : [];
      });
      return items.length ? { ...result, items } : null;
    },
    applyCompletion: (...args) => current.applyCompletion(...args),
    shouldTriggerFileCompletion: (...args) => current.shouldTriggerFileCompletion?.(...args) ?? false,
  };
}

/** Gate the actual submitted text, including pasted input and custom submit keybindings. */
export class JustSimpleEditor extends CustomEditor {
  notify?: (message: string) => void;
  override handleInput(data: string) {
    const submit = this.onSubmit;
    this.onSubmit = text => {
      const match = /^\/(\S+)([\s\S]*)$/.exec(text);
      if (match?.[1] === "settings") text = `/config${match[2]}`;
      else if (match?.[1] === "hotkeys") text = "/help";
      const command = /^\/(\S+)/.exec(text)?.[1];
      if (text.startsWith("!") || command && !Object.hasOwn(commands, command)) {
        this.notify?.("此入口未在 JustSimple 中启用；输入 /help 查看可用操作。"); return;
      }
      submit?.(text);
    };
    try { super.handleInput(data); } finally { this.onSubmit = submit; }
  }
}

/** Presentation and curated settings only; Pi remains the state owner. */
export function installInterface(pi: ExtensionAPI, settings: SettingsManager,
  command: (name: Command, handler: (args: string, ctx: ExtensionCommandContext) => Promise<void>) => void) {
  pi.on("session_start", (_event, ctx) => {
    ctx.ui.setHeader((_tui, theme) => new Text(theme.bold(theme.fg("accent", `JustSimple · ${VERSION}`)), 1, 0));
    ctx.ui.setWorkingMessage("正在分析 · Esc 中断");
    ctx.ui.setWorkingIndicator({ frames: ["·"] });
    ctx.ui.setHiddenThinkingLabel("分析思路");
    ctx.ui.addAutocompleteProvider(completions);
    ctx.ui.setEditorComponent((tui, theme, keybindings) => {
      const editor = new JustSimpleEditor(tui, theme, keybindings);
      editor.notify = message => ctx.ui.notify(message, "warning");
      return editor;
    });
  });
  command("help", async (_args, ctx) => showDocument(ctx, "使用帮助", `${interfaceHelp}\n${scannerUsage}`));
  command("config", async (args, ctx) => {
    const section = args.trim();
    if (section && section !== "thinking") throw new Error("用法：/config 或 /config thinking");
    do {
      const entries = [
        `思考强度 · ${thinkingLabel(pi.getThinkingLevel())}（按当前模型保存）`,
        `自动整理上下文 · ${settings.getCompactionEnabled() ? "开启" : "关闭"}（默认开启，保留审计索引）`,
        `工具结果 · ${ctx.ui.getToolsExpanded() ? "展开" : "收起"}（当前界面，默认收起）`,
        "扫描参数 · 默认值与使用说明", "返回",
      ];
      const choice = section === "thinking" ? entries[0] : await select(ctx, "审计设置 · 模型 /model · 认证 /login", entries);
      if (choice === undefined || choice === "返回") break;
      if (choice === entries[0]) {
        if (!ctx.model?.reasoning) ctx.ui.notify("当前模型不提供可调整的思考强度；可用 /model 切换模型。", "info");
        else {
          const keys = Object.keys(levels) as (keyof typeof levels)[];
          const labels = keys.map(key => `${levels[key]} · ${key}${key === pi.getThinkingLevel() ? "（当前）" : ""}`);
          const chosen = await select(ctx, "思考强度 · 较高强度通常需要更长时间", labels, Math.max(0, keys.indexOf(pi.getThinkingLevel() as keyof typeof levels)));
          if (chosen !== undefined) {
            pi.setThinkingLevel(keys[labels.indexOf(chosen)]!);
            settings.setModelThinkingLevel(ctx.model.provider, ctx.model.id, pi.getThinkingLevel());
          }
        }
      } else if (choice === entries[1]) settings.setCompactionEnabled(!settings.getCompactionEnabled());
      else if (choice === entries[2]) ctx.ui.setToolsExpanded(!ctx.ui.getToolsExpanded());
      else await showDocument(ctx, "扫描参数", scannerUsage);
      await settings.flush();
      const failures = settings.drainErrors();
      if (failures.length) throw new AggregateError(failures.map(failure => failure.error), `设置未能保存：${failures.map(failure => failure.error.message).join("；")}`);
      if (section) break;
    } while (true);
  });
}
