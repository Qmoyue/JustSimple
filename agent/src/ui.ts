import type { Dirent } from "node:fs";
import { readdir, realpath, stat } from "node:fs/promises";
import { dirname, join, resolve } from "node:path";
import type { ExtensionCommandContext } from "@earendil-works/pi-coding-agent";
import { Input, matchesKey, SelectList, Text, truncateToWidth } from "@earendil-works/pi-tui";

const dialogOptions = { overlay: true, overlayOptions: { width: "100%", maxHeight: "90%", anchor: "center" } } as const;

/** Product dialogs reuse the TUI's editing, navigation and bounded list rendering. */
export function select(ctx: ExtensionCommandContext, title: string, options: readonly string[], initial = 0) {
  return ctx.ui.custom<string | undefined>((tui, theme, _keys, done) => {
    const list = new SelectList(options.map(value => ({ value, label: value })), Math.max(1, Math.min(8, tui.terminal.rows - 8)), {
      selectedPrefix: text => theme.fg("accent", text), selectedText: text => theme.fg("accent", text),
      description: text => theme.fg("dim", text), scrollInfo: () => theme.fg("dim", `共 ${options.length} 项`), noMatch: () => "没有可选项",
    });
    list.setSelectedIndex(initial); list.onSelect = item => done(item.value); list.onCancel = () => done(undefined);
    return {
      invalidate: () => list.invalidate(),
      render: width => [...new Text(theme.bold(truncateToWidth(`JustSimple · ${title}`, Math.max(1, width - 2), "…")), 1, 1).render(width), ...list.render(width),
        "", ...new Text(theme.fg("dim", "↑↓ 选择 · Enter 确定 · Esc 返回"), 1, 0).render(width)],
      handleInput(data) { if (matchesKey(data, "ctrl+c")) done(undefined); else list.handleInput(data); tui.requestRender(); },
      handleMouse: event => list.handleMouse(event),
    };
  }, dialogOptions);
}

export function input(ctx: ExtensionCommandContext, title: string, placeholder = "") {
  return ctx.ui.custom<string | undefined>((tui, theme, _keys, done) => {
    const field = new Input({ prompt: "› ", placeholder, placeholderStyle: text => theme.fg("dim", text) });
    field.onSubmit = done; field.onEscape = () => done(undefined);
    return {
      get focused() { return field.focused; }, set focused(value) { field.focused = value; },
      invalidate: () => field.invalidate(),
      render: width => [...new Text(theme.bold(`JustSimple · ${title}`), 1, 1).render(width), ...field.render(width),
        "", ...new Text(theme.fg("dim", "Enter 确定 · Esc 返回"), 1, 0).render(width)],
      handleInput(data) { if (matchesKey(data, "ctrl+c")) done(undefined); else field.handleInput(data); tui.requestRender(); },
      handleMouse: event => field.handleMouse(event),
    };
  }, dialogOptions);
}

export function commandPath(value: string, cwd: string): string {
  const text = value.trim();
  const unquoted = (text.startsWith('"') && text.endsWith('"')) || (text.startsWith("'") && text.endsWith("'")) ? text.slice(1, -1) : text;
  if (!unquoted) throw new Error("Path must not be empty");
  return resolve(cwd, unquoted);
}

/** Browsing never changes the session or executes a target. */
export async function choosePath(ctx: ExtensionCommandContext, title: string, kind: "directory" | "target"): Promise<string | undefined> {
  if (!ctx.hasUI) throw new Error("Specify a path when no interactive terminal is available");
  let directory = ctx.cwd;
  let offset = 0;
  let entries: Dirent[] | undefined;
  while (true) {
    entries ??= (await readdir(directory, { withFileTypes: true }))
      .filter(entry => !entry.name.startsWith(".") && (entry.isDirectory() || kind === "target" && /\.(jar|war|class)$/i.test(entry.name)))
      .sort((a, b) => Number(b.isDirectory()) - Number(a.isDirectory()) || a.name.localeCompare(b.name));
    const visible = entries.slice(offset, offset + 100);
    const labels = visible.map(entry => `${entry.isDirectory() ? "目录" : "文件"} · ${entry.name}`);
    const choice = await select(ctx, `${title} · ${directory}`,
      [...labels, ...(kind === "directory" ? ["使用此目录"] : ["选择此类目录"]), "上一级",
        ...(offset ? ["上一页"] : []), ...(offset + visible.length < entries.length ? ["下一页"] : []), "输入其他路径…"]);
    if (choice === undefined) return undefined;
    if (choice === "使用此目录" || choice === "选择此类目录") return realpath(directory);
    if (choice === "上一级") { directory = dirname(directory); offset = 0; entries = undefined; continue; }
    if (choice === "下一页") { offset += 100; continue; }
    if (choice === "上一页") { offset = Math.max(0, offset - 100); continue; }
    if (choice === "输入其他路径…") {
      const text = await input(ctx, title, directory);
      if (text === undefined) return undefined;
      const path = commandPath(text, ctx.cwd);
      const info = await stat(path);
      if (kind === "directory" && !info.isDirectory()) throw new Error(`Not a directory: ${path}`);
      return realpath(path);
    }
    const entry = visible[labels.indexOf(choice)];
    if (!entry) throw new Error("The selected directory entry is no longer available");
    const path = join(directory, entry.name);
    if (entry.isDirectory()) { directory = path; offset = 0; entries = undefined; }
    else return realpath(path);
  }
}

/** Native, scrollable read-only document; unlike an editor it cannot imply saved changes. */
export async function showDocument(ctx: ExtensionCommandContext, title: string, content: string) {
  await ctx.ui.custom<void>((tui, theme, _keys, done) => {
    const document = new Text(content, 1, 0);
    let offset = 0, height = 1, total = 1;
    return {
      invalidate: () => document.invalidate(),
      render(width) {
        const lines = document.render(width);
        const heading = new Text(theme.bold(truncateToWidth(`JustSimple · ${title}`, Math.max(1, width - 2), "…")), 1, 1).render(width);
        total = Math.max(1, lines.length);
        height = Math.max(1, Math.floor(tui.terminal.rows * 0.9) - heading.length - 2);
        offset = Math.max(0, Math.min(offset, Math.max(0, total - height)));
        const footer = total > height ? `${offset + 1}–${Math.min(total, offset + height)}/${total} · ↑↓ 翻阅 · PgUp/PgDn 翻页 · Esc 返回` : "Esc 返回";
        return [...heading, ...lines.slice(offset, offset + height), "", ...new Text(theme.fg("dim", truncateToWidth(footer, Math.max(1, width - 2), "…")), 1, 0).render(width)];
      },
      handleInput(data) {
        if (matchesKey(data, "escape") || matchesKey(data, "enter") || matchesKey(data, "ctrl+c")) { done(); return; }
        if (matchesKey(data, "up")) offset--;
        if (matchesKey(data, "down")) offset++;
        if (matchesKey(data, "pageUp")) offset -= height;
        if (matchesKey(data, "pageDown")) offset += height;
        if (matchesKey(data, "home")) offset = 0;
        if (matchesKey(data, "end")) offset = total - height;
        tui.requestRender();
      },
    };
  }, dialogOptions);
}
