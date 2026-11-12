import { createHash, randomUUID } from "node:crypto";
import { lstat, mkdir, readFile, realpath, rename, rm, writeFile } from "node:fs/promises";
import { isAbsolute, join, relative } from "node:path";
import { Board, type BoardSnapshot, type Change } from "./board.ts";
import type { ScannerBridge, ScannerOptions } from "./bridge.ts";
import { missing, writeJson } from "./files.ts";
import { VERSION } from "./version.ts";

export const resource = (name: string) => new URL(`../resources/${name}`, import.meta.url);
export interface Finding { itemIds: string[]; title: string; impact: string; chain: string; conditions: string; remediation: string }
export interface Report { summary: string; scope: string; findings: Finding[]; unexplored: string }
export type Phase = "explore" | "report";
export const skillPages: readonly string[] = ["index", "scan", "explore", "verify", "board", "report"];
type InputManifest = Pick<ScannerOptions, "input" | "jdk" | "dependencies" | "staticData">;

const sharedTools = ["scanner_read_result", "board_read", "skill_read", "audit_phase"];
const phaseTools: Record<Phase, readonly string[]> = {
  explore: ["scanner_find_symbols", "scanner_find_entries", "scanner_inspect_method", "scanner_expand_graph",
    "scanner_resolve_dispatch", "scanner_trace_source", "scanner_lookup_knowledge", "scanner_scan_target",
    "scanner_check_connection", ...sharedTools, "board_update"],
  report: [...sharedTools, "write_report"],
};

/** Owns audit phases and report publication; Board and Pi own their respective state. */
export class Audit {
  private readonly board: Board;
  private frozen?: BoardSnapshot;
  private stage: Phase = "explore";
  readonly directory: string;
  readonly changed: () => void;
  private readonly input: InputManifest;
  private constructor(board: Board, directory: string, input: InputManifest, changed: () => void) {
    this.board = board; this.directory = directory; this.changed = changed;
    this.input = structuredClone(input);
  }
  static async open(root: string, session: string, scope: string, bridge: ScannerBridge, input: InputManifest, changed: () => void) {
    const name = createHash("sha256").update(`${session}\0${scope}`).digest("hex").slice(0, 32);
    const directory = join(root, "tasks", name);
    const board = await Board.open(directory, scope, (ref, output, limit, signal) => bridge.exportResult(ref, output, limit, signal));
    await writeJson(join(directory, "input.json"), { ...input, scope, version: VERSION });
    return new Audit(board, directory, input, changed);
  }
  get phase(): Phase { return this.stage; }
  get toolNames(): string[] { return [...phaseTools[this.phase]]; }
  overview() { return { phase: this.phase, ...this.board.overview() }; }
  read(options: Parameters<Board["read"]>[0]) { return this.board.read(options); }
  async update(changes: readonly Change[], focus?: string | null, signal?: AbortSignal) {
    if (this.phase !== "explore") throw new Error("Blackboard changes require the exploration phase; call audit_phase with phase explore before updating, then return to report");
    const result = await this.board.update(changes, focus, signal); this.changed(); return result;
  }
  allowed(name: string): boolean { return phaseTools[this.phase].includes(name); }
  async transition(phase: Phase, reason: string, signal?: AbortSignal) {
    if (!reason.trim()) throw new Error("Explain why analysis is ending or resuming");
    signal?.throwIfAborted(); await this.board.flush();
    if (phase === "report") {
      const snapshot = this.board.snapshot();
      const necessary = new Set(snapshot.items.filter(item => item.status === "success").flatMap(item => item.evidence));
      await this.board.validateEvidence(snapshot, necessary, signal);
      await writeJson(join(this.directory, "snapshot.json"), snapshot, signal);
      this.frozen = snapshot;
    } else this.frozen = undefined;
    this.stage = phase; this.changed();
    return { phase, reason, snapshotVersion: this.frozen?.version, available: this.toolNames };
  }
  async skill(page: string) {
    if (!skillPages.includes(page)) throw new Error("Unknown built-in skill page");
    if (page === "report" && this.phase !== "report") throw new Error("When exploration is complete, call audit_phase with phase report before reading the report chapter");
    const content = await readFile(resource(`audit/${page === "index" ? "SKILL" : page}.md`), "utf8");
    return page === "report" ? `${content}\n${await readFile(resource("audit/report-template.md"), "utf8")}` : content;
  }
  async writeReport(report: Report, signal?: AbortSignal) {
    const snapshot = this.frozen;
    if (this.phase !== "report" || !snapshot || this.board.version !== snapshot.version) throw new Error("A current report-phase snapshot is required");
    signal?.throwIfAborted();
    const used = new Set<string>();
    for (const finding of report.findings) for (const id of finding.itemIds) {
      if (!snapshot.items.some(item => item.id === id && item.status === "success")) throw new Error(`Report finding needs a success item: ${id}. Resume exploration with audit_phase, create/update the scoped question with captured evidence, then return to report; do not invent item IDs.`);
      used.add(id);
    }
    const omitted = snapshot.items.filter(item => item.status === "success" && !used.has(item.id));
    if (omitted.length) throw new Error(`Report must account for recorded findings: ${omitted.map(item => item.id).join(", ")}`);
    const refs = new Set(snapshot.items.flatMap(item => item.evidence));
    for (const ref of snapshot.evidence) if (ref.unavailable) refs.delete(ref.id);
    const parent = join(this.directory, "reports");
    const output = join(parent, `revision-${snapshot.version}`);
    const existing = await lstat(output).catch(error => {
      if (missing(error)) return undefined;
      throw error;
    });
    if (existing) throw new Error(`Report revision already exists: ${output}`);
    await mkdir(parent, { recursive: true });
    const staging = join(parent, `.writing-${randomUUID()}`); await mkdir(staging);
    try {
      const selected = await this.board.exportEvidence(snapshot, refs, join(staging, "evidence"), signal);
      const findings = report.findings.map((finding, index) => {
        const items = snapshot.items.filter(item => finding.itemIds.includes(item.id));
        return `### ${index + 1}. ${finding.title}\n\n${finding.impact}\n\n链路：${finding.chain}\n\n成立条件：${finding.conditions}\n\n修复方向：${finding.remediation}\n\n`
          + items.map(item => `- ${item.id}@${snapshot.version} · ${item.binding}\n  - 依据：${item.reason}\n  - 证据：${item.evidence.join(", ")}\n  - 假设：${item.assumptions.join("；") || "未另行提供"}`).join("\n");
      }).join("\n\n") || "本次范围内未形成可报告发现。";
      const pending = snapshot.items.filter(item => item.status === "open" || item.status === "pending");
      const unresolved = [report.unexplored, ...(pending.length ? [`${pending.length} 个未决或未收尾问题；完整范围见[黑板快照](board.json)。`] : []),
        ...pending.slice(0, 20).map(item => {
          const unavailable = snapshot.evidence.filter(ref => item.evidence.includes(ref.id) && ref.unavailable)
            .map(ref => `${ref.id}: ${ref.unavailable}`).join("；");
          return `- ${item.id} · ${item.question.slice(0, 180)}\n`
            + (unavailable ? `  证据不可用：${unavailable.slice(0, 500)}\n` : "")
            + `  ${[item.reason, ...item.unresolved].filter(Boolean).join("；").slice(0, 500)}`;
        }),
        ...(pending.length > 20 ? ["其余条目保留在黑板快照中。"] : [])].filter(Boolean).join("\n\n") || "未另行记录。";
      const sources = [`输入身份：\`${snapshot.scope}\`；黑板版本：${snapshot.version}。`, "[黑板快照](board.json) · [证据清单](evidence.json)",
        ...selected.map(ref => `- ${ref.id} · [原始快照](evidence/${ref.file}) · ${ref.source.operation}\n  查询参数与运行范围见证据清单。\n  选择：\`${JSON.stringify({ path: ref.path ?? [], ids: ref.ids })}\`\n  SHA-256：\`${ref.sha256}\``)].join("\n\n");
      const template = await readFile(resource("audit/report-template.md"), "utf8");
      const input = `目标：\`${this.input.input}\`\n\nJDK：\`${this.input.jdk}\`\n\n依赖：${(this.input.dependencies ?? []).map(path => `\`${path}\``).join("、") || "无显式依赖"}\n\n静态输入：${this.input.staticData ?? "未提供"}\n\nJustSimple ${VERSION}`;
      const sections: Record<string, string> = { summary: report.summary, scope: `${input}\n\n${report.scope}`, findings, unresolved, sources };
      const content = template.replace(/\{\{(summary|scope|findings|unresolved|sources)\}\}/g, (_match, key: string) => sections[key]!);
      await writeJson(join(staging, "board.json"), snapshot, signal);
      await writeJson(join(staging, "evidence.json"), { scope: snapshot.scope, version: snapshot.version, evidence: selected }, signal);
      await writeJson(join(staging, "input.json"), { ...this.input, scope: snapshot.scope, version: VERSION }, signal);
      await writeFile(join(staging, "report.md"), content, { encoding: "utf8", signal });
      signal?.throwIfAborted(); await rename(staging, output);
      return { output, report: join(output, "report.md"), snapshotVersion: snapshot.version, findings: report.findings.length, evidence: selected.length };
    } catch (error) {
      try {
        const directory = await realpath(staging);
        const owned = relative(await realpath(parent), directory);
        if (!owned || owned.startsWith("..") || isAbsolute(owned)) throw new Error("Report temporary directory escaped its owner");
        await rm(directory, { recursive: true, force: true });
      } catch (cleanup) { throw new AggregateError([error, cleanup], "Report failed and its temporary directory could not be removed", { cause: error }); }
      throw error;
    }
  }
}
