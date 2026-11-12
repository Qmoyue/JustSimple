import { isAbsolute, resolve } from "node:path";
import { parseArgs } from "node:util";
import { Type } from "typebox";
import { Value } from "typebox/value";
import type { ScanBudgets, ScannerOptions } from "./bridge.ts";

export const scannerUsage = `扫描与审计参数

/scan-only [参数]  完整静态扫描并生成报告，无需模型
/agent [参数]      使用同一输入范围进入交互审计

  --mode application|component  应用入口 / 公共组件边界；首次默认 application
  --dependency <路径或group:artifact:version>  补充依赖，可重复；坐标只读取本地仓库
  --facts <JSON>               提供已知静态输入，不执行目标
  --entry 'owner#name(desc)'    指定精确 JVM 入口，可重复
  --sink 'owner#name(desc)'     指定关注的调用终点，可重复
  --knowledge all|none|selected  知识引导：首次默认 all；知识不代替程序证据
  --knowledge-id <ID>          仅 selected 使用，至少一个，可重复
  --steps <N>                 传播工作量预算
  --contexts <N> --depth <N>   分析上下文与调用深度预算
  --relations <N> --findings <N> --alternatives <N>  证据、候选与替代支持预算
  --output <新目录>            纯扫描报告目录；默认 workspace/.local/scans/scan-<ID>
  --jdk-home <目录>            覆盖本次使用的 JDK 类库

默认预算：contexts 5000、steps 200000、depth 20、relations 30000、findings 1000、alternatives 64；均可主动增大。
预算控制单次扫描工作量；Agent 可加深或分批续查，无总工具次数限制。截断保留证据与待查项，不代表排除风险。
同一目标与 JDK 下省略参数，沿用最近的模式、依赖、静态输入、方法、知识和预算；输出始终使用新目录。
首页用 /target、/jdk-home 配置输入与类库，/workspace 选择工作目录，/maven-home 选择本地依赖仓库。
路径相对工作目录；含空格的路径和方法签名请加引号。Esc 取消读取或扫描，已有结果保留。`;

interface Method { owner: string; name: string; descriptor: string }
export interface ScanRequest {
  mode: "APPLICATION" | "COMPONENT";
  entries: Method[];
  sinks: Method[];
  knowledge: "all" | "none" | "selected";
  knowledgeIds: string[];
  budgets: Partial<ScanBudgets>;
}
export interface ScanSetup { options: ScannerOptions; scan: ScanRequest; output?: string }

const pathSchema = Type.String({ minLength: 1, maxLength: 4096 });
const methodSchema = Type.Object({ owner: pathSchema, name: pathSchema, descriptor: pathSchema }, { additionalProperties: false });
const savedSetupSchema = Type.Object({
  output: Type.Optional(pathSchema),
  options: Type.Object({ input: pathSchema, jdk: pathSchema, dependencies: Type.Optional(Type.Array(pathSchema, { maxItems: 1000 })), staticData: Type.Optional(pathSchema) }, { additionalProperties: false }),
  scan: Type.Object({ mode: Type.Union([Type.Literal("APPLICATION"), Type.Literal("COMPONENT")]),
    entries: Type.Array(methodSchema, { maxItems: 1000 }), sinks: Type.Array(methodSchema, { maxItems: 1000 }),
    knowledge: Type.Union([Type.Literal("all"), Type.Literal("none"), Type.Literal("selected")]), knowledgeIds: Type.Array(pathSchema, { maxItems: 1000 }),
    budgets: Type.Object(Object.fromEntries(["contexts", "steps", "depth", "relations", "findings", "alternatives"].map(key => [key, Type.Optional(Type.Integer({ minimum: 1, maximum: 2147483647 }))])), { additionalProperties: false }),
  }, { additionalProperties: false }),
}, { additionalProperties: false });

/** Persisted input scope cannot select a Java executable, host JAR or resource policy. */
export function restoreSetup(value: unknown): ScanSetup {
  if (!Value.Check(savedSetupSchema, value)) throw new Error("Invalid saved scanner target; select /target again");
  const setup = value as ScanSetup;
  const paths = [setup.options.input, setup.options.jdk, ...(setup.options.dependencies ?? []), ...(setup.output ? [setup.output] : [])];
  if (setup.options.staticData) paths.push(setup.options.staticData);
  if (!paths.every(isAbsolute)
    || (setup.scan.knowledge === "selected") !== (setup.scan.knowledgeIds.length > 0)) throw new Error("Invalid saved scanner target paths or knowledge selection");
  return setup;
}

/** Command text is tokenized without shell expansion; Windows backslashes stay literal. */
function words(text: string): string[] {
  const result: string[] = [];
  let word = "", quote = "", started = false;
  for (const char of text) {
    if (quote) {
      if (char === quote) quote = ""; else word += char;
    } else if (char === '"' || char === "'") { quote = char; started = true; }
    else if (/\s/.test(char)) {
      if (started) result.push(word);
      word = ""; started = false;
    } else { word += char; started = true; }
  }
  if (quote) throw new Error("Unclosed quote in scan arguments");
  if (started) result.push(word);
  return result;
}

function method(text: string): Method {
  const match = /^([^#\s]+)#([^#(\s]+)(\([^\s]*\)[^\s]+)$/.exec(text);
  if (!match) throw new Error(`Expected owner#name(descriptor): ${text}`);
  return { owner: match[1]!.replaceAll(".", "/"), name: match[2]!, descriptor: match[3]! };
}

export function parseScannerArgs(text: string, cwd: string, jdk?: string,
  defaults: { previous?: ScanSetup; input?: string; mavenRepository?: string } = {}): ScanSetup | undefined {
  const args = words(text);
  const { values, positionals } = parseArgs({ args, allowPositionals: true, options: {
    help: { type: "boolean" }, output: { type: "string" }, "jdk-home": { type: "string" }, dependency: { type: "string", multiple: true },
    facts: { type: "string" }, mode: { type: "string" }, entry: { type: "string", multiple: true }, sink: { type: "string", multiple: true },
    knowledge: { type: "string" }, "knowledge-id": { type: "string", multiple: true },
    contexts: { type: "string" }, steps: { type: "string" }, depth: { type: "string" },
    relations: { type: "string" }, findings: { type: "string" }, alternatives: { type: "string" },
  } });
  if (values.help || (!args.length && !defaults.input && !defaults.previous)) return undefined;
  const selectedInput = positionals[0] ?? defaults.input ?? defaults.previous?.options.input;
  if (positionals.length > 1 || (defaults.input !== undefined && positionals.length > 0) || !selectedInput) {
    throw new Error("Specify one input path or select /target first");
  }
  const selectedJdk = values["jdk-home"] ?? jdk ?? (positionals.length === 0 ? defaults.previous?.options.jdk : undefined);
  if (!selectedJdk) throw new Error("Specify --jdk-home or set JAVA_HOME to the target JDK");
  const path = (value: string) => {
    if (!value) throw new Error("Paths must not be empty");
    return resolve(cwd, value);
  };
  const target = path(selectedInput), targetJdk = path(selectedJdk);
  const previous = defaults.previous?.options.input === target && defaults.previous.options.jdk === targetJdk ? defaults.previous : undefined;
  const mode = values.mode ?? previous?.scan.mode.toLowerCase() ?? "application";
  if (mode !== "application" && mode !== "component") throw new Error("--mode must be application or component");
  const knowledge = values.knowledge ?? previous?.scan.knowledge ?? "all";
  if (knowledge !== "all" && knowledge !== "none" && knowledge !== "selected") throw new Error("--knowledge must be all, none or selected");
  const ids = values["knowledge-id"] ?? (values.knowledge ? [] : previous?.scan.knowledgeIds) ?? [];
  if ((knowledge === "selected") !== (ids.length > 0)) throw new Error("--knowledge selected requires --knowledge-id; other modes do not accept IDs");
  const budgets: Partial<ScanBudgets> = { ...previous?.scan.budgets };
  for (const key of ["contexts", "steps", "depth", "relations", "findings", "alternatives"] as const) {
    const value = values[key];
    if (value === undefined) continue;
    if (!/^[1-9]\d*$/.test(value) || !Number.isSafeInteger(Number(value)) || Number(value) > 2147483647) throw new Error(`--${key} must be a positive 32-bit integer`);
    budgets[key] = Number(value);
  }
  return {
    ...(values.output === undefined ? {} : { output: path(values.output) }),
    options: { input: target, jdk: targetJdk,
      dependencies: values.dependency === undefined ? previous?.options.dependencies ?? [] : values.dependency.map(value => dependency(value, cwd, defaults.mavenRepository)),
      ...(values.facts === undefined ? (previous?.options.staticData ? { staticData: previous.options.staticData } : {}) : { staticData: path(values.facts) }) },
    scan: { mode: mode === "application" ? "APPLICATION" : "COMPONENT", entries: values.entry ? values.entry.map(method) : previous?.scan.entries ?? [],
      sinks: values.sink ? values.sink.map(method) : previous?.scan.sinks ?? [], knowledge, knowledgeIds: ids, budgets },
  };
}

function dependency(value: string, cwd: string, repository?: string): string {
  const coordinate = /^([^:/\\]+):([^:/\\]+):([^:/\\]+)$/.exec(value);
  if (!coordinate) {
    if (!value) throw new Error("Dependency paths must not be empty");
    return resolve(cwd, value);
  }
  const group = coordinate[1]!, artifact = coordinate[2]!, version = coordinate[3]!;
  if (![...group.split("."), artifact, version].every(part => /^[A-Za-z0-9_][A-Za-z0-9_.-]*$/.test(part) && part !== "." && part !== "..")) throw new Error(`Invalid Maven coordinate: ${value}`);
  if (!repository) throw new Error("Select a Maven local repository with /maven-home first");
  return resolve(repository, ...group.split("."), artifact, version, `${artifact}-${version}.jar`);
}
