import type { ExtensionFactory, ToolDefinition } from "@earendil-works/pi-coding-agent";
import { Text } from "@earendil-works/pi-tui";
import { Type, type TSchema } from "typebox";
import { Value } from "typebox/value";
import { ScannerBridge, type Json, type Operation, type ResultRef, type ScannerOptions } from "./bridge.ts";

const integer = (minimum = 0, maximum = 2147483647) => Type.Integer({ minimum, maximum });
const text = Type.String({ minLength: 1, maxLength: 4096 });
const object = <T extends Record<string, TSchema>>(properties: T) => Type.Object(properties, { additionalProperties: false });
const method = object({ owner: text, name: text, descriptor: text, loader: Type.Optional(integer()) });
const methods = Type.Array(method, { maxItems: 1000 });
const strings = Type.Array(text, { maxItems: 1000 });
const queryScope = { scanRef: Type.Optional(Type.String({ minLength: 1, maxLength: 4096,
  description: "A resultRef returned by scanner_scan_target only. Omit for the original input, including another view of the same method. Read a query resultRef with scanner_read_result." })) };
const mode = Type.Optional(Type.Union([Type.Literal("APPLICATION"), Type.Literal("COMPONENT")]));
const support = object({ relation: integer(), support: integer() });

/** Official Pi ToolDefinitions only. The caller owns registration and closes the returned bridge. */
export async function createScannerTools(options: ScannerOptions, signal?: AbortSignal) {
  const bridge = await ScannerBridge.open(options, signal);
  const max = bridge.scanLimits;
  const budgets = object(Object.fromEntries(Object.entries(max).map(([key, ceiling]) => [key,
    Type.Optional(Type.Integer({ minimum: 1, maximum: ceiling, default: bridge.scanDefaults[key as keyof typeof max] })),
  ])));
  function define<T extends TSchema>(name: Operation, description: string, parameters: T,
    preview?: (args: Record<string, unknown>, result: ResultRef) => string[] | undefined): ToolDefinition<T, Json> {
    return {
      name: `scanner_${name}`, label: name.replaceAll("_", " "), description, parameters,
      executionMode: "sequential",
      renderCall(args, theme) {
        const member = (args as Record<string, unknown>).method as { owner?: string; name?: string } | undefined;
        return new Text(`${theme.fg("toolTitle", name.replaceAll("_", " "))}${member ? ` ${member.owner}#${member.name}` : ""}`, 0, 0);
      },
      renderResult(result, { expanded }) {
        const details = result.details;
        if (expanded) return new Text(JSON.stringify(details ?? result.content, null, 2), 0, 0);
        if (details && typeof details === "object" && !Array.isArray(details)) {
          const summary = details.summary;
          const counts = summary && typeof summary === "object" && !Array.isArray(summary)
            ? Object.entries(summary).filter(([, value]) => value === null || typeof value !== "object").map(([key, value]) => `${key} ${value}`).join(" · ")
            : `${details.kind ?? "result"}${details.next === undefined ? "" : ` · next ${details.next}`}`;
          return new Text(`${counts}\n${details.resultRef ?? ""}`, 0, 0);
        }
        return new Text(result.content.filter(block => block.type === "text").map(block => block.text).join("\n"), 0, 0);
      },
      async execute(_id, params, signal, onUpdate) {
        if (!Value.Check(parameters, params)) {
          const errors = Value.Errors(parameters, params).slice(0, 3).map((error) => `${error.instancePath || "/"}: ${error.message}`);
          throw new Error(`Invalid scanner_${name} parameters: ${errors.join("; ")}`);
        }
        signal?.throwIfAborted();
        onUpdate?.({ content: [{ type: "text", text: name }], details: { operation: name, state: "running" } });
        const result = await bridge.call(name, params, signal, progress => onUpdate?.({
          content: [{ type: "text", text: `${progress.stage} · steps ${progress.steps} · contexts ${progress.contexts} · relations ${progress.relations}` }],
          details: progress as unknown as Json,
        }));
        let visible: Json = result as unknown as Json;
        if (preview && "summary" in result) {
          const ref: ResultRef = result;
          const path = preview(params as Record<string, unknown>, ref);
          if (path) {
            const page = await bridge.call("read_result", { resultRef: ref.resultRef, path: ["value", ...path], limit: 8, characters: 3000 }, signal);
            visible = { ...ref, preview: page as unknown as Json };
          }
        }
        return { content: [{ type: "text", text: JSON.stringify(visible) }], details: visible };
      },
    };
  }
  const tools = [
    define("find_symbols", "Find declared methods by case-insensitive literal substring (no wildcards). Default scope target searches application classes only; candidates adds dependencies and static definitions, not the JDK. Use exact owner to read a JDK class. Empty search results prove absence only in that scope. An exact owner also returns parent, interfaces, access, loader and fields under value.classes. Inherited methods require resolve_dispatch, then inspect the actual declaring owner. Metadata is not reachability or exploit proof.", object({
      ...queryScope,
      query: Type.Optional(Type.String({ maxLength: 4096 })), owner: Type.Optional(text), loader: Type.Optional(integer()),
      scope: Type.Optional(Type.Union([Type.Literal("target"), Type.Literal("candidates")], { default: "target" })),
    }), args => args.owner ? [] : ["methods"]),
    define("find_entries", "Discover application or component entry boundaries, or check explicit entries. Caller reachability and deployment assumptions stay separate.", object({ ...queryScope, mode, entries: Type.Optional(methods) }), () => ["value"]),
    define("inspect_method", "Read a declared method's ASM instructions/operands or lowered facts, CFG, guards and value origins. Resolve inherited declarations first. Locations are ASM indexes including labels/debug nodes. Bytecode summary.offset/next delimit this method slice; use summary.next as the next inspect_method offset (-1 ends the method). read_result.next only pages this saved slice, starting at array offset 0 for each new ref.", object({
      ...queryScope,
      method, view: Type.Optional(Type.Union([Type.Literal("bytecode"), Type.Literal("facts")])), offset: Type.Optional(integer()), limit: Type.Optional(integer(1, 1000)),
    }), (args, result) => args.view === "facts" ? (result.summary.actions === undefined ? undefined : ["facts", "actions"])
      : (result.summary.instructions === undefined ? undefined : ["value", "instructions"])),
    define("expand_graph", "Batch-expand symbolic calls or caller sites with explicit method/edge/depth budgets. Resume frontier cursors; edges do not establish runtime binding. Native or unavailable bodies remain gaps.", object({
      ...queryScope,
      scope: Type.Array(object({ method, depth: Type.Optional(integer()), offset: Type.Optional(integer()) }), { minItems: 1, maxItems: 1000 }),
      direction: Type.Optional(Type.Union([Type.Literal("OUTGOING"), Type.Literal("INCOMING")])), depth: Type.Optional(integer(1)),
      methods: Type.Optional(integer(1)), edges: Type.Optional(integer(1)),
    }), () => ["edges"]),
    define("resolve_dispatch", "Resolve actual method declarations within supplied receiver types/loaders. Retains native targets, missing-dependency issues and remaining receivers. Does not create receiver objects.", object({
      ...queryScope,
      method, upper: text, loader: Type.Optional(integer()), receivers: Type.Array(object({ name: text, loader: Type.Optional(integer()) }), { maxItems: 10000 }),
      receiverBudget: Type.Optional(integer(1)), targetBudget: Type.Optional(integer(1)),
    }), (_args, result) => result.summary.targets === undefined ? undefined : ["value", "targets"]),
    define("trace_source", "Mechanically trace one method-local value origin to parameters, calls, fields, arrays and frontier. Calls/heap reads remain next questions; trace membership is not object alias proof.", object({
      ...queryScope,
      method, origin: Type.Union([object({ kind: Type.Literal("Parameter"), slot: integer(0, 65535) }), object({ kind: Type.Literal("Producer"), instruction: integer() })]),
      budget: Type.Optional(integer(1)),
    }), (_args, result) => result.summary.visited === undefined ? undefined : ["value", "plan"]),
    define("lookup_knowledge", "List built-in reference IDs, match guidance against actual methods, or read selected reference structures. Knowledge guides exploration and supplies no current-program proof.", object({ ...queryScope, methods: Type.Optional(methods), ids: Type.Optional(strings) }), (args) => args.methods && (args.methods as unknown[]).length ? ["value"] : []),
    define("scan_target", "Run a fresh static scan with chosen entries, sinks, knowledge and budgets. Omitted budgets use schema defaults, not ceilings; raise them or narrow scope when useful. No total tool-call limit. Returns candidate counts, gaps and evidence; candidates are not verified exploits.", object({
      mode, entries: Type.Optional(methods), sinks: Type.Optional(methods), budgets: Type.Optional(budgets), demandGuidance: Type.Optional(Type.Boolean()),
      knowledge: Type.Optional(Type.Union([Type.Literal("all"), Type.Literal("none"), Type.Literal("selected")])), knowledgeIds: Type.Optional(strings),
    })),
    define("check_connection", "Check the dependency closure of selected scan relations and supports using shared path/value semantics. Multiple supports require an explicit choice. CLOSED means stored support closure, not attacker control or exploitation; gaps and cycles remain pending.", object({
      resultRef: text, relations: Type.Array(integer(), { minItems: 1, maxItems: 1000 }), supports: Type.Optional(Type.Array(support, { maxItems: 30000 })), budget: Type.Optional(integer(1)),
    }), () => []),
    define("read_result", "Read bounded evidence pages. Scan refs have top-level findings, relations, breakpoints, inputRequirements; query refs wrap data in value. Omit path to discover keys; follow next and deferred instead of repeating analysis. Batch IDs are evidence IDs, not array indexes. Release discards resources. No arbitrary files.", object({
      resultRef: text, action: Type.Optional(Type.Union([Type.Literal("read"), Type.Literal("release")])), path: Type.Optional(Type.Array(Type.String({ maxLength: 4096 }), { maxItems: 64 })),
      ids: Type.Optional(Type.Array(integer(), { minItems: 1, maxItems: 64, uniqueItems: true })),
      offset: Type.Optional(integer()), limit: Type.Optional(integer(1, 100)), characters: Type.Optional(integer(256, 16000)),
    })),
  ];
  return { tools, bridge, close: () => bridge.close() };
}

export type { ScannerOptions, ScanBudgets } from "./bridge.ts";

/** Registration adapter only; session creation, built-in tool policy and orchestration belong to the host. */
export function scannerExtension(options: ScannerOptions): ExtensionFactory {
  return async (pi) => {
    const scanner = await createScannerTools(options);
    try {
      for (const tool of scanner.tools) pi.registerTool<TSchema, Json>(tool);
      pi.on("session_shutdown", () => scanner.close());
    } catch (error) { await scanner.close(); throw error; }
  };
}
