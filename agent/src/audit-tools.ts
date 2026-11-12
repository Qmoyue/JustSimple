import type { ToolDefinition } from "@earendil-works/pi-coding-agent";
import { Text } from "@earendil-works/pi-tui";
import { Type, type Static, type TSchema } from "typebox";
import { Value } from "typebox/value";
import { changeSchema } from "./board.ts";
import { Audit, skillPages, type Phase, type Report } from "./audit.ts";
import type { Json } from "./bridge.ts";

const text = Type.String({ maxLength: 8000 });
const integer = (minimum: number, maximum: number) => Type.Integer({ minimum, maximum });
const object = <T extends Record<string, TSchema>>(properties: T) => Type.Object(properties, { additionalProperties: false });

export function auditTools(audit: Audit): ToolDefinition<TSchema, Json>[] {
  function tool<T extends TSchema>(name: string, description: string, parameters: T,
    execute: (args: Static<T>, signal?: AbortSignal) => Promise<unknown>): ToolDefinition<T, Json> {
    return { name, label: name, description, parameters, defaultActive: false, executionMode: "sequential",
      renderCall: () => new Text(name, 0, 0),
      renderResult: (result, { expanded }) => {
        const details = result.details;
        const summary = details && typeof details === "object" && !Array.isArray(details)
          ? details.report ?? details.phase ?? (details.version === undefined ? "" : `revision ${details.version}`) : "";
        return new Text(expanded ? JSON.stringify(details ?? result.content, null, 2) : `${name}${summary ? ` · ${summary}` : ""}`, 0, 0);
      },
      async execute(_id, args, signal) {
        if (!audit.allowed(name)) throw new Error(`Tool is unavailable in ${audit.phase} phase`);
        if (!Value.Check(parameters, args)) throw new Error(`Invalid ${name} arguments`);
        signal?.throwIfAborted(); const value = await execute(args, signal) as Json;
        return { content: [{ type: "text", text: JSON.stringify(value) }], details: value };
      },
    };
  }
  const tools: ToolDefinition<TSchema, Json>[] = [
    tool("board_read", "Read bounded audit overview, one question, local dependencies or durable evidence. Evidence snapshots retain original input and loader scopes; old live references cannot be reused in a new run.", object({
      view: Type.Optional(Type.Union(["overview", "item", "graph", "evidence"].map(value => Type.Literal(value)))),
      id: Type.Optional(Type.String({ pattern: "^[QE][1-9][0-9]*$" })), status: Type.Optional(Type.Union(["open", "pending", "dead", "success"].map(value => Type.Literal(value)))),
      query: Type.Optional(Type.String({ maxLength: 512, description: "Filter question, binding/path scope or next action by case-insensitive text; this does not merge bindings." })),
      part: Type.Optional(Type.Union([Type.Literal("data"), Type.Literal("source")], { description: "For evidence, read data by default or bounded source/query metadata explicitly." })),
      path: Type.Optional(Type.Array(Type.String({ maxLength: 512 }), { maxItems: 32 })), offset: Type.Optional(integer(0, 2147483647)),
      limit: Type.Optional(integer(1, 100)), characters: Type.Optional(integer(256, 16000)),
    }), args => audit.read(args)),
    tool("board_update", "Record scoped questions. NEW: omit id, supply question and binding. Use changed for Q IDs and captures for durable E IDs. Attach tool observations to the same item via capture or existing evidence, including pending items. success/dead require reason and support/counterexample bytecode or connection evidence. No automatic status propagation.", object({
      changes: Type.Array(changeSchema, { maxItems: 32 }), focus: Type.Optional(Type.Union([Type.String({ pattern: "^Q[1-9][0-9]*$" }), Type.Null()])),
    }), (args, signal) => audit.update(args.changes, args.focus, signal)),
    tool("skill_read", "Read audit guidance on demand. Use verify before real risk claims. For the report chapter, first complete exploration and call audit_phase with phase report.", object({
      page: Type.Union(skillPages.map(value => Type.Literal(value))),
    }), async args => ({ page: args.page, content: await audit.skill(args.page) })),
    tool("audit_phase", "End analysis with explicit reasoning to freeze task evidence and open the next stage, or resume exploration. Pending questions may remain. Tool permissions change at execution time.", object({
      phase: Type.Union([Type.Literal("explore"), Type.Literal("report")]), reason: Type.String({ minLength: 1, maxLength: 4000 }),
    }), (args: { phase: Phase; reason: string }, signal) => audit.transition(args.phase, args.reason, signal)),
  ];
  if (audit.phase === "report") tools.push(tool("write_report", "Write a Markdown audit report from the frozen blackboard and evidence. Read the report skill first. Cover recorded success items; include conditions, representative chains, remediation and unexplored scope. Output path is task-owned.", object({
    summary: text, scope: text, unexplored: text,
    findings: Type.Array(object({ itemIds: Type.Array(Type.String({ pattern: "^Q[1-9][0-9]*$" }), { minItems: 1, maxItems: 32, uniqueItems: true }),
      title: Type.String({ minLength: 1, maxLength: 300 }), impact: text, chain: text, conditions: text, remediation: text }), { maxItems: 100 }),
  }), (args: Report, signal) => audit.writeReport(args, signal)));
  return tools;
}
