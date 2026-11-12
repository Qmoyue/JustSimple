import assert from "node:assert/strict";
import { execFile } from "node:child_process";
import { promisify } from "node:util";
import { mkdir, writeFile } from "node:fs/promises";
import { join } from "node:path";
import type { Terminal } from "@earendil-works/pi-tui";
import { cleanup, temporary } from "./work.ts";

export const run = promisify(execFile);
export const javaHome = process.env.JAVA_HOME!;
assert.ok(javaHome, "JAVA_HOME is required to compile static fixtures");
export async function fixture() {
  const directory = await temporary("native-tui-");
  try {
    const classes = join(directory, ".静态 样例"); await mkdir(classes);
    const source = join(directory, "Sample.java");
    await writeFile(source, `public class Sample {
      static { if (System.nanoTime() != 0) throw new AssertionError("Target must never execute"); }
      public static Object entry(Object value) { return sink(value); }
      public static Object sink(Object value) { return value; }
    }`, "utf8");
    await run(join(javaHome, "bin", "javac"), ["-encoding", "UTF-8", "-d", classes, source]);
    return { directory, classes };
  } catch (error) {
    try { await cleanup(directory); }
    catch (cleanupError) { throw new AggregateError([error, cleanupError], "Fixture setup and cleanup failed", { cause: error }); }
    throw error;
  }
}
export async function modelConfig(agentDir: string, baseUrl = "http://127.0.0.1:9/v1") {
  await mkdir(agentDir, { recursive: true });
  await writeFile(join(agentDir, "models.json"), JSON.stringify({ providers: { fixture: { baseUrl, api: "openai-completions", apiKey: "fixture-only",
    models: [{ id: "fixture-model", contextWindow: 128000, maxTokens: 4096 }] } } }), "utf8");
  await writeFile(join(agentDir, "settings.json"), JSON.stringify({ defaultProvider: "fixture", defaultModel: "fixture-model", quietStartup: true, retry: { enabled: false } }), "utf8");
}
export class TestTerminal implements Terminal {
  columns = 120; rows = 40; kittyProtocolActive = false;
  input?: (data: string) => void;
  output = "";
  start(input: (data: string) => void) { this.input = input; }
  stop() { this.input = undefined; }
  async drainInput() {}
  write(data: string) { this.output = (this.output + data).slice(-256000); }
  moveBy() {} hideCursor() {} showCursor() {} clearLine() {} clearFromCursor() {} clearScreen() {}
  setTitle() {} setProgress() {} setProgramStatus() {}
}
export async function waitFor(condition: () => boolean, message: string, milliseconds = 10000) {
  const end = Date.now() + milliseconds;
  while (!condition()) {
    assert.ok(Date.now() < end, message);
    await new Promise(resolve => setTimeout(resolve, 10));
  }
}
