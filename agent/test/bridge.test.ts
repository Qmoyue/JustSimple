import { test } from "node:test";
import assert from "node:assert/strict";
import { writeFile } from "node:fs/promises";
import { join } from "node:path";
import { ScannerBridge } from "../src/bridge.ts";
import { javaHome, run } from "./runtime-fixture.ts";
import { cleanup, temporary } from "./work.ts";

async function withProtocolHost(body: string, check: (bridge: ScannerBridge) => Promise<void>) {
  const directory = await temporary("protocol-fixture-");
  try {
    const budgets = { contexts: 1, steps: 1, depth: 1, relations: 1, findings: 1, alternatives: 1 };
    const ready = JSON.stringify({ id: "ready", protocol: 1, inputId: "protocol-fixture", scanLimits: budgets, scanDefaults: budgets });
    const source = join(directory, "ToolMain.java");
    await writeFile(source, `
      package io.just.agent.bridge;
      public class ToolMain {
        public static void main(String[] args) throws Exception {
          System.out.println(${JSON.stringify(ready)});
          var input = new java.io.BufferedReader(new java.io.InputStreamReader(System.in, java.nio.charset.StandardCharsets.UTF_8));
          ${body}
        }
      }`, "utf8");
    await run(join(javaHome, "bin", "javac"), ["-encoding", "UTF-8", "-d", directory, source]);
    const bridge = await ScannerBridge.open({ bridgeJar: directory, input: directory, jdk: javaHome });
    try { await check(bridge); }
    finally { await bridge.close(); }
  } finally { await cleanup(directory); }
}

test("an incomplete protocol reply rejects the caller instead of leaving it pending", async () => {
  await withProtocolHost(`input.readLine(); System.out.println(${JSON.stringify('{"id":"1"}')}); while (input.readLine() != null) {}`, async (bridge) => {
    let timer: ReturnType<typeof setTimeout> | undefined;
    try {
      await assert.rejects(Promise.race([
        bridge.call("find_symbols", {}),
        new Promise<never>((_, reject) => { timer = setTimeout(() => reject(new Error("protocol caller did not settle")), 2000); }),
      ]), /Scanner reply has no result or error/);
    } finally { clearTimeout(timer); }
  });
});

test("UTF-8 diagnostics survive byte boundaries between child-process chunks", async () => {
  await withProtocolHost(`
    input.readLine();
    for (byte value : "诊断😀 café".getBytes(java.nio.charset.StandardCharsets.UTF_8)) {
      System.err.write(value); System.err.flush(); Thread.sleep(25);
    }
    System.exit(2);`, async (bridge) => {
    await assert.rejects(bridge.call("find_symbols", {}), (error: Error) => {
      assert.ok(error.message.includes("诊断😀 café"), error.message); return true;
    });
  });
});

test("an oversized reply rejects the pending call while the host is still writing", async () => {
  await withProtocolHost(`
    input.readLine();
    System.out.print(" ".repeat(256001)); System.out.flush();
    while (input.readLine() != null) {}`, async (bridge) => {
    let timer: ReturnType<typeof setTimeout> | undefined;
    try {
      await assert.rejects(Promise.race([
        bridge.call("read_result", {}),
        new Promise<never>((_, reject) => { timer = setTimeout(() => reject(new Error("reply did not settle before EOF")), 2000); }),
      ]), /reply exceeds 256K characters/);
    } finally { clearTimeout(timer); }
  });
});

test("malformed UTF-8 in a reply is rejected instead of replacing text", async () => {
  await withProtocolHost(`
    input.readLine();
    System.out.print(${JSON.stringify('{"id":"1","result":{"directory":"')});
    System.out.write(0x80);
    System.out.println(${JSON.stringify('","files":[]}}')}); System.out.flush();`, async (bridge) => {
    await assert.rejects(bridge.call("read_result", {}), /UTF-8/i);
  });
});

test("cancelling in-flight work sends its request ID and leaves the host usable", async () => {
  const progress = { stage: "READ", entries: 0, contexts: 0, steps: 0, relations: 0, queued: 0 };
  const line = (value: unknown) => JSON.stringify(JSON.stringify(value));
  await withProtocolHost(`
    input.readLine();
    System.out.println(${line({ id: "1", progress })});
    if (!${line({ id: "1", cancel: true })}.equals(input.readLine())) throw new AssertionError("expected cancellation of request 1");
    System.out.println(${line({ id: "1", error: { code: "CANCELLED", message: "local work interrupted" } })});
    input.readLine();
    System.out.println(${line({ id: "2", result: { bytes: 4 } })});
    while (input.readLine() != null) {}`, async bridge => {
    const controller = new AbortController();
    await assert.rejects(bridge.call("find_symbols", {}, controller.signal, () => controller.abort()), /CANCELLED: local work interrupted/);
    assert.deepEqual(await bridge.call("read_result", {}), { bytes: 4 });
  });
});
