import { test } from "node:test";
import assert from "node:assert/strict";
import { mkdir, readFile, readdir, truncate, writeFile } from "node:fs/promises";
import { join } from "node:path";
import { readJson, writeJson } from "../src/files.ts";
import { cleanup, temporary } from "./work.ts";

test("the JSON write limit applies to persisted UTF-8 bytes and a failed replacement preserves the record", async t => {
  const directory = await temporary("json-capacity-"); t.after(() => cleanup(directory));
  const file = join(directory, "state.json");
  await writeJson(file, { state: "retained" });
  const original = await readFile(file, "utf8");
  const value = { text: "中".repeat(3 * 1024 * 1024) };
  const stored = JSON.stringify(value);
  assert.ok(stored.length < 8 * 1024 * 1024, "UTF-16 character count is insufficient for the file budget");
  assert.ok(Buffer.byteLength(stored) > 8 * 1024 * 1024);
  await assert.rejects(writeJson(file, value), /8 MiB|byte capacity/);
  assert.equal(await readFile(file, "utf8"), original);
  const record = await readJson(file);
  assert.deepEqual(record.value, { state: "retained" });
  assert.equal(record.bytes.toString("utf8"), original);
  assert.deepEqual(await readdir(directory), ["state.json"]);
  const oversized = join(directory, "oversized.json");
  await writeFile(oversized, "");
  await truncate(oversized, 8 * 1024 * 1024 + 1);
  await assert.rejects(readJson(oversized), /JSON input exceeds 8 MiB/);
});

test("a failed JSON rename preserves the destination and removes the staged file", async t => {
  const directory = await temporary("json-rename-"); t.after(() => cleanup(directory));
  const destination = join(directory, "state.json");
  await mkdir(destination);
  const marker = join(destination, "keep.txt");
  await writeFile(marker, "retained", "utf8");
  await assert.rejects(writeJson(destination, { state: "new" }), { syscall: "rename" });
  assert.equal(await readFile(marker, "utf8"), "retained");
  assert.deepEqual(await readdir(directory), ["state.json"]);
});
