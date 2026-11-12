import { after, test } from "node:test";
import assert from "node:assert/strict";
import { mkdirSync, mkdtempSync, readdirSync, realpathSync, rmSync, rmdirSync, writeFileSync } from "node:fs";
import { dirname, isAbsolute, join, relative, resolve } from "node:path";
import { fileURLToPath } from "node:url";
import { checkRepository } from "./check-repo.mjs";

const scratch = resolve(dirname(fileURLToPath(import.meta.url)), "../.local/work/repo-check");
mkdirSync(scratch, { recursive: true });
after(() => { if (readdirSync(scratch).length === 0) rmdirSync(scratch); });

function fixture(t) {
  const root = mkdtempSync(join(scratch, "fixture-"));
  t.after(() => {
    const owned = relative(realpathSync(scratch), realpathSync(root));
    assert.ok(owned && owned !== ".." && !owned.startsWith(`..${process.platform === "win32" ? "\\" : "/"}`) && !isAbsolute(owned));
    rmSync(root, { recursive: true, force: true });
  });
  function write(path, value) {
    const file = join(root, path);
    mkdirSync(dirname(file), { recursive: true });
    writeFileSync(file, value, "utf8");
  }
  write("README.md", "# Repo\n\n[使用](docs/%E4%BD%BF%E7%94%A8.md)\n\n```md\n[example](not-a-file.md)\n```\n");
  write("docs/使用.md", "# 使用\n");
  return { root, write, check: files => checkRepository(root, files ?? []) };
}

test("indexed UTF-8 documentation accepts encoded paths and ignores fenced examples and private work", t => {
  const repo = fixture(t);
  repo.write(".git", "gitdir: worktree-metadata\n");
  repo.write(".local/work/notes.md", "[private](absent.md)");
  repo.write("agent/node_modules/dependency/README.md", "[dependency](absent.md)");
  repo.write("agent/resources/AGENTS.md", "# Built-in instructions\n");
  repo.write("agent/resources/audit/SKILL.md", "# Built-in audit guidance\n");
  repo.write("agent/resources/audit/scan.md", "# Candidate selection\n");
  repo.write("agent/resources/audit/verify.md", "# Feasibility checks\n");
  repo.write("agent/resources/audit/report-template.md", "# Report\n");
  repo.write("docs/使用.md", "# 使用\n\n~~~md\n[example](not-a-link.md)\n~~~~\n");
  assert.deepEqual(repo.check(["README.md", "pnpm-lock.yaml"]), []);
});

test("temporary work stays private without a fixed record format; retired locations are rejected", t => {
  const repo = fixture(t);
  repo.write(".ENV.local", "LOCAL_OPTION=fixture\n");
  repo.write("TODO.md", "Current development task");
  repo.write(".local/work/handoff.md", "Current task");
  repo.write(".local/work/sample/input.json", "{}");
  repo.write(".local/work/build.log", "Current log");
  repo.write(".local/benchmark/results/scores.csv", "TP,FP");
  repo.write(".local/agent/session.json", "{}");
  assert.deepEqual(repo.check(), []);

  for (const name of ["development", "tasks", "scratch", "verification"]) repo.write(`.local/${name}/old.md`, "Previous round");
  const errors = repo.check();
  assert.equal(errors.length, 4);
  for (const name of ["development", "tasks", "scratch", "verification"]) {
    assert.ok(errors.some(error => error.includes(`Retired development location: .local/${name}; use .local/work/`)));
  }
});

test("root artifacts and component-local documentation are found without relying on Git visibility", t => {
  const repo = fixture(t);
  repo.write("NOTES.md", "ignored scratch");
  repo.write("work/diagnostic.json", "{}");
  repo.write("agent/docs/summary.md", "# Summary");
  repo.write("bridge/AGENTS.md", "# Misplaced development guidance");
  const errors = repo.check();
  assert.ok(errors.some(error => error.includes("Unexpected root entry: NOTES.md")));
  assert.ok(errors.some(error => error.includes("Unexpected root entry: work")));
  assert.ok(errors.some(error => error.includes("Product documentation belongs in docs/: agent/docs/summary.md")));
  assert.ok(errors.some(error => error.includes("Product documentation belongs in docs/: bridge/AGENTS.md")));
});

test("broken local links, reference links and unindexed pages fail the check", t => {
  const repo = fixture(t);
  repo.write("docs/使用.md", "[missing](absent.md)\n\n[other]: another-absent.md\n");
  repo.write("docs/orphan.md", "# Orphan");
  const errors = repo.check();
  assert.ok(errors.some(error => error.includes("Broken local link") && error.endsWith("absent.md")));
  assert.ok(errors.some(error => error.includes("another-absent.md")));
  assert.ok(errors.some(error => error.includes("not reachable") && error.endsWith("docs/orphan.md")));
});

test("public links cannot depend on private files or machine-local paths", t => {
  const repo = fixture(t);
  repo.write(".local/data.json", "{}");
  repo.write("TODO.md", "Current development task");
  repo.write("docs/使用.md", "[private](../.local/data.json)\n[task](../TODO.md)\n[task alias](../todo.md)\n[local](file:///tmp/report.md)\n[outside](../../outside.md)\n");
  const errors = repo.check();
  assert.ok(errors.some(error => error.includes("outside public repository files") && error.includes(".local/data.json")));
  assert.ok(errors.some(error => error.includes("outside public repository files") && error.includes("TODO.md")));
  assert.ok(errors.some(error => error.includes("outside public repository files") && error.includes("todo.md")));
  assert.ok(errors.some(error => error.includes("repository-relative") && error.includes("file:///")));
  assert.ok(errors.some(error => error.includes("outside public repository files") && error.includes("../../outside.md")));
});

test("publication candidates reject private inputs, credentials, generated files and other lockfiles", t => {
  const repo = fixture(t);
  const privateFiles = ["TODO.md", ".local/benchmark/sample.jar", "agent/.env", "agent/.ENV.local", "scanner/target/report.json", "package-lock.json", "scanner/Benchmark/SAMPLE.JAR"];
  const errors = repo.check([...privateFiles, "pnpm-lock.yaml", ".env.example"]);
  for (const file of privateFiles) assert.ok(errors.some(error => error === `Private, generated or unsupported publication file: ${file}`));
  assert.equal(errors.length, privateFiles.length);
});

test("invalid UTF-8 documentation fails with its file location", t => {
  const repo = fixture(t);
  repo.write("docs/使用.md", Buffer.from([0xff]));
  assert.ok(repo.check().some(error => error.startsWith("Cannot read UTF-8 document docs/使用.md:")));
});
