import { test } from "node:test";
import assert from "node:assert/strict";
import { copyFile, mkdir, unlink, writeFile } from "node:fs/promises";
import { join } from "node:path";
import { checkJdk, inspectTarget, inputIdentity } from "../src/environment.ts";
import { cleanup, temporary } from "./work.ts";
import { javaHome, run } from "./runtime-fixture.ts";

async function identityPlatform(directory: string) {
  const jdk = join(directory, "jdk"), library = join(jdk, "lib");
  await mkdir(library, { recursive: true });
  await writeFile(join(jdk, "release"), 'JAVA_VERSION="1.8.0"\n');
  await writeFile(join(library, "rt.jar"), "runtime fixture");
  return jdk;
}

test("target hints read actual class headers and keep multi-release and nested dependencies separate", async t => {
  const directory = await temporary("target-headers-"); t.after(() => cleanup(directory));
  const classes = join(directory, "classes"); await mkdir(classes);
  assert.equal((await inspectTarget(classes)).classes, 0, "empty target scopes can still be paired with explicit dependencies");
  const source = join(directory, "Versioned.java");
  await writeFile(source, 'public class Versioned { static { if (System.nanoTime() != 0) throw new AssertionError("Never execute"); } public static void entry() {} }', "utf8");
  await run(join(javaHome, "bin", "javac"), ["-encoding", "UTF-8", "--release", "8", "-d", classes, source]);
  const base = await inspectTarget(classes); assert.equal(base.minimumJdk, 8); assert.equal(base.classes, 1); assert.equal(base.partial, false);
  const versioned = join(classes, "META-INF", "versions", "11"); await mkdir(versioned, { recursive: true });
  await run(join(javaHome, "bin", "javac"), ["-encoding", "UTF-8", "--release", "11", "-d", versioned, source]);
  const nested = join(directory, "nested.jar"); await run(join(javaHome, "bin", "jar"), ["cf", nested, "-C", versioned, "."]);
  await copyFile(nested, join(classes, "dependency.jar"));
  const archive = join(directory, "application.jar"); await run(join(javaHome, "bin", "jar"), ["cf", archive, "-C", classes, "."]);
  const hint = await inspectTarget(archive);
  assert.equal(hint.minimumJdk, 8); assert.equal(hint.multiReleaseMax, 11); assert.equal(hint.partial, true); assert.equal(hint.classes, 2);
  const bad = join(directory, "bad.class"); await writeFile(bad, Buffer.alloc(8));
  await assert.rejects(inspectTarget(bad), /invalid classfile/);
});

test("durable scope identity changes when external classfile facts change", async t => {
  const directory = await temporary("scope-identity-"); t.after(() => cleanup(directory));
  const classes = join(directory, "classes"); await mkdir(classes);
  const manifests = join(directory, "输入 清单"); await mkdir(manifests);
  const external = join(directory, "External.class"); await writeFile(external, "class-a");
  const facts = join(manifests, "facts.json"); await writeFile(facts, JSON.stringify({ objects: [{ id: "bytes", type: "[B", classfile: "../External.class" }] }), "utf8");
  const options = { input: classes, jdk: await identityPlatform(directory), staticData: facts };
  const first = await inputIdentity(options);
  await writeFile(external, "class-b");
  assert.notEqual(await inputIdentity(options), first);
  await assert.rejects(inputIdentity(options, AbortSignal.abort()), { name: "AbortError" });
});

test("durable scope identity distinguishes target roles even when the same class bytes are read", async t => {
  const directory = await temporary("scope-roles-"); t.after(() => cleanup(directory));
  const classes = join(directory, "classes"); await mkdir(classes);
  await writeFile(join(classes, "A.class"), "class A");
  await writeFile(join(classes, "B.class"), "class B");
  const jdk = await identityPlatform(directory);
  const application = { input: classes, jdk };
  const component = { input: join(classes, "A.class"), dependencies: [join(classes, "B.class")], jdk };
  const identity = await inputIdentity(application);
  assert.notEqual(await inputIdentity(component), identity, "target exposure differs from dependency-only bytecode");
  assert.equal(await inputIdentity({ ...application, dependencies: [] }), identity);
});

test("durable identity uses the selected legacy platform when jmods also exists", async t => {
  const directory = await temporary("scope-platform-"); t.after(() => cleanup(directory));
  const input = join(directory, "classes"), jdk = join(directory, "jdk");
  const library = join(jdk, "jre", "lib"), modules = join(jdk, "jmods");
  await mkdir(input); await mkdir(library, { recursive: true }); await mkdir(modules);
  const runtime = join(library, "rt.jar"), module = join(modules, "java.base.jmod");
  await writeFile(join(jdk, "release"), 'JAVA_VERSION="1.8.0"\n');
  await writeFile(runtime, "runtime-a"); await writeFile(module, "module-a");
  assert.equal(await checkJdk(jdk), "1.8.0");

  const options = { input, jdk };
  const original = await inputIdentity(options);
  await writeFile(runtime, "runtime-b");
  const changed = await inputIdentity(options);
  assert.notEqual(changed, original);
  await writeFile(module, "module-b");
  assert.equal(await inputIdentity(options), changed);
  await unlink(runtime); await unlink(module);
  await assert.rejects(checkJdk(jdk), /Target JDK needs rt.jar or jmods/);
  await assert.rejects(inputIdentity(options), /Target JDK needs rt.jar or jmods/);
});
