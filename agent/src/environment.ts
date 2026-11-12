import { execFile } from "node:child_process";
import { promisify } from "node:util";
import { createHash } from "node:crypto";
import { createReadStream } from "node:fs";
import { readdir, readFile, realpath, stat } from "node:fs/promises";
import { delimiter, dirname, join, resolve } from "node:path";
import { bridgeClasspath, type ScannerOptions } from "./bridge.ts";
import { missing, readJson } from "./files.ts";

export interface TargetInfo { path: string; classes: number; minimumJdk: number; multiReleaseMax: number; partial: boolean }

export async function inspectTarget(path: string, signal?: AbortSignal): Promise<TargetInfo> {
  path = await realpath(path);
  if (!(await stat(path)).isDirectory() && !/\.(jar|war|class)$/i.test(path)) throw new Error("Target must be a JAR, WAR, class or class directory");
  const { stdout } = await promisify(execFile)("java", ["-cp", bridgeClasspath(), "io.just.agent.bridge.TargetInfo", path],
    { encoding: "utf8", windowsHide: true, maxBuffer: 128000, timeout: 60000, signal });
  const result = JSON.parse(stdout) as TargetInfo;
  if (result.path !== path || !Number.isInteger(result.classes) || !Number.isInteger(result.minimumJdk)) throw new Error("Invalid target header response");
  return result;
}

function ignoreMissingPath(error: unknown) {
  if (missing(error) || (error as NodeJS.ErrnoException)?.code === "ENOTDIR") return undefined;
  throw error;
}

async function archiveInfo(path: string) {
  const info = await stat(path).catch(ignoreMissingPath);
  return info?.isFile() ? info : undefined;
}

type PlatformArchives = { runtime: string; bytes: number } | { modules: string[] };

async function platformArchives(jdk: string): Promise<PlatformArchives> {
  // Match Inputs.openPlatform: rt.jar takes precedence over the module archives.
  for (const directory of ["jre/lib", "lib"]) {
    const runtime = join(jdk, directory, "rt.jar");
    const info = await archiveInfo(runtime);
    if (info) return { runtime, bytes: info.size };
  }
  const directory = join(jdk, "jmods");
  const names = (await readdir(directory).catch(ignoreMissingPath))?.filter(name => name.endsWith(".jmod"));
  if (!names?.length) throw new Error(`Target JDK needs rt.jar or jmods: ${jdk}`);
  return { modules: names.map(name => join(directory, name)) };
}

export async function checkJdk(path: string): Promise<string> {
  const release = new TextDecoder("utf-8", { fatal: true }).decode(await readFile(join(path, "release")));
  const version = /^JAVA_VERSION="([^"]+)"/m.exec(release)?.[1];
  if (!version) throw new Error(`Not a JDK/JRE directory: ${path}`);
  await platformArchives(path);
  return version;
}

/** Content identity for durable evidence. Directory walks never follow target links. */
export async function inputIdentity(options: Pick<ScannerOptions, "input" | "jdk" | "dependencies" | "staticData">, signal?: AbortSignal): Promise<string> {
  const manifest = options.staticData ? resolve(options.staticData) : null;
  const hash = createHash("sha256");
  hash.update(JSON.stringify({ schema: "justsimple-input/v2", input: resolve(options.input),
    dependencies: (options.dependencies ?? []).map(path => resolve(path)), jdk: resolve(options.jdk),
    staticData: manifest }));
  hash.update("\0");
  let entries = 0;
  function visit() {
    signal?.throwIfAborted();
    if (++entries > 150000) throw new Error("Input identity exceeds 150000 entries");
  }
  function fileHeader(path: string, bytes: number) {
    hash.update(JSON.stringify({ path, bytes })); hash.update("\0");
  }
  async function file(path: string, size?: number) {
    visit();
    fileHeader(path, size ?? (await stat(path)).size);
    for await (const bytes of createReadStream(path, { signal })) hash.update(bytes);
    hash.update("\0");
  }
  async function classes(path: string) {
    const info = await stat(path);
    if (!info.isDirectory()) { await file(path, info.size); return; }
    visit();
    for (const entry of (await readdir(path, { withFileTypes: true })).sort((a, b) => a.name.localeCompare(b.name))) {
      signal?.throwIfAborted();
      if (entry.isSymbolicLink()) throw new Error(`Linked input member: ${join(path, entry.name)}`);
      if (entry.isDirectory()) await classes(join(path, entry.name));
      else if (entry.name.endsWith(".class")) await file(join(path, entry.name));
      else visit();
    }
  }
  await classes(options.input);
  for (const dependency of options.dependencies ?? []) await classes(dependency);
  if (manifest) {
    visit();
    const { value, bytes } = await readJson(manifest, signal);
    fileHeader(manifest, bytes.length);
    hash.update(bytes); hash.update("\0");
    const facts = value as { objects?: { classfile?: unknown }[] };
    if (Array.isArray(facts.objects)) for (const object of facts.objects) if (typeof object?.classfile === "string")
      await file(resolve(dirname(manifest), object.classfile));
  }
  await file(join(options.jdk, "release"));
  const platform = await platformArchives(options.jdk);
  if ("runtime" in platform) {
    await file(platform.runtime, platform.bytes);
    for (const name of ["jce.jar", "jsse.jar", "charsets.jar"]) {
      const path = join(dirname(platform.runtime), name);
      const info = await archiveInfo(path);
      if (info) await file(path, info.size);
    }
  } else {
    for (const path of platform.modules.sort()) await file(path);
  }
  for (const artifact of bridgeClasspath().split(delimiter)) await file(artifact);
  return hash.digest("hex");
}
