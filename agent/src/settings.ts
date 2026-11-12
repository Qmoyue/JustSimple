import { homedir } from "node:os";
import { isAbsolute, join } from "node:path";
import { missing, readJson, writeJson } from "./files.ts";

interface Preferences {
  workspace?: string;
  target?: string;
  jdk?: string;
  jdks: readonly string[];
  mavenRepository: string;
}

/** Scanner preferences only; Pi owns models, credentials, sessions and its settings. */
export class ScannerSettings {
  readonly file: string;
  private data: Preferences;
  private pending: Promise<void> = Promise.resolve();
  private constructor(file: string, data: Preferences) { this.file = file; this.data = data; }
  get value(): Readonly<Preferences> { return this.data; }

  static async load(agentDir: string) {
    const file = join(agentDir, "scanner.json");
    let value: unknown = {};
    try {
      ({ value } = await readJson(file));
    } catch (error) {
      if (!missing(error)) throw error;
    }
    return new ScannerSettings(file, preferences(value));
  }

  save(patch: Partial<Preferences>) {
    const task = this.pending.then(() => this.write(patch));
    this.pending = task.catch(() => {});
    return task;
  }

  private async write(patch: Partial<Preferences>) {
    const next = preferences({ ...this.data, ...patch });
    await writeJson(this.file, next);
    this.data = next;
  }
}

function preferences(value: unknown): Preferences {
  if (!value || typeof value !== "object" || Array.isArray(value)) throw new Error("scanner.json must be an object");
  const data = value as Record<string, unknown>;
  for (const key of Object.keys(data)) if (!["workspace", "target", "jdk", "jdks", "mavenRepository"].includes(key)) throw new Error(`Unknown scanner setting: ${key}`);
  for (const key of ["workspace", "target", "jdk", "mavenRepository"] as const) {
    if (data[key] !== undefined && (typeof data[key] !== "string" || !isAbsolute(data[key]))) throw new Error(`${key} must be an absolute path`);
  }
  if (data.jdks !== undefined && (!Array.isArray(data.jdks) || !data.jdks.every(path => typeof path === "string" && isAbsolute(path)))) throw new Error("jdks must contain absolute paths");
  return { ...(data.workspace === undefined ? {} : { workspace: data.workspace as string }),
    ...(data.target === undefined ? {} : { target: data.target as string }),
    ...(data.jdk === undefined ? {} : { jdk: data.jdk as string }),
    jdks: [...new Set((data.jdks ?? []) as string[])], mavenRepository: (data.mavenRepository as string | undefined) ?? join(homedir(), ".m2", "repository") };
}
