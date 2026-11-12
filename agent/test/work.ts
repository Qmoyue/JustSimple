import { mkdir, mkdtemp, realpath, rm } from "node:fs/promises";
import { isAbsolute, join, relative } from "node:path";
import { fileURLToPath } from "node:url";

export const work = fileURLToPath(new URL("../../.local/work/", import.meta.url));
export async function temporary(prefix: string) { await mkdir(work, { recursive: true }); return mkdtemp(join(work, prefix)); }
export async function cleanup(directory: string) {
  const owned = relative(await realpath(work), await realpath(directory));
  if (!owned || owned.startsWith("..") || isAbsolute(owned)) throw new Error("Test cleanup escaped its work directory");
  await rm(directory, { recursive: true, force: true });
}
