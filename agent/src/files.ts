import { constants } from "node:fs";
import { mkdir, open, rename, rm, writeFile } from "node:fs/promises";
import { dirname } from "node:path";
import { randomUUID } from "node:crypto";

const MAX_JSON_BYTES = 8 * 1024 * 1024;

export async function readJson(file: string, signal?: AbortSignal) {
  try {
    signal?.throwIfAborted();
    const source = await open(file, constants.O_RDONLY | (constants.O_NONBLOCK ?? 0));
    try {
      const info = await source.stat();
      if (!info.isFile()) throw new Error("JSON input must be a regular file");
      if (info.size > MAX_JSON_BYTES) throw new Error("JSON input exceeds 8 MiB");
      const buffer = Buffer.allocUnsafe(info.size + 1);
      let length = 0;
      while (length < buffer.length) {
        signal?.throwIfAborted();
        const { bytesRead } = await source.read(buffer, length, buffer.length - length, length);
        if (bytesRead === 0) break;
        length += bytesRead;
      }
      if (length > MAX_JSON_BYTES) throw new Error("JSON input exceeds 8 MiB");
      if (length !== info.size) throw new Error("JSON input changed size while reading");
      signal?.throwIfAborted();
      const bytes = buffer.subarray(0, length);
      const value: unknown = JSON.parse(new TextDecoder("utf-8", { fatal: true }).decode(bytes).replace(/^\uFEFF/, ""));
      return { value, bytes };
    } finally { await source.close(); }
  } catch (error) {
    signal?.throwIfAborted();
    throw new Error(`Reading ${file}: ${error instanceof Error ? error.message : error}`, { cause: error });
  }
}

export function missing(error: unknown): boolean {
  return (error as NodeJS.ErrnoException)?.code === "ENOENT" || (error instanceof Error && (error.cause as NodeJS.ErrnoException)?.code === "ENOENT");
}

/** The caller serializes updates; the previous file survives errors and cancellation. */
export async function writeJson(file: string, value: unknown, signal?: AbortSignal): Promise<void> {
  const temporary = `${file}.${randomUUID()}.tmp`;
  signal?.throwIfAborted();
  const content = `${JSON.stringify(value, null, 2)}\n`;
  if (Buffer.byteLength(content, "utf8") > MAX_JSON_BYTES) throw new Error(`JSON output exceeds 8 MiB: ${file}`);
  await mkdir(dirname(file), { recursive: true });
  try {
    await writeFile(temporary, content, { encoding: "utf8", mode: 0o600, signal });
    signal?.throwIfAborted();
    await rename(temporary, file);
  } catch (error) {
    try { await rm(temporary, { force: true }); }
    catch (cleanup) {
      throw new AggregateError([error, cleanup], `Writing ${file} failed\n${String(error)}\nTemporary file cleanup failed\n${String(cleanup)}`);
    }
    throw error;
  }
}
