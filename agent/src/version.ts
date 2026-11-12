import { readJson } from "./files.ts";
import { fileURLToPath } from "node:url";

const { value } = await readJson(fileURLToPath(new URL("../../package.json", import.meta.url)));
const manifest = value as { version?: unknown };
if (typeof manifest.version !== "string") throw new Error("Missing JustSimple product version");
export const VERSION = manifest.version;
