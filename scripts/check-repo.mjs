import { execFileSync } from "node:child_process";
import { existsSync, lstatSync, readFileSync, readdirSync, realpathSync } from "node:fs";
import { dirname, isAbsolute, relative, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const rootFiles = new Set([
  "README.md", "AGENTS.md", "CLAUDE.md", "TODO.md", "LICENSE", "pom.xml", "package.json", "pnpm-lock.yaml",
  "pnpm-workspace.yaml", ".editorconfig", ".gitattributes", ".gitignore", ".npmrc",
]);
const localDirectories = new Set([
  ".git", ".local", ".agents", ".codex", ".claude", ".aws", ".idea", ".vscode", ".settings", ".history",
  ".cache", ".venv", ".m2", ".pnpm-store", "node_modules", "target", "dist", "__pycache__",
]);
const privateDirectories = new Set([...localDirectories, "benchmark", "work", "scratch", "tmp", "temp"]);
const rootDirectories = new Set(["scanner", "bridge", "agent", "docs", "scripts", ".github", ...localDirectories]);
const localFiles = new Set([".git", ".DS_Store", "Thumbs.db", "Desktop.ini", ".classpath", ".project", ".factorypath", "local.properties", ".npmrc.local"]);
const otherLocks = new Set(["package-lock.json", "npm-shrinkwrap.json", "yarn.lock"]);
const pathName = value => value.replaceAll("\\", "/");
const environmentFile = name => name === ".env" || name.startsWith(".env.");
const outside = path => path === ".." || path.startsWith("../") || isAbsolute(path);

function privatePath(file) {
  const parts = pathName(file).split("/");
  const name = parts.at(-1);
  const lower = name.toLowerCase();
  return (parts.length === 1 && lower === "todo.md") || parts.some(part => privateDirectories.has(part.toLowerCase())) || localFiles.has(name) || otherLocks.has(name)
    || (environmentFile(lower) && lower !== ".env.example" && lower !== ".env.sample")
    || /\.(?:pem|key|p12|pfx|class|jar|war|ear|log|hprof|jfr)$/i.test(name);
}

/**
 * @param {string} directory Repository root.
 * @param {string[]} publicationFiles Git index paths and non-ignored untracked paths, relative to root.
 * @returns {string[]} Directory, documentation and publication errors.
 */
export function checkRepository(directory, publicationFiles) {
  const root = realpathSync(directory);
  const errors = new Set();
  const documents = new Map();
  const decoder = new TextDecoder("utf-8", { fatal: true });
  const fail = message => errors.add(message);

  for (const file of publicationFiles) {
    if (privatePath(file)) fail(`Private, generated or unsupported publication file: ${file}`);
  }
  for (const entry of readdirSync(root, { withFileTypes: true })) {
    const allowed = entry.isDirectory() || entry.isSymbolicLink()
      ? rootDirectories.has(entry.name)
      : rootFiles.has(entry.name) || localFiles.has(entry.name) || environmentFile(entry.name.toLowerCase());
    if (!allowed) fail(`Unexpected root entry: ${entry.name}; keep work artifacts in .local/`);
  }

  const local = resolve(root, ".local");
  if (existsSync(local)) {
    const info = lstatSync(local);
    if (info.isSymbolicLink() || !info.isDirectory()) fail(".local/ must be a local directory");
    else for (const entry of readdirSync(local, { withFileTypes: true })) {
      if (["development", "tasks", "scratch", "verification"].includes(entry.name)) {
        fail(`Retired development location: .local/${entry.name}; use .local/work/`);
      }
      if (entry.name === "work" && (!entry.isDirectory() || entry.isSymbolicLink())) fail(".local/work/ must be a local directory");
    }
  }

  function visit(directory) {
    for (const entry of readdirSync(directory, { withFileTypes: true })) {
      const absolute = resolve(directory, entry.name);
      const file = pathName(relative(root, absolute));
      if (privatePath(file)) continue;
      if (entry.isSymbolicLink()) { fail(`Public symlink is outside this check's scope: ${file}`); continue; }
      if (entry.isDirectory()) { visit(absolute); continue; }
      if (!entry.isFile() || !file.endsWith(".md")) continue;
      const entryDocument = file === "README.md" || file === "AGENTS.md" || file === "CLAUDE.md";
      const runtimeDocument = file === "agent/resources/AGENTS.md" || file.startsWith("agent/resources/audit/");
      if (!entryDocument && !runtimeDocument && !file.startsWith("docs/") && !file.startsWith(".github/")) {
        fail(`Product documentation belongs in docs/: ${file}`);
      }
      try {
        const text = decoder.decode(readFileSync(absolute));
        // Examples are data, not navigation. Reference-style link definitions are checked too.
        const markdown = text.replace(/^ {0,3}((`|~)\2{2,})(?!\2)[^\n]*\n[\s\S]*?^ {0,3}\1\2*[ \t]*$/gm, "");
        const links = [...markdown.matchAll(/!?\[[^\]]*\]\(\s*(<[^>]+>|[^\s)]+)(?:\s+["'][^"']*["'])?\s*\)/g)].map(match => match[1]);
        links.push(...[...markdown.matchAll(/^ {0,3}\[[^\]]+\]:\s*(<[^>]+>|[^\s]+)/gm)].map(match => match[1]));
        documents.set(file, { links, targets: [] });
      } catch (error) { fail(`Cannot read UTF-8 document ${file}: ${error.message}`); }
    }
  }
  visit(root);

  for (const [file, document] of documents) {
    for (const raw of document.links) {
      const link = raw.replace(/^<|>$/g, "");
      if (/^(?:file:|[A-Za-z]:[\\/]|\/)/i.test(link)) { fail(`Use a repository-relative or HTTPS link in ${file}: ${link}`); continue; }
      if (/^[A-Za-z][A-Za-z\d+.-]*:/.test(link)) continue;
      let target;
      try { target = decodeURIComponent(link.split("#", 1)[0]); }
      catch { fail(`Invalid link encoding in ${file}: ${link}`); continue; }
      if (!target) continue;
      const absolute = resolve(root, dirname(file), target);
      const name = pathName(relative(root, absolute));
      if (outside(name) || privatePath(name)) { fail(`Public document ${file} links outside public repository files: ${link}`); continue; }
      if (!existsSync(absolute)) { fail(`Broken local link in ${file}: ${link}`); continue; }
      if (outside(pathName(relative(root, realpathSync(absolute))))) { fail(`Link escapes repository in ${file}: ${link}`); continue; }
      document.targets.push(name);
    }
  }
  const reachable = new Set();
  const pending = ["README.md"];
  while (pending.length) {
    const file = pending.pop();
    if (reachable.has(file)) continue;
    reachable.add(file);
    pending.push(...(documents.get(file)?.targets ?? []));
  }
  for (const file of documents.keys()) {
    if (file.startsWith("docs/") && !reachable.has(file)) fail(`Document is not reachable from README.md: ${file}`);
  }
  return [...errors];
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  process.stdout.setDefaultEncoding("utf8");
  process.stderr.setDefaultEncoding("utf8");
  try {
    const root = fileURLToPath(new URL("../", import.meta.url));
    const publicationFiles = execFileSync("git", ["ls-files", "--cached", "--others", "--exclude-standard", "-z"], { cwd: root, encoding: "utf8" }).split("\0").filter(Boolean);
    const errors = checkRepository(root, publicationFiles);
    if (errors.length) { process.stderr.write(errors.map(error => `- ${error}\n`).join("")); process.exitCode = 1; }
    else process.stdout.write("Repository checks passed.\n");
  } catch (error) { process.stderr.write(`Repository check failed: ${error.message}\n`); process.exitCode = 1; }
}
