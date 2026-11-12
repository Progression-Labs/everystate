// Host bindings for Node-compatible runtimes (Node, Bun, Deno's node: compatibility layer).
import * as fs from 'node:fs';
import * as path from 'node:path';
import { spawnSync } from 'node:child_process';
import type { Host } from './main.ts';

export function nodeHost(): Host {
  return {
    fs, path,
    stdout: s => { process.stdout.write(s); },
    exit: c => { process.exitCode = c; },
    env: process.env,
    io: {
      readFile: p => fs.readFileSync(p, 'utf8'),
      writeFile: (p, d) => { fs.mkdirSync(path.dirname(path.resolve(p)), { recursive: true }); fs.writeFileSync(p, d); },
      appendFile: (p, d) => { fs.mkdirSync(path.dirname(path.resolve(p)), { recursive: true }); fs.appendFileSync(p, d); },
      exists: p => fs.existsSync(p),
      readBytes: p => new Uint8Array(fs.readFileSync(p)),
      writeBytes: (p, d) => { fs.mkdirSync(path.dirname(path.resolve(p)), { recursive: true }); fs.writeFileSync(p, d); },
      exec: (command, env) => {
        const r = spawnSync(command[0], command.slice(1), { encoding: 'utf8', env: env ? { ...process.env, ...env } : process.env });
        return { exitValue: r.status ?? 1, stdout: r.stdout ?? '', stderr: r.stderr ?? '' };
      },
      env: process.env as Record<string, string>,
    },
  };
}
