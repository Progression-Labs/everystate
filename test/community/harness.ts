// Test driver: checks a spec like the CLI does, but always provides the host IO hooks that the
// community-module overrides (Json, CSV, IOUtils) read through `ev.hooks.io`.
// usage: node --experimental-strip-types harness.ts [-config X.cfg] Spec.tla   (paths in specs are relative to the cwd)
import * as fs from 'node:fs';
import * as path from 'node:path';
import { spawnSync } from 'node:child_process';
import { parseConfig } from '../../src/cfg.ts';
import { buildModel } from '../../src/model.ts';
import { Checker } from '../../src/checker.ts';
import { BUNDLED } from '../../src/bundled.ts';
import { TlaError } from '../../src/lexer.ts';

const mkParent = (p: string) => fs.mkdirSync(path.dirname(path.resolve(p)), { recursive: true });
export const nodeIO = {
  readFile: (p: string) => fs.readFileSync(p, 'utf8'),
  writeFile: (p: string, data: string) => { mkParent(p); fs.writeFileSync(p, data); },
  appendFile: (p: string, data: string) => fs.appendFileSync(p, data),
  exists: (p: string) => fs.existsSync(p),
  env: process.env as Record<string, string>,
  readBytes: (p: string) => new Uint8Array(fs.readFileSync(p)),
  writeBytes: (p: string, data: Uint8Array) => { mkParent(p); fs.writeFileSync(p, data); },
  exec: (command: string[], env?: Record<string, string>) => {
    const r = spawnSync(command[0], command.slice(1), { encoding: 'utf8', env: { ...process.env, ...env } });
    if (r.error) throw new TlaError(`Cannot run program "${command[0]}": ${r.error.message}`, undefined, undefined, 'eval');
    return { exitValue: r.status ?? 1, stdout: r.stdout, stderr: r.stderr };
  },
};

const argv = process.argv.slice(2);
let spec = '', config: string | null = null;
for (let i = 0; i < argv.length; i++) { if (argv[i] === '-config') config = argv[++i]; else spec = argv[i]; }
const dir = path.dirname(path.resolve(spec)), root = path.basename(spec, '.tla');
const cfgPath = config ? (fs.existsSync(config) ? config : path.join(dir, config)) : path.join(dir, root + '.cfg');
const resolve = (name: string): string | null => {
  const p = path.join(dir, name + '.tla');
  return fs.existsSync(p) ? fs.readFileSync(p, 'utf8') : BUNDLED[name] ?? null;
};
try {
  const model = buildModel(root, resolve, parseConfig(fs.readFileSync(cfgPath, 'utf8')), { print: s => process.stdout.write(s + '\n') });
  model.ev.hooks.io ??= nodeIO;
  const res = new Checker(model, { checkDeadlock: model.checkDeadlock }).run();
  process.stdout.write(`${res.status}${res.name ? ' ' + res.name : ''}${res.message ? ': ' + res.message : ''}\n`);
  process.exit(res.status === 'ok' ? 0 : 12);
} catch (e) {
  if (!(e instanceof TlaError)) throw e;
  process.stdout.write(`Error (${e.kind}): ${e.message}\n`);
  process.exit(150);
}
