#!/usr/bin/env node
// Minimal command line for the WebAssembly build (used by bench.mjs): reads the spec, the modules next
// to it and the config from disk, runs check() and prints one JSON line like `everystate -json`.
// usage: node wasm/cli.mjs [-config FILE] [-deadlock] SPEC.tla
import fs from 'node:fs';
import path from 'node:path';
import { check } from './everystate.mjs';
const argv = process.argv.slice(2);
let config = null, deadlock = true, spec = null;
for (let i = 0; i < argv.length; i++) {
  if (argv[i] === '-config') config = argv[++i];
  else if (argv[i] === '-deadlock') deadlock = false;
  else if (!argv[i].startsWith('-')) spec = argv[i];
}
if (!spec) { console.error('usage: node wasm/cli.mjs [-config FILE] [-deadlock] SPEC.tla'); process.exit(1); }
const dir = path.dirname(path.resolve(spec)), root = path.basename(spec, '.tla');
const modules = {};
for (const f of fs.readdirSync(dir)) if (f.endsWith('.tla')) modules[f.slice(0, -4)] = fs.readFileSync(path.join(dir, f), 'utf8');
const cfg = fs.readFileSync(config ?? path.join(dir, root + '.cfg'), 'utf8');
try {
  const { result } = check({ root, modules, config: cfg, deadlock, print: l => console.log(l) });
  console.log(JSON.stringify({ status: result.status, name: result.name, message: result.message, generated: result.generated, distinct: result.distinct, queue: result.queue, depth: result.depth }));
} catch (e) {
  console.log(JSON.stringify({ status: 'setup-error', message: e.message }));
  process.exit(150);
}
