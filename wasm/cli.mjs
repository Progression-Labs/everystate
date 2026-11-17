#!/usr/bin/env node
// Minimal command line for the WebAssembly build (used by bench.mjs): reads the spec, the modules next
// to it and the config from disk, runs check() and prints one JSON line like `everystate -json`.
// usage: node wasm/cli.mjs [-config FILE] [-deadlock] SPEC.tla
//        node wasm/cli.mjs conform [-config FILE] [-hidden N] [-stutter] [-behavior] [-limit N] [-noconstraints] -trace TRACE SPEC.tla
import fs from 'node:fs';
import path from 'node:path';
import { check, conform } from './everystate.mjs';
const argv = process.argv.slice(2);
const conformMode = argv[0] === 'conform' && argv.length > 1;
if (conformMode) argv.shift();
const opts = {};
let trace = null;
let config = null, deadlock = true, spec = null;
for (let i = 0; i < argv.length; i++) {
  if (argv[i] === '-config') config = argv[++i];
  else if (argv[i] === '-deadlock') deadlock = false;
  else if (conformMode && argv[i] === '-trace') trace = argv[++i];
  else if (conformMode && (argv[i] === '-hidden' || argv[i] === '-limit')) opts[argv[i].slice(1)] = Number(argv[++i]);
  else if (conformMode && argv[i] === '-stutter') opts.stutter = true;
  else if (conformMode && (argv[i] === '-behavior' || argv[i] === '-behaviour')) opts.behavior = true;
  else if (conformMode && argv[i] === '-noconstraints') opts.constraints = false;
  else if (!argv[i].startsWith('-')) { if (spec && conformMode) trace ??= argv[i]; else spec = argv[i]; }
}
if (!spec) { console.error('usage: node wasm/cli.mjs [-config FILE] [-deadlock] SPEC.tla'); process.exit(1); }
const dir = path.dirname(path.resolve(spec)), root = path.basename(spec, '.tla');
const modules = {};
for (const f of fs.readdirSync(dir)) if (f.endsWith('.tla')) modules[f.slice(0, -4)] = fs.readFileSync(path.join(dir, f), 'utf8');
const cfg = fs.readFileSync(config ?? path.join(dir, root + '.cfg'), 'utf8');
if (conformMode) {
  if (!trace) { console.error('usage: node wasm/cli.mjs conform [-config FILE] -trace TRACE SPEC.tla'); process.exit(1); }
  const codes = { conforms: 0, mismatch: 20, 'trace-error': 21, limit: 22, invariant: 12, assumption: 10 };
  let result, code;
  try {
    result = fs.existsSync(trace)
      ? conform({ root, modules, config: cfg, trace: fs.readFileSync(trace, 'utf8'), ...opts, print: l => console.log(l) })
      : { status: 'trace-error', message: `cannot read the trace file ${trace}` };
    code = codes[result.status] ?? 255;
  } catch (e) {
    result = { status: 'setup-error', kind: e.kind, message: e.message };
    code = e.kind === 'config' ? 151 : 150;
  }
  console.log(JSON.stringify(result));
  process.exit(code);
}
try {
  const { result } = check({ root, modules, config: cfg, deadlock, print: l => console.log(l) });
  console.log(JSON.stringify({ status: result.status, name: result.name, message: result.message, generated: result.generated, distinct: result.distinct, queue: result.queue, depth: result.depth }));
  // the native binary's exit status
  const codes = { ok: 0, assumption: 10, deadlock: 11, invariant: 12, 'invariant-init': 12, 'action-property': 13, 'implied-init': 13, liveness: 13, incomplete: 75 };
  process.exitCode = codes[result.status] ?? 255;
} catch (e) {
  console.log(JSON.stringify({ status: 'setup-error', message: e.message }));
  process.exit(150);
}
