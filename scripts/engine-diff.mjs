#!/usr/bin/env node
// Differential test of two everystate builds (or two EVERYSTATE_ENGINE settings of one build): every model
// is run by both sides, as `-json` (status, counts, the full trace) and as plain text; the outputs must be
// identical apart from timestamps and durations. Zero differences are allowed.
//
// usage: node scripts/engine-diff.mjs --a SIDE --b SIDE [--corpus examples,bench,tlc,dir:PATH,...] [--jobs N]
//                                     [--timeout SEC] [--max-runtime SEC] [--filter STR] [--env K=V ...]
//   SIDE    a path to an everystate binary, or `engine:NAME` (this build with EVERYSTATE_ENGINE=NAME),
//           or `env:K=V` (this build with that variable set)
//   corpus  examples  the tlaplus/Examples models of the conformance gate (manifest.json, exhaustive search)
//           bench     the 12 BENCHMARK.md models
//           tlc       every (spec, cfg) pair of TLC's test-model directory
//           dir:PATH  every (spec, cfg) pair under PATH (e.g. the cfg directory written by feynman-bench.ts);
//                     a Module-*.cfg beside Module.tla is run against Module.tla
//   env: EXAMPLES (default /home/user/refs/Examples), TLC_TESTS (default the test-model dir of /home/user/refs/tlaplus)
import fs from 'node:fs';
import path from 'node:path';
import { spawn } from 'node:child_process';

const args = process.argv.slice(2);
const opt = (n, d) => { const i = args.indexOf(n); return i >= 0 ? args[i + 1] : d; };
const here = path.resolve(import.meta.dirname, '..');
const BIN = path.join(here, 'target/release/everystate');
const EXAMPLES = process.env.EXAMPLES ?? '/home/user/refs/Examples';
const TLC_TESTS = process.env.TLC_TESTS ?? '/home/user/refs/tlaplus/tlatools/org.lamport.tlatools/test-model';
const jobs = Number(opt('--jobs', 3)), timeout = Number(opt('--timeout', 120)) * 1000, maxRuntime = Number(opt('--max-runtime', 5));
const filter = opt('--filter', '');
const extraEnv = {};
args.forEach((a, i) => { if (a === '--env') { const [k, ...v] = args[i + 1].split('='); extraEnv[k] = v.join('='); } });
const side = s => {
  if (!s) throw new Error('--a and --b are required');
  if (s.startsWith('engine:')) return { bin: BIN, env: { EVERYSTATE_ENGINE: s.slice(7) }, name: s };
  if (s.startsWith('env:')) { const [k, ...v] = s.slice(4).split('='); return { bin: BIN, env: { [k]: v.join('=') }, name: s }; }
  return { bin: path.resolve(s), env: {}, name: s };
};
const A = side(opt('--a')), B = side(opt('--b'));

const cases = []; // { cwd, cfg, spec, flags }
const pairsUnder = (root, flags) => {
  const walk = d => {
    for (const f of fs.readdirSync(d, { withFileTypes: true })) {
      const p = path.join(d, f.name);
      if (f.isDirectory()) walk(p);
      else if (f.name.endsWith('.cfg')) {
        let spec = p.slice(0, -4) + '.tla';
        if (!fs.existsSync(spec) && f.name.includes('-')) spec = path.join(d, f.name.split('-')[0] + '.tla');
        if (fs.existsSync(spec)) cases.push({ cwd: d, cfg: f.name, spec: path.basename(spec), flags });
      }
    }
  };
  walk(root);
};
for (const c of opt('--corpus', 'examples,bench').split(',')) {
  if (c === 'examples') {
    const secs = r => r === 'unknown' ? 1e9 : r.split(':').reduce((a, x) => a * 60 + Number(x), 0);
    for (const d of fs.readdirSync(path.join(EXAMPLES, 'specifications'))) {
      const mf = path.join(EXAMPLES, 'specifications', d, 'manifest.json');
      if (!fs.existsSync(mf)) continue;
      for (const mod of JSON.parse(fs.readFileSync(mf, 'utf8')).modules) for (const m of mod.models) {
        if (m.mode !== 'exhaustive search' || secs(m.runtime) > maxRuntime || m.result === 'unknown') continue;
        cases.push({ cwd: EXAMPLES, cfg: m.path, spec: mod.path, flags: ['-Dtlc2.tool.impl.Tool.cdot=true'] });
      }
    }
  } else if (c === 'bench') {
    const src = fs.readFileSync(path.join(here, 'scripts/bench.mjs'), 'utf8');
    for (const m of src.matchAll(/\['(specifications\/[^']+\.cfg)', '(specifications\/[^']+\.tla)'/g)) cases.push({ cwd: EXAMPLES, cfg: m[1], spec: m[2], flags: [] });
  } else if (c === 'tlc') pairsUnder(TLC_TESTS, []);
  else if (c.startsWith('dir:')) pairsUnder(path.resolve(c.slice(4)), ['-deadlock']);
  else throw new Error(`unknown corpus ${c}`);
}
const todo = cases.filter(c => !filter || path.join(c.cwd, c.cfg).includes(filter));

const run = (s, c, json) => new Promise(res => {
  const p = spawn(s.bin, [...c.flags, ...(json ? ['-json'] : []), '-config', c.cfg, c.spec], { cwd: c.cwd, stdio: ['ignore', 'pipe', 'pipe'], env: { ...process.env, ...extraEnv, ...s.env } });
  let o = '', e = '';
  p.stdout.on('data', d => { if (o.length < 64e6) o += d; });
  p.stderr.on('data', d => { if (e.length < 4e6) e += d; });
  const timer = setTimeout(() => p.kill('SIGKILL'), timeout);
  p.on('close', (code, sig) => { clearTimeout(timer); res({ o, e, code, timedOut: sig === 'SIGKILL' }); });
});
// what may differ between two runs of the same model: clock readings
const scrub = s => s
  .replace(/\(\d{4}-\d\d-\d\d \d\d:\d\d:\d\d\)/g, '(T)')
  .replace(/\d{4}-\d\d-\d\d \d\d:\d\d:\d\d/g, 'T')
  .replace(/Finished in [^\n]*/g, 'Finished in D')
  .replace(/\(\d[\d,]* s\/min, \d[\d,]* ds\/min\)/g, '(RATE)')
  .replace(/"(ms|elapsedMs|durationMs|seconds)":\s*[\d.]+/g, '"$1":0')
  .replace(/in \d+(\.\d+)?\s?(ms|s|min)\b/g, 'in D');
const firstDiff = (x, y) => {
  const a = x.split('\n'), b = y.split('\n');
  for (let i = 0; i < Math.max(a.length, b.length); i++) if (a[i] !== b[i]) return `line ${i + 1}: A=${(a[i] ?? '<end>').slice(0, 160)} | B=${(b[i] ?? '<end>').slice(0, 160)}`;
  return '';
};
let next = 0, same = 0, skipped = 0;
const diffs = [];
async function worker() {
  while (next < todo.length) {
    const c = todo[next++];
    const id = path.join(c.cwd, c.cfg);
    let bad = '';
    for (const json of [true, false]) {
      const [ra, rb] = [await run(A, c, json), await run(B, c, json)];
      if (ra.timedOut || rb.timedOut) {
        // a model too big for the time limit proves nothing either way, unless only one side is too slow
        if (ra.timedOut !== rb.timedOut) bad = `${json ? 'json' : 'text'}: only ${ra.timedOut ? 'A' : 'B'} timed out`;
        else bad = 'skip';
        break;
      }
      if (ra.code !== rb.code) { bad = `${json ? 'json' : 'text'}: exit ${ra.code} vs ${rb.code}`; break; }
      const [x, y] = [scrub(ra.o), scrub(rb.o)];
      if (x !== y) { bad = `${json ? 'json' : 'text'} stdout: ${firstDiff(x, y)}`; break; }
      const [ex, ey] = [scrub(ra.e), scrub(rb.e)];
      if (ex !== ey) { bad = `${json ? 'json' : 'text'} stderr: ${firstDiff(ex, ey)}`; break; }
    }
    if (bad === 'skip') skipped++;
    else if (bad) { diffs.push(`${id}: ${bad}`); process.stderr.write('X'); }
    else { same++; if (same % 20 === 0) process.stderr.write('.'); }
  }
}
await Promise.all(Array.from({ length: jobs }, worker));
process.stderr.write('\n');
for (const d of diffs) console.log('DIFF ' + d);
console.log(`A=${A.name} B=${B.name}: ${todo.length} models, ${same} identical, ${diffs.length} different, ${skipped} skipped (both timed out)`);
process.exit(diffs.length ? 1 : 0);
