#!/usr/bin/env node
// Runs models with EVERYSTATE_CACHE_STATS=1 and tabulates the step-cache estimate per model:
// action-instance evaluations, distinct (instance, reads) keys, hit rate, and the worst action.
// usage: node scripts/cache-stats.mjs [--bin PATH] [--corpus examples,bench,dir:PATH] [--timeout SEC] [--min-calls N] [--json FILE]
import fs from 'node:fs';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
const args = process.argv.slice(2);
const opt = (n, d) => { const i = args.indexOf(n); return i >= 0 ? args[i + 1] : d; };
const here = path.resolve(import.meta.dirname, '..');
const BIN = path.resolve(opt('--bin', path.join(here, 'target/release/everystate')));
const EXAMPLES = process.env.EXAMPLES ?? '/home/user/refs/Examples';
const timeout = Number(opt('--timeout', 120)) * 1000, minCalls = Number(opt('--min-calls', 0)), maxRuntime = Number(opt('--max-runtime', 5));
const cases = [];
for (const c of opt('--corpus', 'bench').split(',')) {
  if (c === 'examples') {
    const secs = r => r === 'unknown' ? 1e9 : r.split(':').reduce((a, x) => a * 60 + Number(x), 0);
    for (const d of fs.readdirSync(path.join(EXAMPLES, 'specifications'))) {
      const mf = path.join(EXAMPLES, 'specifications', d, 'manifest.json');
      if (!fs.existsSync(mf)) continue;
      for (const mod of JSON.parse(fs.readFileSync(mf, 'utf8')).modules) for (const m of mod.models) {
        if (m.mode !== 'exhaustive search' || secs(m.runtime) > maxRuntime || m.result === 'unknown') continue;
        cases.push({ cwd: EXAMPLES, cfg: m.path, spec: mod.path, flags: ['-Dtlc2.tool.impl.Tool.cdot=true'], name: path.basename(m.path, '.cfg') });
      }
    }
  } else if (c === 'bench') {
    const src = fs.readFileSync(path.join(here, 'scripts/bench.mjs'), 'utf8');
    for (const m of src.matchAll(/\['(specifications\/[^']+\.cfg)', '(specifications\/[^']+\.tla)'/g)) cases.push({ cwd: EXAMPLES, cfg: m[1], spec: m[2], flags: [], name: path.basename(m[1], '.cfg') });
  } else if (c.startsWith('dir:')) {
    const root = path.resolve(c.slice(4));
    for (const d of fs.readdirSync(root).sort()) {
      const p = path.join(root, d);
      if (!fs.statSync(p).isDirectory()) continue;
      for (const f of fs.readdirSync(p)) if (f.endsWith('.cfg') && fs.existsSync(path.join(p, f.slice(0, -4) + '.tla'))) cases.push({ cwd: p, cfg: f, spec: f.slice(0, -4) + '.tla', flags: ['-deadlock'], name: d });
    }
  } else throw new Error(`unknown corpus ${c}`);
}
const rows = [];
console.log(['model'.padEnd(34), 'distinct'.padStart(9), 'calls'.padStart(10), 'keys'.padStart(9), 'hit %'.padStart(7), 'uncach %'.padStart(8), ' worst action (calls, hit %)'].join(' '));
for (const c of cases) {
  const r = spawnSync(BIN, [...c.flags, '-json', '-config', c.cfg, c.spec], { cwd: c.cwd, encoding: 'utf8', timeout, maxBuffer: 1 << 28, env: { ...process.env, EVERYSTATE_CACHE_STATS: '1' } });
  let j = {};
  try { j = JSON.parse(r.stdout.trim().split('\n').at(-1)); } catch {}
  const tot = /total: (\d+) calls, (\d+) distinct keys .*?hit rate ([\d.]+)%, uncacheable ([\d.]+)%/.exec(r.stderr ?? '');
  if (!tot) { console.log(`${c.name.padEnd(34)} ${r.error?.code === 'ETIMEDOUT' ? 'timeout' : 'no estimate (' + (j.status ?? 'no result') + ')'}`); continue; }
  // the action with the most misses
  let worst = null;
  for (const m of (r.stderr ?? '').matchAll(/^  (.+?)\s+line\s+(\d+) col\s+(\d+)\s+(\d+)\s+(\d+)\s+([\d.]+)%\s+([\d.]+)%/gm)) {
    const calls = +m[4], hit = +m[6], miss = calls * (1 - hit / 100);
    if (!worst || miss > worst.miss) worst = { name: `${m[1].trim()}@${m[2]}`, calls, hit, miss };
  }
  const row = { model: c.name, status: j.status, distinct: j.distinct, calls: +tot[1], keys: +tot[2], hit: +tot[3], uncacheable: +tot[4], worst: worst && { name: worst.name, calls: worst.calls, hit: worst.hit } };
  if (row.calls < minCalls) continue;
  rows.push(row);
  console.log([c.name.slice(0, 34).padEnd(34), String(row.distinct ?? '?').padStart(9), String(row.calls).padStart(10), String(row.keys).padStart(9), row.hit.toFixed(2).padStart(7), row.uncacheable.toFixed(2).padStart(8), worst ? ` ${worst.name.slice(0, 40)} (${worst.calls}, ${worst.hit}%)` : ''].join(' '));
}
if (opt('--json', '')) fs.writeFileSync(opt('--json'), JSON.stringify(rows, null, 1) + '\n');
