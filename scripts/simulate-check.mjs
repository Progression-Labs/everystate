// Cross-checks simulation mode against exhaustive checking on the small models of the tlaplus/Examples
// corpus: a model that passes exhaustively must pass every simulation run, and for a model that fails
// exhaustively the script reports whether simulation finds the same violation. Every simulation runs
// with EVERYSTATE_SIM_REPLAY=1, so each reported trace is replayed against the exhaustive checker's
// initial states and successor function (a trace that is not a behaviour gives status "replay-failed").
// usage: node scripts/simulate-check.mjs EXAMPLES_DIR [--max-runtime SEC] [--timeout SEC] [--traces N]
//          [--depth N] [--seeds N] [--filter STR] [--jobs N] [--list]
import fs from 'node:fs';
import path from 'node:path';
import { spawn } from 'node:child_process';
const args = process.argv.slice(2);
const root = args[0];
const opt = (n, d) => { const i = args.indexOf(n); return i >= 0 ? args[i + 1] : d; };
const maxRuntime = Number(opt('--max-runtime', 5)), timeout = Number(opt('--timeout', 120)) * 1000;
const traces = Number(opt('--traces', 500)), depth = Number(opt('--depth', 100)), seeds = Number(opt('--seeds', 3));
const filter = opt('--filter', ''), jobs = Number(opt('--jobs', 4));
const bin = process.env.EVERYSTATE_CMD ?? path.resolve(import.meta.dirname, '../target/release/everystate');
const secs = r => r === 'unknown' ? 1e9 : r.split(':').reduce((a, x) => a * 60 + Number(x), 0);
const cases = [];
for (const d of fs.readdirSync(path.join(root, 'specifications'))) {
  const mf = path.join(root, 'specifications', d, 'manifest.json');
  if (!fs.existsSync(mf)) continue;
  for (const mod of JSON.parse(fs.readFileSync(mf, 'utf8')).modules) for (const m of mod.models) {
    if (m.mode !== 'exhaustive search' || secs(m.runtime) > maxRuntime || m.result === 'unknown') continue;
    if (filter && !m.path.includes(filter)) continue;
    cases.push({ spec: path.join(root, mod.path), cfg: path.join(root, m.path) });
  }
}
const run = (argv) => new Promise(res => {
  const p = spawn(bin, ['-Dtlc2.tool.impl.Tool.cdot=true', '-json', ...argv], { stdio: ['ignore', 'pipe', 'pipe'], env: { ...process.env, EVERYSTATE_SIM_REPLAY: '1' } });
  let o = '';
  p.stdout.on('data', d => { o += d; });
  const timer = setTimeout(() => p.kill('SIGKILL'), timeout);
  p.on('close', (code, sig) => {
    clearTimeout(timer);
    let r = null;
    try { r = JSON.parse(o.trim().split('\n').pop()); } catch {}
    res(sig === 'SIGKILL' ? { status: 'timeout' } : r ?? { status: 'crash' });
  });
});
const what = r => r.status + (r.name ? ' ' + r.name : '');
const results = [];
let next = 0;
async function worker() {
  while (next < cases.length) {
    const c = cases[next++];
    const full = await run(['-config', c.cfg, c.spec]);
    const sims = [];
    for (let seed = 1; seed <= seeds; seed++) sims.push(await run(['-simulate', `num=${traces}`, '-depth', String(depth), '-seed', String(seed), '-config', c.cfg, c.spec]));
    const bad = sims.filter(s => ['replay-failed', 'crash', 'timeout'].includes(s.status));
    let verdict, detail = '';
    if (bad.length) { verdict = 'BROKEN'; detail = bad.map(s => s.status + ': ' + (s.message ?? '')).join(' | '); }
    else if (full.status === 'ok') {
      const wrong = sims.filter(s => s.status !== 'ok');
      verdict = wrong.length ? 'FALSE-ALARM' : 'OK-OK';
      detail = wrong.map(s => `seed ${s.seed}: ${what(s)} ${(s.message ?? '').split('\n')[0]}`).join(' | ');
    } else {
      const found = sims.filter(s => what(s) === what(full)).length, other = sims.filter(s => s.status !== 'ok' && what(s) !== what(full));
      verdict = found ? 'FOUND' : other.length ? 'OTHER' : 'MISSED';
      detail = `exhaustive: ${what(full)}; simulation: ${sims.map(what).join(', ')}`;
    }
    results.push({ verdict, cfg: path.relative(root, c.cfg), detail, generated: sims.reduce((a, s) => a + (s.generated ?? 0), 0) });
    process.stderr.write(verdict === 'OK-OK' ? '.' : verdict[0]);
  }
}
await Promise.all(Array.from({ length: jobs }, worker));
process.stderr.write('\n');
const tally = {};
for (const r of results) tally[r.verdict] = (tally[r.verdict] ?? 0) + 1;
results.sort((a, b) => a.cfg.localeCompare(b.cfg));
for (const r of results) if (r.verdict !== 'OK-OK' || args.includes('--list')) console.log(`${r.verdict.padEnd(11)} ${r.cfg}  ${r.detail}`);
console.log(JSON.stringify(tally), `of ${results.length} models, ${seeds} seeds x ${traces} traces each`);
process.exit(tally.BROKEN || tally['FALSE-ALARM'] ? 1 : 0);
