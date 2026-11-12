// Runs verify.js on the tlaplus/Examples corpus and compares against the results recorded in the
// official manifest.json files (result kind, distinct states, total states, depth).
// usage: node scripts/conformance.mjs EXAMPLES_DIR [--max-runtime SEC] [--timeout SEC] [--filter STR] [--jobs N]
import fs from 'node:fs';
import path from 'node:path';
import { spawn } from 'node:child_process';
const args = process.argv.slice(2);
const root = args[0];
const opt = (n, d) => { const i = args.indexOf(n); return i >= 0 ? args[i + 1] : d; };
const maxRuntime = Number(opt('--max-runtime', 30)), timeout = Number(opt('--timeout', 120)) * 1000;
const filter = opt('--filter', ''), jobs = Number(opt('--jobs', 4));
const cli = path.resolve(import.meta.dirname, '../src/cli.ts');
const secs = r => r === 'unknown' ? 1e9 : r.split(':').reduce((a, x) => a * 60 + Number(x), 0);
const cases = [];
for (const d of fs.readdirSync(path.join(root, 'specifications'))) {
  const mf = path.join(root, 'specifications', d, 'manifest.json');
  if (!fs.existsSync(mf)) continue;
  for (const mod of JSON.parse(fs.readFileSync(mf, 'utf8')).modules) for (const m of mod.models) {
    if (m.mode !== 'exhaustive search' || secs(m.runtime) > maxRuntime || m.result === 'unknown') continue;
    if (filter && !m.path.includes(filter)) continue;
    cases.push({ spec: path.join(root, mod.path), cfg: path.join(root, m.path), exp: m });
  }
}
const kind = s => ({ ok: 'success', invariant: 'safety failure', 'invariant-init': 'safety failure', 'action-property': 'safety failure',
  'implied-init': 'safety failure', deadlock: 'deadlock failure', liveness: 'liveness failure', assumption: 'assumption failure' }[s] ?? s);
const results = [];
let next = 0;
async function worker() {
  while (next < cases.length) {
    const c = cases[next++];
    const t0 = Date.now();
    const out = await new Promise(res => {
      const p = spawn(process.execPath, ['--experimental-strip-types', '--no-warnings', '--stack-size=30000', '--max-old-space-size=3000', cli, '-json', '-config', c.cfg, c.spec], { stdio: ['ignore', 'pipe', 'pipe'] });
      let o = '', e = '';
      p.stdout.on('data', d => { o += d; }); p.stderr.on('data', d => { e += d; });
      const timer = setTimeout(() => { p.kill('SIGKILL'); }, timeout);
      p.on('close', (code, sig) => { clearTimeout(timer); res({ o, e, code, sig }); });
    });
    let r = null;
    try { r = JSON.parse(out.o.trim().split('\n').pop()); } catch {}
    let verdict, detail = '';
    if (out.sig === 'SIGKILL') { verdict = 'TIMEOUT'; }
    else if (!r) { verdict = 'CRASH'; detail = (out.e || out.o).trim().split('\n').slice(0, 3).join(' | ').slice(0, 300); }
    else if (kind(r.status) !== c.exp.result) { verdict = 'FAIL'; detail = `expected ${c.exp.result}, got ${r.status}${r.name ? ' ' + r.name : ''}: ${(r.message ?? '').split('\n').slice(0, 3).join(' | ').slice(0, 300)}`; }
    else {
      const diffs = [];
      if (c.exp.result === 'success') {
        if (c.exp.distinctStates !== undefined && c.exp.distinctStates !== r.distinct) diffs.push(`distinct ${r.distinct} != ${c.exp.distinctStates}`);
        if (c.exp.totalStates !== undefined && c.exp.totalStates !== r.generated) diffs.push(`generated ${r.generated} != ${c.exp.totalStates}`);
        if (args.includes("--depth") && c.exp.stateDepth !== undefined && c.exp.stateDepth !== r.depth) diffs.push(`depth ${r.depth} != ${c.exp.stateDepth}`);
      }
      verdict = diffs.length ? 'COUNT' : 'PASS'; detail = diffs.join(', ');
    }
    results.push({ verdict, cfg: path.relative(root, c.cfg), detail, ms: Date.now() - t0 });
    process.stderr.write(verdict === 'PASS' ? '.' : verdict[0]);
  }
}
await Promise.all(Array.from({ length: jobs }, worker));
process.stderr.write('\n');
const tally = {};
for (const r of results) tally[r.verdict] = (tally[r.verdict] ?? 0) + 1;
results.sort((a, b) => a.cfg.localeCompare(b.cfg));
for (const r of results) if (r.verdict !== 'PASS') console.log(`${r.verdict.padEnd(7)} ${r.cfg}  ${r.detail}`);
console.log(JSON.stringify(tally), `of ${results.length}`);
if (args.includes('--times')) for (const r of results.sort((a, b) => b.ms - a.ms).slice(0, 15)) console.log(r.ms, r.cfg);
