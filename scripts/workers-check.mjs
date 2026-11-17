// Checks that `-workers N` gives the result of `-workers 1` on the tlaplus/Examples corpus: the whole
// `-json` result line must be identical (verdict, violated property, message, generated / distinct
// state counts, queue, depth and the complete counterexample trace).
//
// usage: node scripts/workers-check.mjs EXAMPLES_DIR [--workers 4] [--eager] [--chunk N] [--repeat 1]
//          [--max-runtime SEC] [--timeout SEC] [--filter STR] [--jobs 2] [--dump]
//
//   --eager    start the workers at the first level and search every level in parallel, however small
//              (EVERYSTATE_PAR_MIN=1); without it the binary decides, as in normal use
//   --chunk N  states per unit of work (EVERYSTATE_PAR_CHUNK); 1 interleaves the workers as much as possible
//   --repeat K run the parallel side K times per model (to catch races)
//   --dump     also compare the `-dump dot,actionlabels` state graph byte for byte
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { spawn } from 'node:child_process';
const args = process.argv.slice(2);
const root = args[0];
const opt = (n, d) => { const i = args.indexOf(n); return i >= 0 ? args[i + 1] : d; };
const maxRuntime = Number(opt('--max-runtime', 5)), timeout = Number(opt('--timeout', 120)) * 1000;
const filter = opt('--filter', ''), jobs = Number(opt('--jobs', 2));
const workers = opt('--workers', '4'), repeat = Number(opt('--repeat', 1));
const eager = args.includes('--eager'), chunk = opt('--chunk', ''), dump = args.includes('--dump');
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
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'workers-check-'));
let seq = 0;
function run(c, w, par) {
  return new Promise(res => {
    const env = { ...process.env };
    delete env.EVERYSTATE_PAR_MIN; delete env.EVERYSTATE_PAR_CHUNK;
    env.EVERYSTATE_PAR_DEBUG = '1';
    if (par && eager) env.EVERYSTATE_PAR_MIN = '1';
    if (par && chunk) env.EVERYSTATE_PAR_CHUNK = chunk;
    const dot = dump ? path.join(tmp, `g${seq++}.dot`) : null;
    const argv = ['-Dtlc2.tool.impl.Tool.cdot=true', '-workers', String(w), '-json', ...(dot ? ['-dump', 'dot,actionlabels', dot] : []), '-config', c.cfg, c.spec];
    const p = spawn(bin, argv, { stdio: ['ignore', 'pipe', 'pipe'], env });
    let o = '', e = '';
    p.stdout.on('data', d => { o += d; }); p.stderr.on('data', d => { e += d; });
    const timer = setTimeout(() => { p.kill('SIGKILL'); }, timeout);
    p.on('close', (code, sig) => {
      clearTimeout(timer);
      let graph = '';
      if (dot && fs.existsSync(dot)) { graph = fs.readFileSync(dot, 'utf8'); fs.rmSync(dot); }
      res({ out: o.trim().split('\n').pop() ?? '', all: o, err: e, code, sig, graph });
    });
  });
}
const results = [];
let next = 0;
async function worker() {
  while (next < cases.length) {
    const c = cases[next++];
    const base = await run(c, 1, false);
    let verdict = 'SAME', detail = '', how = '';
    for (let k = 0; k < repeat && verdict === 'SAME'; k++) {
      const par = await run(c, workers, true);
      const dbg = /^par: (\d+) levels, (\d+) of (\d+) states expanded by workers(?:; stopped: (.*))?$/m.exec(par.err);
      how = !dbg ? 'no parallel search' : dbg[4] ? (dbg[4] === 'violation or error' ? 'parallel until the violation' : 'fell back: ' + dbg[4]) : dbg[1] === '0' ? 'never parallel (small)' : 'parallel';
      if (base.sig || par.sig) { verdict = 'TIMEOUT'; }
      else if (par.code !== base.code) { verdict = 'DIFF'; detail = `exit ${par.code} != ${base.code} ${par.err.slice(0, 300)}`; }
      else if (par.all !== base.all) {
        verdict = 'DIFF';
        let a = null, b = null;
        try { a = JSON.parse(base.out); b = JSON.parse(par.out); } catch {}
        if (a && b) {
          const d = [];
          for (const k of ['status', 'name', 'message', 'generated', 'distinct', 'queue', 'depth']) if (JSON.stringify(a[k]) !== JSON.stringify(b[k])) d.push(`${k} ${JSON.stringify(b[k])} != ${JSON.stringify(a[k])}`);
          if ((a.trace?.length ?? -1) !== (b.trace?.length ?? -1)) d.push(`trace length ${b.trace?.length} != ${a.trace?.length}`);
          else if (JSON.stringify(a.trace) !== JSON.stringify(b.trace)) d.push('same trace length, different trace');
          detail = d.join(', ') || 'output differs';
        } else detail = `no JSON result: ${(par.err || par.all).slice(0, 300)}`;
      }
      else if (par.graph !== base.graph) { verdict = 'DIFF'; detail = 'state graph dump differs'; }
    }
    results.push({ verdict, cfg: path.relative(root, c.cfg), detail, how });
    process.stderr.write(verdict === 'SAME' ? '.' : verdict[0]);
  }
}
await Promise.all(Array.from({ length: jobs }, worker));
process.stderr.write('\n');
fs.rmSync(tmp, { recursive: true, force: true });
const tally = {};
for (const r of results) tally[r.verdict] = (tally[r.verdict] ?? 0) + 1;
results.sort((a, b) => a.cfg.localeCompare(b.cfg));
for (const r of results) if (r.verdict !== 'SAME') console.log(`${r.verdict.padEnd(7)} ${r.cfg}  ${r.detail}`);
console.log(`workers ${workers}${eager ? ' eager' : ''}${chunk ? ' chunk ' + chunk : ''}${repeat > 1 ? ' x' + repeat : ''}${dump ? ' +dump' : ''}:`, JSON.stringify(tally), `of ${results.length}`);
const hows = {};
for (const r of results) hows[r.how] = (hows[r.how] ?? 0) + 1;
console.log('how the parallel runs went:', JSON.stringify(hows, null, 1));
if (args.includes('--list')) for (const r of results) console.log(`  ${r.how.padEnd(40)} ${r.cfg}`);
process.exit(results.every(r => r.verdict === 'SAME') ? 0 : 1);
