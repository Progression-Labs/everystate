#!/usr/bin/env node
// Wall-clock time of the larger benchmark models with 1, 2 and 4 workers: everystate (`-workers N`)
// against Java TLC (`-workers N`). The machine's 1-minute load average is recorded at the start of
// every single run, and so is the number of cores that were busy during the second before it (from
// /proc/stat; the load average also counts the benchmark's own earlier runs), because a busy machine
// hides a speedup.
//
// usage: node scripts/bench-workers.mjs [--runs 3] [--workers 1,2,4] [--only substring] [--skip tlc]
//                                       [--wait-load 1.0] [--timeout 900]
//   --wait-busy C   before each run, wait (up to 5 minutes) until fewer than C cores are busy
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { spawnSync } from 'node:child_process';

const here = path.resolve(import.meta.dirname, '..');
const EXAMPLES = process.env.EXAMPLES ?? '/home/user/refs/Examples';
const TLA2TOOLS = process.env.TLA2TOOLS ?? '/home/user/refs/tla2tools.jar';
const TLA_LIBRARY = process.env.TLA_LIBRARY ?? '/home/user/refs/tlapm/library:/home/user/refs/CommunityModules/modules';
const RS = process.env.EVERYSTATE_CMD ?? path.join(here, 'target/release/everystate');
const args = process.argv.slice(2);
const opt = (n, d) => { const i = args.indexOf(n); return i >= 0 ? args[i + 1] : d; };
const RUNS = Number(opt('--runs', 3)), ONLY = opt('--only', ''), SKIP = opt('--skip', '').split(',');
const WORKERS = opt('--workers', '1,2,4').split(',').map(Number);
const WAIT = Number(opt('--wait-busy', 0)), TIMEOUT = Number(opt('--timeout', 900)) * 1000;
const MODELS = [
  ['specifications/byzpaxos/VoteProof.cfg', 'specifications/byzpaxos/VoteProof.tla'],
  ['specifications/NanoBlockchain/MCNanoMedium.cfg', 'specifications/NanoBlockchain/MCNano.tla'],
  ['specifications/Bakery-Boulangerie/MCBakery.cfg', 'specifications/Bakery-Boulangerie/MCBakery.tla'],
  ['specifications/lamport_mutex/MCLamportMutex.cfg', 'specifications/lamport_mutex/MCLamportMutex.tla'],
  ['specifications/btree/MCbtree.cfg', 'specifications/btree/MCbtree.tla'],
  ['specifications/GameOfLife/GameOfLife.cfg', 'specifications/GameOfLife/GameOfLife.tla'],
].filter(m => !ONLY || m[0].includes(ONLY));

const sleep = ms => Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, ms);
const stat = () => { try { return fs.readFileSync('/proc/stat', 'utf8').split('\n')[0].trim().split(/\s+/).slice(1, 9).map(Number); } catch { return null; } };
/** Cores busy over the next second (all processes); NaN where /proc/stat does not exist. */
function busyCores() {
  const a = stat();
  sleep(1000);
  const b = stat();
  if (!a || !b) return NaN;
  const d = b.map((x, i) => x - a[i]), total = d.reduce((x, y) => x + y, 0);
  return total ? os.cpus().length * (total - d[3] - d[4]) / total : NaN;
}
function calm() {
  let busy = busyCores();
  for (let i = 0; WAIT && i < 150 && busy >= WAIT; i++) { sleep(1000); busy = busyCores(); }
  return busy;
}
function timed(cmd, argv, opts) {
  const busy = calm();
  const load = os.loadavg()[0];
  const t0 = process.hrtime.bigint();
  const r = spawnSync(cmd, argv, { encoding: 'utf8', timeout: TIMEOUT, maxBuffer: 1 << 28, ...opts });
  return { secs: Number(process.hrtime.bigint() - t0) / 1e9, load, busy, out: (r.stdout ?? '') + (r.stderr ?? '') };
}
const engines = {
  everystate: (cfg, spec, w) => {
    const r = timed(RS, ['-workers', String(w), '-json', '-config', cfg, spec], { cwd: EXAMPLES });
    let j = null;
    try { j = JSON.parse(r.out.trim().split('\n').pop()); } catch {}
    return { ...r, counts: j ? `${j.status} ${j.generated}/${j.distinct}` : 'no result', depth: j?.depth };
  },
  tlc: (cfg, spec, w) => {
    const meta = fs.mkdtempSync(path.join(os.tmpdir(), 'tlc-meta-'));
    const env = { ...process.env }; delete env.JAVA_TOOL_OPTIONS;
    const r = timed('java', ['-XX:+UseParallelGC', `-DTLA-Library=${TLA_LIBRARY}`, '-cp', TLA2TOOLS, 'tlc2.TLC', '-workers', String(w), '-metadir', meta,
      '-config', path.join(EXAMPLES, cfg), path.basename(spec)], { cwd: path.dirname(path.join(EXAMPLES, spec)), env });
    fs.rmSync(meta, { recursive: true, force: true });
    const m = /(\d+) states generated, (\d+) distinct states found/.exec(r.out);
    return { ...r, counts: m && /No error has been found/.test(r.out) ? `ok ${m[1]}/${m[2]}` : 'no result' };
  },
};
for (const s of SKIP) delete engines[s];
const med = a => [...a].sort((x, y) => x - y)[Math.floor(a.length / 2)];
const rows = [];
for (const [cfg, spec] of MODELS) {
  const name = path.basename(cfg, '.cfg');
  const row = { name, cells: {}, counts: new Set(), depths: new Set() };
  for (const [eng, run] of Object.entries(engines)) for (const w of WORKERS) {
    const secs = [], loads = [], busy = [];
    for (let i = 0; i < RUNS; i++) {
      const r = run(cfg, spec, w);
      secs.push(r.secs); loads.push(r.load); busy.push(r.busy); row.counts.add(r.counts); if (eng === 'everystate') row.depths.add(r.depth);
      process.stderr.write(`${name} ${eng} workers=${w} run ${i + 1}: ${r.secs.toFixed(2)} s (load ${r.load.toFixed(2)}, ${r.busy.toFixed(1)} cores busy before) ${r.counts}\n`);
    }
    row.cells[`${eng}${w}`] = { med: med(secs), min: Math.min(...secs), load: med(loads), busy: med(busy) };
  }
  rows.push(row);
}
const cols = Object.keys(engines).flatMap(e => WORKERS.map(w => `${e}${w}`));
const f = x => x.toFixed(2);
console.log(`Median (best) wall-clock seconds of ${RUNS} runs; "load" is the range over the cells of the median 1-minute load average at the start of a run, "busy" the same for the number of cores in use during the second before a run.\n`);
console.log(`| model | ${Object.keys(engines).flatMap(e => WORKERS.map(w => `${e} ${w}w s`)).join(' | ')} | ${Object.keys(engines).flatMap(e => WORKERS.filter(w => w > 1).map(w => `${e} speedup ${w}w`)).join(' | ')} | load | busy | counts agree |`);
console.log(`|---|${cols.map(() => '---:').join('|')}|${Object.keys(engines).flatMap(e => WORKERS.filter(w => w > 1).map(() => '---:')).join('|')}|---|---|---|`);
for (const r of rows) {
  const sp = Object.keys(engines).flatMap(e => WORKERS.filter(w => w > 1).map(w => r.cells[`${e}1`] ? `${f(r.cells[`${e}1`].med / r.cells[`${e}${w}`].med)}x (${f(r.cells[`${e}1`].min / r.cells[`${e}${w}`].min)}x)` : '-'));
  const loads = cols.map(c => r.cells[c].load), bus = cols.map(c => r.cells[c].busy);
  console.log(`| ${r.name} | ${cols.map(c => `${f(r.cells[c].med)} (${f(r.cells[c].min)})`).join(' | ')} | ${sp.join(' | ')} | ${f(Math.min(...loads))}-${f(Math.max(...loads))} | ${f(Math.min(...bus))}-${f(Math.max(...bus))} | ${r.counts.size === 1 && r.depths.size <= 1 ? 'yes' : 'NO: ' + [...r.counts].join(' vs ')} |`);
}
