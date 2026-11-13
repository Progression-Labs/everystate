#!/usr/bin/env node
// Head-to-head benchmark: everystate (Rust, native and WebAssembly) vs the TypeScript implementation (Node and Bun) vs Java TLC,
// all single-threaded, on a fixed list of safety-only models from tlaplus/Examples.
//
// usage: node scripts/bench.mjs [--runs 3] [--only substring] [--skip tlc,bun] [--timeout 900]
//
// Every engine is run RUNS times per model, sequentially; the median wall-clock time is reported.
// All engines must report the same generated/distinct state counts, otherwise the row is flagged.
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { spawnSync } from 'node:child_process';

const here = path.resolve(import.meta.dirname, '..');
const EXAMPLES = process.env.EXAMPLES ?? '/home/user/refs/Examples';
const TS_CLI = process.env.TS_CLI ?? path.resolve(here, 'ts-engine-removed/cli.ts');
const TLA2TOOLS = process.env.TLA2TOOLS ?? '/home/user/refs/tla2tools.jar';
const TLA_LIBRARY = process.env.TLA_LIBRARY ?? '/home/user/refs/tlapm/library:/home/user/refs/CommunityModules/modules';
const RS = path.join(here, 'target/release/everystate');
const WASM_CLI = path.join(here, 'wasm/cli.mjs');

const args = process.argv.slice(2);
const opt = (n, d) => { const i = args.indexOf(n); return i >= 0 ? args[i + 1] : d; };
const RUNS = Number(opt('--runs', 3));
const ONLY = opt('--only', '');
const SKIP = opt('--skip', '').split(',').filter(Boolean);
const TIMEOUT = Number(opt('--timeout', 900)) * 1000;

// [config path relative to EXAMPLES, spec path, note]
const MODELS = [
  ['specifications/transaction_commit/TCommit.cfg', 'specifications/transaction_commit/TCommit.tla', 'tiny (startup)'],
  ['specifications/acp/ACP_SB_TLC.cfg', 'specifications/acp/ACP_SB_TLC.tla', 'sets, quantifiers'],
  ['specifications/StaleViewShrink/StaleShrinkV6Wait2x.cfg', 'specifications/StaleViewShrink/StaleShrink.tla', 'records'],
  ['specifications/barriers/Barriers.cfg', 'specifications/barriers/Barriers.tla', 'functions (PlusCal)'],
  ['specifications/TeachingConcurrency/SimpleRegular.cfg', 'specifications/TeachingConcurrency/SimpleRegular.tla', 'functions (PlusCal)'],
  ['specifications/SimplifiedFastPaxos/Paxos.cfg', 'specifications/SimplifiedFastPaxos/Paxos.tla', 'symmetry, sets of records'],
  ['specifications/byzpaxos/VoteProof.cfg', 'specifications/byzpaxos/VoteProof.tla', 'set heavy, quantifiers'],
  ['specifications/NanoBlockchain/MCNanoMedium.cfg', 'specifications/NanoBlockchain/MCNano.tla', 'VIEW, records, sets'],
  ['specifications/Bakery-Boulangerie/MCBakery.cfg', 'specifications/Bakery-Boulangerie/MCBakery.tla', 'functions (PlusCal)'],
  ['specifications/lamport_mutex/MCLamportMutex.cfg', 'specifications/lamport_mutex/MCLamportMutex.tla', 'functions of sequences'],
  ['specifications/btree/MCbtree.cfg', 'specifications/btree/MCbtree.tla', 'function / set heavy'],
  ['specifications/GameOfLife/GameOfLife.cfg', 'specifications/GameOfLife/GameOfLife.tla', 'recursive operators, functions'],
].filter(m => !ONLY || m[0].includes(ONLY));

function timed(cmd, argv, opts = {}) {
  const t0 = process.hrtime.bigint();
  const r = spawnSync(cmd, argv, { encoding: 'utf8', timeout: TIMEOUT, maxBuffer: 1 << 28, ...opts });
  const secs = Number(process.hrtime.bigint() - t0) / 1e9;
  return { secs, out: (r.stdout ?? '') + (r.stderr ?? ''), stdout: r.stdout ?? '', timedOut: r.signal === 'SIGTERM' || r.error?.code === 'ETIMEDOUT' };
}
const lastJson = s => { try { return JSON.parse(s.trim().split('\n').pop()); } catch { return null; } };

const engines = {
  rust: (cfg, spec) => { const r = timed(RS, ['-json', '-config', cfg, spec], { cwd: EXAMPLES }); const j = lastJson(r.stdout); return { ...r, generated: j?.generated, distinct: j?.distinct, status: j?.status }; },
  wasm: (cfg, spec) => { const r = timed('node', [WASM_CLI, '-config', cfg, spec], { cwd: EXAMPLES }); const j = lastJson(r.stdout); return { ...r, generated: j?.generated, distinct: j?.distinct, status: j?.status }; },
  node: (cfg, spec) => { const r = timed('node', ['--experimental-strip-types', '--no-warnings', TS_CLI, '-json', '-config', cfg, spec], { cwd: EXAMPLES }); const j = lastJson(r.stdout); return { ...r, generated: j?.generated, distinct: j?.distinct, status: j?.status }; },
  bun: (cfg, spec) => { const r = timed('bun', [TS_CLI, '-json', '-config', cfg, spec], { cwd: EXAMPLES }); const j = lastJson(r.stdout); return { ...r, generated: j?.generated, distinct: j?.distinct, status: j?.status }; },
  tlc: (cfg, spec) => {
    const meta = fs.mkdtempSync(path.join(os.tmpdir(), 'tlc-meta-'));
    const env = { ...process.env }; delete env.JAVA_TOOL_OPTIONS;
    const dir = path.dirname(path.join(EXAMPLES, spec));
    const r = timed('java', ['-XX:+UseParallelGC', `-DTLA-Library=${TLA_LIBRARY}`, '-cp', TLA2TOOLS, 'tlc2.TLC', '-workers', '1', '-metadir', meta,
      '-config', path.join(EXAMPLES, cfg), path.basename(spec)], { cwd: dir, env });
    fs.rmSync(meta, { recursive: true, force: true });
    const m = /(\d+) states generated, (\d+) distinct states found/.exec(r.out);
    const ok = /No error has been found/.test(r.out);
    return { ...r, generated: m ? Number(m[1]) : undefined, distinct: m ? Number(m[2]) : undefined, status: ok ? 'ok' : 'not-ok' };
  },
};
for (const s of SKIP) delete engines[s];
if (!fs.existsSync(TS_CLI)) { delete engines.node; delete engines.bun; } // TypeScript engine not present

// Peak RSS of one run, in MB: /usr/bin/time -v when available, otherwise getrusage(RUSAGE_CHILDREN) via python3.
function peakRssMb(cmd, argv) {
  if (fs.existsSync('/usr/bin/time')) {
    const r = spawnSync('/usr/bin/time', ['-v', cmd, ...argv], { encoding: 'utf8', cwd: EXAMPLES, timeout: TIMEOUT, maxBuffer: 1 << 28 });
    const m = /Maximum resident set size \(kbytes\): (\d+)/.exec(r.stderr ?? '');
    return m ? Math.round(Number(m[1]) / 1024) : null;
  }
  const py = 'import resource,subprocess,sys\nsubprocess.run(sys.argv[1:],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)\nprint(resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss)';
  const r = spawnSync('python3', ['-c', py, cmd, ...argv], { encoding: 'utf8', cwd: EXAMPLES, timeout: TIMEOUT });
  const kb = Number((r.stdout ?? '').trim());
  return Number.isFinite(kb) && kb > 0 ? Math.round(kb / 1024) : null;
}

const median = a => { const s = [...a].sort((x, y) => x - y); return s[Math.floor(s.length / 2)]; };
const f = (x, d = 2) => x === undefined || x === null ? 'n/a' : x.toFixed(d);
const rate = (n, s) => s ? Math.round(n / s).toLocaleString('en-US') : 'n/a';

console.error(`# ${os.cpus()[0].model}, ${os.cpus().length} cores, load ${os.loadavg().map(x => x.toFixed(2)).join(' ')}; ${RUNS} runs each, median`);
const rows = [];
for (const [cfg, spec, note] of MODELS) {
  const res = {};
  for (const [name, run] of Object.entries(engines)) {
    const times = []; let last = null;
    for (let i = 0; i < RUNS; i++) { last = run(cfg, spec); times.push(last.secs); if (last.timedOut) break; }
    res[name] = { secs: last.timedOut ? null : median(times), generated: last.generated, distinct: last.distinct, status: last.status, timedOut: last.timedOut };
    console.error(`${cfg} ${name}: ${times.map(t => t.toFixed(2)).join(' ')}  gen=${last.generated} distinct=${last.distinct} ${last.status}`);
  }
  const ref = res.rust;
  const agree = Object.values(res).every(r => r.timedOut || (r.generated === ref.generated && r.distinct === ref.distinct));
  const rss = { rust: peakRssMb(RS, ['-json', '-config', cfg, spec]) };
  if (engines.node) rss.node = peakRssMb('node', ['--experimental-strip-types', '--no-warnings', TS_CLI, '-json', '-config', cfg, spec]);
  rows.push({ cfg, note, res, agree, rss });
}

const names = Object.keys(engines);
const label = { rust: 'Rust', wasm: 'Rust/WASM (Node)', node: 'TS/Node', bun: 'TS/Bun', tlc: 'TLC (1 worker)' };
let md = `| model | distinct | generated | ${names.map(n => label[n] + ' s').join(' | ')} | Rust states/s | TS/Node states/s | TLC states/s | Rust vs Node | Rust vs Bun | Rust vs TLC | RSS Rust MB | RSS Node MB | counts agree |\n`;
md += `|---|---:|---:|${names.map(() => '---:').join('|')}|---:|---:|---:|---:|---:|---:|---:|---:|---|\n`;
for (const r of rows) {
  const g = r.res.rust.generated, rs = r.res.rust.secs;
  const sp = n => r.res[n]?.secs && rs ? f(r.res[n].secs / rs, 1) + 'x' : 'n/a';
  md += `| ${path.basename(r.cfg, '.cfg')} (${r.note}) | ${r.res.rust.distinct} | ${g} | ${names.map(n => r.res[n].timedOut ? 'timeout' : f(r.res[n].secs)).join(' | ')} | ${rate(g, rs)} | ${rate(g, r.res.node?.secs)} | ${rate(g, r.res.tlc?.secs)} | ${sp('node')} | ${sp('bun')} | ${sp('tlc')} | ${r.rss.rust ?? 'n/a'} | ${r.rss.node ?? 'n/a'} | ${r.agree ? 'yes' : '**NO**'} |\n`;
}
console.log(md);
if (rows.some(r => !r.agree)) process.exitCode = 1;
