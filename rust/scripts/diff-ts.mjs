// Differential test of the Rust engine against the TypeScript engine: runs both CLIs on every
// (X.tla, X.cfg) pair under a directory and compares the complete TLC-style text output
// (timestamps, durations and the banner line are normalised).
// usage: node rust/scripts/diff-ts.mjs DIR [--timeout SEC] [--jobs N] [--filter STR] [--cache FILE] [--show N] [--tool]
import fs from 'node:fs';
import path from 'node:path';
import { spawn } from 'node:child_process';
const args = process.argv.slice(2);
const root = path.resolve(args[0]);
const opt = (n, d) => { const i = args.indexOf(n); return i >= 0 ? args[i + 1] : d; };
const timeout = Number(opt('--timeout', 60)) * 1000, jobs = Number(opt('--jobs', 3)), filter = opt('--filter', '');
const cacheFile = opt('--cache', ''), show = Number(opt('--show', 12)), tool = args.includes('--tool');
const cli = path.resolve(import.meta.dirname, '../../src/cli.ts');
const rs = path.resolve(import.meta.dirname, '../target/release/everystate');
const cache = cacheFile && fs.existsSync(cacheFile) ? JSON.parse(fs.readFileSync(cacheFile, 'utf8')) : {};
const cases = [];
const walk = d => {
  for (const f of fs.readdirSync(d, { withFileTypes: true })) {
    const p = path.join(d, f.name);
    if (f.isDirectory()) walk(p);
    else if (f.name.endsWith('.cfg')) {
      const spec = p.slice(0, -4) + '.tla';
      if (fs.existsSync(spec) && (!filter || p.includes(filter))) cases.push({ spec, cfg: p });
    }
  }
};
walk(root);
const run = (cmd, argv, cwd) => new Promise(res => {
  const p = spawn(cmd, argv, { cwd, stdio: ['ignore', 'pipe', 'pipe'] });
  let o = '';
  p.stdout.on('data', d => { if (o.length < 4e6) o += d; }); p.stderr.on('data', d => { if (o.length < 4e6) o += d; });
  const timer = setTimeout(() => p.kill('SIGKILL'), timeout);
  p.on('close', (code, sig) => { clearTimeout(timer); res({ o, code, timedOut: sig === 'SIGKILL' }); });
});
const norm = r => r.timedOut ? 'TIMEOUT' : (r.o
  .replace(/\d{4}-\d\d-\d\d \d\d:\d\d:\d\d/g, 'NOW')
  .replace(/Finished in \S+( \S+)? at/g, 'Finished in T at')
  .replace(/\(everystate [^)]*\)/g, '(everystate)')
  .replace(/\(\d[\d,]* s\/min\)/g, '(N s/min)').replace(/\(\d[\d,]* ds\/min\)/g, '(N ds/min)')
  .replace(/^Progress\(\d+\) at NOW.*\n/gm, '')
  + `\n[exit ${r.code}]`);
let next = 0, same = 0; const diffs = [], timeouts = [];
async function worker() {
  while (next < cases.length) {
    const c = cases[next++];
    const dir = path.dirname(c.spec), key = path.relative(root, c.cfg) + (tool ? '#tool' : '');
    const extra = tool ? ['-tool'] : [];
    let ts = cache[key];
    if (ts === undefined) {
      ts = norm(await run(process.execPath, ['--experimental-strip-types', '--no-warnings', '--stack-size=30000', '--max-old-space-size=3000', cli, ...extra, '-config', path.basename(c.cfg), path.basename(c.spec)], dir));
      cache[key] = ts;
      if (cacheFile) fs.writeFileSync(cacheFile, JSON.stringify(cache));
    }
    const mine = norm(await run(rs, [...extra, '-config', path.basename(c.cfg), path.basename(c.spec)], dir));
    if (ts === 'TIMEOUT') { timeouts.push(key + ' (ts)'); process.stderr.write('t'); continue; }
    if (mine === ts) { same++; process.stderr.write('.'); } else { diffs.push({ key, ts, mine }); process.stderr.write('D'); }
  }
}
await Promise.all(Array.from({ length: jobs }, worker));
process.stderr.write('\n');
diffs.sort((a, b) => a.key.localeCompare(b.key));
for (const d of diffs) {
  const a = d.ts.split('\n'), b = d.mine.split('\n');
  let i = 0; while (i < a.length && i < b.length && a[i] === b[i]) i++;
  console.log(`DIFF ${d.key} (first difference at line ${i + 1})`);
  for (const l of a.slice(i, i + show)) console.log('    ts: ' + l.slice(0, 220));
  for (const l of b.slice(i, i + show)) console.log('    rs: ' + l.slice(0, 220));
}
console.log(JSON.stringify({ total: cases.length, same, diff: diffs.length, tsTimeout: timeouts.length }));
