// Differential test: run the reference Java TLC and everystate on every (spec, cfg) pair found under a
// directory and compare outcome class and state counts.
// usage: node scripts/diff-tlc.mjs DIR [--jar tla2tools.jar] [--timeout SEC] [--jobs N] [--filter STR] [--cache FILE]
import fs from 'node:fs';
import path from 'node:path';
import { spawn } from 'node:child_process';
const args = process.argv.slice(2);
const root = path.resolve(args[0]);
const opt = (n, d) => { const i = args.indexOf(n); return i >= 0 ? args[i + 1] : d; };
const jar = opt('--jar', '/home/user/refs/tla2tools.jar'), timeout = Number(opt('--timeout', 60)) * 1000;
const jobs = Number(opt('--jobs', 3)), filter = opt('--filter', ''), cacheFile = opt('--cache', '');
const cli = path.resolve(import.meta.dirname, '../src/cli.ts');
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
  const p = spawn(cmd, argv, { cwd, stdio: ['ignore', 'pipe', 'pipe'], env: { ...process.env, JAVA_TOOL_OPTIONS: '' } });
  let o = '';
  p.stdout.on('data', d => { if (o.length < 4e6) o += d; }); p.stderr.on('data', d => { if (o.length < 4e6) o += d; });
  const timer = setTimeout(() => p.kill('SIGKILL'), timeout);
  p.on('close', (code, sig) => { clearTimeout(timer); res({ o, code, timedOut: sig === 'SIGKILL' }); });
});
// Summarise a TLC-format output into a comparable record.
function summarise(r) {
  if (r.timedOut) return { kind: 'timeout' };
  const o = r.o;
  const m = /(\d+) states generated, (\d+) distinct states found, (\d+) states left on queue\.\s*$/m.exec(o.split('\n').filter(l => !l.startsWith('Progress')).join('\n'));
  let kind = 'other:' + r.code;
  if (/No error has been found/.test(o)) kind = 'ok';
  else if (/Invariant .* is violated/.test(o)) kind = 'invariant:' + /Invariant (.*) is violated/.exec(o)[1];
  else if (/Deadlock reached/.test(o)) kind = 'deadlock';
  else if (/Action property .* is violated/.test(o)) kind = 'action-property';
  else if (/Property .* is violated by the initial state/.test(o)) kind = 'implied-init';
  else if (/Temporal propert(ies|y) .*(were|was) violated/.test(o)) kind = 'liveness';
  else if (/Assumption .* is false/.test(o)) kind = 'assumption';
  else if (/not completely specified/.test(o)) kind = 'incomplete';
  else if (/Parsing or semantic analysis failed|Fatal errors while parsing|\*\*\* Errors:/.test(o)) kind = 'parse-error';
  else if (/configuration file|The constant parameter|TLC found an error in the config|is not defined in the spec/i.test(o) && !m) kind = 'config-error';
  else if (/Error:/.test(o)) kind = 'error';
  const traceLen = (o.match(/^State \d+: </gm) ?? []).length;
  return { kind, generated: m ? +m[1] : undefined, distinct: m ? +m[2] : undefined, queue: m ? +m[3] : undefined, traceLen, exit: r.code };
}
const results = [];
let next = 0;
async function worker() {
  while (next < cases.length) {
    const c = cases[next++];
    const dir = path.dirname(c.spec), key = path.relative(root, c.cfg);
    let ref = cache[key];
    if (!ref) {
      const meta = fs.mkdtempSync('/tmp/tlcmeta-');
      const r = await run('java', ['-XX:+UseParallelGC', '-Xss16m', '-cp', jar, 'tlc2.TLC', '-workers', '1', '-lncheck', 'final', '-metadir', meta, '-config', path.basename(c.cfg), path.basename(c.spec)], dir);
      fs.rmSync(meta, { recursive: true, force: true });
      ref = summarise(r);
      if (ref.kind.startsWith('other') || ref.kind === 'error') ref.tail = r.o.split('\n').filter(l => /Error|error/.test(l)).slice(0, 2).join(' | ').slice(0, 200);
      cache[key] = ref;
      if (cacheFile) fs.writeFileSync(cacheFile, JSON.stringify(cache));
    }
    const alt = process.env.EVERYSTATE_CMD ?? (fs.existsSync(cli) ? undefined : path.resolve(import.meta.dirname, '../rust/target/release/everystate')); // the Rust binary when the TypeScript engine is absent; // alternative engine with the same command line (e.g. the Rust binary)
    const r = alt ? await run(alt, ['-config', path.basename(c.cfg), path.basename(c.spec)], dir)
      : await run(process.execPath, ['--experimental-strip-types', '--no-warnings', '--stack-size=30000', '--max-old-space-size=3000', cli, '-config', path.basename(c.cfg), path.basename(c.spec)], dir);
    const mine = summarise(r);
    if (mine.kind.startsWith('other') || mine.kind === 'error' || mine.kind === 'parse-error' || mine.kind === 'config-error') mine.tail = r.o.split('\n').filter(l => /Error|error|at line|Unknown|Expected/.test(l)).slice(0, 2).join(' | ').slice(0, 220);
    let verdict = 'PASS';
    const cls = k => k.split(':')[0];
    if (ref.kind === 'timeout') verdict = 'SKIP';
    else if (mine.kind === 'timeout') verdict = 'TIMEOUT';
    else if (cls(ref.kind) !== cls(mine.kind)) verdict = 'KIND';
    else if (['ok', 'invariant', 'deadlock', 'action-property', 'liveness'].includes(cls(ref.kind)) && (ref.generated !== mine.generated || ref.distinct !== mine.distinct)) verdict = cls(ref.kind) === 'ok' || cls(ref.kind) === 'deadlock' && false ? 'COUNT' : 'COUNT';
    else if (ref.kind !== mine.kind) verdict = 'NAME';
    else if (['invariant', 'deadlock', 'action-property'].includes(cls(ref.kind)) && ref.traceLen !== mine.traceLen) verdict = 'TRACE';
    results.push({ verdict, key, ref, mine });
    process.stderr.write(verdict === 'PASS' ? '.' : verdict[0]);
  }
}
await Promise.all(Array.from({ length: jobs }, worker));
process.stderr.write('\n');
results.sort((a, b) => a.key.localeCompare(b.key));
const tally = {};
for (const r of results) {
  tally[r.verdict] = (tally[r.verdict] ?? 0) + 1;
  if (r.verdict !== 'PASS' && r.verdict !== 'SKIP') {
    const f = x => `${x.kind}${x.generated !== undefined ? ` ${x.generated}/${x.distinct}/${x.queue}` : ''}${x.traceLen ? ` trace=${x.traceLen}` : ''}${x.tail ? ' [' + x.tail + ']' : ''}`;
    console.log(`${r.verdict.padEnd(7)} ${r.key}\n          tlc:  ${f(r.ref)}\n          mine: ${f(r.mine)}`);
  }
}
console.log(JSON.stringify(tally), 'of', results.length);
