// `-workers N` against `-workers 1` on test/workers/Base.tla: for every configuration below the complete
// output (TLC text and -tool framing, the -json line, the `-dump dot` graph and the exit status) must be
// the same, apart from the banner's worker count, times, and the one line that says the search went
// back to one worker. Each case also states whether it has to fall back.
//
// usage: node test/workers.mjs [--workers 4] [--bin path/to/everystate] [--repeat 3]
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
const args = process.argv.slice(2);
const opt = (n, d) => { const i = args.indexOf(n); return i >= 0 ? args[i + 1] : d; };
const here = import.meta.dirname;
const bin = opt('--bin', process.env.EVERYSTATE_CMD ?? path.resolve(here, '../target/release/everystate'));
const workers = opt('--workers', '4'), repeat = Number(opt('--repeat', 3));
const spec = path.join(here, 'workers/Base.tla');
const C = ['CONSTANTS N = 40', 'P = {p1, p2, p3}'], S = ['CONSTANTS N = 12', 'P = {p1, p2}'];
// name, configuration lines, expected exit status, substring of the fall-back reason ('' = stays parallel)
const cases = [
  ['ok', [...C, 'INIT Init', 'NEXT Next', 'INVARIANT TypeOK'], 0, ''],
  ['invariant', [...C, 'INIT Init', 'NEXT Next', 'INVARIANT TypeOK Bad'], 12, ''],
  ['symmetry', [...C, 'INIT Init', 'NEXT Next', 'INVARIANT TypeOK Bad', 'SYMMETRY Perms'], 12, ''],
  ['symmetry-ok', [...C, 'INIT Init', 'NEXT Next', 'INVARIANT TypeOK', 'SYMMETRY Perms'], 0, ''],
  ['view', [...C, 'INIT Init', 'NEXT Next', 'INVARIANT TypeOK', 'VIEW View'], 0, ''],
  ['constraints-alias', [...C, 'INIT Init', 'NEXT Next', 'INVARIANT TypeOK Bad', 'CONSTRAINT Cons', 'ACTION_CONSTRAINT ACons', 'ALIAS Al'], 12, ''],
  ['constraints-ok', [...C, 'INIT Init', 'NEXT Next', 'INVARIANT TypeOK', 'CONSTRAINT Cons', 'ACTION_CONSTRAINT ACons'], 0, ''],
  ['many-init', [...S, 'INIT ManyInit', 'NEXT Next', 'INVARIANT TypeOK', 'CONSTRAINT Cons'], 0, ''],
  ['bad-init', [...S, 'INIT BadInit', 'NEXT Next', 'INVARIANT InitInv'], 12, ''],
  ['deadlock', [...S, 'INIT Init', 'NEXT DeadNext'], 11, ''],
  ['error', [...S, 'INIT Init', 'NEXT ErrNext', 'INVARIANT TypeOK'], 255, ''],
  ['incomplete', [...S, 'INIT Init', 'NEXT PartNext', 'CHECK_DEADLOCK FALSE'], 75, ''],
  ['action-property', [...S, 'INIT Init', 'NEXT Next', 'PROPERTY ActProp'], 13, ''],
  ['level', [...S, 'INIT Init', 'NEXT LevelNext', 'INVARIANT TypeOK LevelInv'], 12, ''],
  ['subset-value', [...S, 'INIT Init', 'NEXT SubNext', 'CHECK_DEADLOCK FALSE'], 0, ''],
  ['liveness', [...S, 'SPECIFICATION Spec', 'PROPERTY Live'], 13, ''],
  ['liveness-view', [...S, 'SPECIFICATION Spec', 'PROPERTY Live', 'VIEW View'], 13, ''],
  ['liveness-symmetry', [...S, 'SPECIFICATION Spec', 'PROPERTY Live', 'SYMMETRY Perms'], 13, ''],
  ['print', ['CONSTANTS N = 6', 'P = {p1}', 'INIT Init', 'NEXT PrintNext', 'INVARIANT TypeOK'], 0, 'prints'],
  ['tlcset', [...S, 'INIT Init', 'NEXT SetNext', 'INVARIANT TypeOK'], 0, 'TLCSet'],
  ['tlcget-register', [...S, 'INIT Init', 'NEXT RegNext', 'INVARIANT TypeOK'], 0, 'TLCGet'],
  ['tlcget-statistics', [...S, 'INIT Init', 'NEXT StatNext', 'INVARIANT TypeOK'], 0, 'TLCGet'],
  ['random', [...S, 'INIT Init', 'NEXT RandNext', 'INVARIANT TypeOK'], 0, 'random'],
  ['new-string', [...S, 'INIT Init', 'NEXT StrNext', 'CHECK_DEADLOCK FALSE'], 0, 'string'],
  ['predicate-set-value', [...S, 'INIT Init', 'NEXT FiltNext', 'CHECK_DEADLOCK FALSE'], 0, 'cannot be passed'],
];
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'workers-test-'));
const NOTE = /^The search continues with 1 worker instead of \d+: (.*)\n/m;
const norm = s => s.replace(/\d{4}-\d\d-\d\d \d\d:\d\d:\d\d/g, 'T').replace(/with \d+ workers? on \d+ cores/, 'with W').replace(/Finished in \d+\w*( \d+\w+)?/, 'Finished in')
  .replace(/\(([\d,]+) s\/min\)|\(([\d,]+) ds\/min\)/g, '(R)').replace(NOTE, '');
function run(cfg, w, flags, par) {
  const env = { ...process.env };
  delete env.EVERYSTATE_PAR_MIN; delete env.EVERYSTATE_PAR_CHUNK;
  if (par) { env.EVERYSTATE_PAR_MIN = '1'; env.EVERYSTATE_PAR_CHUNK = par; }
  const dot = path.join(tmp, 'g.dot');
  fs.rmSync(dot, { force: true });
  const r = spawnSync(bin, ['-workers', String(w), ...flags, '-dump', 'dot,actionlabels', dot, '-config', cfg, spec], { encoding: 'utf8', env, maxBuffer: 1 << 28 });
  const out = (r.stdout ?? '') + (r.stderr ?? '');
  return { code: r.status, out: norm(out), note: NOTE.exec(out)?.[1] ?? '', graph: fs.existsSync(dot) ? fs.readFileSync(dot, 'utf8') : '' };
}
let failed = 0;
for (const [name, lines, exit, fallback] of cases) {
  const cfg = path.join(tmp, name + '.cfg');
  fs.writeFileSync(cfg, lines.join('\n') + '\n');
  const problems = [];
  for (const flags of [[], ['-tool'], ['-json']]) {
    const a = run(cfg, 1, flags, null);
    if (a.code !== exit) problems.push(`${flags[0] ?? 'text'}: exit ${a.code}, expected ${exit}`);
    for (let k = 0; k < repeat; k++) {
      const b = run(cfg, workers, flags, ['1', '3', ''][k % 3] || null);
      const what = `${flags[0] ?? 'text'} run ${k + 1}`;
      if (b.code !== a.code) problems.push(`${what}: exit ${b.code} != ${a.code}`);
      else if (b.out !== a.out) problems.push(`${what}: output differs`);
      else if (b.graph !== a.graph) problems.push(`${what}: state graph differs`);
      if (flags[0] !== '-json' && k % 3 < 2 && (fallback ? !b.note.includes(fallback) : b.note !== '')) problems.push(`${what}: fall-back note is "${b.note}", expected ${fallback ? `one about "${fallback}"` : 'none'}`);
    }
  }
  if (problems.length) failed++;
  console.log(`${problems.length ? 'FAIL' : 'ok  '} ${name}${problems.length ? '\n     ' + [...new Set(problems)].join('\n     ') : ''}`);
}
fs.rmSync(tmp, { recursive: true, force: true });
console.log(`${cases.length - failed} pass, ${failed} fail (workers ${workers})`);
process.exit(failed ? 1 : 0);
