// Runs the community-module fixtures and the upstream CommunityModules test specs of test/community
// through the Rust binary (same expectations as test/community.test.ts: exit code 0 and success).
// usage: node test/community.mjs
import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
const bin = path.resolve(import.meta.dirname, '../target/release/everystate');
const src = path.resolve(import.meta.dirname, './community');
// work on a scratch copy: the specs write files
const here = fs.mkdtempSync(path.join(os.tmpdir(), 'everystate-community-'));
fs.cpSync(src, here, { recursive: true });
const ENV = { ...process.env, SOME_TEST_ENV_VAR: 'TLCFTW', 'SOME-TEST-ENV-VAR': 'TLCFTW', SOME_TEST_ENV_VAR_N23: '23' };
let pass = 0, fail = 0;
function run(cwd, spec) {
  const r = spawnSync(bin, ['-config', spec + '.cfg', spec + '.tla'], { cwd, env: ENV, encoding: 'utf8', timeout: 300_000 });
  const out = r.stdout + r.stderr;
  if (r.status === 0 && /No error has been found/.test(out)) { pass++; console.log('ok   ' + spec); }
  else { fail++; console.log(`FAIL ${spec} (exit ${r.status})\n` + out.split('\n').filter(l => !/^(Parsing|Semantic|TLC2|Running|Starting|Computing)/.test(l)).slice(0, 12).map(l => '       ' + l).join('\n')); }
}
for (const d of ['io', 'json']) fs.mkdirSync(path.join(here, 'build', d), { recursive: true });
for (const spec of ['SequencesExtFixture', 'FoldsFixture', 'MiscFixture', 'GraphsFixture', 'UndirectedGraphsFixture', 'JsonFixture', 'IOFixture', 'IOExecFixture']) run(here, spec);
const official = path.join(here, 'official', 'tests');
const work = path.join(here, 'build', 'official');
fs.rmSync(work, { recursive: true, force: true });
for (const d of ['tests', 'build/tests', 'build/json', 'target/json']) fs.mkdirSync(path.join(work, d), { recursive: true });
for (const f of fs.readdirSync(official)) fs.copyFileSync(path.join(official, f), path.join(work, 'tests', f));
for (const spec of ['SequencesExtTests', 'FoldsTests', 'BagsExtTests', 'BitwiseTests', 'CombinatoricsTests', 'DyadicRationalsTests', 'GraphsTests', 'StatisticsTests',
  'UndirectedGraphsTests', 'CSVTests', 'JsonTests', 'VectorClocksTests', 'IOUtilsTests']) run(work, 'tests/' + spec);
console.log('-- known to be blocked in the TypeScript engine too:');
const before = [pass, fail];
for (const spec of ['FiniteSetsExtTests', 'FunctionsTests', 'RelationTests']) run(work, 'tests/' + spec);
console.log(JSON.stringify({ pass: before[0], fail: before[1], blockedPass: pass - before[0], blockedFail: fail - before[1] }));
fs.rmSync(here, { recursive: true, force: true });
process.exit(before[1] ? 1 : 0);
