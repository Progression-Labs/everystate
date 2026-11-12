// Tests for the native CommunityModules overrides (src/community.ts).
//   node --experimental-strip-types --no-warnings --test test/community.test.ts
//
// Every spec is a list of ASSUMEs; it passes when the checker exits with code 0 and reports success.
//  - test/community/*Fixture.tla: our own fixtures. Each expected value was confirmed against the Java TLC with
//    the CommunityModules overrides on the classpath (scripts/tlc.sh with COMMUNITY_JAR=...), run from
//    test/community with SOME_TEST_ENV_VAR=TLCFTW.
//  - test/community/official/tests/*.tla: unmodified copies of the upstream CommunityModules test specs.
// No Java is needed to run the tests.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import * as fs from 'node:fs';
import * as path from 'node:path';
import { OVERRIDES } from '../src/community.ts';
import { EvalError, TupleV } from '../src/values.ts';

const here = path.join(import.meta.dirname, 'community');
const cli = path.join(import.meta.dirname, '..', 'src', 'cli.ts');
// Like the CLI, but its `ev.hooks.io` also has the optional readBytes/writeBytes (IOSerialize/IODeserialize) and
// exec (IOExec*) hooks, and writeFile creates missing parent directories.
const harness = path.join(here, 'harness.ts');
const ENV = { ...process.env, SOME_TEST_ENV_VAR: 'TLCFTW', 'SOME-TEST-ENV-VAR': 'TLCFTW', SOME_TEST_ENV_VAR_N23: '23' };

function check(driver: string, cwd: string, spec: string): { code: number | null; out: string } {
  const r = spawnSync(process.execPath, ['--experimental-strip-types', '--no-warnings', driver, '-config', spec + '.cfg', spec + '.tla'],
    { cwd, env: ENV, encoding: 'utf8', timeout: 300_000 });
  return { code: r.status, out: r.stdout + r.stderr };
}
function assertOk(driver: string, cwd: string, spec: string): void {
  const { code, out } = check(driver, cwd, spec);
  assert.ok(code === 0 && /^ok\b|No error has been found/m.test(out), `${spec} failed (exit code ${code}):\n${out.slice(0, 4000)}`);
}

// ---- our fixtures ----
for (const spec of ['SequencesExtFixture', 'FoldsFixture', 'MiscFixture', 'GraphsFixture', 'UndirectedGraphsFixture']) {
  test(`fixture ${spec} (CLI)`, () => assertOk(cli, here, spec));
}
// Json.java creates missing parent directories itself; the CLI's writeFile hook does not, so they are made here.
for (const d of ['io', 'json']) fs.mkdirSync(path.join(here, 'build', d), { recursive: true });
test('fixture JsonFixture (CLI, file IO through ev.hooks.io)', () => assertOk(cli, here, 'JsonFixture'));
test('fixture IOFixture (harness: text and binary file IO, environment)', () => assertOk(harness, here, 'IOFixture'));
test('fixture IOExecFixture (harness: process execution through ev.hooks.io.exec)', { skip: process.platform === 'win32' }, () => assertOk(harness, here, 'IOExecFixture'));

// ---- upstream CommunityModules test specs ----
// The specs expect the repository root as working directory (tests/..., build/...), so they run in a scratch copy.
const official = path.join(here, 'official', 'tests');
const work = path.join(here, 'build', 'official');
fs.rmSync(work, { recursive: true, force: true });
fs.mkdirSync(path.join(work, 'tests'), { recursive: true });
for (const d of ['build/tests', 'build/json', 'target/json']) fs.mkdirSync(path.join(work, d), { recursive: true });
fs.mkdirSync(path.join(work, 'unpatched'), { recursive: true });
// Every upstream spec starts with `ASSUME LET T == INSTANCE TLC IN T!PrintT("...")`, which the evaluator cannot
// run yet (applying an operator of a LET-instantiated builtin module crashes in Evaluator.applyOp). Until that is
// fixed, that single line is replaced in the scratch copy; the todo test below tracks the unpatched form.
const LET_INSTANCE = /^ASSUME LET T == INSTANCE TLC IN T!PrintT\(.*\)\s*$/m;
for (const f of fs.readdirSync(official)) {
  const src = path.join(official, f);
  if (f.endsWith('.tla')) {
    fs.copyFileSync(src, path.join(work, 'unpatched', f));
    fs.writeFileSync(path.join(work, 'tests', f), fs.readFileSync(src, 'utf8').replace(LET_INSTANCE, 'ASSUME TRUE'));
  } else {
    fs.copyFileSync(src, path.join(work, 'tests', f));
    if (f.endsWith('.cfg')) fs.copyFileSync(src, path.join(work, 'unpatched', f));
  }
}

const PURE = ['SequencesExtTests', 'FoldsTests', 'BagsExtTests', 'BitwiseTests', 'CombinatoricsTests', 'DyadicRationalsTests',
  'GraphsTests', 'StatisticsTests', 'UndirectedGraphsTests'];
const WITH_IO = ['CSVTests', 'JsonTests', 'VectorClocksTests'];
for (const spec of PURE) test(`official ${spec} (CLI)`, () => assertOk(cli, work, 'tests/' + spec));
for (const spec of WITH_IO) test(`official ${spec} (CLI, file IO through ev.hooks.io)`, () => assertOk(cli, work, 'tests/' + spec));
// IOUtilsTests deserializes a binary file written by TLC, which needs the optional readBytes/writeBytes hooks.
test('official IOUtilsTests (harness: binary file IO, environment)', () => assertOk(harness, work, 'tests/IOUtilsTests'));

// Upstream specs that do not pass yet because of features outside src/community.ts.
const BLOCKED: Record<string, string> = {
  FiniteSetsExtTests: 'AssertError expects the location suffix TLC appends to a failed CHOOSE ("...\\nline 163, col 26 to line 164, col 64 of module FiniteSetsExt")',
  FunctionsTests: '{"one"} \\subseteq DOMAIN <<>> must be FALSE, not an "is in the integer interval 1..0" error',
  RelationTests: 'the parser rejects an infix operator symbol applied in prefix form: <(x, y)',
};
for (const [spec, why] of Object.entries(BLOCKED)) {
  test(`official ${spec} (blocked: ${why})`, { todo: true }, () => assertOk(harness, work, 'tests/' + spec));
}
test('official FoldsTests, unpatched (blocked: LET T == INSTANCE TLC IN T!PrintT(...) crashes in Evaluator.applyOp)', { todo: true },
  () => assertOk(cli, path.join(work, 'unpatched'), 'FoldsTests'));

// ---- host access ----
const call = (mod: string, op: string, hooks: object, args: unknown[]) => OVERRIDES[mod][op][0]({ hooks } as any, args as any[]);
const hostless = { readFile: () => '', writeFile: () => {}, appendFile: () => {}, exists: () => false, env: {} };

test('file operators fail with an EvalError when the host provides no ev.hooks.io', () => {
  const cases: [string, string, unknown[]][] = [
    ['Json', 'JsonDeserialize', ['x.json']], ['Json', 'ndJsonDeserialize', ['x.json']], ['Json', 'JsonSerialize', ['x.json', new TupleV([1])]],
    ['CSV', 'CSVRecords', ['x.csv']], ['IOUtils', 'IOEnv', []], ['IOUtils', 'IODeserialize', ['x.vos', false]],
  ];
  for (const [mod, op, args] of cases) {
    assert.throws(() => call(mod, op, {}, args), (e: unknown) => e instanceof EvalError && /File IO is not available/.test(e.message), `${mod}!${op}`);
  }
});
test('IOExec and binary serialization report "not supported" when the host lacks the optional hooks', () => {
  const isUnsupported = (e: unknown) => e instanceof EvalError && /is not supported/.test(e.message);
  assert.throws(() => call('IOUtils', 'IOExec', { io: hostless }, [new TupleV(['ls'])]), isUnsupported);
  assert.throws(() => call('IOUtils', 'IOSerialize', { io: hostless }, [1, 'x.vos', false]), isUnsupported);
  assert.throws(() => call('IOUtils', 'IODeserialize', { io: hostless }, ['x.vos', false]), isUnsupported);
});
test('pure operators need no host', () => {
  assert.equal(call('Json', 'ToJson', {}, [true]), 'true');
  assert.equal(call('IOUtils', 'atoi', {}, ['-42']), -42);
  assert.equal(call('Combinatorics', 'choose', {}, [10, 3]), 120);
});
