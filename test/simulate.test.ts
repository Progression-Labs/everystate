// Simulation mode (-simulate) of the native binary: output layout, options, reproducibility, and above
// all soundness. Every trace a simulation reports is replayed here against the state graph that
// exhaustive checking writes with -dump: its first state must be an initial state of that graph and
// every step one of its edges, by the action the trace names.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { check as checkWasm } from '../wasm/everystate.mjs';

const bin =path.resolve(import.meta.dirname, '../target/release/everystate' + (process.platform === 'win32' ? '.exe' : ''));
const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'everystate-simulate-'));
process.on('exit', () => fs.rmSync(dir, { recursive: true, force: true }));

/** Writes NAME.tla, NAME.cfg and NAME_graph.cfg (the model without the properties to check). */
function spec(name: string, body: string, model: string, props: string) {
  fs.writeFileSync(path.join(dir, name + '.tla'), `---- MODULE ${name} ----\n${body}\n====\n`);
  fs.writeFileSync(path.join(dir, name + '.cfg'), model + '\n' + props + '\n');
  fs.writeFileSync(path.join(dir, name + '_graph.cfg'), model + '\n');
}
function run(args: string[], env: Record<string, string> = {}) {
  const r = spawnSync(bin, args, { cwd: dir, encoding: 'utf8', timeout: 120_000, env: { ...process.env, ...env } });
  return { code: r.status, out: r.stdout + r.stderr };
}
type Result = {
  status: string; name?: string; message?: string; mode?: string; generated: number; distinct: number; queue: number; depth: number;
  traces?: number; seed?: number; aril?: number; loopTo?: number; trace?: { action: string | null; state: Record<string, string> }[];
};
function simulate(name: string, ...flags: string[]): Result & { code: number | null } {
  const r = run(['-json', '-simulate', ...flags, name], { EVERYSTATE_SIM_REPLAY: '1' });
  return { ...JSON.parse(r.out.trim().split('\n').pop()!), code: r.code };
}
const check = (name: string, ...flags: string[]): Result => JSON.parse(run(['-json', ...flags, name]).out.trim().split('\n').pop()!);

const squash = (s: string) => s.replace(/\s+/g, '');
/** The complete state graph of a model, from exhaustive checking: initial states and labelled edges. */
function graph(name: string) {
  const file = path.join(dir, name + '.dot');
  const r = run(['-deadlock', '-config', name + '_graph.cfg', '-dump', 'dot,actionlabels', file, name]);
  assert.equal(r.code, 0, r.out);
  const unesc = (s: string) => squash(s.replace(/\\n/g, '\n').replace(/\\"/g, '"').replace(/\\\\/g, '\\'));
  const label = new Map<string, string>(), inits = new Set<string>(), edges = new Set<string>();
  for (const line of fs.readFileSync(file, 'utf8').split('\n')) {
    let m;
    if ((m = /^(-?\d+) -> (-?\d+) \[label="(.*)",color=/.exec(line))) edges.add(`${m[1]}>${m[2]}>${m[3]}`);
    else if ((m = /^(-?\d+) \[label="(.*)"(,style = filled)?\];?$/.exec(line))) {
      label.set(unesc(m[2]), m[1]);
      if (m[3]) inits.add(m[1]);
    }
  }
  return { label, inits, edges };
}
/** Asserts that the trace of a simulation result is a path of the model's state graph. */
function replay(name: string, r: Result) {
  const g = graph(name);
  const vars = Object.keys(r.trace![0].state);
  const id = (state: Record<string, string>) => {
    const text = vars.length === 1 ? `${vars[0]} = ${state[vars[0]]}` : vars.map(v => `/\\ ${v} = ${state[v]}`).join('\n');
    const n = g.label.get(squash(text));
    assert.ok(n !== undefined, `not a reachable state of ${name}: ${text}`);
    return n;
  };
  const ids = r.trace!.map(t => id(t.state));
  assert.ok(g.inits.has(ids[0]), 'the first state of the trace is not an initial state');
  assert.equal(r.trace![0].action, null);
  for (let i = 1; i < ids.length; i++) assert.ok(g.edges.has(`${ids[i - 1]}>${ids[i]}>${r.trace![i].action}`), `step ${i} -> ${i + 1} (${r.trace![i].action}) is not a step of ${name}`);
  if (r.loopTo !== undefined && r.loopTo >= 0) assert.ok([...g.edges].some(e => e.startsWith(`${ids.at(-1)}>${ids[r.loopTo!]}>`)), 'the step back to the loop is not a step of the model');
  return ids;
}

spec('DieHard', `EXTENDS Naturals
VARIABLES big, small
Init == big = 0 /\\ small = 0
FillSmall == small' = 3 /\\ big' = big
FillBig == big' = 5 /\\ small' = small
EmptySmall == small' = 0 /\\ big' = big
EmptyBig == big' = 0 /\\ small' = small
Min(m, n) == IF m < n THEN m ELSE n
SmallToBig == /\\ big' = Min(big + small, 5)
              /\\ small' = small - (big' - big)
BigToSmall == /\\ small' = Min(big + small, 3)
              /\\ big' = big - (small' - small)
Next == FillSmall \\/ FillBig \\/ EmptySmall \\/ EmptyBig \\/ SmallToBig \\/ BigToSmall
Spec == Init /\\ [][Next]_<<big, small>>
TypeOK == small \\in 0..3 /\\ big \\in 0..5
NotSolved == big # 4`, 'SPECIFICATION Spec', 'INVARIANTS TypeOK NotSolved');

spec('Mutex', `EXTENDS Naturals
CONSTANT N
VARIABLES pc, turn
Procs == 1..N
Init == pc = [p \\in Procs |-> "idle"] /\\ turn \\in Procs
Try(p) == pc[p] = "idle" /\\ pc' = [pc EXCEPT ![p] = "waiting"] /\\ turn' = turn
Enter(p) == pc[p] = "waiting" /\\ pc' = [pc EXCEPT ![p] = "critical"] /\\ turn' = turn
Exit(p) == pc[p] = "critical" /\\ pc' = [pc EXCEPT ![p] = "idle"] /\\ turn' = (turn % N) + 1
Next == \\E p \\in Procs : Try(p) \\/ Enter(p) \\/ Exit(p)
Spec == Init /\\ [][Next]_<<pc, turn>>
Mutex == \\A p, q \\in Procs : p # q => ~(pc[p] = "critical" /\\ pc[q] = "critical")`, 'SPECIFICATION Spec\nCONSTANT N = 3', 'INVARIANT Mutex');

spec('Stuck', `EXTENDS Naturals
VARIABLES x, y
Init == x \\in {0, 1} /\\ y = 0
Up == x < 3 /\\ x' = x + 1 /\\ y' = y
Side == y < 2 /\\ y' = y + 1 /\\ x' = x
Next == Up \\/ Side`, 'INIT Init\nNEXT Next', '');

spec('Mono', `EXTENDS Naturals
VARIABLE n
Init == n = 0
Step == n' = (n + 1) % 4
Idle == n' = n
Next == Step \\/ Idle
Spec == Init /\\ [][Next]_n
Mono == [][n' >= n]_n`, 'SPECIFICATION Spec', 'PROPERTY Mono');

spec('Live', `EXTENDS Naturals
VARIABLES n, m
Init == n = 0 /\\ m \\in {0, 1}
Inc == n' = (n + 1) % 3 /\\ m' = m
Flip == n = 2 /\\ m' = 1 - m /\\ n' = n
Next == Inc \\/ Flip
Spec == Init /\\ [][Next]_<<n, m>> /\\ WF_<<n, m>>(Next)
Stable == <>[](m = 1)
Returns == []<>(n = 2)`, 'SPECIFICATION Spec', 'PROPERTY Stable');
fs.writeFileSync(path.join(dir, 'LiveOk.cfg'), 'SPECIFICATION Spec\nPROPERTY Returns\n');

spec('Bounded', `EXTENDS Naturals
VARIABLE n
Init == n = 0
Next == n' = n + 1
Small == n < 5
Low == n < 5`, 'INIT Init\nNEXT Next\nCONSTRAINT Small', '');

const SEEDS = [1, 2, 3, 4, 5, 6, 7, 8];

test('an invariant violation is found, and its trace is a behaviour of the model', () => {
  for (const seed of SEEDS) {
    const r = simulate('DieHard', 'num=2000', '-seed', String(seed));
    assert.equal(r.status, 'invariant', `seed ${seed}`);
    assert.equal(r.name, 'NotSolved');
    assert.equal(r.code, 12);
    assert.equal(r.trace!.at(-1)!.state.big, '4');
    replay('DieHard', r);
  }
  assert.equal(check('DieHard').status, 'invariant');
});

test('a model that passes exhaustively passes every simulation', () => {
  assert.equal(check('Mutex').status, 'invariant'); // three processes can all enter
  fs.writeFileSync(path.join(dir, 'Mutex1.cfg'), 'SPECIFICATION Spec\nCONSTANT N = 1\nINVARIANT Mutex\n');
  assert.equal(check('Mutex', '-config', 'Mutex1.cfg').status, 'ok');
  assert.equal(check('Live', '-config', 'LiveOk.cfg').status, 'ok');
  for (const seed of SEEDS) {
    const a = simulate('Mutex', 'num=300', '-seed', String(seed), '-config', 'Mutex1.cfg');
    assert.deepEqual([a.status, a.traces, a.code], ['ok', 300, 0]);
    const b = simulate('Live', 'num=300', '-seed', String(seed), '-config', 'LiveOk.cfg');
    assert.deepEqual([b.status, b.traces, b.code], ['ok', 300, 0]);
    const c = simulate('Mutex', 'num=300', '-seed', String(seed));
    assert.equal(c.status, 'invariant');
    replay('Mutex', c);
  }
});

test('deadlock: reported with a real trace, not reported with -deadlock, and not caused by a CONSTRAINT', () => {
  for (const seed of SEEDS) {
    const r = simulate('Stuck', 'num=50', '-seed', String(seed));
    assert.equal(r.status, 'deadlock');
    assert.equal(r.code, 11);
    const last = r.trace!.at(-1)!.state;
    assert.deepEqual([last.x, last.y], ['3', '2']);
    replay('Stuck', r);
    const off = simulate('Stuck', 'num=50', '-seed', String(seed), '-deadlock');
    assert.deepEqual([off.status, off.traces], ['ok', 50]);
    // every behaviour of Bounded runs into the constraint; the state there has a successor
    const b = simulate('Bounded', 'num=50', '-seed', String(seed));
    assert.deepEqual([b.status, b.traces, b.depth], ['ok', 50, 5]);
  }
  // an invariant is still checked on the state that the constraint excludes, as in TLC
  fs.writeFileSync(path.join(dir, 'BoundedInv.cfg'), 'INIT Init\nNEXT Next\nCONSTRAINT Small\nINVARIANT Low\n');
  const v = simulate('Bounded', 'num=5', '-seed', '1', '-config', 'BoundedInv.cfg');
  assert.deepEqual([v.status, v.name, v.trace!.at(-1)!.state.n], ['invariant', 'Low', '5']);
});

test('an action property is checked on every step; stuttering steps are left out of the trace', () => {
  for (const seed of SEEDS) {
    const r = simulate('Mono', 'num=200', '-seed', String(seed));
    assert.equal(r.status, 'action-property');
    assert.equal(r.name, 'Mono');
    assert.equal(r.code, 13);
    assert.deepEqual(r.trace!.map(t => t.state.n), ['0', '1', '2', '3', '0']);
    assert.deepEqual(r.trace!.map(t => t.action), [null, 'Step', 'Step', 'Step', 'Step']);
    replay('Mono', r);
  }
});

test('temporal properties are checked on each behaviour; a counterexample is a real lasso', () => {
  for (const seed of SEEDS) {
    const r = simulate('Live', 'num=200', '-seed', String(seed));
    assert.equal(r.status, 'liveness');
    assert.equal(r.code, 13);
    assert.ok(r.loopTo !== undefined && r.loopTo >= 0);
    replay('Live', r);
    // the loop never reaches m = 1 for good: some state of it has m = 0
    assert.ok(r.trace!.slice(r.loopTo).some(t => t.state.m === '0'));
  }
  assert.equal(check('Live').status, 'liveness');
});

test('the same seed repeats the run; another seed or aril gives another one', () => {
  const a = simulate('DieHard', 'num=2000', '-seed', '42');
  const b = simulate('DieHard', 'num=2000', '-seed', '42');
  assert.deepEqual(a, b);
  assert.equal(a.seed, 42);
  assert.equal(a.aril, 0);
  const runs = [simulate('DieHard', 'num=2000', '-seed', '43'), simulate('DieHard', 'num=2000', '-seed', '42', '-aril', '1'), simulate('DieHard', 'num=2000', '-seed', '44')];
  assert.ok(runs.some(r => JSON.stringify(r.trace) !== JSON.stringify(a.trace)));
  const c = simulate('DieHard', 'num=2000', '-seed', '42', '-aril', '1');
  assert.deepEqual(c, runs[1]);
  // without -seed one is chosen and reported; using it repeats the run
  const free = simulate('DieHard', 'num=2000');
  assert.ok(Number.isSafeInteger(free.seed));
  assert.deepEqual(simulate('DieHard', 'num=2000', '-seed', String(free.seed)), free);
});

test('the JSON result: fields of a simulation, and a bounded default', () => {
  const r = simulate('Bounded', 'num=7', '-depth', '3', '-seed', '9');
  assert.deepEqual(r, { status: 'ok', mode: 'simulate', generated: 1 + 7 * 3, distinct: -1, queue: -1, depth: 4, traces: 7, seed: 9, aril: 0, code: 0 });
  // -json without num= stops after 1000 behaviours instead of running forever
  const d = simulate('Bounded', '-seed', '9');
  assert.deepEqual([d.status, d.traces, d.depth], ['ok', 1000, 5]);
  // exhaustive results are unchanged
  assert.deepEqual(check('Bounded'), { status: 'ok', generated: 6, distinct: 5, queue: 0, depth: 5 });
});

test('text output follows TLC: banner, initial states, trace, statistics, exit status', () => {
  const r = run(['-simulate', 'num=50', '-depth', '10', '-seed', '1', 'Mono']);
  assert.equal(r.code, 13);
  const lines = r.out.split('\n').filter(l => !/^(Parsing file|Semantic processing)/.test(l)).map(l => l.replace(/\d{4}-\d\d-\d\d \d\d:\d\d:\d\d/, 'TS').replace(/in \d+s at/, 'in 00s at'));
  assert.match(lines[1], /^Running Random Simulation with seed 1 with 1 worker on 1 cores with 0MB heap and 0MB offheap memory \(everystate .*\)\.$/);
  assert.deepEqual(lines.slice(2, 8), [
    'Starting... (TS)',
    'Computed 1 initial states...',
    'Finished computing initial states: 1 distinct state generated at TS.',
    'Error: Action property Mono is violated.',
    'Error: The behavior up to this point is:',
    'State 1: <Init line 4, col 9 to line 4, col 13 of module Mono>',
  ]);
  const tail = lines.slice(lines.indexOf('State 5: <Step line 5, col 9 to line 5, col 24 of module Mono>'));
  assert.equal(tail[1], 'n = 0');
  assert.match(tail[3], /^The number of states generated: \d+$/);
  assert.equal(tail[4], 'Simulation using seed 1 and aril 0');
  assert.match(tail[5], /^Progress: \d+ states checked, \d+ traces generated \(trace length: mean=\d+, var\(x\)=\d+, sd=\d+\)$/);
  assert.equal(tail[6], 'Finished in 00s at (TS)');

  const ok = run(['-simulate', 'num=20', '-depth', '4', '-seed', '1', 'Bounded']);
  assert.equal(ok.code, 0);
  assert.match(ok.out, /\nProgress: 81 states checked, 20 traces generated \(trace length: mean=4, var\(x\)=0, sd=0\)\nThe number of states generated: 81\nSimulation using seed 1 and aril 0\nFinished in/);

  const tool = run(['-tool', '-simulate', 'num=20', '-depth', '4', '-seed', '1', 'Bounded']).out;
  assert.match(tool, /@!@!@STARTMSG 2188:0 @!@!@\nRunning Random Simulation with seed 1 /);
  assert.match(tool, /@!@!@STARTMSG 2269:0 @!@!@\nComputed 1 initial states\.\.\.\n@!@!@ENDMSG 2269 @!@!@/);
  assert.match(tool, /@!@!@STARTMSG 2209:0 @!@!@\nProgress\(20\) at [-\d: ]+: 81 states generated, -1 distinct states found, -1 states left on queue\.\n@!@!@ENDMSG 2209 @!@!@/);
  assert.match(tool, /@!@!@STARTMSG 2210:0 @!@!@\nThe number of states generated: 81\nSimulation using seed 1 and aril 0\n@!@!@ENDMSG 2210 @!@!@/);
});

test('options: the java stand-in, file=, and the errors TLC gives for bad values', () => {
  const j = run(['java', '-cp', 'tla2tools.jar', 'tlc2.TLC', '-simulate', 'num=30', '-depth', '5', '-seed', '3', '-deadlock', 'Stuck']);
  assert.equal(j.code, 0);
  assert.match(j.out, /Running Random Simulation with seed 3 /);
  assert.match(j.out, /Progress: \d+ states checked, 30 traces generated/);

  const prefix = path.join(dir, 'traces', 't');
  assert.equal(run(['-simulate', `num=2,file=${prefix}`, '-depth', '2', '-seed', '1', 'Bounded']).code, 0);
  assert.equal(
    fs.readFileSync(prefix + '_0_1', 'utf8'),
    `---------------- MODULE ${prefix}_0_1 -----------------\n` +
      '\\* <Init line 4, col 9 to line 4, col 13 of module Bounded>\nSTATE_1 == \nn = 0\n\n\n' +
      '\\* <Next line 5, col 9 to line 5, col 18 of module Bounded>\nSTATE_2 == \nn = 1\n\n\n' +
      '\\* <Next line 5, col 9 to line 5, col 18 of module Bounded>\nSTATE_3 == \nn = 2\n\n\n' +
      '=================================================\n',
  );
  const bad = (args: string[], message: RegExp) => {
    const r = run([...args, 'Bounded']);
    assert.equal(r.code, 1);
    assert.match(r.out, message);
  };
  bad(['-simulate', '-depth', 'x'], /^Error: An integer for trace length required\. But encountered x\n/);
  bad(['-simulate', '-seed', '1.5'], /^Error: An integer for seed required\. But encountered 1\.5\n/);
  bad(['-simulate', '-aril'], /^Error: An integer for aril required\. But encountered Bounded\n/);
  bad(['-simulate', 'file=x'], /^Error: You need to specify a 'num' argument when using the 'file' argument/);
  bad(['-generate'], /-generate .* is not supported/);
});

test('the WebAssembly build makes the same random choices as the native binary', () => {
  const modules = { DieHard: fs.readFileSync(path.join(dir, 'DieHard.tla'), 'utf8') };
  const config = fs.readFileSync(path.join(dir, 'DieHard.cfg'), 'utf8');
  for (const seed of [1, 7, 123456789]) {
    const native = simulate('DieHard', 'num=5000', '-depth', '40', '-seed', String(seed));
    const wasm = checkWasm({ root: 'DieHard', modules, config, simulate: { traces: 5000, depth: 40, seed } }).result;
    assert.deepEqual([wasm.status, wasm.traces, wasm.generated, wasm.depth], [native.status, native.traces, native.generated, native.depth]);
    assert.deepEqual(wasm.trace!.map(t => t.action?.name ?? null), native.trace!.map(t => t.action));
  }
});
