// End-to-end tests of the programmatic API on small in-memory specifications. Expected numbers were
// produced by the reference Java TLC (tla2tools 1.8.0).
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { check, fmt } from './everystate.mjs';

const DIEHARD = `---- MODULE DieHard ----
EXTENDS Naturals
VARIABLES big, small
TypeOK == small \\in 0..3 /\\ big \\in 0..5
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
NotSolved == big # 4
====`;

test('DieHard: invariant violation with the shortest trace', () => {
  const { result, model } = check({ root: 'DieHard', modules: { DieHard: DIEHARD }, config: 'SPECIFICATION Spec\nINVARIANTS TypeOK NotSolved' });
  assert.equal(result.status, 'invariant');
  assert.equal(result.name, 'NotSolved');
  assert.deepEqual([result.generated, result.distinct, result.queue, result.depth], [73, 14, 1, 7]);
  assert.deepEqual(result.trace!.map(t => t.action?.name ?? 'Init'), ['Init', 'FillBig', 'BigToSmall', 'EmptySmall', 'BigToSmall', 'FillBig', 'BigToSmall']);
  const last = result.trace!.at(-1)!.state;
  assert.equal(fmt(last[model.vars.findIndex(v => v.name === 'big')]), '4');
});

test('DieHard: full state space without the puzzle invariant', () => {
  const { result } = check({ root: 'DieHard', modules: { DieHard: DIEHARD }, config: 'SPECIFICATION Spec\nINVARIANT TypeOK' });
  assert.equal(result.status, 'ok');
  assert.deepEqual([result.generated, result.distinct, result.queue], [97, 16, 0]);
});

test('deadlock is reported unless disabled', () => {
  const spec = `---- MODULE D ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x < 3 /\\ x' = x + 1\n====`;
  const cfg = 'INIT Init\nNEXT Next';
  const a = check({ root: 'D', modules: { D: spec }, config: cfg });
  assert.equal(a.result.status, 'deadlock');
  assert.equal(a.result.trace!.length, 4);
  const b = check({ root: 'D', modules: { D: spec }, config: cfg, deadlock: false });
  assert.equal(b.result.status, 'ok');
  assert.deepEqual([b.result.generated, b.result.distinct], [4, 4]);
});

test('liveness: weak fairness lets the counter loop forever below 3', () => {
  const spec = `---- MODULE L ----
EXTENDS Naturals
VARIABLE x
vars == <<x>>
Init == x = 0
Up == x < 2 /\\ x' = x + 1
Back == x = 2 /\\ x' = 1
Next == Up \\/ Back
Spec == Init /\\ [][Next]_vars /\\ WF_vars(Next)
ReachesThree == <>(x = 3)
ReachesTwo == <>(x = 2)
====`;
  const bad = check({ root: 'L', modules: { L: spec }, config: 'SPECIFICATION Spec\nPROPERTY ReachesThree' });
  assert.equal(bad.result.status, 'liveness');
  assert.deepEqual(bad.result.trace!.map(t => fmt(t.state[0])), ['0', '1', '2']);
  assert.equal(bad.result.loopTo, 1);
  assert.equal(bad.result.loopAction?.name, 'Back');
  const good = check({ root: 'L', modules: { L: spec }, config: 'SPECIFICATION Spec\nPROPERTY ReachesTwo' });
  assert.equal(good.result.status, 'ok');
});

test('constants, model values, symmetry and records', () => {
  const spec = `---- MODULE S ----
EXTENDS Naturals, FiniteSets, TLC
CONSTANTS Procs, None
VARIABLES owner, waiting
Init == owner = None /\\ waiting = {}
Request(p) == p \\notin waiting /\\ owner # p /\\ waiting' = waiting \\cup {p} /\\ UNCHANGED owner
Grant(p) == owner = None /\\ p \\in waiting /\\ owner' = p /\\ waiting' = waiting \\ {p}
Release(p) == owner = p /\\ owner' = None /\\ UNCHANGED waiting
Next == \\E p \\in Procs : Request(p) \\/ Grant(p) \\/ Release(p)
Spec == Init /\\ [][Next]_<<owner, waiting>>
Mutex == Cardinality({p \\in Procs : owner = p}) <= 1
Sym == Permutations(Procs)
====`;
  const cfg = 'SPECIFICATION Spec\nCONSTANTS Procs = {p1, p2, p3}\n None = None\nINVARIANT Mutex\n';
  const plain = check({ root: 'S', modules: { S: spec }, config: cfg });
  const sym = check({ root: 'S', modules: { S: spec }, config: cfg + 'SYMMETRY Sym\n' });
  assert.equal(plain.result.status, 'ok');
  assert.equal(sym.result.status, 'ok');
  assert.deepEqual([plain.result.generated, plain.result.distinct], [49, 20]);
  assert.deepEqual([sym.result.generated, sym.result.distinct], [19, 7]);
});

test('errors: unknown operator and missing constant', () => {
  assert.throws(() => check({ root: 'E', modules: { E: '---- MODULE E ----\nVARIABLE x\nInit == x = Foo\nNext == x\' = x\n====' }, config: 'INIT Init\nNEXT Next' }), /Unknown operator/);
  assert.throws(() => check({ root: 'E', modules: { E: '---- MODULE E ----\nCONSTANT C\nVARIABLE x\nInit == x = C\nNext == x\' = x\n====' }, config: 'INIT Init\nNEXT Next' }), /not assigned a value/);
});
