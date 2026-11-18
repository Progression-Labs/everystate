#!/usr/bin/env node
// Differential fuzzing: random small specifications (actor-style ones with a message bag or set, and
// plain ones with counters, sequences, sets and records) are checked by two everystate builds or engine
// settings; `-json` output (status, counts, full trace) and text output must be identical.
//
// usage: node scripts/fuzz-specs.mjs --a SIDE --b SIDE [--n 200] [--seed 1] [--keep DIR] [--timeout SEC]
//   SIDE as in engine-diff.mjs: a binary path, `engine:NAME` or `env:K=V`
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { spawnSync } from 'node:child_process';

const args = process.argv.slice(2);
const opt = (n, d) => { const i = args.indexOf(n); return i >= 0 ? args[i + 1] : d; };
const here = path.resolve(import.meta.dirname, '..');
const BIN = path.join(here, 'target/release/everystate');
const side = s => {
  if (!s) throw new Error('--a and --b are required');
  if (s.startsWith('engine:')) return { bin: BIN, env: { EVERYSTATE_ENGINE: s.slice(7) }, name: s };
  if (s.startsWith('env:')) { const [k, ...v] = s.slice(4).split('='); return { bin: BIN, env: { [k]: v.join('=') }, name: s };
  }
  return { bin: path.resolve(s), env: {}, name: s };
};
const A = side(opt('--a')), B = side(opt('--b'));
const N = Number(opt('--n', 200)), seed0 = Number(opt('--seed', 1)), timeout = Number(opt('--timeout', 20)) * 1000;
const dir = opt('--keep', '') || fs.mkdtempSync(path.join(os.tmpdir(), 'fuzz-specs-'));
fs.mkdirSync(dir, { recursive: true });

function rng(seed) { // mulberry32
  let a = seed >>> 0;
  const next = () => { a = (a + 0x6D2B79F5) >>> 0; let t = a; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; };
  return { int: n => Math.floor(next() * n), pick: xs => xs[Math.floor(next() * xs.length)], chance: p => next() < p };
}

// ---- an actor-style spec: replicas with local state, a network of messages, faults ----
function actorSpec(r, name) {
  const bag = r.chance(0.6), nrep = 2 + r.int(2), K = 2 + r.int(3), faults = r.int(3), sends = 1 + r.int(2);
  const reps = ['"a"', '"b"', '"c"'].slice(0, nrep);
  const send = m => bag ? `net (+) SetToBag({${m}})` : `net \\cup {${m}}`;
  const take = bag ? 'net (-) SetToBag({m})' : 'net \\ {m}';
  const has = bag ? 'BagIn(m, net)' : 'm \\in net';
  const dom = bag ? 'DOMAIN net' : 'net';
  const empty = bag ? 'EmptyBag' : '{}';
  // (the first applies st outside its domain: an evaluation error part of the way through a state's successors)
  const upd = r.chance(0.08) ? '@ + st[m.val]' : r.pick(['(@ + m.val) % K', 'IF m.val > @ THEN m.val ELSE @', 'm.val', '(@ + 1) % K']);
  const reply = r.chance(0.5);
  const viaOp = r.chance(0.5); // state update through an operator with delayed arguments
  const letForm = r.chance(0.4);
  const lines = [];
  lines.push(`---- MODULE ${name} ----`, 'EXTENDS Naturals, Bags, FiniteSets, Sequences, TLC', 'CONSTANTS K, Faults, Sends',
    `Reps == {${reps.join(', ')}}`, 'Other(x) == CHOOSE o \\in Reps : o # x',
    'VARIABLES st, seen, net, sent, faults, log', 'vars == <<st, seen, net, sent, faults, log>>',
    `Init == /\\ st = [x \\in Reps |-> 0] /\\ seen = [x \\in Reps |-> {}] /\\ net = ${empty}`,
    '        /\\ sent = [x \\in Reps |-> 0] /\\ faults = 0 /\\ log = <<>>',
    'Set(x, v) == st\' = [st EXCEPT ![x] = v]',
    'Send(x) ==',
    '  /\\ sent[x] < Sends /\\ sent\' = [sent EXCEPT ![x] = @ + 1]',
    `  /\\ net' = ${send('[type |-> "Put", to |-> Other(x), from |-> x, val |-> (st[x] + sent[x] + 1) % K]')}`,
    r.chance(0.5) ? '  /\\ UNCHANGED <<st, seen, faults, log>>' : '  /\\ UNCHANGED st /\\ UNCHANGED <<seen, faults>> /\\ log\' = log',
    'Deliver(m) ==',
    `  /\\ ${has}`,
    '  /\\ CASE m.type = "Put" ->');
  if (letForm) {
    lines.push(`            LET new == [st EXCEPT ![m.to] = ${upd}]`, '                big == new[m.to] >= st[m.to]',
      '            IN /\\ st\' = new',
      `               /\\ seen' = [seen EXCEPT ![m.to] = IF big THEN @ \\cup {m.val} ELSE @]`);
  } else if (viaOp) {
    lines.push(`            /\\ Set(m.to, ${upd.replaceAll('@', 'st[m.to]')})`, '            /\\ seen\' = [seen EXCEPT ![m.to] = @ \\cup {m.val}]');
  } else {
    lines.push(`            /\\ st' = [st EXCEPT ![m.to] = ${upd}]`, '            /\\ seen\' = [seen EXCEPT ![m.to] = @ \\cup {m.val}]');
  }
  lines.push(reply
    ? `            /\\ net' = ${bag ? '(net (-) SetToBag({m})) (+) SetToBag({[type |-> "Ack", to |-> m.from, val |-> m.val]})' : '(net \\ {m}) \\cup {[type |-> "Ack", to |-> m.from, val |-> m.val]}'}`
    : `            /\\ net' = ${take}`);
  lines.push('            /\\ log\' = (IF Len(log) < 2 THEN Append(log, m.val) ELSE log)',
    '       [] m.type = "Ack" ->',
    `            /\\ net' = ${take}`,
    r.chance(0.5) ? '            /\\ UNCHANGED <<st, seen, log>>' : '            /\\ st\' = st /\\ UNCHANGED <<seen, log>>',
    '  /\\ UNCHANGED <<sent, faults>>',
    'Lose(m) ==',
    `  /\\ faults < Faults /\\ ${has}`,
    `  /\\ net' = ${take} /\\ faults' = faults + 1`,
    '  /\\ UNCHANGED <<st, seen, sent, log>>',
    'Restart(x) ==',
    '  /\\ faults < Faults /\\ faults\' = faults + 1',
    `  /\\ st' = [st EXCEPT ![x] = 0] /\\ UNCHANGED <<seen, net, sent, log>>`);
  const dup = bag && r.chance(0.4);
  if (dup) lines.push('Dup(m) ==', '  /\\ faults < Faults /\\ faults\' = faults + 1 /\\ net\' = net (+) SetToBag({m})', '  /\\ UNCHANGED <<st, seen, sent, log>>');
  lines.push('Next == \\/ \\E x \\in Reps : Send(x) \\/ Restart(x)',
    `        \\/ \\E m \\in ${dom} : Deliver(m) \\/ Lose(m)${dup ? ' \\/ Dup(m)' : ''}`);
  const invs = ['\\A x \\in Reps : st[x] < K', `\\A x \\in Reps : Cardinality(seen[x]) <= ${1 + r.int(2)}`, `Len(log) < ${1 + r.int(2)}`,
    `net # ${empty} \\/ \\A x, y \\in Reps : st[x] = st[y]`, `faults < ${1 + r.int(3)}`, `\\A x \\in Reps : st[x] # ${r.int(K)}`];
  lines.push(`Inv == ${r.pick(invs)}`, 'Bound == faults <= 1', 'View == <<st, net, sent, faults>>',
    'Step == [][faults\' >= faults]_vars', '====');
  const cfg = ['CONSTANTS', `  K = ${K}`, `  Faults = ${faults}`, `  Sends = ${sends}`, 'INIT Init', 'NEXT Next'];
  if (r.chance(0.7)) cfg.push('INVARIANT Inv');
  if (r.chance(0.15)) cfg.push('CONSTRAINT Bound');
  if (r.chance(0.15)) cfg.push('VIEW View');
  if (r.chance(0.1)) cfg.push('PROPERTY Step');
  return { tla: lines.join('\n') + '\n', cfg: cfg.join('\n') + '\n', flags: r.chance(0.7) ? ['-deadlock'] : [] };
}

// ---- a plain spec: counters, a sequence, a set, a record, processes with a program counter ----
function plainSpec(r, name) {
  const P = 2 + r.int(2), M = 2 + r.int(3);
  const lines = [`---- MODULE ${name} ----`, 'EXTENDS Naturals, Sequences, FiniteSets, TLC', 'CONSTANTS M',
    `Procs == 1..${P}`, 'VARIABLES pc, x, q, s, rec', 'vars == <<pc, x, q, s, rec>>',
    'Max(S) == CHOOSE v \\in S : \\A w \\in S : v >= w',
    'Init == /\\ pc = [p \\in Procs |-> "a"] /\\ x = 0 /\\ q = <<>> /\\ s = {} /\\ rec = [n |-> 0, f |-> [p \\in Procs |-> 0]]',
    'Bump(v, d) == (v + d) % M'];
  const stepA = r.pick([
    '/\\ x\' = Bump(x, p) /\\ UNCHANGED <<q, s, rec>>',
    '/\\ x\' \\in {x, Bump(x, 1)} /\\ UNCHANGED <<q, s, rec>>',
    '/\\ \\E d \\in 1..2 : x\' = Bump(x, d) /\\ UNCHANGED <<q, s>> /\\ rec\' = [rec EXCEPT !.f[p] = Bump(@, 1)]',
    '/\\ (IF x < M - 1 THEN x\' = x + 1 ELSE x\' = 0) /\\ UNCHANGED <<q, s, rec>>',
  ]);
  const stepB = r.pick([
    '/\\ Len(q) < 2 /\\ q\' = Append(q, x) /\\ UNCHANGED <<x, s, rec>>',
    '/\\ q\' = (IF Len(q) < 2 THEN Append(q, p) ELSE Tail(q)) /\\ s\' = s \\cup {x} /\\ UNCHANGED <<x, rec>>',
    '/\\ s\' = (s \\cup {Bump(x, p)}) \\ {0} /\\ UNCHANGED <<x, q>> /\\ rec\' = [rec EXCEPT !.n = Cardinality(s)]',
    '/\\ (LET t == IF s = {} THEN 0 ELSE Max(s) IN rec\' = [rec EXCEPT !.n = t, !.f[p] = t]) /\\ UNCHANGED <<x, q, s>>',
  ]);
  const stepC = r.pick([
    '/\\ UNCHANGED <<x, q, s, rec>>',
    '/\\ q\' = Tail(q) /\\ UNCHANGED <<x, s, rec>>', // fails on the empty sequence
    '/\\ q # <<>> /\\ q\' = Tail(q) /\\ x\' = Head(q) % M /\\ UNCHANGED <<s, rec>>',
    '/\\ (CASE x = 0 -> s\' = {} [] x = 1 -> s\' = s \\cup {p} [] OTHER -> s\' = s) /\\ UNCHANGED <<x, q, rec>>',
  ]);
  lines.push(`A(p) == /\\ pc[p] = "a" /\\ pc' = [pc EXCEPT ![p] = "b"] ${stepA}`,
    `B(p) == /\\ pc[p] = "b" /\\ pc' = [pc EXCEPT ![p] = ${r.chance(0.5) ? '"c"' : 'IF x = 0 THEN "a" ELSE "c"'}] ${stepB}`,
    `C(p) == /\\ pc[p] = "c" /\\ pc' = [pc EXCEPT ![p] = ${r.chance(0.5) ? '"a"' : '"done"'}] ${stepC}`,
    'Next == \\E p \\in Procs : A(p) \\/ B(p) \\/ C(p)');
  const invs = ['x < M', 'Len(q) <= 2', `Cardinality(s) < ${1 + r.int(3)}`, `rec.n < ${1 + r.int(3)}`, '\\E p \\in Procs : pc[p] # "done"', `x # ${r.int(M)} \\/ q = <<>>`];
  lines.push(`Inv == ${r.pick(invs)}`, 'Bound == Len(q) < 2', 'View == <<pc, x, s>>', 'Step == [][x\' # x \\/ pc\' # pc \\/ UNCHANGED vars]_vars', '====');
  const cfg = ['CONSTANTS', `  M = ${M}`, 'INIT Init', 'NEXT Next'];
  if (r.chance(0.7)) cfg.push('INVARIANT Inv');
  if (r.chance(0.15)) cfg.push('CONSTRAINT Bound');
  if (r.chance(0.15)) cfg.push('VIEW View');
  if (r.chance(0.15)) cfg.push('PROPERTY Step');
  return { tla: lines.join('\n') + '\n', cfg: cfg.join('\n') + '\n', flags: r.chance(0.5) ? ['-deadlock'] : [] };
}

const scrub = s => s.replace(/^step-cache estimate[^\n]*\n(  [^\n]*\n)*/gm, '').replace(/\(\d{4}-\d\d-\d\d \d\d:\d\d:\d\d\)/g, '(T)').replace(/\d{4}-\d\d-\d\d \d\d:\d\d:\d\d/g, 'T').replace(/Finished in [^\n]*/g, 'Finished in D');
const run = (s, d, name, flags, json) => {
  const r = spawnSync(s.bin, [...flags, ...(json ? ['-json'] : []), '-config', `${name}.cfg`, `${name}.tla`], { cwd: d, encoding: 'utf8', timeout, maxBuffer: 1 << 28, env: { ...process.env, ...s.env } });
  return { o: scrub(r.stdout ?? ''), e: scrub(r.stderr ?? ''), code: r.status, timedOut: r.error?.code === 'ETIMEDOUT' };
};
let same = 0, skipped = 0;
const bad = [], statuses = {};
for (let i = 0; i < N; i++) {
  const seed = seed0 * 100003 + i, r = rng(seed), name = `F${seed}`;
  const spec = r.chance(0.6) ? actorSpec(r, name) : plainSpec(r, name);
  const d = path.join(dir, name);
  fs.mkdirSync(d, { recursive: true });
  fs.writeFileSync(path.join(d, `${name}.tla`), spec.tla);
  fs.writeFileSync(path.join(d, `${name}.cfg`), spec.cfg);
  let verdict = '';
  for (const json of [true, false]) {
    const [x, y] = [run(A, d, name, spec.flags, json), run(B, d, name, spec.flags, json)];
    if (x.timedOut || y.timedOut) { verdict = x.timedOut === y.timedOut ? 'skip' : 'only one side timed out'; break; }
    if (x.code !== y.code || x.o !== y.o || x.e !== y.e) { verdict = `${json ? 'json' : 'text'} output differs (exit ${x.code} vs ${y.code})`; break; }
    if (json) { try { const s = JSON.parse(x.o.trim().split('\n').at(-1)).status; statuses[s] = (statuses[s] ?? 0) + 1; } catch { statuses.unparsed = (statuses.unparsed ?? 0) + 1; } }
  }
  if (verdict === 'skip') skipped++;
  else if (verdict) bad.push(`${d}: ${verdict}`);
  else { same++; if (!opt('--keep', '')) fs.rmSync(d, { recursive: true, force: true }); }
}
for (const b of bad) console.log('DIFF ' + b);
console.log(`A=${A.name} B=${B.name}: ${N} random specs (seed ${seed0}), ${same} identical, ${bad.length} different, ${skipped} skipped; outcomes ${JSON.stringify(statuses)}`);
process.exit(bad.length ? 1 : 0);
