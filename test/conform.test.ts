// Trace conformance (`everystate conform`, `conform()` in the WebAssembly API): matching rules, partial
// observations, hidden steps, stuttering, diagnostics, and the property that every behaviour found by
// exhaustive exploration conforms while a trace with an impossible step never does.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { conform, TlaError } from '../wasm/everystate.mjs';

const here = import.meta.dirname;
const bin = path.resolve(here, '../target/release/everystate');
const exampleDir = path.resolve(here, '../skills/formal-verification/example');
const read = (p: string) => fs.readFileSync(p, 'utf8');
const cli = (args: string[], cwd = here) => {
  const r = spawnSync(bin, args, { cwd, encoding: 'utf8' });
  return { code: r.status, out: r.stdout };
};

// ---- matching rules ----

const TYPES = `---- MODULE Types ----
EXTENDS Naturals, Sequences
CONSTANTS a, b
VARIABLES n, flag, str, mv, seq, set, rec, fn, ifn, nested, recs, empty, none
vars == <<n, flag, str, mv, seq, set, rec, fn, ifn, nested, recs, empty, none>>
Init == /\\ n = 1 /\\ flag = TRUE /\\ str = "hi" /\\ mv = a
        /\\ seq = <<1, 2, 3>> /\\ set = {3, 1, 2}
        /\\ rec = [x |-> 1, y |-> "s"]
        /\\ fn = [p \\in {a, b} |-> IF p = a THEN 0 ELSE 1]
        /\\ ifn = [i \\in {3, 5} |-> i * 2]
        /\\ nested = [q |-> <<{a}, {}>>, m |-> [p \\in {a, b} |-> {<<1, "x">>}]]
        /\\ recs = {[k |-> 1, j |-> 1], [k |-> 1, j |-> 2]}
        /\\ empty = <<>> /\\ none = {}
Next == UNCHANGED vars
====`;
const TYPES_CFG = 'INIT Init\nNEXT Next\nCONSTANTS a = a\n b = b';
const types = (state: Record<string, unknown>) => conform({ root: 'Types', modules: { Types: TYPES }, config: TYPES_CFG, trace: [{ state }] }).status;

test('matching: JSON is read according to the type of the spec value', () => {
  const yes: Record<string, unknown>[] = [
    { n: 1, flag: true, str: 'hi' },
    { n: 1.0 },
    { mv: 'a' }, // a string matches a model value of that name
    { seq: [1, 2, 3] },
    { seq: { '1': 1, '2': 2, '3': 3 } }, // a sequence is a function on 1..n
    { seq: { '2': 2, '...': true } },
    { set: [1, 2, 3] },
    { set: [2, 3, 1] }, // sets are unordered
    { rec: { x: 1, y: 's' } },
    { rec: { y: 's', x: 1 } },
    { rec: { x: 1, '...': 0 } }, // partial record
    { rec: { '...': 0 } },
    { fn: { a: 0, b: 1 } }, // model-value keys
    { fn: { b: 1, '...': 0 } },
    { ifn: { '3': 6, '5': 10 } }, // integer keys
    { nested: { q: [['a'], []], m: { a: [[1, 'x']], b: [[1, 'x']] } } },
    { nested: { m: { a: [[1, 'x']], '...': 0 }, '...': 0 } },
    { recs: [{ k: 1, j: 2 }, { k: 1, j: 1 }] },
    // the first element matches both records; the pairing has to be found, not guessed
    { recs: [{ k: 1, '...': 0 }, { k: 1, j: 1 }] },
    { empty: [] },
    { empty: {} }, // the empty sequence is also the empty function
    { none: [] },
    {},
  ];
  for (const s of yes) assert.equal(types(s), 'conforms', JSON.stringify(s));
  const no: Record<string, unknown>[] = [
    { n: 2 },
    { n: '1' },
    { n: 1.5 },
    { n: true },
    { n: null },
    { flag: 'TRUE' },
    { flag: 1 },
    { str: 'Hi' },
    { mv: 'b' },
    { seq: [3, 2, 1] }, // sequences are ordered
    { seq: [1, 2] },
    { seq: [1, 2, 3, 4] },
    { set: [1, 2] },
    { set: [1, 2, 3, 3] }, // duplicates never match a set
    { set: [1, 2, 4] },
    { set: { '1': 1, '2': 2, '3': 3 } },
    { rec: { x: 1 } }, // a missing field without "..."
    { rec: { x: 1, y: 's', z: 0 } },
    { rec: { x: 1, z: 0, '...': 0 } },
    { rec: [1, 's'] },
    { fn: { a: 0, b: 0 } },
    { fn: { a: 0, c: 1 } },
    { ifn: { '3': 6 } },
    { ifn: [6, 10] },
    { nested: { q: [[], ['a']], m: { a: [[1, 'x']], b: [[1, 'x']] } } },
    { recs: [{ k: 1, j: 1 }, { k: 1, j: 1 }] },
    { recs: [{ k: 1, '...': 0 }, { k: 2, '...': 0 }] },
    { empty: [1] },
    { empty: null },
    { none: {} },
  ];
  for (const s of no) assert.equal(types(s), 'mismatch', JSON.stringify(s));
});

test('matching: the mismatch names the variable and shows both values as JSON', () => {
  const r = conform({ root: 'Types', modules: { Types: TYPES }, config: TYPES_CFG, trace: [{ state: { n: 1, set: [1, 2], fn: { a: 0, b: 1 } } }] });
  assert.equal(r.status, 'mismatch');
  assert.equal(r.line, 1);
  assert.equal(r.lastMatched, null);
  assert.equal(r.message, 'No initial state of the spec has the observed values.');
  assert.deepEqual(r.nearest, [{ action: null, differs: [{ var: 'set', observed: [1, 2], expected: [1, 2, 3] }] }]);
});

// ---- partial observations, hidden steps, stuttering, limits, constraints, invariants ----

const TWO = `---- MODULE Two ----
EXTENDS Naturals
VARIABLES x, y
Init == x = 0 /\\ y = 0
IncX == x < 3 /\\ x' = x + 1 /\\ y' = y
IncY == y < 3 /\\ y' = y + 1 /\\ x' = x
Next == IncX \\/ IncY
Bound == x < 2
YSmall == y < 2
SumSmall == x + y < 3
====`;
const two = (trace: object[] | string, extra: object = {}, config = 'INIT Init\nNEXT Next') => conform({ root: 'Two', modules: { Two: TWO }, config, trace, ...extra });

test('partial observations: unobserved variables are unconstrained', () => {
  const r = two([{ state: { x: 0 } }, { state: { x: 1 } }, { state: { x: 1 } }, { state: { x: 2 } }], { behavior: true });
  assert.equal(r.status, 'conforms');
  assert.equal(r.observations, 4);
  assert.equal(r.candidates, 1); // the third step can only have been IncY
  assert.deepEqual(r.behavior!.map(s => [s.line, s.action, s.state.x, s.state.y]), [[1, null, '0', '0'], [2, 'IncX', '1', '0'], [3, 'IncY', '1', '1'], [4, 'IncX', '2', '1']]);
  // an observation with no variables at all still is one step
  const any = two([{ state: {} }, { state: {} }, { state: {} }]);
  assert.equal(any.status, 'conforms');
  assert.equal(any.candidates, 3); // (2,0) (1,1) (0,2)
  // only the action is known
  const acts = two([{ state: { x: 0, y: 0 } }, { action: 'IncY' }, { action: 'IncY' }, { action: 'IncY' }, { action: 'IncX', state: { y: 3 } }]);
  assert.equal(acts.status, 'conforms');
  assert.equal(two([{ state: { x: 0, y: 0 } }, { action: 'IncY' }, { action: 'IncY' }, { action: 'IncY' }, { action: 'IncY' }]).line, 5);
});

test('the first observation may be a step: the initial state is then unlogged', () => {
  const r = two([{ action: 'IncX', state: { x: 1 } }, { action: 'IncY', state: { y: 1 } }], { behavior: true });
  assert.equal(r.status, 'conforms');
  assert.deepEqual(r.behavior!.map(s => s.line), [null, 1, 2]);
  assert.equal(two([{ action: 'IncX', state: { x: 2 } }]).status, 'mismatch');
});

test('hidden steps: off by default, hinted at, and bounded by -hidden', () => {
  const trace = [{ state: { x: 0, y: 0 } }, { state: { x: 2, y: 1 } }];
  const strict = two(trace);
  assert.equal(strict.status, 'mismatch');
  assert.equal(strict.line, 2);
  assert.match(strict.hints!.join('\n'), /rerun with -hidden 2/);
  assert.equal(two(trace, { hidden: 1 }).status, 'mismatch');
  const r = two(trace, { hidden: 2, behavior: true });
  assert.equal(r.status, 'conforms');
  assert.deepEqual(r.behavior!.map(s => s.line), [1, null, null, 2]);
  // hidden steps are optional: a fully logged trace still conforms
  assert.equal(two([{ state: { x: 0, y: 0 } }, { state: { x: 1, y: 0 } }], { hidden: 3 }).status, 'conforms');
  // with hidden steps the first observation need not be the initial state
  assert.equal(two([{ state: { x: 1, y: 1 } }]).status, 'mismatch');
  assert.equal(two([{ state: { x: 1, y: 1 } }], { hidden: 2 }).status, 'conforms');
  assert.equal(two([{ state: { x: 1, y: 1 } }], { hidden: 1 }).status, 'mismatch');
  // the last step before an observation with an action is that action
  assert.equal(two([{ state: { x: 0, y: 0 } }, { action: 'IncX', state: { x: 1, y: 1 } }], { hidden: 1 }).status, 'conforms');
  assert.equal(two([{ state: { x: 0, y: 0 } }, { action: 'IncX', state: { x: 0, y: 2 } }], { hidden: 3 }).status, 'mismatch');
});

test('stuttering: a repeated observation is a step unless -stutter is given', () => {
  const trace = [{ state: { x: 0, y: 0 } }, { state: { x: 0, y: 0 } }, { state: { x: 1, y: 0 } }];
  const strict = two(trace);
  assert.equal(strict.status, 'mismatch');
  assert.equal(strict.line, 2);
  assert.match(strict.hints!.join('\n'), /rerun with -stutter/);
  const r = two(trace, { stutter: true, behavior: true });
  assert.equal(r.status, 'conforms');
  assert.deepEqual(r.behavior!.map(s => [s.line, s.action]), [[1, null], [2, '(stuttering)'], [3, 'IncX']]);
  // an observation that names an action is never a stuttering step
  assert.equal(two([{ state: { x: 0, y: 0 } }, { action: 'IncX', state: { x: 0, y: 0 } }], { stutter: true }).status, 'mismatch');
  // stuttering does not make an impossible step possible
  assert.equal(two([{ state: { x: 0, y: 0 } }, { state: { x: 0, y: 0 } }, { state: { x: 2, y: 0 } }], { stutter: true }).line, 3);
});

test('the candidate set is bounded', () => {
  const r = two([{ state: {} }, { state: {} }, { state: {} }], { limit: 2 });
  assert.equal(r.status, 'limit');
  assert.equal(r.failed!.line, 3);
  assert.equal(r.lastMatched!.line, 2);
  assert.match(r.hints!.join('\n'), /-limit/);
  assert.equal(two([{ state: {} }, { state: {} }, { state: {} }], { limit: 3 }).status, 'conforms');
});

test('CONSTRAINT bounds apply as in model checking, and can be switched off', () => {
  const cfg = 'INIT Init\nNEXT Next\nCONSTRAINT Bound';
  const trace = [{ state: { x: 0 } }, { state: { x: 1 } }, { state: { x: 2 } }];
  const r = two(trace, {}, cfg);
  assert.equal(r.status, 'mismatch');
  assert.equal(r.line, 3);
  assert.match(r.hints!.join('\n'), /Bound.*-noconstraints/);
  assert.equal(two(trace, { constraints: false }, cfg).status, 'conforms');
});

test('invariants of the configuration are checked on the matched states', () => {
  const full = [{ state: { x: 0, y: 0 } }, { state: { x: 1, y: 0 } }, { state: { x: 1, y: 1 } }, { state: { x: 1, y: 2 } }, { state: { x: 2, y: 2 } }];
  const r = two(full, {}, 'INIT Init\nNEXT Next\nINVARIANT YSmall');
  assert.equal(r.status, 'invariant');
  assert.equal(r.name, 'YSmall');
  assert.equal(r.line, 4);
  assert.equal(r.behavior!.length, 4);
  assert.equal(r.behavior!.at(-1)!.state.y, '2');
  // every state consistent with the trace violates it, although no variable was observed
  const blind = two([{ state: {} }, { state: {} }, { state: {} }, { state: {} }], {}, 'INIT Init\nNEXT Next\nINVARIANT SumSmall');
  assert.equal(blind.status, 'invariant');
  assert.equal(blind.line, 4);
  // only some of the consistent states violate it: a note, not a verdict about this run
  const some = two([{ state: {} }, { state: {} }, { state: {} }], {}, 'INIT Init\nNEXT Next\nINVARIANT YSmall');
  assert.equal(some.status, 'conforms');
  assert.match(some.notes!.join('\n'), /Invariant YSmall is violated in 1 of the 3 spec states consistent with the trace at line 3/);
});

// ---- action parameters ----

const PROCS = `---- MODULE Procs ----
CONSTANT Procs
VARIABLE pc
Init == pc = [p \\in Procs |-> "idle"]
Start(p) == pc[p] = "idle" /\\ pc' = [pc EXCEPT ![p] = "busy"]
Stop(p) == pc[p] = "busy" /\\ pc' = [pc EXCEPT ![p] = "idle"]
Next == \\E p \\in Procs : Start(p) \\/ Stop(p)
====`;
const procs = (trace: object[]) => conform({ root: 'Procs', modules: { Procs: PROCS }, config: 'INIT Init\nNEXT Next\nCONSTANT Procs = {p1, p2}', trace });

test('action parameters are matched against the values the action was taken with', () => {
  assert.equal(procs([{ action: 'Start', params: ['p1'] }, { action: 'Stop', params: { p: 'p1' }, state: { pc: { p1: 'idle', p2: 'idle' } } }]).status, 'conforms');
  // one process's log: it only knows its own entry of pc
  assert.equal(procs([{ action: 'Start', params: ['p2'], state: { pc: { p2: 'busy', '...': 0 } } }]).status, 'conforms');
  const r = procs([{ action: 'Start', params: ['p1'] }, { action: 'Stop', params: ['p2'] }]);
  assert.equal(r.status, 'mismatch');
  assert.equal(r.line, 2);
  assert.equal(r.message, 'Stop cannot happen here with these parameters; the spec allows it with (p1).');
  assert.deepEqual(r.enabled!.map(e => e.action), ['Stop(p1)', 'Start(p2)']);
  // without parameters, any instance of the action will do
  assert.equal(procs([{ action: 'Start' }, { action: 'Start' }]).candidates, 1);
  assert.equal(procs([{ action: 'Start' }]).candidates, 2);
  const none = procs([{ action: 'Start' }, { action: 'Start' }, { action: 'Start' }]);
  assert.equal(none.message, 'Start cannot happen here: the spec does not allow it in the state the trace has reached.');
  assert.equal(procs([{ action: 'Start', params: ['p1', 'p2'] }]).status, 'mismatch');
  assert.equal(procs([{ action: 'Start', params: { q: 'p1' } }]).status, 'trace-error');
});

// ---- the trace itself ----

test('trace formats: JSON Lines, a JSON array, objects; other keys and entries are ignored', () => {
  const lines = '{"state":{"x":0}}\n\n{"ts":1,"level":"info","msg":"boot"}\r\n{"ts":2,"action":"IncX","state":{"x":1},"note":[1,{"a":null}]}\n';
  const a = two(lines);
  assert.deepEqual([a.status, a.observations, a.ignored], ['conforms', 2, 1]);
  const arr = two('[\n  {"state": {"x": 0}},\n  {"action": "IncX"},\n  {"action": "IncX", "state": {"x": 3}}\n]\n');
  assert.deepEqual([arr.status, arr.line, arr.failed!.index], ['mismatch', 4, 3]);
  assert.equal(two('[]').status, 'trace-error');
  assert.equal(two('﻿{"state":{"x":0}}').status, 'conforms');
  assert.equal(two('{"state":{"x":0}}\n{"action":"IncX","state":{"x":1e0}}').status, 'conforms');
  assert.equal(two('{"state":{"x":0,"y":"\\u0041"}}').status, 'mismatch');
});

test('trace errors are reported with their line, apart from mismatches', () => {
  const bad = (trace: string) => {
    const r = two(trace);
    assert.equal(r.status, 'trace-error', trace);
    return r;
  };
  assert.equal(bad('{"state":{"x":0}}\n{"state":{"x":1}\n').line, 2);
  assert.equal(bad('{"state":{"x":0}}\nnot json').line, 2);
  assert.equal(bad('{"state":{"x":0}} {"state":{"x":1}}').line, 1);
  assert.match(bad('{"state":{"x":0}}\n{"state":{"z":1}}').message!, /"z" is not a variable of Two. Its variables are: x, y\./);
  assert.match(bad('{"action":"IncZ"}').message!, /"IncZ" is not an action of Two. Its actions are: IncX, IncY\./);
  assert.match(bad('{"action":"IncX","params":[1]}').message!, /"params" cannot be checked for action IncX/);
  bad('{"state":[1]}');
  bad('{"action":7}');
  bad('[1]');
  bad('{"state":{"x":0,"x":0}}');
  bad('{"level":"info"}');
  bad('');
  assert.throws(() => conform({ root: 'Two', modules: { Two: TWO.replace('Init ==', 'Init =') }, config: 'INIT Init\nNEXT Next', trace: [] }), TlaError);
});

// ---- diagnostics on the worked example, and the command line ----

test('diagnostics: the skill example reports the double charge at line 5', () => {
  const input = { root: 'Charge', modules: { Charge: read(path.join(exampleDir, 'Charge.tla')) }, config: read(path.join(exampleDir, 'Charge.cfg')) };
  const ok = conform({ ...input, trace: read(path.join(exampleDir, 'charge-ok.jsonl')) });
  assert.deepEqual([ok.status, ok.observations, ok.candidates], ['conforms', 6, 1]);
  const r = conform({ ...input, trace: read(path.join(exampleDir, 'charge-double.jsonl')) });
  assert.equal(r.status, 'mismatch');
  assert.deepEqual(r.failed, { index: 5, line: 5, observation: { action: 'Handle', state: { charges: 2 } } });
  assert.deepEqual(r.lastMatched, { index: 4, line: 4, candidates: 1 });
  assert.equal(r.message, 'Handle can happen here, but it does not produce the observed values.');
  assert.deepEqual(r.before, [{ charges: 1 }]);
  assert.deepEqual(r.nearest, [{ action: 'Handle', differs: [{ var: 'charges', observed: 2, expected: 1 }] }]);
  assert.deepEqual(r.enabled!.map(e => [e.action, e.produces.charges]), [['Send', 1], ['Handle', 1], ['LoseReply', 1], ['Receive', 1]]);
  // against the model of the broken server the same run is allowed, and breaks the promise
  const broken = conform({ ...input, config: read(path.join(exampleDir, 'ChargeBroken.cfg')), trace: read(path.join(exampleDir, 'charge-double.jsonl')) });
  assert.deepEqual([broken.status, broken.name, broken.line], ['invariant', 'ChargedAtMostOnce', 5]);
});

test('command line: exit codes, text report, -json, -behavior', () => {
  const ok = cli(['conform', '-trace', 'charge-ok.jsonl', 'Charge.tla'], exampleDir);
  assert.equal(ok.code, 0);
  assert.equal(ok.out, 'Trace conforms: 6 observations matched; the recorded run is a behaviour of Charge.\n');
  const bad = cli(['conform', '-trace', 'charge-double.jsonl', 'Charge'], exampleDir);
  assert.equal(bad.code, 20);
  assert.match(bad.out, /^Error: Trace does not conform to Charge: line 5 \(observation 5 of 6\) cannot be matched\./);
  assert.match(bad.out, /last matched: line 4 \(1 spec state consistent with the trace up to there\)/);
  assert.match(bad.out, /Handle: charges is 1 in the spec, 2 in the trace/);
  const json = cli(['conform', '-json', '-trace', 'charge-double.jsonl', 'Charge.tla'], exampleDir);
  assert.equal(json.code, 20);
  assert.equal(JSON.parse(json.out).failed.line, 5);
  const inv = cli(['conform', '-config', 'ChargeBroken.cfg', 'Charge.tla', 'charge-double.jsonl'], exampleDir);
  assert.equal(inv.code, 12);
  assert.match(inv.out, /^Error: Invariant ChargedAtMostOnce is violated by the recorded behaviour at line 5\./);
  const beh = cli(['conform', '-behavior', '-trace', 'charge-ok.jsonl', 'Charge.tla'], exampleDir);
  assert.equal(beh.code, 0);
  assert.match(beh.out, /State 1: <Initial predicate>\n\/\\ inFlight = 0\n/);
  assert.match(beh.out, /State 6: <Receive line \d+, col \d+ to line \d+, col \d+ of module Charge>\n/);
  // errors that are not about the run
  assert.equal(cli(['conform', '-trace', 'missing.jsonl', 'Charge.tla'], exampleDir).code, 21);
  assert.equal(cli(['conform', '-trace', 'Charge.cfg', 'Charge.tla'], exampleDir).code, 21);
  assert.equal(cli(['conform', '-trace', 'charge-ok.jsonl', 'Missing.tla'], exampleDir).code, 151);
  assert.equal(cli(['conform', '-trace', 'charge-ok.jsonl', '-config', 'Charge.tla', 'Charge.tla'], exampleDir).code, 151);
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'conform-'));
  fs.writeFileSync(path.join(dir, 'Bad.tla'), '---- MODULE Bad ----\nVARIABLE x\nInit == x =\n====\n');
  fs.writeFileSync(path.join(dir, 'Bad.cfg'), 'INIT Init\nNEXT Init\n');
  fs.writeFileSync(path.join(dir, 't.jsonl'), '{"state":{"x":0}}\n');
  assert.equal(cli(['conform', '-trace', 't.jsonl', 'Bad.tla'], dir).code, 150);
  fs.rmSync(dir, { recursive: true });
  assert.equal(cli(['conform', '-trace', 'charge-ok.jsonl', '-limit', '0', 'Charge.tla'], exampleDir).code, 22);
  assert.equal(cli(['conform', 'Charge.tla'], exampleDir).code, 1);
  const help = cli(['conform', '-help']);
  assert.equal(help.code, 0);
  assert.match(help.out, /Exit status: 0 the trace conforms, 20 it does not/);
});

// ---- behaviours of the reachable state graph conform; impossible steps never do ----

/** JSON for a value printed by TLC, in the form `conform` documents (sets as arrays, functions as objects). */
function tlaToJson(text: string): unknown {
  let i = 0;
  const ws = () => { while (/\s/.test(text[i] ?? '')) i++; };
  const eat = (s: string) => { ws(); if (text.startsWith(s, i)) { i += s.length; return true; } return false; };
  const key = (v: unknown) => String(v);
  const list = (close: string): unknown[] => {
    const out: unknown[] = [];
    if (eat(close)) return out;
    do out.push(value()); while (eat(','));
    assert.ok(eat(close), `expected ${close} at ${i} in ${text}`);
    return out;
  };
  function value(): unknown {
    ws();
    if (eat('<<')) return list('>>');
    if (eat('{')) return list('}');
    if (eat('[')) {
      const o: Record<string, unknown> = {};
      do { ws(); const k = /^\w+/.exec(text.slice(i))![0]; i += k.length; assert.ok(eat('|->')); o[k] = value(); } while (eat(','));
      assert.ok(eat(']'));
      return o;
    }
    if (eat('(')) {
      const o: Record<string, unknown> = {};
      do { const k = value(); assert.ok(eat(':>')); o[key(k)] = value(); } while (eat('@@'));
      assert.ok(eat(')'));
      return o;
    }
    if (text[i] === '"') {
      const m = /^"((?:[^"\\]|\\.)*)"/.exec(text.slice(i))!;
      i += m[0].length;
      return JSON.parse(m[0]);
    }
    const m = /^-?\w+/.exec(text.slice(i));
    assert.ok(m, `cannot parse ${text.slice(i)}`);
    i += m[0].length;
    if (/^-?\d+$/.test(m[0])) {
      if (!eat('..')) return Number(m[0]);
      const hi = Number(/^-?\d+/.exec(text.slice(i))![0]);
      i = text.indexOf(String(hi), i) + String(hi).length;
      return Array.from({ length: Math.max(0, hi - Number(m[0]) + 1) }, (_, k) => Number(m[0]) + k);
    }
    return m[0] === 'TRUE' ? true : m[0] === 'FALSE' ? false : m[0];
  }
  const v = value();
  ws();
  assert.equal(i, text.length, `trailing text in ${text}`);
  return v;
}

type State = Record<string, unknown>;
/** The reachable state graph, from `everystate -dump dot,actionlabels`. */
function stateGraph(specPath: string, extra: string[] = []) {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'conform-'));
  const dot = path.join(dir, 'graph.dot');
  cli([...extra, '-dump', 'dot,actionlabels', dot, specPath]);
  const states = new Map<string, State>();
  const inits: string[] = [];
  const edges: [string, string, string][] = [];
  for (const line of read(dot).split('\n')) {
    const node = /^(-?\d+) \[label="(.*)"(,style = filled)?\];?$/.exec(line);
    const edge = /^(-?\d+) -> (-?\d+) \[label="(.*?)"/.exec(line);
    if (edge) edges.push([edge[1], edge[2], edge[3]]);
    else if (node) {
      const label = node[2].replace(/\\n/g, '\n').replace(/\\"/g, '"').replace(/\\\\/g, '\\');
      const st: State = {};
      for (const part of label.split(/^(?:\/\\ )/m).filter(p => p.trim())) {
        const eq = part.indexOf(' = ');
        st[part.slice(0, eq).replace(/^\/\\ /, '').trim()] = tlaToJson(part.slice(eq + 3).trim());
      }
      states.set(node[1], st);
      if (node[3]) inits.push(node[1]);
    }
  }
  fs.rmSync(dir, { recursive: true });
  // breadth-first tree: one behaviour to every reachable state
  const parent = new Map<string, [string, string] | null>(inits.map(s => [s, null]));
  const out = new Map<string, [string, string][]>();
  for (const [f, t, a] of edges) out.set(f, [...(out.get(f) ?? []), [t, a]]);
  const queue = [...inits];
  for (let q = 0; q < queue.length; q++) for (const [t, a] of out.get(queue[q]) ?? []) if (!parent.has(t)) { parent.set(t, [queue[q], a]); queue.push(t); }
  const behaviour = (id: string) => {
    const steps: { id: string; action?: string }[] = [];
    for (let cur: string | undefined = id; cur !== undefined; ) {
      const p: [string, string] | null = parent.get(cur)!;
      steps.push({ id: cur, action: p?.[1] });
      cur = p?.[0];
    }
    return steps.reverse();
  };
  return { states, inits, edges, out, behaviour };
}

function checkGraphProperty(name: string, tla: string, config: string, modules: Record<string, string>, observed: string[], extraArgs: string[] = []) {
  const g = stateGraph(tla, extraArgs);
  const run = (trace: object[], extra: object = {}) => conform({ root: name, modules, config, trace, ...extra });
  const pick = (s: State, vars: string[]) => Object.fromEntries(vars.map(v => [v, s[v]]));
  assert.ok(g.states.size > 1);
  let mutated = 0;
  // every behaviour found by exhaustive exploration conforms: the shortest one to each state, extended
  // by each step from it (so every edge of the graph is covered)
  for (const id of g.states.keys()) {
    const b = g.behaviour(id);
    // fully observed with actions: exactly one spec state is consistent with it
    const full = b.map(s => ({ action: s.action, state: g.states.get(s.id)! }));
    const r = run(full);
    assert.equal(r.status, 'conforms', `${name}: behaviour to ${JSON.stringify(g.states.get(id))}: ${r.message}`);
    assert.equal(r.candidates, 1);
    // with only some variables and no actions
    assert.equal(run(b.map(s => ({ state: pick(g.states.get(s.id)!, observed) }))).status, 'conforms');
    const succ = g.out.get(id) ?? [];
    for (const [t, a] of succ) {
      const step = run([...full, { action: a, state: g.states.get(t)! }]);
      assert.equal(step.status, 'conforms', `${name}: step ${a} to ${JSON.stringify(g.states.get(t))}: ${step.message}`);
    }
    // an impossible step is found, at its line: go on to a state that is not a successor
    const targets = new Set(succ.map(e => e[0]));
    const other = [...g.states.keys()].find(o => o !== id && !targets.has(o));
    if (other === undefined) continue;
    const bad = run([...full, { state: g.states.get(other)! }]);
    assert.equal(bad.status, 'mismatch');
    assert.equal(bad.line, b.length + 1);
    assert.equal(bad.lastMatched!.line, b.length);
    mutated++;
  }
  return { ...g, mutated };
}

test('property: behaviours of the reachable graph conform, impossible steps do not (TwoPhase, tlaplus/Examples)', () => {
  // test/conform/ holds TwoPhase.tla, TCommit.tla and TwoPhase.cfg, unchanged from tlaplus/Examples
  // (specifications/transaction_commit, MIT license)
  const dir = path.join(here, 'conform');
  const modules = { TwoPhase: read(path.join(dir, 'TwoPhase.tla')), TCommit: read(path.join(dir, 'TCommit.tla')) };
  const config = read(path.join(dir, 'TwoPhase.cfg'));
  const g = checkGraphProperty('TwoPhase', path.join(dir, 'TwoPhase.tla'), config, modules, ['tmState', 'tmPrepared']);
  assert.deepEqual([g.states.size, g.mutated], [288, 288]);

  // a hand-written run as three resource managers and a transaction manager would log it
  const run = [
    { state: { tmState: 'init', msgs: [] } },
    { action: 'RMPrepare', params: ['r1'], state: { rmState: { r1: 'prepared', '...': 0 } } },
    { action: 'RMPrepare', params: ['r3'], state: { rmState: { r3: 'prepared', '...': 0 } } },
    { action: 'TMRcvPrepared', params: ['r3'], state: { tmPrepared: ['r3'] } },
    { action: 'RMPrepare', params: ['r2'], state: { msgs: [{ type: 'Prepared', rm: 'r2' }, { type: 'Prepared', rm: 'r1' }, { type: 'Prepared', rm: 'r3' }] } },
    { action: 'TMRcvPrepared', params: ['r1'], state: { tmPrepared: ['r1', 'r3'] } },
    { action: 'TMRcvPrepared', params: ['r2'] },
    { action: 'TMCommit', state: { tmState: 'committed' } },
    { action: 'RMRcvCommitMsg', params: ['r2'], state: { rmState: { r1: 'prepared', r2: 'committed', r3: 'prepared' } } },
  ];
  const ok = conform({ root: 'TwoPhase', modules, config, trace: run, behavior: true });
  assert.deepEqual([ok.status, ok.candidates], ['conforms', 1]);
  // the filled-in behaviour is itself a conforming, fully observed trace
  const filled = ok.behavior!.map(s => ({ action: s.action, state: Object.fromEntries(Object.entries(s.state).map(([k, v]) => [k, tlaToJson(v)])) }));
  assert.equal(conform({ root: 'TwoPhase', modules, config, trace: filled }).status, 'conforms');
  // mutate one step: the transaction manager commits before r2's vote arrived
  const early = run.filter((_, i) => i !== 6);
  const r = conform({ root: 'TwoPhase', modules, config, trace: early });
  assert.equal(r.status, 'mismatch');
  assert.equal(r.line, 7);
  assert.equal(r.failed!.observation.action, 'TMCommit');
  assert.equal(r.message, 'TMCommit cannot happen here: the spec does not allow it in the state the trace has reached.');
  assert.ok(r.enabled!.some(e => e.action === 'TMRcvPrepared(r2)'));
  assert.match(r.hints!.join('\n'), /rerun with -hidden 1/);
  assert.equal(conform({ root: 'TwoPhase', modules, config, trace: early, hidden: 1 }).status, 'conforms');
  // mutate one value: a resource manager commits although the decision was to abort
  const wrong = [run[0], { action: 'TMAbort' }, { action: 'RMRcvAbortMsg', params: ['r1'], state: { rmState: { r1: 'committed', '...': 0 } } }];
  const w = conform({ root: 'TwoPhase', modules, config, trace: wrong });
  assert.equal(w.line, 3);
  assert.deepEqual(w.nearest![0].differs[0].expected, { r1: 'aborted', r2: 'working', r3: 'working' });
});

test('property: behaviours of the reachable graph conform, impossible steps do not (Charge)', () => {
  const tla = path.join(exampleDir, 'Charge.tla');
  const g = checkGraphProperty('Charge', tla, read(path.join(exampleDir, 'Charge.cfg')), { Charge: read(tla) }, ['charges', 'confirmed']);
  assert.deepEqual([g.states.size, g.mutated], [29, 29]);
});

// Development aid: CONFORM_SPECS="dir/A.tla:dir/A.cfg,dir/B.tla:dir/B.cfg" runs the same property on other
// specifications (with small state graphs), for instance from a checkout of tlaplus/Examples. Remove SYMMETRY
// from the configuration first: with it the dumped graph is a quotient whose edges are not literal steps.
for (const entry of (process.env.CONFORM_SPECS ?? '').split(',').filter(Boolean)) {
  const [tla, cfg] = entry.split(':');
  test(`property: ${tla}`, () => {
    const dir = path.dirname(tla);
    const modules = Object.fromEntries(fs.readdirSync(dir).filter(f => f.endsWith('.tla')).map(f => [f.slice(0, -4), read(path.join(dir, f))]));
    const g = checkGraphProperty(path.basename(tla, '.tla'), tla, read(cfg), modules, [], ['-config', cfg]);
    console.log(`${tla}: ${g.states.size} states, ${g.edges.length} steps, ${g.mutated} impossible steps`);
  });
}
