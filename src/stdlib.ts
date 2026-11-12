// Native implementations of the TLA+ standard modules.
import type { Def, ModuleInfo, Builtin } from './modules.ts';
import type { Evaluator } from './eval.ts';
import { Closure, DefRef } from './eval.ts';
import {
  EvalError, SetBase, SetV, IntervalV, InfSetV, SeqSetV, LazySetV, CrossV, RecSetV, FcnSetV, TupleV, RecordV, FcnV, ModelValue, modelValue,
  valEq, compare, mkSet, BOOLEAN_SET, makeFcn, makeFcnFromPairs, domainElems, fcnValues, isFcn, fmt, EMPTY_TUPLE, bsearch,
} from './values.ts';
import type { Value } from './values.ts';

export type Fn = (ev: Evaluator, a: any[]) => Value;
type Spec = [number, Fn, Partial<Builtin>?] | SetBase | TupleV;

export const fail = (msg: string): never => { throw new EvalError(msg); };
const ORD = ['first', 'second', 'third', 'fourth'];
export function int(v: Value, op: string, i: number): number {
  if (typeof v !== 'number') fail(`The ${ORD[i]} argument of ${op} should be an integer, but instead it is:\n${fmt(v)}`);
  return v;
}
function nat(v: Value, op: string, i: number): number {
  if (typeof v !== 'number' || v < 0) fail(`The ${ORD[i]} argument of ${op} should be a natural number, but instead it is:\n${fmt(v)}`);
  return v;
}
export function seq(v: Value, op: string, i: number): Value[] {
  if (v instanceof TupleV) return v.e;
  return fail(`The ${ORD[i]} argument of ${op} should be a sequence, but instead it is:\n${fmt(v)}`);
}
export function set(v: Value, op: string, i: number): SetBase {
  if (v instanceof SetBase) return v;
  return fail(`The ${ORD[i]} argument of ${op} should be a set, but instead it is:\n${fmt(v)}`);
}
function checkInt(n: number, what: string): number {
  if (n > 2147483647 || n < -2147483648) fail(`Overflow when computing ${what}`);
  return n;
}

// A product / function set / record set that an empty component makes empty although another one is infinite.
function emptyProduct(x: SetBase): boolean {
  const empty = (y: SetBase): boolean => y instanceof IntervalV ? y.hi < y.lo : y instanceof SetV ? y.e.length === 0 : emptyProduct(y);
  if (x instanceof CrossV || x instanceof RecSetV) return x.sets.some(empty);
  if (x instanceof FcnSetV) return empty(x.rng) && !empty(x.dom);
  return false;
}

function module(name: string, exts: ModuleInfo[], defs: Record<string, Spec>): ModuleInfo {
  const info: ModuleInfo = { name, syms: new Map(), exports: new Map(), consts: [], vars: [], assumes: [], ownDefs: [], order: [] };
  for (const e of exts) for (const [k, v] of e.exports) { info.syms.set(k, v); info.exports.set(k, v); }
  for (const [n, spec] of Object.entries(defs)) {
    let def: Def;
    if (Array.isArray(spec) && typeof spec[1] === 'function') {
      const [arity, fn, opts] = spec as [number, Fn, Partial<Builtin>?];
      const params = [];
      for (let i = 0; i < arity; i++) params.push({ name: `p${i}`, arity: opts?.ops?.includes(i) ? 1 : 0 });
      def = { k: 'def', name: n, params, body: null, module: name, local: false, loc: [0, 0, 0, 0], builtin: { fn, ...opts } };
    } else {
      const value = spec;
      def = { k: 'def', name: n, params: [], body: null, module: name, local: false, loc: [0, 0, 0, 0], builtin: { fn: () => value } };
    }
    info.syms.set(n, def);
    info.exports.set(n, def);
    info.ownDefs.push(def);
  }
  return info;
}

export function toStr(v: Value): string { return typeof v === 'string' ? v : fmt(v); }

export function globalDefs(): Map<string, Def> {
  const g = module('<builtin>', [], { BOOLEAN: BOOLEAN_SET, STRING: new InfSetV('STRING') });
  return g.syms as Map<string, Def>;
}

export function buildStdlib(io: { print: (s: string) => void }): Map<string, ModuleInfo> {
  const Naturals = module('Naturals', [], {
    '+': [2, (_, a) => checkInt(int(a[0], '+', 0) + int(a[1], '+', 1), `${a[0]}+${a[1]}`)],
    '-': [2, (_, a) => checkInt(int(a[0], '-', 0) - int(a[1], '-', 1), `${a[0]}-${a[1]}`)],
    '*': [2, (_, a) => checkInt(int(a[0], '*', 0) * int(a[1], '*', 1), `${a[0]}*${a[1]}`)],
    '^': [2, (_, a) => {
      const b = int(a[0], '^', 0), e = int(a[1], '^', 1);
      if (e < 0) fail(`The second argument of ^ should be a natural number, but instead it is:\n${e}`);
      return checkInt(b ** e, `${b}^${e}`);
    }],
    '<': [2, (_, a) => int(a[0], '<', 0) < int(a[1], '<', 1)],
    '>': [2, (_, a) => int(a[0], '>', 0) > int(a[1], '>', 1)],
    '<=': [2, (_, a) => int(a[0], '<=', 0) <= int(a[1], '<=', 1)],
    '>=': [2, (_, a) => int(a[0], '>=', 0) >= int(a[1], '>=', 1)],
    '..': [2, (_, a) => new IntervalV(int(a[0], '..', 0), int(a[1], '..', 1))],
    '\\div': [2, (_, a) => {
      const x = int(a[0], '\\div', 0), y = int(a[1], '\\div', 1);
      if (y === 0) fail('The second argument of \\div is 0.');
      return Math.floor(x / y);
    }],
    '%': [2, (_, a) => {
      const x = int(a[0], '%', 0), y = int(a[1], '%', 1);
      if (y <= 0) fail(`The second argument of % should be a positive number, but instead it is:\n${y}`);
      const r = x % y;
      return r < 0 ? r + y : r;
    }],
    'Nat': new InfSetV('Nat'),
  });
  const Integers = module('Integers', [Naturals], {
    'Int': new InfSetV('Int'),
    '-.': [1, (_, a) => checkInt(-int(a[0], '-.', 0), `-${a[0]}`)],
  });
  const Reals = module('Reals', [Integers], {
    'Real': new InfSetV('Real'),
    '/': [2, (_, a) => {
      const x = int(a[0], '/', 0), y = int(a[1], '/', 1);
      if (y === 0) fail('The second argument of / is 0.');
      if (x % y !== 0) fail('TLC cannot handle real numbers that are not integers.');
      return x / y;
    }],
    'Infinity': [0, () => fail('TLC cannot evaluate Infinity.')],
  });

  const Sequences = module('Sequences', [], {
    'Seq': [1, (_, a) => new SeqSetV(set(a[0], 'Seq', 0))],
    'Len': [1, (_, a) => typeof a[0] === 'string' ? a[0].length : seq(a[0], 'Len', 0).length],
    '\\o': [2, (_, a) => {
      if (typeof a[0] === 'string' && typeof a[1] === 'string') return a[0] + a[1];
      const x = seq(a[0], '\\o', 0), y = seq(a[1], '\\o', 1);
      return x.length === 0 ? a[1] : y.length === 0 ? a[0] : new TupleV(x.concat(y));
    }],
    'Append': [2, (_, a) => { const s = seq(a[0], 'Append', 0).slice(); s.push(a[1]); return new TupleV(s); }],
    'Head': [1, (_, a) => {
      const s = seq(a[0], 'Head', 0);
      if (s.length === 0) fail('Attempted to apply Head to the empty sequence.');
      return s[0];
    }],
    'Tail': [1, (_, a) => {
      const s = seq(a[0], 'Tail', 0);
      if (s.length === 0) fail('Attempted to apply Tail to the empty sequence.');
      return new TupleV(s.slice(1));
    }],
    'SubSeq': [3, (_, a) => {
      if (typeof a[0] === 'string') return a[0].slice(int(a[1], 'SubSeq', 1) - 1, int(a[2], 'SubSeq', 2));
      const s = seq(a[0], 'SubSeq', 0), m = int(a[1], 'SubSeq', 1), n = int(a[2], 'SubSeq', 2);
      if (m > n) return EMPTY_TUPLE;
      if (m < 1 || n > s.length) fail(`The ${m < 1 ? 'second' : 'third'} argument of SubSeq must be in the domain of its first argument:\n${fmt(a[0])}\n, but instead it is\n${m < 1 ? m : n}`);
      return new TupleV(s.slice(m - 1, n));
    }],
    'SelectSeq': [2, (ev, a) => {
      const s = seq(a[0], 'SelectSeq', 0);
      return new TupleV(s.filter(x => {
        const r = ev.applyOp(a[1], [x]);
        if (typeof r !== 'boolean') fail(`The second argument of SelectSeq must return a boolean, but it returned:\n${fmt(r)}`);
        return r;
      }));
    }, { ops: [1] }],
  });

  const FiniteSets = module('FiniteSets', [], {
    'IsFiniteSet': [1, (_, a) => set(a[0], 'IsFiniteSet', 0).enumerable()],
    'Cardinality': [1, (_, a) => {
      const s = set(a[0], 'Cardinality', 0);
      if (!s.enumerable()) {
        if (emptyProduct(s)) return 0;
        fail(`Attempted to compute the cardinality of the infinite set ${fmt(s)}`);
      }
      return s.size();
    }],
  });

  const registers = new Map<number | string, Value>();
  const TLC = module('TLC', [], {
    'Print': [2, (_, a) => { io.print(`${fmt(a[0])}  ${fmt(a[1])}`); return a[1]; }],
    'PrintT': [1, (_, a) => { io.print(fmt(a[0])); return true; }],
    'Assert': [2, (_, a) => {
      if (typeof a[0] !== 'boolean') fail(`The first argument of Assert should be a boolean, but instead it is:\n${fmt(a[0])}`);
      if (!a[0]) {
        const e = new EvalError(`The first argument of Assert evaluated to FALSE; the second argument was:\n${fmt(a[1])}`);
        e.kind = 'assert';
        throw e;
      }
      return true;
    }],
    'JavaTime': [0, () => Math.floor(Date.now() / 1000) & 0x7fffffff],
    'TLCGet': [1, (ev, a) => {
      ev.stTouch++; // never a constant: definitions using it must not be cached
      if (typeof a[0] === 'string') {
        const key = a[0];
        if (key.startsWith('s:')) {
          const v = registers.get(key);
          if (v === undefined) fail(`TLCGet(${key}) was undefined.`);
          return v;
        }
        if (key === 'all' || key === 'all:named') {
          const pairs: [Value, Value][] = [];
          for (const [k, v] of registers) if ((typeof k === 'string') === (key === 'all:named')) pairs.push([k, new TupleV([v])]);
          return makeFcnFromPairs(pairs);
        }
        const h = ev.hooks.tlcGet?.(a[0]);
        if (h === undefined) fail(`TLCGet(${fmt(a[0])}) is not supported.`);
        return h;
      }
      const v = registers.get(int(a[0], 'TLCGet', 0));
      if (v === undefined) fail(`TLCGet(${a[0]}) was undefined.`);
      return v;
    }],
    'TLCSet': [2, (ev, a) => {
      if (typeof a[0] === 'string') {
        if (a[0].startsWith('s:')) registers.set(a[0], a[1]);
        else ev.hooks.tlcSet?.(a[0], a[1]);
        return true;
      }
      registers.set(int(a[0], 'TLCSet', 0), a[1]);
      return true;
    }],
    ':>': [2, (_, a) => makeFcn([a[0]], [a[1]])],
    '@@': [2, (_, a) => {
      if (!isFcn(a[0])) fail(`The first argument of @@ should be a function, but instead it is:\n${fmt(a[0])}`);
      if (!isFcn(a[1])) fail(`The second argument of @@ should be a function, but instead it is:\n${fmt(a[1])}`);
      const d0 = domainElems(a[0]), v0 = fcnValues(a[0]), d1 = domainElems(a[1]), v1 = fcnValues(a[1]);
      if (d1.length === 0) return a[0];
      if (d0.length === 0) return a[1];
      const pairs: [Value, Value][] = d0.map((d, i) => [d, v0[i]]);
      // first function wins: list its pairs first; makeFcnFromPairs keeps the first of equal keys (stable sort)
      for (let i = 0; i < d1.length; i++) pairs.push([d1[i], v1[i]]);
      return makeFcnFromPairs(pairs);
    }],
    'Permutations': [1, (_, a) => {
      const s = set(a[0], 'Permutations', 0).elems();
      const out: Value[] = [];
      const used = new Array(s.length).fill(false);
      const cur: Value[] = [];
      const rec = () => {
        if (cur.length === s.length) { out.push(makeFcn(s, cur.slice())); return; }
        for (let i = 0; i < s.length; i++) {
          if (used[i]) continue;
          used[i] = true; cur.push(s[i]); rec(); cur.pop(); used[i] = false;
        }
      };
      rec();
      return mkSet(out);
    }],
    'SortSeq': [2, (ev, a) => {
      const s = seq(a[0], 'SortSeq', 0).slice();
      // stable insertion via Array.sort with the user's strict comparison
      s.sort((x, y) => (ev.applyOp(a[1], [x, y]) === true ? -1 : ev.applyOp(a[1], [y, x]) === true ? 1 : 0));
      return new TupleV(s);
    }, { ops: [1] }],
    'RandomElement': [1, (ev, a) => {
      const s = set(a[0], 'RandomElement', 0).elems();
      if (s.length === 0) fail('Attempted to apply RandomElement to the empty set.');
      return s[Math.floor(ev.hooks.random() * s.length)];
    }],
    'Any': new LazySetV('Any', () => true),
    'ToString': [1, (_, a) => fmt(a[0])],
    'TLCEval': [1, (_, a) => a[0]],
  });

  const TLCExt = module('TLCExt', [], {
    'AssertEq': [2, (_, a) => {
      const eq = valEq(a[0], a[1]);
      if (!eq) io.print(`\nAssertion failed:\n${fmt(a[0])}\n!=\n${fmt(a[1])}\n`);
      return eq;
    }],
    'AssertError': [2, (ev, a) => {
      const expected = ev.unthunk(a[0]);
      try {
        ev.unthunk(a[1]);
      } catch (e) {
        if (e instanceof EvalError) {
          if (e.message === expected) return true;
          io.print(`\nAssertion failed:\n${fmt(expected)}\n!=\n${fmt(e.message)}\n`);
          return false;
        }
        throw e;
      }
      return false;
    }, { lazy: true }],
    'TLCModelValue': [1, (_, a) => modelValue(String(a[0]))],
    'TLCDefer': [1, () => true],
    'PickSuccessor': [1, () => true],
    'TLCNoOp': [1, (_, a) => a[0]],
    'TLCCache': [2, (_, a) => a[0]],
    'TLCGetOrDefault': [2, (_, a) => registers.get(int(a[0], 'TLCGetOrDefault', 0)) ?? a[1]],
    'TLCGetAndSet': [4, (ev, a) => {
      const old = registers.get(int(a[0], 'TLCGetAndSet', 0)) ?? a[3];
      registers.set(a[0], ev.applyOp(a[1], [old, a[2]]));
      return old;
    }, { ops: [1] }],
    'TLCFP': [1, (ev, a) => ev.hooks.fp?.(a[0]) ?? 0],
    'Trace': [0, ev => (ev.stTouch++, ev.hooks.trace?.()) ?? fail('Trace is not available in this context.')],
    'CounterExample': [0, ev => (ev.stTouch++, ev.hooks.counterExample?.()) ?? fail('CounterExample is not available in this context.')],
    'ToTrace': [1, () => fail('ToTrace is not supported.')],
  });

  // ---- Bags ----
  const bagPairs = (b: Value, op: string): [Value[], number[]] => {
    if (!isFcn(b)) fail(`Attempted to apply ${op} to the non-bag value:\n${fmt(b)}`);
    return [domainElems(b), fcnValues(b) as number[]];
  };
  const mkBag = (m: [Value, number][]) => makeFcnFromPairs(m.filter(p => p[1] > 0) as [Value, Value][]);
  const Bags = module('Bags', [], {
    'IsABag': [1, (_, a) => isFcn(a[0]) && fcnValues(a[0]).every(x => typeof x === 'number' && x > 0)],
    'BagToSet': [1, (_, a) => new SetV(domainElems(a[0]).slice())],
    'SetToBag': [1, (_, a) => { const e = set(a[0], 'SetToBag', 0).elems(); return makeFcn(e, e.map(() => 1)); }],
    'BagIn': [2, (_, a) => bsearch(bagPairs(a[1], 'BagIn')[0], a[0]) >= 0],
    'EmptyBag': EMPTY_TUPLE,
    '\\oplus': [2, (_, a) => {
      const [d0, v0] = bagPairs(a[0], '(+)'), [d1, v1] = bagPairs(a[1], '(+)');
      const out: [Value, number][] = d0.map((d, i) => [d, v0[i]]);
      for (let i = 0; i < d1.length; i++) {
        const k = bsearch(d0, d1[i]);
        if (k >= 0) out[k][1] = checkInt(out[k][1] + v1[i], `${out[k][1]}+${v1[i]}`); else out.push([d1[i], v1[i]]);
      }
      return mkBag(out);
    }],
    '\\ominus': [2, (_, a) => {
      const [d0, v0] = bagPairs(a[0], '(-)'), [d1, v1] = bagPairs(a[1], '(-)');
      return mkBag(d0.map((d, i) => { const k = bsearch(d1, d); return [d, k >= 0 ? v0[i] - v1[k] : v0[i]]; }));
    }],
    'BagUnion': [1, (_, a) => {
      const out: [Value, number][] = [];
      for (const b of set(a[0], 'BagUnion', 0).elems()) {
        const [d, v] = bagPairs(b, 'BagUnion');
        for (let i = 0; i < d.length; i++) {
          const hit = out.find(p => valEq(p[0], d[i]));
          if (hit) hit[1] = checkInt(hit[1] + v[i], `${hit[1]}+${v[i]}`); else out.push([d[i], v[i]]);
        }
      }
      return mkBag(out);
    }],
    '\\sqsubseteq': [2, (_, a) => {
      const [d0, v0] = bagPairs(a[0], '\\sqsubseteq'), [d1, v1] = bagPairs(a[1], '\\sqsubseteq');
      return d0.every((d, i) => { const k = bsearch(d1, d); return k >= 0 && v0[i] <= v1[k]; });
    }],
    'SubBag': [1, (_, a) => {
      const [d, v] = bagPairs(a[0], 'SubBag');
      const out: Value[] = [];
      const cur: [Value, number][] = [];
      const rec = (i: number) => {
        if (i === d.length) { out.push(mkBag(cur.slice())); return; }
        for (let c = 0; c <= v[i]; c++) { cur.push([d[i], c]); rec(i + 1); cur.pop(); }
      };
      rec(0);
      return mkSet(out);
    }],
    'BagOfAll': [2, (ev, a) => {
      const [d, v] = bagPairs(a[1], 'BagOfAll');
      const out: [Value, number][] = [];
      for (let i = 0; i < d.length; i++) {
        const x = ev.applyOp(a[0], [d[i]]);
        const hit = out.find(p => valEq(p[0], x));
        if (hit) hit[1] += v[i]; else out.push([x, v[i]]);
      }
      return mkBag(out);
    }, { ops: [0] }],
    'BagCardinality': [1, (_, a) => bagPairs(a[0], 'BagCardinality')[1].reduce((x, y) => checkInt(x + y, `${x}+${y}`), 0)],
    'CopiesIn': [2, (_, a) => { const [d, v] = bagPairs(a[1], 'CopiesIn'); const k = bsearch(d, a[0]); return k >= 0 ? v[k] : 0; }],
  });

  // ---- _Possible (support module of the _POSSIBLE config keyword) ----
  const POSSIBLE_KEY = 's:_possible';
  const possibleCounts = (): Value => registers.get(POSSIBLE_KEY) ?? EMPTY_TUPLE;
  const Possible = module('_Possible', [], {
    '_Track': [2, (_, a) => {
      if (typeof a[0] !== 'boolean') fail(`Attempted to evaluate an expression of form IF P THEN ... ELSE ..., but P was the non-boolean value:\n${fmt(a[0])}`);
      const old = possibleCounts();
      const d = domainElems(old), v = fcnValues(old);
      const pairs: [Value, Value][] = d.map((x, i) => [x, v[i]]);
      const hit = pairs.find(p => p[0] === a[1]);
      if (hit) { if (a[0]) hit[1] = (hit[1] as number) + 1; }
      else pairs.push([a[1], a[0] ? 1 : 0]);
      registers.set(POSSIBLE_KEY, makeFcnFromPairs(pairs));
      return true;
    }],
    '_Counts': [0, ev => { ev.stTouch++; return possibleCounts(); }],
    '_CheckName': [1, (_, a) => {
      const c = possibleCounts();
      const d = domainElems(c), v = fcnValues(c);
      const i = d.indexOf(a[0]);
      if (i >= 0 && v[i] !== 0) return true;
      io.print(fmt(c));
      return false;
    }],
    '_PrintCounts': [0, () => { io.print(fmt(possibleCounts())); return true; }],
  });

  const subsetsOfSize = (b: Value[], k: number): Value[] => {
    const out: Value[] = [];
    const idx: number[] = [];
    const rec = (start: number, left: number) => {
      if (left === 0) { out.push(new SetV(idx.map(i => b[i]))); return; }
      for (let i = start; i <= b.length - left; i++) { idx.push(i); rec(i + 1, left - 1); idx.pop(); }
    };
    rec(0, k);
    return out;
  };
  // A set known to be empty without enumerating it (components are asked in order, like TLC).
  const knownEmpty = (x: SetBase): boolean => {
    if (x instanceof CrossV) return x.sets.some(knownEmpty);
    if (x instanceof RecSetV) return x.sets.some(knownEmpty);
    if (x instanceof FcnSetV) return knownEmpty(x.rng) && !knownEmpty(x.dom);
    if (x instanceof IntervalV) return x.hi < x.lo;
    if (x instanceof SetV) return x.e.length === 0;
    if (x instanceof InfSetV) return false;
    return x.enumerable() && x.size() === 0;
  };
  // A uniformly drawn element of a non-empty finite set, without enumerating products and function sets.
  const randomElem = (ev: Evaluator, x: SetBase): Value => {
    const rnd = (n: number) => Math.min(n - 1, Math.floor(ev.hooks.random() * n));
    if (x instanceof IntervalV) return x.lo + rnd(x.hi - x.lo + 1);
    if (x instanceof CrossV) return new TupleV(x.sets.map(c => randomElem(ev, c)));
    if (x instanceof RecSetV) return new RecordV(x.names, x.sets.map(c => randomElem(ev, c)));
    if (x instanceof FcnSetV) { const d = x.dom.elems(); return makeFcn(d, d.map(() => randomElem(ev, x.rng))); }
    const e = x.elems();
    return e[rnd(e.length)];
  };
  const finiteSet = (v: Value, op: string, i: number, what: string): SetBase => {
    if (v instanceof SetBase && (knownEmpty(v) || v.enumerable())) return v;
    return fail(`The ${ORD[i]} argument of ${op} should be a ${what}, but instead it is:\n${fmt(v)}`);
  };
  const cardOf = (x: SetBase): number => knownEmpty(x) ? 0 : x.size();
  const randomSubset = (ev: Evaluator, k: number, x: SetBase): Value => {
    const n = cardOf(x);
    if (n === 0) return mkSet([]);
    if (k >= n) return mkSet(x.elems().slice());
    if (n <= 4 * k || n <= 64) {
      const e = x.elems().slice();
      for (let i = e.length - 1; i > 0; i--) { const j = Math.floor(ev.hooks.random() * (i + 1)); [e[i], e[j]] = [e[j], e[i]]; }
      return mkSet(e.slice(0, k));
    }
    let out: Value[] = [];
    while (out.length < k) {
      const more: Value[] = [];
      for (let i = out.length; i < k; i++) more.push(randomElem(ev, x));
      out = mkSet(out.concat(more)).elems();
    }
    return new SetV(out);
  };
  const randomSetOfSubsets = (ev: Evaluator, picks: number, p: number, x: SetBase): Value => {
    const e = x.elems();
    const out: Value[] = [];
    for (let i = 0; i < picks; i++) out.push(new SetV(e.filter(() => ev.hooks.random() < p)));
    return mkSet(out);
  };
  const tooManyPicks = (picks: number, n: number, op: string): void => {
    if (32 - Math.clz32(picks) > n && picks > 2 ** n) fail(`The first argument of ${op} should be a nonnegative integer that is smaller than the subset's size of 2^${n}, but instead it is:\n${picks}`);
  };
  const Randomization = module('Randomization', [], {
    'RandomSubset': [2, (ev, a) => {
      if (typeof a[0] !== 'number') fail(`The first argument of RandomSubset should be a nonnegative integer, but instead it is:\n${fmt(a[0])}`);
      const x = finiteSet(a[1], 'RandomSubset', 1, 'a finite set');
      if (a[0] < 0) fail(`Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.Value tlc2.module.Randomization.RandomSubset(tlc2.value.impl.Value,tlc2.value.impl.Value),\nbut it produced the following error:\n${a[0]}`);
      return randomSubset(ev, a[0], x);
    }],
    'RandomSetOfSubsets': [3, (ev, a) => {
      if (typeof a[0] !== 'number' || a[0] < 0) fail(`The first argument of RandomSetOfSubsets should be a nonnegative integer, but instead it is:\n${fmt(a[0])}`);
      if (typeof a[1] !== 'number' || a[1] < 0) fail(`The second argument of RandomSetOfSubsets should be a nonnegative integer, but instead it is:\n${fmt(a[1])}`);
      const x = finiteSet(a[2], 'RandomSetOfSubsets', 2, 'finite set');
      const n = cardOf(x);
      tooManyPicks(a[0], n, 'RandomSetOfSubsets');
      if (n < a[1]) fail(`The second argument of RandomSetOfSubsets should be a nonnegative integer in range 0..Cardinality(S), but instead it is:\n${fmt(a[1])}`);
      return randomSetOfSubsets(ev, a[0], n === 0 ? 0 : a[1] / n, x);
    }],
    'RandomSubsetSet': [3, (ev, a) => {
      if (typeof a[0] !== 'number' || a[0] < 0) fail(`The first argument of RandomSubsetSetProbability should be a nonnegative integer, but instead it is:\n${fmt(a[0])}`);
      const p = typeof a[1] === 'string' && a[1].trim() !== '' ? Number(a[1]) : NaN;
      if (typeof a[1] !== 'string') fail(`The second argument of RandomSubsetSetProbability should be a string literal representing a probability, but instead it is:\n${fmt(a[1])}`);
      if (Number.isNaN(p) || p < 0 || p > 1) fail(`The second argument of RandomSubsetSetProbability should be a string literal does not represent a parsable probability, but instead it is:\n${fmt(a[1])}`);
      const x = finiteSet(a[2], 'RandomSubsetSetProbability', 2, 'finite set');
      tooManyPicks(a[0], cardOf(x), 'RandomSubsetSetProbability');
      return randomSetOfSubsets(ev, a[0], p, x);
    }],
    'TestRandomSetOfSubsets': [3, () => true],
  });
  void subsetsOfSize; void compare; void Closure; void DefRef; void RecordV; void FcnV; void ModelValue;

  const m = new Map<string, ModuleInfo>();
  for (const x of [Naturals, Integers, Reals, Sequences, FiniteSets, TLC, TLCExt, Bags, Randomization, Possible]) m.set(x.name, x);
  return m;
}

