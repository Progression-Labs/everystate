// Native implementations of the TLA+ standard modules.
import type { Def, ModuleInfo, Builtin } from './modules.ts';
import type { Evaluator } from './eval.ts';
import { Closure, DefRef } from './eval.ts';
import {
  EvalError, SetBase, SetV, IntervalV, InfSetV, SeqSetV, LazySetV, TupleV, RecordV, FcnV, ModelValue, modelValue,
  valEq, compare, mkSet, BOOLEAN_SET, makeFcn, makeFcnFromPairs, domainElems, fcnValues, isFcn, fmt, EMPTY_TUPLE, bsearch,
} from './values.ts';
import type { Value } from './values.ts';

type Fn = (ev: Evaluator, a: any[]) => Value;
type Spec = [number, Fn, Partial<Builtin>?] | SetBase | TupleV;

const fail = (msg: string): never => { throw new EvalError(msg); };
const ORD = ['first', 'second', 'third', 'fourth'];
function int(v: Value, op: string, i: number): number {
  if (typeof v !== 'number') fail(`The ${ORD[i]} argument of ${op} should be an integer, but instead it is:\n${fmt(v)}`);
  return v;
}
function nat(v: Value, op: string, i: number): number {
  if (typeof v !== 'number' || v < 0) fail(`The ${ORD[i]} argument of ${op} should be a natural number, but instead it is:\n${fmt(v)}`);
  return v;
}
function seq(v: Value, op: string, i: number): Value[] {
  if (v instanceof TupleV) return v.e;
  return fail(`The ${ORD[i]} argument of ${op} should be a sequence, but instead it is:\n${fmt(v)}`);
}
function set(v: Value, op: string, i: number): SetBase {
  if (v instanceof SetBase) return v;
  return fail(`The ${ORD[i]} argument of ${op} should be a set, but instead it is:\n${fmt(v)}`);
}
function checkInt(n: number, what: string): number {
  if (n > 2147483647 || n < -2147483648) fail(`Overflow when computing ${what}`);
  return n;
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
    '+': [2, (_, a) => checkInt(int(a[0], '+', 0) + int(a[1], '+', 1), `${a[0]} + ${a[1]}`)],
    '-': [2, (_, a) => checkInt(int(a[0], '-', 0) - int(a[1], '-', 1), `${a[0]} - ${a[1]}`)],
    '*': [2, (_, a) => checkInt(int(a[0], '*', 0) * int(a[1], '*', 1), `${a[0]} * ${a[1]}`)],
    '^': [2, (_, a) => {
      const b = int(a[0], '^', 0), e = int(a[1], '^', 1);
      if (e < 0) fail(`The second argument of ^ should be a natural number, but instead it is:\n${e}`);
      return checkInt(b ** e, `${b} ^ ${e}`);
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
      if (!s.enumerable()) fail(`Attempted to compute the cardinality of the infinite set ${fmt(s)}`);
      return s.size();
    }],
  });

  const registers = new Map<number, Value>();
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
      if (typeof a[0] === 'string') {
        const h = ev.hooks.tlcGet?.(a[0]);
        if (h === undefined) fail(`TLCGet(${fmt(a[0])}) is not supported.`);
        return h;
      }
      const v = registers.get(int(a[0], 'TLCGet', 0));
      if (v === undefined) fail(`TLCGet(${a[0]}) was undefined.`);
      return v;
    }],
    'TLCSet': [2, (ev, a) => {
      if (typeof a[0] === 'string') { ev.hooks.tlcSet?.(a[0], a[1]); return true; }
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
    'Trace': [0, ev => ev.hooks.trace?.() ?? fail('Trace is not available in this context.')],
    'CounterExample': [0, ev => ev.hooks.counterExample?.() ?? fail('CounterExample is not available in this context.')],
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
        if (k >= 0) out[k][1] += v1[i]; else out.push([d1[i], v1[i]]);
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
          if (hit) hit[1] += v[i]; else out.push([d[i], v[i]]);
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
    'BagCardinality': [1, (_, a) => bagPairs(a[0], 'BagCardinality')[1].reduce((x, y) => x + y, 0)],
    'CopiesIn': [2, (_, a) => { const [d, v] = bagPairs(a[1], 'CopiesIn'); const k = bsearch(d, a[0]); return k >= 0 ? v[k] : 0; }],
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
  const Randomization = module('Randomization', [], {
    'RandomSubset': [2, (ev, a) => {
      const k = int(a[0], 'RandomSubset', 0), s = set(a[1], 'RandomSubset', 1).elems().slice();
      if (k < 0 || k > s.length) fail(`The first argument of RandomSubset should be between 0 and the cardinality of the set, but it is ${k}`);
      for (let i = s.length - 1; i > 0; i--) { const j = Math.floor(ev.hooks.random() * (i + 1)); [s[i], s[j]] = [s[j], s[i]]; }
      return mkSet(s.slice(0, k));
    }],
    'RandomSetOfSubsets': [3, (ev, a) => {
      const k = int(a[0], 'RandomSetOfSubsets', 0), n = int(a[1], 'RandomSetOfSubsets', 1), s = set(a[2], 'RandomSetOfSubsets', 2).elems();
      const out: Value[] = [];
      for (let i = 0; i < k; i++) {
        const pick = s.filter(() => ev.hooks.random() < (s.length ? n / s.length : 0));
        out.push(new SetV(pick));
      }
      return mkSet(out);
    }],
    'RandomSubsetSet': [3, (ev, a) => {
      const k = int(a[0], 'RandomSubsetSet', 0), s = set(a[2], 'RandomSubsetSet', 2).elems();
      const out: Value[] = [];
      for (let i = 0; i < k; i++) out.push(new SetV(s.filter(() => ev.hooks.random() < 0.5)));
      return mkSet(out);
    }],
    'TestRandomSetOfSubsets': [3, () => true],
  });
  void subsetsOfSize; void compare; void Closure; void DefRef; void RecordV; void FcnV; void ModelValue;

  const m = new Map<string, ModuleInfo>();
  for (const x of [Naturals, Integers, Reals, Sequences, FiniteSets, TLC, TLCExt, Bags, Randomization]) m.set(x.name, x);
  return m;
}

// Native overrides for operators of bundled (TLA+-source) modules, applied after loading for speed.
export const OVERRIDES: Record<string, Record<string, [Fn, Partial<Builtin>?]>> = {
  FiniteSetsExt: {
    FoldSet: [(ev, a) => {
      let acc = a[1];
      for (const x of set(a[2], 'FoldSet', 2).elems()) acc = ev.applyOp(a[0], [x, acc]);
      return acc;
    }, { ops: [0] }],
    Quantify: [(ev, a) => set(a[0], 'Quantify', 0).elems().filter(x => ev.applyOp(a[1], [x]) === true).length, { ops: [1] }],
    SumSet: [(_, a) => set(a[0], 'SumSet', 0).elems().reduce((x: number, y) => x + int(y, 'SumSet', 0), 0)],
    ProductSet: [(_, a) => set(a[0], 'ProductSet', 0).elems().reduce((x: number, y) => x * int(y, 'ProductSet', 0), 1)],
    Max: [(_, a) => { const e = set(a[0], 'Max', 0).elems(); if (!e.length) fail('Max of the empty set is undefined.'); return e.reduce((x, y) => (int(y, 'Max', 0) > x ? y : x), int(e[0], 'Max', 0)); }],
    Min: [(_, a) => { const e = set(a[0], 'Min', 0).elems(); if (!e.length) fail('Min of the empty set is undefined.'); return e.reduce((x, y) => (int(y, 'Min', 0) < x ? y : x), int(e[0], 'Min', 0)); }],
    kSubset: [(_, a) => {
      const k = int(a[0], 'kSubset', 0), b = set(a[1], 'kSubset', 1).elems();
      if (k < 0 || k > b.length) return new SetV([]);
      const out: Value[] = [];
      const idx: number[] = [];
      const rec = (start: number, left: number) => {
        if (left === 0) { out.push(new SetV(idx.map(i => b[i]))); return; }
        for (let i = start; i <= b.length - left; i++) { idx.push(i); rec(i + 1, left - 1); idx.pop(); }
      };
      rec(0, k);
      return new SetV(out);
    }],
  },
  Functions: {
    FoldFunction: [(ev, a) => {
      let acc = a[1];
      for (const x of fcnValues(a[2])) acc = ev.applyOp(a[0], [x, acc]);
      return acc;
    }, { ops: [0] }],
    FoldFunctionOnSet: [(ev, a) => {
      let acc = a[1];
      for (const d of set(a[3], 'FoldFunctionOnSet', 3).elems()) acc = ev.applyOp(a[0], [ev.applyFcn(a[2], d), acc]);
      return acc;
    }, { ops: [0] }],
  },
  SequencesExt: {
    FoldSeq: [(ev, a) => { let acc = a[1]; for (const x of seq(a[2], 'FoldSeq', 2)) acc = ev.applyOp(a[0], [x, acc]); return acc; }, { ops: [0] }],
    FoldLeft: [(ev, a) => { let acc = a[1]; for (const x of seq(a[2], 'FoldLeft', 2)) acc = ev.applyOp(a[0], [acc, x]); return acc; }, { ops: [0] }],
    FoldRight: [(ev, a) => { let acc = a[2]; const s = seq(a[1], 'FoldRight', 1); for (let i = s.length - 1; i >= 0; i--) acc = ev.applyOp(a[0], [s[i], acc]); return acc; }, { ops: [0] }],
    ToSet: [(_, a) => mkSet(seq(a[0], 'ToSet', 0).slice())],
    Reverse: [(_, a) => new TupleV(seq(a[0], 'Reverse', 0).slice().reverse())],
    Range: [(_, a) => mkSet(fcnValues(a[0]).slice())],
    Contains: [(_, a) => seq(a[0], 'Contains', 0).some(x => valEq(x, a[1]))],
    Cons: [(_, a) => new TupleV([a[0], ...seq(a[1], 'Cons', 1)])],
    Front: [(_, a) => { const s = seq(a[0], 'Front', 0); if (!s.length) fail('Attempted to apply Front to the empty sequence.'); return new TupleV(s.slice(0, -1)); }],
    Last: [(_, a) => { const s = seq(a[0], 'Last', 0); if (!s.length) fail('Attempted to apply Last to the empty sequence.'); return s[s.length - 1]; }],
    IsPrefix: [(_, a) => { const s = seq(a[0], 'IsPrefix', 0), t = seq(a[1], 'IsPrefix', 1); return s.length <= t.length && s.every((x, i) => valEq(x, t[i])); }],
    IsSuffix: [(_, a) => { const s = seq(a[0], 'IsSuffix', 0), t = seq(a[1], 'IsSuffix', 1); const o = t.length - s.length; return o >= 0 && s.every((x, i) => valEq(x, t[o + i])); }],
    SetToSeq: [(_, a) => new TupleV(set(a[0], 'SetToSeq', 0).elems().slice())],
  },
  Folds: {
    MapThenFoldSet: [(ev, a) => {
      // MapThenFoldSet(op(_,_), base, f(_), choose(_), S)
      let acc = a[1];
      const es = set(a[4], 'MapThenFoldSet', 4).elems();
      for (const x of es) acc = ev.applyOp(a[0], [ev.applyOp(a[2], [x]), acc]);
      return acc;
    }, { ops: [0, 2, 3] }],
  },
};
