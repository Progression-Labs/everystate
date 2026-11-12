// Native overrides for operators of the bundled TLA+ community modules. The TLA+ definitions in the
// module sources remain the specification; these replace them for speed or because the TLA+
// definition is not executable (TLC ships the same operators as Java overrides).
// Format: OVERRIDES[module][operator] = [fn(ev, args), { ops: indices of operator-valued args }].
import type { Builtin } from './modules.ts';
import { fail, int, seq, set } from './stdlib.ts';
import type { Fn } from './stdlib.ts';
import { SetV, TupleV, valEq, mkSet, fcnValues } from './values.ts';
import type { Value } from './values.ts';

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
