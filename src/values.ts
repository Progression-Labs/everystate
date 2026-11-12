// Runtime values. Booleans, integers and strings are native JS values; everything else is a class.
// Functions are kept in canonical form: domain 1..n => TupleV, non-empty all-string domain => RecordV,
// anything else => FcnV. Sets are either an explicit sorted SetV or one of the symbolic set classes.
import { TlaError } from './lexer.ts';

export type Value = any;

export class EvalError extends TlaError {
  constructor(msg: string) { super(msg, undefined, undefined, 'eval'); }
}
const err = (msg: string): never => { throw new EvalError(msg); };

// ---- string interning: TLC orders strings by first-seen order, not lexicographically ----
const strIds = new Map<string, number>();
export function strId(s: string): number {
  let id = strIds.get(s);
  if (id === undefined) { id = strIds.size + 1; strIds.set(s, id); }
  return id;
}
export function resetInterning(): void { strIds.clear(); modelValues.clear(); }

export class ModelValue {
  name: string;
  id: number;
  type: string | null; // typed model values: "a_1" has type "a"
  constructor(name: string, id: number) {
    this.name = name;
    this.id = id;
    this.type = name.length > 2 && name[1] === '_' ? name[0] : null;
  }
}
const modelValues = new Map<string, ModelValue>();
export function modelValue(name: string): ModelValue {
  let m = modelValues.get(name);
  if (!m) { m = new ModelValue(name, strId(name)); modelValues.set(name, m); }
  return m;
}
export function allModelValues(): ModelValue[] { return [...modelValues.values()]; }

export class TupleV {
  e: Value[];
  constructor(e: Value[]) { this.e = e; }
}
export class RecordV {
  names: string[]; // sorted by string order
  vals: Value[];
  constructor(names: string[], vals: Value[]) { this.names = names; this.vals = vals; }
  get(name: string): Value | undefined {
    const i = this.names.indexOf(name);
    return i < 0 ? undefined : this.vals[i];
  }
}
export class FcnV {
  dom: Value[]; // sorted, deduplicated
  vals: Value[];
  constructor(dom: Value[], vals: Value[]) { this.dom = dom; this.vals = vals; }
}
export const EMPTY_TUPLE = new TupleV([]);

export abstract class SetBase {
  abstract contains(v: Value): boolean;
  abstract elems(): Value[]; // normalized (sorted, deduplicated); throws if not enumerable
  enumerable(): boolean { return true; }
  size(): number { return this.elems().length; }
}

export class SetV extends SetBase {
  e: Value[];
  constructor(sortedElems: Value[]) { super(); this.e = sortedElems; }
  contains(v: Value): boolean { return bsearch(this.e, v) >= 0; }
  elems(): Value[] { return this.e; }
  size(): number { return this.e.length; }
}
export const EMPTY_SET = new SetV([]);
export const BOOLEAN_SET = new SetV([false, true]);

export class IntervalV extends SetBase {
  lo: number; hi: number;
  private cache: Value[] | null = null;
  constructor(lo: number, hi: number) { super(); this.lo = lo; this.hi = hi; }
  contains(v: Value): boolean { return typeof v === 'number' ? Number.isInteger(v) && v >= this.lo && v <= this.hi : (typeof v === 'object' && v instanceof ModelValue ? false : err(`Attempted to check if the value:\n${fmt(v)}\nis in the integer interval ${fmt(this)}`)); }
  elems(): Value[] {
    if (!this.cache) {
      const a: number[] = [];
      for (let i = this.lo; i <= this.hi; i++) a.push(i);
      this.cache = a;
    }
    return this.cache;
  }
  size(): number { return Math.max(0, this.hi - this.lo + 1); }
}

export class SubsetV extends SetBase {
  base: SetBase;
  private cache: Value[] | null = null;
  constructor(base: SetBase) { super(); this.base = base; }
  contains(v: Value): boolean {
    if (!(v instanceof SetBase)) return err(`Attempted to check if the non-set value:\n${fmt(v)}\nis in ${fmt(this)}`);
    if (!v.enumerable()) return err('Attempted to check if a non-enumerable set is an element of SUBSET');
    for (const x of v.elems()) if (!this.base.contains(x)) return false;
    return true;
  }
  enumerable(): boolean { return this.base.enumerable(); }
  size(): number { return 2 ** this.base.size(); }
  elems(): Value[] {
    if (this.cache) return this.cache;
    const b = this.base.elems();
    const n = b.length;
    if (n > 26) err(`Attempted to enumerate SUBSET of a set with ${n} elements; this is too large.`);
    const out: Value[] = [];
    // by size, then lexicographic: this is the normalized set order
    const idx: number[] = [];
    const rec = (start: number, k: number) => {
      if (k === 0) { out.push(new SetV(idx.map(i => b[i]))); return; }
      for (let i = start; i <= n - k; i++) { idx.push(i); rec(i + 1, k - 1); idx.pop(); }
    };
    for (let k = 0; k <= n; k++) rec(0, k);
    return (this.cache = out);
  }
}

export class FcnSetV extends SetBase {
  dom: SetBase; rng: SetBase;
  private cache: Value[] | null = null;
  constructor(dom: SetBase, rng: SetBase) { super(); this.dom = dom; this.rng = rng; }
  contains(v: Value): boolean {
    const d = domainOf(v);
    if (d === null) return false;
    if (!setEq(d, this.dom)) return false;
    for (const x of fcnValues(v)) if (!this.rng.contains(x)) return false;
    return true;
  }
  enumerable(): boolean { return this.dom.enumerable() && this.rng.enumerable(); }
  size(): number { return this.rng.size() ** this.dom.size(); }
  elems(): Value[] {
    if (this.cache) return this.cache;
    const d = this.dom.elems(), r = this.rng.elems();
    const out: Value[] = [];
    const n = d.length;
    if (r.length === 0) return (this.cache = n === 0 ? [EMPTY_TUPLE] : []);
    const total = r.length ** n;
    if (total > 5e7) err(`Attempted to enumerate a set of functions with ${total} elements; this is too large.`);
    const idx = new Array<number>(n).fill(0);
    for (;;) {
      out.push(makeFcn(d, idx.map(i => r[i])));
      let k = n - 1;
      while (k >= 0 && ++idx[k] === r.length) { idx[k] = 0; k--; }
      if (k < 0) break;
    }
    return (this.cache = sortDedup(out));
  }
}

export class RecSetV extends SetBase {
  names: string[]; sets: SetBase[]; // names sorted
  private cache: Value[] | null = null;
  constructor(names: string[], sets: SetBase[]) { super(); this.names = names; this.sets = sets; }
  contains(v: Value): boolean {
    if (!(v instanceof RecordV) || v.names.length !== this.names.length) return false;
    for (let i = 0; i < this.names.length; i++) {
      if (v.names[i] !== this.names[i] || !this.sets[i].contains(v.vals[i])) return false;
    }
    return true;
  }
  enumerable(): boolean { return this.sets.every(s => s.enumerable()); }
  size(): number { return this.sets.reduce((a, s) => a * s.size(), 1); }
  elems(): Value[] {
    if (this.cache) return this.cache;
    const es = this.sets.map(s => s.elems());
    const out: Value[] = [];
    if (es.some(e => e.length === 0)) return (this.cache = out);
    const n = es.length;
    const idx = new Array<number>(n).fill(0);
    for (;;) {
      out.push(new RecordV(this.names, idx.map((i, k) => es[k][i])));
      let k = n - 1;
      while (k >= 0 && ++idx[k] === es[k].length) { idx[k] = 0; k--; }
      if (k < 0) break;
    }
    return (this.cache = sortDedup(out));
  }
}

export class CrossV extends SetBase {
  sets: SetBase[];
  private cache: Value[] | null = null;
  constructor(sets: SetBase[]) { super(); this.sets = sets; }
  contains(v: Value): boolean {
    if (!(v instanceof TupleV) || v.e.length !== this.sets.length) return false;
    for (let i = 0; i < this.sets.length; i++) if (!this.sets[i].contains(v.e[i])) return false;
    return true;
  }
  enumerable(): boolean { return this.sets.every(s => s.enumerable()); }
  size(): number { return this.sets.reduce((a, s) => a * s.size(), 1); }
  elems(): Value[] {
    if (this.cache) return this.cache;
    const es = this.sets.map(s => s.elems());
    const out: Value[] = [];
    if (es.some(e => e.length === 0)) return (this.cache = out);
    const n = es.length;
    const idx = new Array<number>(n).fill(0);
    for (;;) {
      out.push(new TupleV(idx.map((i, k) => es[k][i])));
      let k = n - 1;
      while (k >= 0 && ++idx[k] === es[k].length) { idx[k] = 0; k--; }
      if (k < 0) break;
    }
    return (this.cache = out);
  }
}

export class SeqSetV extends SetBase {
  base: SetBase;
  constructor(base: SetBase) { super(); this.base = base; }
  contains(v: Value): boolean {
    if (!(v instanceof TupleV)) return false;
    for (const x of v.e) if (!this.base.contains(x)) return false;
    return true;
  }
  enumerable(): boolean { return false; }
  elems(): Value[] { return err(`Attempted to enumerate the non-enumerable set Seq(${fmt(this.base)}).`); }
}

export class InfSetV extends SetBase {
  kind: 'Nat' | 'Int' | 'Real' | 'STRING';
  constructor(kind: 'Nat' | 'Int' | 'Real' | 'STRING') { super(); this.kind = kind; }
  contains(v: Value): boolean {
    switch (this.kind) {
      case 'Nat': return typeof v === 'number' ? Number.isInteger(v) && v >= 0 : v instanceof ModelValue ? false : err(`Attempted to check if the value:\n${fmt(v)}\nis in Nat.`);
      case 'Int': return typeof v === 'number' ? Number.isInteger(v) : v instanceof ModelValue ? false : err(`Attempted to check if the value:\n${fmt(v)}\nis in Int.`);
      case 'Real': return typeof v === 'number' ? true : v instanceof ModelValue ? false : err(`Attempted to check if the value:\n${fmt(v)}\nis in Real.`);
      default: return typeof v === 'string' ? true : v instanceof ModelValue ? false : err(`Attempted to check if the value:\n${fmt(v)}\nis in STRING.`);
    }
  }
  enumerable(): boolean { return false; }
  elems(): Value[] { return err(`Attempted to enumerate the non-enumerable set ${this.kind}.`); }
}

// Lazy union / intersection / difference / filter, used only when an operand is not enumerable.
export class LazySetV extends SetBase {
  desc: string;
  pred: (v: Value) => boolean;
  constructor(desc: string, pred: (v: Value) => boolean) { super(); this.desc = desc; this.pred = pred; }
  contains(v: Value): boolean { return this.pred(v); }
  enumerable(): boolean { return false; }
  elems(): Value[] { return err(`Attempted to enumerate a non-enumerable set (${this.desc}).`); }
}

// A set defined by a membership predicate plus an on-demand enumeration (TLC's lazy SetPred/SetCup/...).
export class DerivedSetV extends SetBase {
  desc: string;
  pred: (v: Value) => boolean;
  gen: (() => Value[]) | null;
  private cache: Value[] | null = null;
  constructor(desc: string, pred: (v: Value) => boolean, gen: (() => Value[]) | null) { super(); this.desc = desc; this.pred = pred; this.gen = gen; }
  contains(v: Value): boolean { return this.cache ? bsearch(this.cache, v) >= 0 : this.pred(v); }
  enumerable(): boolean { return this.gen !== null; }
  elems(): Value[] {
    if (this.cache) return this.cache;
    if (!this.gen) return err(`Attempted to enumerate a non-enumerable set (${this.desc}).`);
    return (this.cache = sortDedup(this.gen()));
  }
}

// ---- kinds, comparison, equality ----
const K_BOOL = 0, K_INT = 1, K_STR = 2, K_MODEL = 3, K_TUPLE = 4, K_REC = 5, K_FCN = 6, K_SET = 7, K_OTHER = 8;
function kindOf(v: Value): number {
  switch (typeof v) {
    case 'boolean': return K_BOOL;
    case 'number': return K_INT;
    case 'string': return K_STR;
  }
  if (v instanceof SetBase) return K_SET;
  if (v instanceof TupleV) return K_TUPLE;
  if (v instanceof RecordV) return K_REC;
  if (v instanceof FcnV) return K_FCN;
  if (v instanceof ModelValue) return K_MODEL;
  return K_OTHER;
}
const KIND_NAME = ['boolean', 'integer', 'string', 'model value', 'tuple', 'record', 'function', 'set', 'operator'];

function cmpFail(a: Value, b: Value): never {
  return err(`Attempted to compare the ${KIND_NAME[kindOf(a)]} ${fmt(a)} with the ${KIND_NAME[kindOf(b)]} ${fmt(b)}`);
}
function eqFail(a: Value, b: Value): never {
  return err(`Attempted to check equality of the ${KIND_NAME[kindOf(a)]} ${fmt(a)} with the ${KIND_NAME[kindOf(b)]} ${fmt(b)}`);
}

// Total order used for set normalization. Mirrors TLC's compareTo.
export function compare(a: Value, b: Value): number {
  if (typeof a === 'number') {
    if (typeof b === 'number') return a < b ? -1 : a > b ? 1 : 0;
    if (b instanceof ModelValue) return modelCmp(b, a) * -1;
    return cmpFail(a, b);
  }
  if (typeof a === 'string') {
    if (typeof b === 'string') return a === b ? 0 : strId(a) - strId(b);
    if (b instanceof ModelValue) return modelCmp(b, a) * -1;
    return cmpFail(a, b);
  }
  if (typeof a === 'boolean') {
    if (typeof b === 'boolean') return a === b ? 0 : a ? 1 : -1;
    if (b instanceof ModelValue) return modelCmp(b, a) * -1;
    return cmpFail(a, b);
  }
  if (a instanceof ModelValue) return modelCmp(a, b);
  if (b instanceof ModelValue) return modelCmp(b, a) * -1;
  if (a instanceof SetBase) {
    if (!(b instanceof SetBase)) return cmpFail(a, b);
    const x = a.elems(), y = b.elems();
    if (x.length !== y.length) return x.length - y.length;
    for (let i = 0; i < x.length; i++) {
      const c = compare(x[i], y[i]);
      if (c !== 0) return c;
    }
    return 0;
  }
  if (a instanceof TupleV) {
    if (b instanceof TupleV) {
      if (a.e.length !== b.e.length) return a.e.length - b.e.length;
      for (let i = 0; i < a.e.length; i++) {
        const c = compare(a.e[i], b.e[i]);
        if (c !== 0) return c;
      }
      return 0;
    }
    if (b instanceof RecordV || b instanceof FcnV) return fcnCmp(a, b);
    return cmpFail(a, b);
  }
  if (a instanceof RecordV) {
    if (b instanceof RecordV) {
      const n = a.names.length;
      if (n !== b.names.length) return n - b.names.length;
      for (let i = 0; i < n; i++) {
        if (a.names[i] !== b.names[i]) return strId(a.names[i]) - strId(b.names[i]);
      }
      for (let i = 0; i < n; i++) {
        const c = compare(a.vals[i], b.vals[i]);
        if (c !== 0) return c;
      }
      return 0;
    }
    if (b instanceof TupleV || b instanceof FcnV) return fcnCmp(a, b);
    return cmpFail(a, b);
  }
  if (a instanceof FcnV) {
    if (b instanceof FcnV || b instanceof TupleV || b instanceof RecordV) return fcnCmp(a, b);
    return cmpFail(a, b);
  }
  return cmpFail(a, b);
}

function modelCmp(m: ModelValue, o: Value): number {
  if (o instanceof ModelValue) return m.id - o.id;
  if (m.type !== null) return err(`Attempted to compare the typed model value ${m.name} with the non-model value\n${fmt(o)}`);
  return -1; // an untyped model value is smaller than every non-model value
}

function fcnCmp(a: Value, b: Value): number {
  const da = domainElems(a), db = domainElems(b);
  if (da.length !== db.length) return da.length - db.length;
  const va = fcnValues(a), vb = fcnValues(b);
  for (let i = 0; i < da.length; i++) {
    const c = compare(da[i], db[i]);
    if (c !== 0) return c;
  }
  for (let i = 0; i < da.length; i++) {
    const c = compare(va[i], vb[i]);
    if (c !== 0) return c;
  }
  return 0;
}

export function valEq(a: Value, b: Value): boolean {
  if (a === b) return true;
  const ta = typeof a, tb = typeof b;
  if (ta !== 'object') {
    if (tb !== 'object') {
      if (ta !== tb) return eqFail(a, b);
      return false;
    }
    if (b instanceof ModelValue) return modelEq(b, a);
    return eqFail(a, b);
  }
  if (tb !== 'object') {
    if (a instanceof ModelValue) return modelEq(a, b);
    return eqFail(a, b);
  }
  if (a instanceof ModelValue) return modelEq(a, b);
  if (b instanceof ModelValue) return modelEq(b, a);
  if (a instanceof SetBase) {
    if (!(b instanceof SetBase)) return eqFail(a, b);
    return setEq(a, b);
  }
  if (a instanceof TupleV) {
    if (b instanceof TupleV) {
      if (a.e.length !== b.e.length) return false;
      for (let i = 0; i < a.e.length; i++) if (!valEq(a.e[i], b.e[i])) return false;
      return true;
    }
    if (b instanceof RecordV || b instanceof FcnV) return false; // canonical forms differ
    return eqFail(a, b);
  }
  if (a instanceof RecordV) {
    if (b instanceof RecordV) {
      const n = a.names.length;
      if (n !== b.names.length) return false;
      for (let i = 0; i < n; i++) if (a.names[i] !== b.names[i]) return false;
      for (let i = 0; i < n; i++) if (!valEq(a.vals[i], b.vals[i])) return false;
      return true;
    }
    if (b instanceof TupleV || b instanceof FcnV) return false;
    return eqFail(a, b);
  }
  if (a instanceof FcnV) {
    if (b instanceof FcnV) {
      const n = a.dom.length;
      if (n !== b.dom.length) return false;
      for (let i = 0; i < n; i++) if (!valEq(a.dom[i], b.dom[i])) return false;
      for (let i = 0; i < n; i++) if (!valEq(a.vals[i], b.vals[i])) return false;
      return true;
    }
    if (b instanceof TupleV || b instanceof RecordV) return false;
    return eqFail(a, b);
  }
  return eqFail(a, b);
}

function modelEq(m: ModelValue, o: Value): boolean {
  if (o instanceof ModelValue) {
    if (m === o) return true;
    if (m.type !== null && o.type !== null && m.type !== o.type) {
      return err(`Attempted to check equality of the differently-typed model values ${m.name} and ${o.name}`);
    }
    return false;
  }
  if (m.type !== null) return err(`Attempted to check equality of typed model value ${m.name} and non-model value\n${fmt(o)}`);
  return false;
}

export function setEq(a: SetBase, b: SetBase): boolean {
  if (a === b) return true;
  if (a instanceof IntervalV && b instanceof IntervalV) return a.size() === b.size() && (a.size() === 0 || a.lo === b.lo);
  if (!a.enumerable() || !b.enumerable()) {
    if (a instanceof InfSetV && b instanceof InfSetV) return a.kind === b.kind;
    if (a.enumerable() !== b.enumerable()) return false;
    return err('Attempted to check equality of two non-enumerable sets.');
  }
  const x = a.elems(), y = b.elems();
  if (x.length !== y.length) return false;
  for (let i = 0; i < x.length; i++) if (!valEq(x[i], y[i])) return false;
  return true;
}

export function bsearch(arr: Value[], v: Value): number {
  let lo = 0, hi = arr.length - 1;
  while (lo <= hi) {
    const mid = (lo + hi) >> 1;
    const c = compare(arr[mid], v);
    if (c === 0) return mid;
    if (c < 0) lo = mid + 1; else hi = mid - 1;
  }
  return -1;
}

export function sortDedup(a: Value[]): Value[] {
  if (a.length < 2) return a;
  let sorted = true;
  for (let i = 1; i < a.length; i++) {
    if (compare(a[i - 1], a[i]) >= 0) { sorted = false; break; }
  }
  if (sorted) return a;
  const s = a.slice().sort(compare);
  const out: Value[] = [s[0]];
  for (let i = 1; i < s.length; i++) if (compare(s[i - 1], s[i]) !== 0) out.push(s[i]);
  return out;
}
export function mkSet(elems: Value[]): SetV { return new SetV(sortDedup(elems)); }

// ---- functions ----
// Build a function from a sorted, deduplicated domain and parallel values, in canonical form.
export function makeFcn(dom: Value[], vals: Value[]): Value {
  const n = dom.length;
  if (n === 0) return EMPTY_TUPLE;
  const d0 = dom[0];
  if (typeof d0 === 'number') {
    if (d0 === 1) {
      let ok = true;
      for (let i = 1; i < n; i++) if (dom[i] !== i + 1) { ok = false; break; }
      if (ok) return new TupleV(vals);
    }
  } else if (typeof d0 === 'string') {
    let ok = true;
    for (let i = 1; i < n; i++) if (typeof dom[i] !== 'string') { ok = false; break; }
    if (ok) return new RecordV(dom as string[], vals);
  }
  return new FcnV(dom, vals);
}
// Build from unsorted pairs.
export function makeFcnFromPairs(pairs: [Value, Value][]): Value {
  pairs.sort((x, y) => compare(x[0], y[0]));
  const dom: Value[] = [], vals: Value[] = [];
  for (let i = 0; i < pairs.length; i++) {
    if (i > 0 && compare(pairs[i - 1][0], pairs[i][0]) === 0) continue;
    dom.push(pairs[i][0]);
    vals.push(pairs[i][1]);
  }
  return makeFcn(dom, vals);
}
export function makeRecord(names: string[], vals: Value[]): RecordV {
  const idx = names.map((_, i) => i).sort((i, j) => strId(names[i]) - strId(names[j]));
  return new RecordV(idx.map(i => names[i]), idx.map(i => vals[i]));
}
export function isFcn(v: Value): boolean { return v instanceof TupleV || v instanceof RecordV || v instanceof FcnV; }
export function domainElems(f: Value): Value[] {
  if (f instanceof TupleV) { const a: number[] = []; for (let i = 1; i <= f.e.length; i++) a.push(i); return a; }
  if (f instanceof RecordV) return f.names;
  if (f instanceof FcnV) return f.dom;
  return err(`Attempted to compute the domain of the non-function value:\n${fmt(f)}`);
}
export function domainOf(f: Value): SetBase | null {
  if (f instanceof TupleV) return new IntervalV(1, f.e.length);
  if (f instanceof RecordV) return new SetV(f.names);
  if (f instanceof FcnV) return new SetV(f.dom);
  return null;
}
export function fcnValues(f: Value): Value[] {
  if (f instanceof TupleV) return f.e;
  if (f instanceof RecordV || f instanceof FcnV) return f.vals;
  return err(`Attempted to apply a function operation to the non-function value:\n${fmt(f)}`);
}

// ---- hashing: two independent 32-bit murmur-style streams ----
export class Hasher {
  h1 = 0x9747b28c | 0;
  h2 = 0x3c6ef372 | 0;
  reset(): void { this.h1 = 0x9747b28c | 0; this.h2 = 0x3c6ef372 | 0; }
  add(x: number): void {
    let k = Math.imul(x, 0xcc9e2d51 | 0);
    k = (k << 15) | (k >>> 17);
    k = Math.imul(k, 0x1b873593);
    let h = this.h1 ^ k;
    h = (h << 13) | (h >>> 19);
    this.h1 = (Math.imul(h, 5) + (0xe6546b64 | 0)) | 0;
    k = Math.imul(x ^ 0x5bd1e995, 0x85ebca6b | 0);
    k = (k << 13) | (k >>> 19);
    k = Math.imul(k, 0xc2b2ae35 | 0);
    h = this.h2 ^ k;
    h = (h << 17) | (h >>> 15);
    this.h2 = (Math.imul(h, 5) + 0x52dce729) | 0;
  }
  value(v: Value): void {
    switch (typeof v) {
      case 'number': this.add(1); this.add(v | 0); if (v > 0x7fffffff || v < -0x80000000) this.add((v / 4294967296) | 0); return;
      case 'boolean': this.add(v ? 3 : 2); return;
      case 'string': this.add(4); this.add(strId(v)); return;
    }
    if (v instanceof TupleV) {
      this.add(5); this.add(v.e.length);
      for (let i = 0; i < v.e.length; i++) this.value(v.e[i]);
    } else if (v instanceof RecordV) {
      this.add(6); this.add(v.names.length);
      for (let i = 0; i < v.names.length; i++) { this.add(strId(v.names[i])); this.value(v.vals[i]); }
    } else if (v instanceof SetBase) {
      const e = v.elems();
      this.add(7); this.add(e.length);
      for (let i = 0; i < e.length; i++) this.value(e[i]);
    } else if (v instanceof FcnV) {
      this.add(8); this.add(v.dom.length);
      for (let i = 0; i < v.dom.length; i++) { this.value(v.dom[i]); this.value(v.vals[i]); }
    } else if (v instanceof ModelValue) {
      this.add(9); this.add(v.id);
    } else err('Attempted to fingerprint a non-value (operator or lazy function).');
  }
  finish(): void {
    let h = this.h1;
    h ^= h >>> 16; h = Math.imul(h, 0x85ebca6b | 0); h ^= h >>> 13; h = Math.imul(h, 0xc2b2ae35 | 0); h ^= h >>> 16;
    this.h1 = h;
    h = this.h2 ^ this.h1;
    h ^= h >>> 15; h = Math.imul(h, 0x2c1b3c6d); h ^= h >>> 12; h = Math.imul(h, 0x297a2d39); h ^= h >>> 15;
    this.h2 = h;
  }
}

// ---- printing (TLC format) ----
function fmtStr(s: string): string {
  let o = '"';
  for (const ch of s) {
    if (ch === '\\') o += '\\\\';
    else if (ch === '"') o += '\\"';
    else if (ch === '\n') o += '\\n';
    else if (ch === '\t') o += '\\t';
    else if (ch === '\r') o += '\\r';
    else if (ch === '\f') o += '\\f';
    else o += ch;
  }
  return o + '"';
}
const isIdent = (s: string) => /^[A-Za-z0-9_]*[A-Za-z][A-Za-z0-9_]*$/.test(s);

export function fmt(v: Value): string {
  switch (typeof v) {
    case 'number': return String(v);
    case 'boolean': return v ? 'TRUE' : 'FALSE';
    case 'string': return fmtStr(v);
    case 'undefined': return '<undefined>';
  }
  if (v instanceof ModelValue) return v.name;
  if (v instanceof TupleV) return '<<' + v.e.map(fmt).join(', ') + '>>';
  if (v instanceof RecordV) return '[' + v.names.map((n, i) => (isIdent(n) ? n : fmtStr(n)) + ' |-> ' + fmt(v.vals[i])).join(', ') + ']';
  if (v instanceof FcnV) return '(' + v.dom.map((d, i) => fmt(d) + ' :> ' + fmt(v.vals[i])).join(' @@ ') + ')';
  if (v instanceof IntervalV) return v.lo + '..' + v.hi;
  if (v instanceof SetV) return '{' + v.e.map(fmt).join(', ') + '}';
  if (v instanceof SubsetV) return 'SUBSET ' + fmt(v.base);
  if (v instanceof FcnSetV) return '[' + fmt(v.dom) + ' -> ' + fmt(v.rng) + ']';
  if (v instanceof RecSetV) return '[' + v.names.map((n, i) => n + ': ' + fmt(v.sets[i])).join(', ') + ']';
  if (v instanceof CrossV) return '(' + v.sets.map(fmt).join(' \\X ') + ')';
  if (v instanceof SeqSetV) return 'Seq(' + fmt(v.base) + ')';
  if (v instanceof InfSetV) return v.kind;
  if (v instanceof LazySetV) return v.desc;
  if (v instanceof DerivedSetV) return v.enumerable() ? '{' + v.elems().map(fmt).join(', ') + '}' : v.desc;
  if (v && typeof v.describe === 'function') return v.describe();
  return '<operator>';
}

export function isSet(v: Value): v is SetBase { return v instanceof SetBase; }
