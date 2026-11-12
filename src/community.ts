// Native overrides for operators of the bundled TLA+ community modules. The TLA+ definitions in the
// module sources remain the specification; these replace them for speed or because the TLA+
// definition is not executable (TLC ships the same operators as Java overrides, see
// CommunityModules/modules/tlc2/overrides/*.java; argument order and error wording follow those).
// Format: OVERRIDES[module][operator] = [fn(ev, args), { ops: indices of operator-valued args }].
//
// Host access (files, environment, processes) goes through `ev.hooks.io` only; nothing here imports
// a runtime module. Required shape:
//   { readFile(path): string; writeFile(path, data): void; appendFile(path, data): void;
//     exists(path): boolean; env: Record<string, string> }
// Optional extensions used when present:
//   readBytes(path): Uint8Array; writeBytes(path, data: Uint8Array): void   (IOSerialize/IODeserialize)
//   exec(command: string[], env?: Record<string, string>): { exitValue: number; stdout: string; stderr: string }
import type { Builtin } from './modules.ts';
import type { Evaluator } from './eval.ts';
import { Lazy, LazyFcn } from './eval.ts';
import { fail, int, seq, set } from './stdlib.ts';
import type { Fn } from './stdlib.ts';
import {
  SetBase, SetV, IntervalV, LazySetV, RecSetV, TupleV, RecordV, FcnV, ModelValue, EMPTY_TUPLE, EMPTY_SET,
  valEq, compare, mkSet, makeFcn, makeFcnFromPairs, makeRecord, isFcn, domainElems, fcnValues, fmt, strId, bsearch,
} from './values.ts';
import type { Value } from './values.ts';

export interface HostIO {
  readFile(path: string): string;
  writeFile(path: string, data: string): void;
  appendFile(path: string, data: string): void;
  exists(path: string): boolean;
  env: Record<string, string>;
  readBytes?(path: string): Uint8Array;
  writeBytes?(path: string, data: Uint8Array): void;
  exec?(command: string[], env?: Record<string, string>): { exitValue: number; stdout: string; stderr: string };
}

// ---- shared helpers ----
const ORD = ['first', 'second', 'third', 'fourth', 'fifth'];
// TLC's EC.TLC_MODULE_ARGUMENT_ERROR / TLC_MODULE_ONE_ARGUMENT_ERROR / TLC_MODULE_ARGUMENT_NOT_IN_DOMAIN.
const argErr = (i: number, op: string, what: string, v: Value): never =>
  fail(`The ${ORD[i]} argument of ${op} should be a ${what}, but instead it is:\n${fmt(v)}`);
const oneArgErr = (op: string, what: string, v: Value): never =>
  fail(`The argument of ${op} should be a ${what}, but instead it is:\n${fmt(v)}`);
const notInDomain = (i: number, op: string, s: Value, v: Value): never =>
  fail(`The ${ORD[i]} argument of ${op} must be in the domain of its first argument:\n${fmt(s)}\n, but instead it is\n${fmt(v)}`);

const isInt = (v: Value): v is number => typeof v === 'number' && Number.isInteger(v);
const int32 = (n: number, what: string): number => (n > 2147483647 || n < -2147483648 ? fail(`Overflow when computing ${what}`) : n);
const str = (v: Value, op: string, i: number): string =>
  typeof v === 'string' ? v : argErr(i, op, 'string', v);
const bool = (v: Value, i: number, op: string, what: string, test: Value): boolean =>
  typeof v === 'boolean' ? v : argErr(i, op, what, test);
const key = (v: Value): string => fmt(v); // canonical values print identically iff they are equal
const tupleOf = (elems: Value[]): TupleV => (elems.length ? new TupleV(elems) : EMPTY_TUPLE);

function io(ev: Evaluator): HostIO {
  const h = ev.hooks.io as HostIO | undefined;
  return h ?? fail('File IO is not available in this environment (the host did not provide ev.hooks.io).');
}
function readText(ev: Evaluator, path: string): string {
  const h = io(ev);
  if (!h.exists(path)) fail(`${path} (No such file or directory)`);
  try { return h.readFile(path); } catch (e) { return fail(`${path} (${(e as Error).message})`); }
}
function hostWrite(f: () => void, path: string): void {
  try { f(); } catch (e) { fail(`${path} (${(e as Error).message})`); }
}

// A function value implemented natively (used for zero-arity definitions such as Combinatorics!factorial).
class NativeFcn extends LazyFcn {
  fn: (arg: Value) => Value;
  name: string;
  constructor(ev: Evaluator, name: string, fn: (arg: Value) => Value) {
    super({} as any, null, ev);
    this.fn = fn;
    this.name = name;
  }
  describe(): string { return `<function ${this.name}>`; }
  apply(arg: Value): Value { return this.fn(arg); }
  domain(): SetBase { return fail(`Attempted to enumerate the domain of the natively implemented function ${this.name}.`); }
  force(): Value { return fail(`Attempted to enumerate the natively implemented function ${this.name}.`); }
}

// ---- folds ----
function foldFunctionOnSet(ev: Evaluator, op: Value, base: Value, fun: Value, indices: Value): Value {
  if (!isFcn(fun) && !(fun instanceof LazyFcn)) argErr(2, 'FoldFunctionOnSet', 'function', fun);
  if (!(indices instanceof SetBase)) argErr(3, 'FoldFunctionOnSet', 'set', indices);
  let acc = base;
  for (const d of (indices as SetBase).elems()) acc = ev.applyOp(op, [ev.applyFcn(fun, d), acc]);
  return acc;
}
function foldFunction(ev: Evaluator, op: Value, base: Value, fun: Value): Value {
  if (!isFcn(fun)) argErr(2, 'FoldFunction', 'function', fun);
  let acc = base;
  for (const x of fcnValues(fun)) acc = ev.applyOp(op, [x, acc]); // values are stored in domain order
  return acc;
}

// ---- sequences ----
function subSeqIndex(s: Value[], t: Value[], from: number): number {
  for (let i = from; i + s.length <= t.length; i++) {
    let ok = true;
    for (let j = 0; j < s.length; j++) if (!valEq(t[i + j], s[j])) { ok = false; break; }
    if (ok) return i;
  }
  return -1;
}
function selectIn(ev: Evaluator, a: Value[], opName: string, last: boolean, sub: boolean): number {
  const s = a[0] instanceof TupleV ? a[0].e : argErr(0, opName, 'sequence', a[0]);
  const test = a[sub ? 3 : 1];
  let from = 1, to = s.length;
  if (sub) {
    if (!isInt(a[1])) argErr(1, opName, 'natural', a[1]);
    if (!isInt(a[2])) argErr(2, opName, 'natural', a[2]);
    from = a[1]; to = a[2];
    if (from > to) return 0;
    if (from < 1 || from > s.length) notInDomain(1, opName, a[0], from);
    if (to < 1 || to > s.length) notInDomain(2, opName, a[0], to);
  }
  const what = last ? 'boolean-valued function' : 'boolean-valued operator';
  const pos = sub ? 3 : 2; // TLC reports "third" for the two-argument variants
  if (last) {
    for (let i = to; i >= from; i--) if (bool(ev.applyOp(test, [s[i - 1]]), pos, opName, what, test)) return i;
  } else {
    for (let i = from; i <= to; i++) if (bool(ev.applyOp(test, [s[i - 1]]), pos, opName, what, test)) return i;
  }
  return 0;
}
function permutations(s: Value[]): Value[] {
  const out: Value[] = [];
  const used = new Array<boolean>(s.length).fill(false);
  const cur: Value[] = [];
  const rec = () => {
    if (cur.length === s.length) { out.push(tupleOf(cur.slice())); return; }
    for (let i = 0; i < s.length; i++) {
      if (used[i]) continue;
      used[i] = true; cur.push(s[i]); rec(); cur.pop(); used[i] = false;
    }
  };
  rec();
  return out;
}

// ---- graphs (Graphs and UndirectedGraphs share AbstractGraphs.java) ----
type Endpoints = (edge: Value) => [Value, Value] | null;
const TUPLE_EDGE: Endpoints = e => (e instanceof TupleV && e.e.length === 2 ? [e.e[0], e.e[1]] : null);
const PAIR_EDGE: Endpoints = e => {
  if (!(e instanceof SetBase) || !e.enumerable()) return null;
  const x = e.elems();
  if (x.length === 0 || x.length > 2) return null;
  return [x[0], x.length === 2 ? x[1] : x[0]];
};
interface Graph { nodes: SetBase; edges: Value[] }
function toGraph(op: string, pos: number, kind: string, v: Value): Graph {
  if (!(v instanceof RecordV)) argErr(pos, op, `${kind} record with a node and an edge field`, v);
  const node = v.get('node'), edge = v.get('edge');
  if (!(node instanceof SetBase)) argErr(pos, op, `${kind} record whose node field is a set`, v);
  if (!(edge instanceof SetBase)) argErr(pos, op, `${kind} record whose edge field is a set`, v);
  node.elems();
  return { nodes: node, edges: edge.elems() };
}
type Mode = 'forward' | 'transpose' | 'symmetric';
function adjacency(g: Graph, parse: Endpoints, mode: Mode): Map<string, Value[]> {
  const adj = new Map<string, Value[]>();
  const add = (from: Value, to: Value) => {
    const k = key(from);
    const l = adj.get(k);
    if (l) l.push(to); else adj.set(k, [to]);
  };
  for (const e of g.edges) {
    const p = parse(e);
    if (!p) continue;
    let [from, to] = p;
    if (!g.nodes.contains(from) || !g.nodes.contains(to)) continue;
    if (mode === 'transpose') [from, to] = [to, from];
    add(from, to);
    if (mode === 'symmetric' && !valEq(from, to)) add(to, from);
  }
  return adj;
}
function reachable(source: Value, adj: Map<string, Value[]>): Set<string> {
  const visited = new Set<string>([key(source)]);
  const frontier = [source];
  for (let i = 0; i < frontier.length; i++) {
    for (const succ of adj.get(key(frontier[i])) ?? []) {
      const k = key(succ);
      if (!visited.has(k)) { visited.add(k); frontier.push(succ); }
    }
  }
  return visited;
}
function simplePath(kind: string, parse: Endpoints, mode: Mode, graph: Value): Value {
  const g = toGraph('SimplePath', 0, kind, graph);
  const adj = adjacency(g, parse, mode);
  const paths: Value[] = [];
  const path: Value[] = [];
  const visited = new Set<string>();
  const extend = (cur: Value) => {
    paths.push(new TupleV(path.slice()));
    for (const succ of adj.get(key(cur)) ?? []) {
      const k = key(succ);
      if (visited.has(k)) continue;
      visited.add(k); path.push(succ);
      extend(succ);
      path.pop(); visited.delete(k);
    }
  };
  for (const start of g.nodes.elems()) {
    path.push(start); visited.add(key(start));
    extend(start);
    visited.delete(key(start)); path.pop();
  }
  return mkSet(paths);
}
function areConnectedIn(kind: string, parse: Endpoints, mode: Mode, m: Value, n: Value, graph: Value): boolean {
  const g = toGraph('AreConnectedIn', 2, kind, graph);
  if (!g.nodes.contains(m) || !g.nodes.contains(n)) return false;
  if (valEq(m, n)) return true;
  return reachable(m, adjacency(g, parse, mode)).has(key(n));
}

// ---- JSON (Json.java, which uses Gson) ----
function jsonStr(s: string): string {
  let o = '"';
  for (let i = 0; i < s.length; i++) {
    const c = s.charCodeAt(i);
    if (c === 0x22) o += '\\"';
    else if (c === 0x5c) o += '\\\\';
    else if (c === 0x09) o += '\\t';
    else if (c === 0x08) o += '\\b';
    else if (c === 0x0a) o += '\\n';
    else if (c === 0x0d) o += '\\r';
    else if (c === 0x0c) o += '\\f';
    else if (c < 0x20 || c === 0x2028 || c === 0x2029) o += '\\u' + c.toString(16).padStart(4, '0');
    else o += s[i];
  }
  return o + '"';
}
const jsonUnsupported = (v: Value): never => fail(`Cannot convert value: unsupported value type (${fmt(v)})`);
const jsonArr = (xs: Value[]): string => '[' + xs.map(jsonNode).join(',') + ']';
function jsonObj(keys: Value[], vals: Value[]): string {
  const m = new Map<string, string>(); // Gson's JsonObject: a repeated key keeps its position, the last value wins
  for (let i = 0; i < keys.length; i++) m.set(typeof keys[i] === 'string' ? keys[i] : fmt(keys[i]), jsonNode(vals[i]));
  return '{' + [...m].map(([k, v]) => jsonStr(k) + ':' + v).join(',') + '}';
}
function jsonNode(v: Value): string {
  switch (typeof v) {
    case 'string': return jsonStr(v);
    case 'number': return String(v);
    case 'boolean': return v ? 'true' : 'false';
  }
  if (v instanceof TupleV) return jsonArr(v.e);
  if (v instanceof RecordV) return jsonObj(v.names, v.vals);
  if (v instanceof FcnV) return jsonObj(v.dom, v.vals);
  if (v instanceof ModelValue) return jsonStr(v.name);
  if (v instanceof LazyFcn) return jsonNode(v.force());
  if (v instanceof SetBase && v.enumerable()) return jsonArr(v.elems());
  return jsonUnsupported(v);
}
function jsonArrayNode(v: Value): string {
  if (v instanceof LazyFcn) v = v.force();
  if (v instanceof TupleV || v instanceof RecordV || v instanceof FcnV || (v instanceof SetBase && v.enumerable())) return jsonNode(v);
  return jsonUnsupported(v);
}
function jsonObjectNode(v: Value): string {
  if (v instanceof LazyFcn) v = v.force();
  // TLC prints a tuple *literal* as {"0":..,"1":..} here but a function with domain 1..n as an array; the two are
  // the same value (and indistinguishable for us), so the array form is used for every non-empty sequence.
  if (v instanceof TupleV) return v.e.length === 0 ? '{}' : jsonArr(v.e);
  if (v instanceof RecordV || v instanceof FcnV) return jsonNode(v);
  return jsonUnsupported(v);
}

// A JSON reader that keeps object members in document order and interns strings in the order Gson + Json.java
// create them (member name, then its value), because TLC orders strings by first use.
class JsonReader {
  s: string;
  i = 0;
  constructor(s: string) { this.s = s; }
  err(msg: string): never { return fail(`Malformed JSON: ${msg} at offset ${this.i}`); }
  ws(): void { while (this.i < this.s.length && ' \t\n\r﻿'.includes(this.s[this.i])) this.i++; }
  document(): Value {
    const v = this.value();
    this.ws();
    if (this.i < this.s.length) this.err('unexpected trailing characters');
    return v;
  }
  value(): Value {
    this.ws();
    const c = this.s[this.i];
    if (c === undefined) return this.err('unexpected end of input');
    if (c === '[') {
      this.i++;
      const out: Value[] = [];
      this.ws();
      if (this.s[this.i] === ']') { this.i++; return EMPTY_TUPLE; }
      for (;;) {
        out.push(this.value());
        this.ws();
        const d = this.s[this.i++];
        if (d === ']') return new TupleV(out);
        if (d !== ',') this.err("expected ',' or ']'");
      }
    }
    if (c === '{') {
      this.i++;
      const m = new Map<string, Value>();
      this.ws();
      if (this.s[this.i] === '}') { this.i++; return EMPTY_TUPLE; }
      for (;;) {
        this.ws();
        if (this.s[this.i] !== '"') this.err('expected a member name');
        const name = this.string();
        this.ws();
        if (this.s[this.i++] !== ':') this.err("expected ':'");
        strId(name);
        m.set(name, this.value());
        this.ws();
        const d = this.s[this.i++];
        if (d === '}') return makeRecord([...m.keys()], [...m.values()]);
        if (d !== ',') this.err("expected ',' or '}'");
      }
    }
    if (c === '"') { const v = this.string(); strId(v); return v; }
    const rest = this.s.slice(this.i);
    const kw = /^(true|false|null)(?![A-Za-z0-9_])/.exec(rest);
    if (kw) {
      this.i += kw[0].length;
      if (kw[0] === 'null') fail('Cannot convert value: unsupported JSON value null');
      return kw[0] === 'true';
    }
    const num = /^-?(0|[1-9]\d*)(\.\d+)?([eE][+-]?\d+)?/.exec(rest);
    if (!num) return this.err(`unexpected character '${c}'`);
    this.i += num[0].length;
    // Gson's getAsInt(): integers wrap to 32 bits, fractions are truncated.
    if (!num[2] && !num[3]) return Number(BigInt.asIntN(32, BigInt(num[0])));
    const x = Math.trunc(Number(num[0]));
    return Number.isFinite(x) ? Number(BigInt.asIntN(32, BigInt(x))) : 0;
  }
  string(): string {
    let o = '';
    this.i++;
    for (;;) {
      const c = this.s[this.i++];
      if (c === undefined) return this.err('unterminated string');
      if (c === '"') return o;
      if (c !== '\\') { o += c; continue; }
      const e = this.s[this.i++];
      switch (e) {
        case 'n': o += '\n'; break;
        case 't': o += '\t'; break;
        case 'r': o += '\r'; break;
        case 'b': o += '\b'; break;
        case 'f': o += '\f'; break;
        case 'u': {
          const h = this.s.slice(this.i, this.i + 4);
          if (!/^[0-9a-fA-F]{4}$/.test(h)) this.err('bad \\u escape');
          o += String.fromCharCode(parseInt(h, 16));
          this.i += 4;
          break;
        }
        case '"': case '\\': case '/': case "'": o += e; break;
        default: this.err('bad escape sequence');
      }
    }
  }
}
const splitLines = (text: string): string[] => {
  const lines = text.split(/\r\n|\n|\r/);
  if (lines.length && lines[lines.length - 1] === '') lines.pop();
  return lines;
};

// java.lang.String.format for the conversions that make sense with string arguments.
function javaFormat(template: string, params: string[]): string {
  let next = 0;
  return template.replace(/%(\d+\$)?([-#+ 0,(<]*)(\d+)?(\.\d+)?([a-zA-Z%])/g, (all, idx, flags, width, prec, conv) => {
    if (conv === 'n') return '\n';
    if (conv === '%') return '%';
    if (conv !== 's' && conv !== 'S') return fail(`Unsupported format conversion ${all} (only %s, %n and %% are supported).`);
    const k = idx ? parseInt(idx, 10) - 1 : flags.includes('<') ? next - 1 : next++;
    if (k < 0 || k >= params.length) return fail(`Format specifier '${all}' has no matching argument.`);
    let v = params[k];
    if (prec) v = v.slice(0, parseInt(prec.slice(1), 10));
    if (conv === 'S') v = v.toUpperCase();
    if (width) v = flags.includes('-') ? v.padEnd(parseInt(width, 10)) : v.padStart(parseInt(width, 10));
    return v;
  });
}

// ---- TLC's binary value format (tlc2.value.ValueOutputStream / ValueInputStream), uncompressed ----
const K_BOOL = 0, K_INT = 1, K_STRING = 3, K_RECORD = 4, K_SETENUM = 5, K_TUPLE = 7, K_FCNRCD = 9, K_MODEL = 21, K_INTERVAL = 23, K_DUMMY = 26;
function encodeValue(v: Value): Uint8Array {
  const out: number[] = [];
  const i32 = (x: number) => { out.push((x >>> 24) & 255, (x >>> 16) & 255, (x >>> 8) & 255, x & 255); };
  const nat = (x: number) => { if (x > 0x7fff) i32(-x); else out.push((x >>> 8) & 255, x & 255); };
  const ustr = (s: string) => {
    out.push(K_STRING);
    i32(0); i32(-1); i32(s.length);
    for (let i = 0; i < s.length; i++) out.push(s.charCodeAt(i) & 255);
  };
  const w = (x: Value): void => {
    if (typeof x === 'boolean') out.push(K_BOOL, x ? 1 : 0);
    else if (typeof x === 'number') { out.push(K_INT); i32(x); }
    else if (typeof x === 'string') ustr(x);
    else if (x instanceof TupleV) { out.push(K_TUPLE); nat(x.e.length); x.e.forEach(w); }
    else if (x instanceof RecordV) {
      // written as "not normalized" (negative length): TLC's field order depends on its own string table
      out.push(K_RECORD); i32(-x.names.length);
      x.names.forEach((n, i) => { ustr(n); w(x.vals[i]); });
    } else if (x instanceof FcnV) {
      out.push(K_FCNRCD); nat(x.dom.length); out.push(2);
      x.dom.forEach((d, i) => { w(d); w(x.vals[i]); });
    } else if (x instanceof IntervalV) { out.push(K_INTERVAL); i32(x.lo); i32(x.hi); }
    else if (x instanceof SetBase && x.enumerable()) { const e = x.elems(); out.push(K_SETENUM); i32(-e.length); e.forEach(w); }
    else if (x instanceof LazyFcn) w(x.force());
    else fail(`IOSerialize cannot serialize the value:\n${fmt(x)}`);
  };
  w(v);
  return Uint8Array.from(out);
}
function decodeValue(b: Uint8Array): Value {
  let p = 0;
  const handles: Value[] = [];
  const need = (n: number) => { if (p + n > b.length) fail('IODeserialize: unexpected end of file.'); };
  const u8 = () => { need(1); return b[p++]; };
  const i16 = () => { need(2); const x = (b[p] << 8) | b[p + 1]; p += 2; return (x << 16) >> 16; };
  const i32 = () => { need(4); const x = (b[p] << 24) | (b[p + 1] << 16) | (b[p + 2] << 8) | b[p + 3]; p += 4; return x; };
  const nat = () => { const r = i16(); return r >= 0 ? r : -((r << 16) | (i16() & 0xffff)); };
  const ustr = (): string => {
    i32(); i32();
    const n = i32();
    need(n);
    let s = '';
    for (let i = 0; i < n; i++) s += String.fromCharCode(b[p++]);
    strId(s);
    return s;
  };
  const r = (): Value => {
    const kind = u8();
    switch (kind) {
      case K_BOOL: return u8() !== 0;
      case K_INT: return i32();
      case K_STRING: { const s = ustr(); handles.push(s); return s; }
      case K_INTERVAL: { const lo = i32(), hi = i32(); return new IntervalV(lo, hi); }
      case K_DUMMY: {
        const idx = nat();
        if (idx >= handles.length || handles[idx] === undefined) fail('IODeserialize: dangling back reference.');
        return handles[idx];
      }
      case K_MODEL: return fail('IODeserialize: model values cannot be deserialized.');
      case K_TUPLE: {
        const h = handles.push(undefined) - 1;
        const n = nat(), e: Value[] = [];
        for (let i = 0; i < n; i++) e.push(r());
        return (handles[h] = tupleOf(e));
      }
      case K_SETENUM: {
        const h = handles.push(undefined) - 1;
        const n = Math.abs(i32()), e: Value[] = [];
        for (let i = 0; i < n; i++) e.push(r());
        return (handles[h] = mkSet(e));
      }
      case K_RECORD: {
        const h = handles.push(undefined) - 1;
        const n = Math.abs(i32());
        const pairs: [Value, Value][] = [];
        for (let i = 0; i < n; i++) {
          let name: Value;
          if (u8() === K_DUMMY) name = handles[nat()];
          else { name = ustr(); handles.push(name); }
          pairs.push([name, r()]);
        }
        return (handles[h] = makeFcnFromPairs(pairs));
      }
      case K_FCNRCD: {
        const h = handles.push(undefined) - 1;
        const n = nat(), info = u8();
        const pairs: [Value, Value][] = [];
        if (info === 0) {
          const lo = i32(); i32();
          for (let i = 0; i < n; i++) pairs.push([lo + i, r()]);
        } else {
          for (let i = 0; i < n; i++) { const d = r(); pairs.push([d, r()]); }
        }
        return (handles[h] = makeFcnFromPairs(pairs));
      }
      default: return fail(`ValueInputStream: Can not unpickle a value of kind ${kind}`);
    }
  };
  return r();
}

// ---- statistics: chi-square goodness of fit (Apache Commons Math ChiSquareTest) ----
function logGamma(x: number): number {
  const c = [76.18009172947146, -86.50532032941677, 24.01409824083091, -1.231739572450155, 0.1208650973866179e-2, -0.5395239384953e-5];
  let y = x, tmp = x + 5.5;
  tmp -= (x + 0.5) * Math.log(tmp);
  let ser = 1.000000000190015;
  for (const cj of c) ser += cj / ++y;
  return -tmp + Math.log(2.5066282746310005 * ser / x);
}
function regularizedGammaP(a: number, x: number): number {
  if (x <= 0) return 0;
  if (x < a + 1) {
    let sum = 1 / a, del = sum, ap = a;
    for (let n = 0; n < 10000; n++) {
      ap += 1; del *= x / ap; sum += del;
      if (Math.abs(del) < Math.abs(sum) * 1e-15) break;
    }
    return sum * Math.exp(-x + a * Math.log(x) - logGamma(a));
  }
  const tiny = 1e-300;
  let bb = x + 1 - a, c = 1 / tiny, d = 1 / bb, h = d;
  for (let i = 1; i < 10000; i++) {
    const an = -i * (i - a);
    bb += 2;
    d = an * d + bb; if (Math.abs(d) < tiny) d = tiny;
    c = bb + an / c; if (Math.abs(c) < tiny) c = tiny;
    d = 1 / d;
    const del = d * c;
    h *= del;
    if (Math.abs(del - 1) < 1e-15) break;
  }
  return 1 - Math.exp(-x + a * Math.log(x) - logGamma(a)) * h;
}

const EXEC_NAMES = ['exitValue', 'stdout', 'stderr'];
const execResult = (exitValue: number, stdout: string, stderr: string): Value => makeRecord(EXEC_NAMES.slice(), [exitValue, stdout, stderr]);
function runProcess(ev: Evaluator, op: string, command: string[], env?: Record<string, string>): Value {
  const h = io(ev);
  if (!h.exec) fail(`${op} is not supported: this host cannot spawn external processes.`);
  const r = h.exec!(command, env);
  return execResult(r.exitValue, r.stdout, r.stderr);
}
const cmdStrings = (v: Value, op: string): string[] => {
  if (!(v instanceof TupleV)) oneArgErr(op, 'sequence', v);
  return (v as TupleV).e.map(x => (typeof x === 'string' ? x : oneArgErr('IOExec', 'sequence', x)));
};
const envRecord = (v: Value, op: string): Record<string, string> => {
  if (!(v instanceof RecordV)) oneArgErr(op, 'record', v);
  const out: Record<string, string> = {};
  (v as RecordV).names.forEach((n, i) => { const x = (v as RecordV).vals[i]; out[n] = typeof x === 'string' ? x : fmt(x); });
  return out;
};

const NO_CHOICE = 'Attempted to compute the value of an expression of form\nCHOOSE x \\in S: P, but no element of S satisfied P.';

export const OVERRIDES: Record<string, Record<string, [Fn, Partial<Builtin>?]>> = {
  FiniteSetsExt: {
    // FoldSet(op, base, set): op(element, accumulator), elements in normalized order.
    FoldSet: [(ev, a) => {
      let acc = a[1];
      for (const x of set(a[2], 'FoldSet', 2).elems()) acc = ev.applyOp(a[0], [x, acc]);
      return acc;
    }, { ops: [0] }],
    Quantify: [(ev, a) => {
      if (!(a[0] instanceof SetBase)) argErr(0, 'Quantify', 'set', a[0]);
      let n = 0;
      for (const x of a[0].elems()) if (bool(ev.applyOp(a[1], [x]), 1, 'Quantify', 'boolean-valued operator', a[1])) n++;
      return n;
    }, { ops: [1] }],
    SumSet: [(_, a) => set(a[0], 'SumSet', 0).elems().reduce((x: number, y) => int32(x + int(y, '+', 0), `${y} + ${x}`), 0)],
    ProductSet: [(_, a) => set(a[0], 'ProductSet', 0).elems().reduce((x: number, y) => int32(x * int(y, '*', 0), `${y} * ${x}`), 1)],
    Max: [(_, a) => { const e = set(a[0], 'Max', 0).elems(); if (!e.length) fail(NO_CHOICE); return e.reduce((x, y) => (int(y, '>=', 0) > x ? y : x), int(e[0], '>=', 0)); }],
    Min: [(_, a) => { const e = set(a[0], 'Min', 0).elems(); if (!e.length) fail(NO_CHOICE); return e.reduce((x, y) => (int(y, '=<', 0) < x ? y : x), int(e[0], '=<', 0)); }],
    kSubset: [(_, a) => {
      if (!isInt(a[0])) argErr(0, 'kSubset', 'natural number', a[0]);
      if (!(a[1] instanceof SetBase)) argErr(1, 'kSubset', 'set', a[1]);
      const k: number = a[0], base: SetBase = a[1];
      if (k < 0) return EMPTY_SET;
      if (k === 0) return new SetV([EMPTY_SET]);
      if (!base.enumerable()) {
        return new LazySetV(`kSubset(${k}, ${fmt(base)})`, v => {
          if (!(v instanceof SetBase)) return fail(`Attempted to check if the non-set value:\n${fmt(v)}\nis in kSubset(${k}, ${fmt(base)})`);
          if (!v.enumerable()) return false;
          const e = v.elems();
          return e.length === k && e.every(x => base.contains(x));
        });
      }
      const b = base.elems();
      if (k > b.length) return EMPTY_SET;
      const out: Value[] = [];
      const idx: number[] = [];
      const rec = (start: number, left: number) => {
        if (left === 0) { out.push(new SetV(idx.map(i => b[i]))); return; }
        for (let i = start; i <= b.length - left; i++) { idx.push(i); rec(i + 1, left - 1); idx.pop(); }
      };
      rec(0, k);
      return new SetV(out); // same-size subsets enumerated lexicographically are in normalized order
    }],
  },
  Functions: {
    Range: [(_, a) => mkSet(fcnValues(a[0] instanceof LazyFcn ? a[0].force() : a[0]).slice())],
    // Lazy only because TLC also accepts a set-of-records expression such as [a: 1, b: 2] here (it never looks at
    // the fields as sets, only compares them); everything else is evaluated normally.
    IsInjective: [(ev, a) => {
      let vals: Value[];
      const t = a[0];
      if (t instanceof Lazy && t.e.k === 'recset') vals = (t.e.fields as { e: any }[]).map(f => ev.eval(f.e, t.ctx));
      else {
        const f0 = ev.unthunk(t);
        const f = f0 instanceof LazyFcn ? f0.force() : f0;
        if (f instanceof RecSetV) vals = f.sets;
        else if (isFcn(f)) vals = fcnValues(f);
        else return oneArgErr('IsInjective', 'function', f);
      }
      for (let i = 0; i < vals.length; i++) for (let j = i + 1; j < vals.length; j++) if (valEq(vals[i], vals[j])) return false;
      return true;
    }, { lazy: true }],
    // AntiFunction(f) == [t \in Range(f) |-> CHOOSE s \in DOMAIN f : f[s] = t]: the first s in domain order.
    AntiFunction: [(_, a) => {
      const f = a[0] instanceof LazyFcn ? a[0].force() : a[0];
      if (!isFcn(f)) oneArgErr('AntiFunction', 'functions', f);
      const dom = domainElems(f), vals = fcnValues(f);
      return makeFcnFromPairs(vals.map((v, i): [Value, Value] => [v, dom[i]])); // stable: the first of equal keys is kept
    }],
    // FoldFunction(op, base, fun): op(fun[x], accumulator), x in normalized domain order.
    FoldFunction: [(ev, a) => foldFunction(ev, a[0], a[1], a[2] instanceof LazyFcn ? a[2].force() : a[2]), { ops: [0] }],
    FoldFunctionOnSet: [(ev, a) => foldFunctionOnSet(ev, a[0], a[1], a[2], a[3]), { ops: [0] }],
  },
  Folds: {
    // MapThenFoldSet(op, base, f, choose, S) == iter[S] where iter[s] == op(f(x), iter[s \ {x}]) with x == choose(s):
    // the element chosen first is combined last. (No Java override exists; this follows the TLA+ definition.)
    MapThenFoldSet: [(ev, a) => {
      if (!(a[4] instanceof SetBase)) fail(`Attempted to check if the non-enumerable value\n${fmt(a[4])}\nis element of\nSUBSET ${fmt(a[4])}`);
      let rest: Value[] = a[4].elems();
      const picked: Value[] = [];
      while (rest.length > 0) {
        const x = ev.applyOp(a[3], [new SetV(rest)]);
        const i = bsearch(rest, x);
        if (i < 0) fail(`The choose operator of MapThenFoldSet returned\n${fmt(x)}\nwhich is not an element of the set it was applied to.`);
        picked.push(rest[i]);
        rest = rest.slice(0, i).concat(rest.slice(i + 1));
      }
      let acc = a[1];
      for (let i = picked.length - 1; i >= 0; i--) acc = ev.applyOp(a[0], [ev.applyOp(a[2], [picked[i]]), acc]);
      return acc;
    }, { ops: [0, 2, 3] }],
  },
  BagsExt: {
    // FoldBag(op, base, bag): op(accumulator, element), once per copy, elements in normalized domain order.
    FoldBag: [(ev, a) => {
      const bag = a[2] instanceof LazyFcn ? a[2].force() : a[2];
      if (!isFcn(bag)) argErr(2, 'FoldBag', 'bag', bag);
      const dom = domainElems(bag), vals = fcnValues(bag);
      let acc = a[1];
      for (let i = 0; i < dom.length; i++) {
        const n = vals[i];
        if (!isInt(n) || n <= 0) {
          fail(`Applying FoldBag to the following value,\nwhich is not an element of Nat:\n${fmt(n)} (in: ${fmt(dom[i])}:>${fmt(n)})`);
        }
        for (let j = 0; j < n; j++) acc = ev.applyOp(a[0], [acc, dom[i]]);
      }
      return acc;
    }, { ops: [0] }],
  },
  SequencesExt: {
    // FoldSeq(op, base, seq) == FoldFunction(op, base, seq): op(element, accumulator), left to right.
    FoldSeq: [(ev, a) => foldFunction(ev, a[0], a[1], a[2]), { ops: [0] }],
    // FoldLeft(op, base, seq): op(accumulator, element), left to right.
    FoldLeft: [(ev, a) => {
      if (!(a[2] instanceof TupleV)) argErr(2, 'FoldLeft', 'sequence', a[2]);
      let acc = a[1];
      for (const x of a[2].e) acc = ev.applyOp(a[0], [acc, x]);
      return acc;
    }, { ops: [0] }],
    // FoldRight(op, seq, base): op(element, accumulator), right to left.
    FoldRight: [(ev, a) => {
      if (!(a[1] instanceof TupleV)) argErr(1, 'FoldRight', 'sequence', a[1]);
      let acc = a[2];
      const s = a[1].e;
      for (let i = s.length - 1; i >= 0; i--) acc = ev.applyOp(a[0], [s[i], acc]);
      return acc;
    }, { ops: [0] }],
    FoldLeftDomain: [(ev, a) => {
      if (!(a[2] instanceof TupleV)) argErr(2, 'FoldLeftDomain', 'sequence', a[2]);
      let acc = a[1];
      for (let i = 1; i <= a[2].e.length; i++) acc = ev.applyOp(a[0], [acc, i]);
      return acc;
    }, { ops: [0] }],
    FoldRightDomain: [(ev, a) => {
      if (!(a[1] instanceof TupleV)) argErr(1, 'FoldRightDomain', 'sequence', a[1]);
      let acc = a[2];
      for (let i = a[1].e.length; i >= 1; i--) acc = ev.applyOp(a[0], [i, acc]);
      return acc;
    }, { ops: [0] }],
    ToSet: [(_, a) => mkSet(fcnValues(a[0] instanceof LazyFcn ? a[0].force() : a[0]).slice())],
    Reverse: [(_, a) => tupleOf(seq(a[0], 'Reverse', 0).slice().reverse())],
    Cons: [(_, a) => new TupleV([a[0], ...seq(a[1], 'Cons', 1)])],
    Front: [(_, a) => (typeof a[0] === 'string' ? a[0].slice(0, -1) : tupleOf(seq(a[0], 'Front', 0).slice(0, -1)))],
    Last: [(ev, a) => { const s = seq(a[0], 'Last', 0); return s.length ? s[s.length - 1] : ev.applyFcn(a[0], 0); }],
    IsSuffix: [(_, a) => { const s = seq(a[0], 'IsSuffix', 0), t = seq(a[1], 'IsSuffix', 1); const o = t.length - s.length; return o >= 0 && s.every((x, i) => valEq(x, t[o + i])); }],
    Contains: [(_, a) => {
      if (!(a[0] instanceof TupleV)) oneArgErr('Contains', 'sequence', a[0]);
      for (const x of a[0].e) if (valEq(x, a[1])) return true;
      return false;
    }],
    IsPrefix: [(_, a) => {
      if (typeof a[0] === 'string' && typeof a[1] === 'string') return a[1].startsWith(a[0]);
      const s = seq(a[0], 'IsPrefix', 0), t = seq(a[1], 'IsPrefix', 1);
      if (s.length > t.length) return false;
      for (let i = 0; i < s.length; i++) if (!valEq(s[i], t[i])) return false;
      return true;
    }],
    SetToSeq: [(_, a) => tupleOf(set(a[0], 'SetToSeq', 0).elems().slice())],
    SetToSeqs: [(_, a) => {
      if (!(a[0] instanceof SetBase) || !a[0].enumerable()) fail(`Applying SetToSeqs to the following value,\nwhich is not a finite set:\n${fmt(a[0])}`);
      return mkSet(permutations(a[0].elems()));
    }],
    LongestCommonPrefix: [(_, a) => {
      if (!(a[0] instanceof SetBase)) oneArgErr('LongestCommonPrefix', 'non-empty set', a[0]);
      const e: Value[] = a[0].elems();
      if (e.length === 0) oneArgErr('LongestCommonPrefix', 'non-empty set', a[0]);
      if (typeof e[0] === 'string') {
        let prefix: string = e[0];
        for (const o of e) {
          if (typeof o !== 'string') oneArgErr('LongestCommonPrefix', 'sequence', a[0]);
          let n = 0;
          while (n < prefix.length && n < o.length && prefix[n] === o[n]) n++;
          prefix = prefix.slice(0, n);
        }
        return prefix;
      }
      if (!(e[0] instanceof TupleV)) oneArgErr('LongestCommonPrefix', 'sequence', a[0]);
      const first: Value[] = e[0].e;
      let upper = first.length;
      for (const o of e) {
        if (!(o instanceof TupleV)) oneArgErr('LongestCommonPrefix', 'sequence', a[0]);
        let n = 0;
        while (n < upper && n < o.e.length && valEq(first[n], o.e[n])) n++;
        upper = n;
      }
      return tupleOf(first.slice(0, upper));
    }],
    SelectInSeq: [(ev, a) => selectIn(ev, a, 'SelectInSeq', false, false), { ops: [1] }],
    SelectInSubSeq: [(ev, a) => selectIn(ev, a, 'SelectInSubSeq', false, true), { ops: [3] }],
    SelectLastInSeq: [(ev, a) => selectIn(ev, a, 'SelectLastInSeq', true, false), { ops: [1] }],
    SelectLastInSubSeq: [(ev, a) => selectIn(ev, a, 'SelectLastInSubSeq', true, true), { ops: [3] }],
    RemoveFirst: [(_, a) => {
      if (!(a[0] instanceof TupleV)) argErr(0, 'RemoveFirst', 'sequence', a[0]);
      const s: Value[] = a[0].e;
      const i = s.findIndex(x => valEq(x, a[1]));
      return i < 0 ? a[0] : tupleOf(s.slice(0, i).concat(s.slice(i + 1)));
    }],
    RemoveFirstMatch: [(ev, a) => {
      if (!(a[0] instanceof TupleV)) argErr(0, 'RemoveFirstMatch', 'sequence', a[0]);
      const s: Value[] = a[0].e;
      const i = s.findIndex(x => bool(ev.applyOp(a[1], [x]), 1, 'RemoveFirstMatch', 'boolean-valued function', a[1]));
      return i < 0 ? a[0] : tupleOf(s.slice(0, i).concat(s.slice(i + 1)));
    }, { ops: [1] }],
    Suffixes: [(_, a) => {
      if (!(a[0] instanceof TupleV)) oneArgErr('Suffixes', 'sequence', a[0]);
      const s: Value[] = a[0].e;
      const out: Value[] = [EMPTY_TUPLE];
      for (let i = s.length - 1; i >= 0; i--) out.push(new TupleV(s.slice(i)));
      return mkSet(out);
    }],
    AllSubSeqs: [(_, a) => {
      if (!(a[0] instanceof TupleV)) oneArgErr('AllSubSeqs', 'sequence', a[0]);
      const s: Value[] = a[0].e;
      if (s.length > 26) fail(`Attempted to enumerate AllSubSeqs of a sequence with ${s.length} elements; this is too large.`);
      const out: Value[] = [];
      for (let m = 0; m < 2 ** s.length; m++) out.push(tupleOf(s.filter((_x, j) => (m & (1 << j)) !== 0)));
      return mkSet(out);
    }],
    // ReplaceFirstSubSeq(r, s, t): replace the first occurrence of the subsequence s in t by r. TLC overrides the
    // string case only; the sequence case is the same computation as the TLA+ definition.
    ReplaceFirstSubSeq: [(_, a) => {
      const [r, s, t] = a;
      if (typeof r === 'string' && typeof s === 'string' && typeof t === 'string') {
        const i = t.indexOf(s);
        return s === '' ? r + t : i < 0 ? t : t.slice(0, i) + r + t.slice(i + s.length);
      }
      const rs = seq(r, 'ReplaceFirstSubSeq', 0), ss = seq(s, 'ReplaceFirstSubSeq', 1), ts = seq(t, 'ReplaceFirstSubSeq', 2);
      const i = subSeqIndex(ss, ts, 0);
      return i < 0 ? t : tupleOf(ts.slice(0, i).concat(rs, ts.slice(i + ss.length)));
    }],
    // ReplaceAllSubSeqs(r, s, t): replace all (non-overlapping, leftmost first) occurrences of s in t by r.
    ReplaceAllSubSeqs: [(_, a) => {
      const [r, s, t] = a;
      if (typeof r === 'string' && typeof s === 'string' && typeof t === 'string') {
        if (s === '') return r + t.split('').join(r);
        return t.split(s).join(r);
      }
      const rs = seq(r, 'ReplaceAllSubSeqs', 0), ss = seq(s, 'ReplaceAllSubSeqs', 1), ts = seq(t, 'ReplaceAllSubSeqs', 2);
      if (valEq(s, t)) return r;
      if (valEq(r, s)) return t;
      const out: Value[] = [];
      if (ss.length === 0) {
        for (const x of ts) { out.push(...rs); out.push(x); }
        return tupleOf(out);
      }
      let i = 0, hit = false;
      while (i < ts.length) {
        if (subSeqIndex(ss, ts, i) === i) { out.push(...rs); i += ss.length; hit = true; } else out.push(ts[i++]);
      }
      return hit ? tupleOf(out) : t;
    }],
  },
  Combinatorics: {
    factorial: [ev => new NativeFcn(ev, 'factorial', n => {
      if (!isInt(n) || n < 0) argErr(0, 'factorial', 'natural number', n);
      let r = 1;
      for (let i = 2; i <= n; i++) { r *= i; if (r > 2147483647) fail(`Overflow when computing ${n}`); }
      return r;
    })],
    choose: [(_, a) => {
      const [n, k] = a;
      if (!isInt(n) || n < 0) argErr(0, 'choose', 'natural number', n);
      if (!isInt(k) || k < 0) argErr(1, 'choose', 'natural number', k);
      if (k === 0 || k === n) return 1;
      if (k === 1 || k === n - 1) return n;
      if (n === 0 || k > n) return 0;
      let r = 1n;
      for (let i = 1n, j = BigInt(n); i <= BigInt(Math.min(k, n - k)); i++, j--) r = (r * j) / i;
      if (r > 2147483647n) fail(`Overflow when computing ${n}choose${k}`);
      return Number(r);
    }],
  },
  Bitwise: {
    And: [(_, a) => int(a[0], 'And', 0) & int(a[1], 'And', 1)],
    Or: [(_, a) => int(a[0], 'Or', 0) | int(a[1], 'Or', 1)],
    Xor: [(_, a) => int(a[0], 'Xor', 0) ^ int(a[1], 'Xor', 1)],
    // Flips only the bits below the highest set bit (the TLA+ definition has no word size to work with).
    Not: [(_, a) => { const x = int(a[0], 'Not', 0); return ~x & (2147483647 >> (Math.clz32(x) - 1)); }],
    shiftR: [(_, a) => (int(a[0], 'shiftR', 0) >>> int(a[1], 'shiftR', 1)) | 0],
  },
  DyadicRationals: {
    Reduce: [(_, a) => {
      const p = a[0];
      if (!(p instanceof RecordV)) oneArgErr('Half', 'record', p);
      const num = int(p.get('num'), 'Reduce', 0), den = int(p.get('den'), 'Reduce', 0);
      let x = Math.abs(num), y = Math.abs(den);
      while (y) [x, y] = [y, x % y];
      if (x === 1) return p;
      if (x === 0) fail('The second argument of \\div is 0.');
      return makeRecord(['den', 'num'], [Math.trunc(den / x), Math.trunc(num / x)]);
    }],
  },
  VectorClocks: {
    // CausalOrder(log, clock(_), node(_), domain(_)): a topological sort of the log by its vector clocks.
    CausalOrder: [(ev, a) => {
      if (!(a[0] instanceof TupleV)) argErr(0, 'CausalOrder', 'sequence', a[0]);
      interface GN { value: Value; clock: Value; time: Value; hosts: Value[]; parents: Set<GN>; children: Set<GN> }
      const log: Value[] = a[0].e;
      const n2l = new Map<string, GN[]>();
      for (const value of log) {
        const nodeId = ev.applyOp(a[2], [value]);
        const clock = ev.applyOp(a[1], [value]);
        const time = ev.applyFcn(clock, nodeId);
        const hosts = set(ev.applyOp(a[3], [clock]), 'CausalOrder', 3).elems();
        const k = key(nodeId);
        let list = n2l.get(k);
        if (!list) n2l.set(k, (list = []));
        list.push({ value, clock, time, hosts, parents: new Set(), children: new Set() });
      }
      // A node's own clock component totally orders its events.
      for (const list of n2l.values()) list.sort((x, y) => compare(x.time, y.time));
      // Merge the per-node logs into a DAG: an event depends on the latest event of every other node it has seen.
      for (const [host, list] of n2l) {
        const global = new Map<string, Value>();
        for (const h of n2l.keys()) global.set(h, 0);
        for (const gn of list) {
          global.set(host, gn.time);
          for (const other of gn.hosts) {
            const ok = key(other), seen = global.get(ok);
            const time = ev.applyFcn(gn.clock, other);
            if (seen === undefined) {
              // a node without events of its own; it cannot precede anything unless the clock says it did something
              if (compare(0, time) < 0) fail(`CausalOrder: the log has no events of node ${fmt(other)}, but a vector clock refers to its event ${fmt(time)}.`);
              continue;
            }
            if (compare(seen, time) < 0) {
              global.set(ok, time);
              const parent = n2l.get(ok)![int(time, 'CausalOrder', 0) - 1];
              if (!parent) fail(`CausalOrder: the log lacks event ${fmt(time)} of node ${fmt(other)} (vector clocks must be continuous).`);
              gn.parents.add(parent);
              parent.children.add(gn);
            }
          }
        }
      }
      // Repeatedly pop the heads that have no pending predecessor.
      const sorted: Value[] = [];
      const heads = new Map<string, number>();
      for (let round = 0; round < log.length && sorted.length < log.length; round++) {
        for (const [host, list] of n2l) {
          const i = heads.get(host) ?? 0;
          if (i >= list.length || list[i].parents.size > 0) continue;
          heads.set(host, i + 1);
          for (const c of list[i].children) c.parents.delete(list[i]);
          sorted.push(list[i].value);
        }
      }
      return tupleOf(sorted);
    }, { ops: [1, 2, 3] }],
  },
  Statistics: {
    // TRUE iff the chi-square goodness-of-fit test does NOT reject, at significance alpha, that `actual` follows `expected`.
    ChiSquare: [(_, a) => {
      if (!isFcn(a[0])) argErr(0, 'ChiSquare', 'function', a[0]);
      if (!isFcn(a[1])) argErr(1, 'ChiSquare', 'function', a[1]);
      if (typeof a[2] !== 'string') argErr(2, 'ChiSquare', 'StringValue representing a double in (0, .5]', a[2]);
      const exp = fcnValues(a[0]).map(v => int(v, 'ChiSquare', 0)), act = fcnValues(a[1]).map(v => int(v, 'ChiSquare', 1));
      const alpha = Number(a[2]);
      if (!(alpha > 0 && alpha <= 0.5)) fail(`out of bounds significance level (${a[2]}), must be between 0 and 0.5`);
      if (exp.length < 2) fail(`${exp.length} is smaller than the minimum (2)`);
      if (exp.length !== act.length) fail(`${exp.length} != ${act.length}`);
      for (const e of exp) if (e <= 0) fail(`element is not strictly positive: ${e}`);
      for (const o of act) if (o < 0) fail(`element is negative: ${o}`);
      const sumE = exp.reduce((x, y) => x + y, 0), sumO = act.reduce((x, y) => x + y, 0);
      const rescale = Math.abs(sumE - sumO) > 10e-6, ratio = rescale ? sumO / sumE : 1;
      let chi = 0;
      for (let i = 0; i < exp.length; i++) {
        const e = rescale ? ratio * exp[i] : exp[i], dev = act[i] - e;
        chi += dev * dev / e;
      }
      const p = 1 - regularizedGammaP((exp.length - 1) / 2, chi / 2);
      return !(p < alpha);
    }],
  },
  Graphs: {
    SimplePath: [(_, a) => simplePath('graph', TUPLE_EDGE, 'forward', a[0])],
    AreConnectedIn: [(_, a) => areConnectedIn('graph', TUPLE_EDGE, 'forward', a[0], a[1], a[2])],
    IsStronglyConnected: [(_, a) => {
      const g = toGraph('IsStronglyConnected', 0, 'graph', a[0]);
      const nodes = g.nodes.elems();
      if (nodes.length === 0) return true;
      return reachable(nodes[0], adjacency(g, TUPLE_EDGE, 'forward')).size === nodes.length
        && reachable(nodes[0], adjacency(g, TUPLE_EDGE, 'transpose')).size === nodes.length;
    }],
  },
  UndirectedGraphs: {
    SimplePath: [(_, a) => simplePath('undirected graph', PAIR_EDGE, 'symmetric', a[0])],
    AreConnectedIn: [(_, a) => areConnectedIn('undirected graph', PAIR_EDGE, 'symmetric', a[0], a[1], a[2])],
    ConnectedComponents: [(_, a) => {
      const g = toGraph('ConnectedComponents', 0, 'undirected graph', a[0]);
      const nodes = g.nodes.elems();
      const parent = new Map<string, string>();
      for (const n of nodes) parent.set(key(n), key(n));
      const find = (k: string): string => {
        let root = k;
        while (parent.get(root) !== root) root = parent.get(root)!;
        while (k !== root) { const next = parent.get(k)!; parent.set(k, root); k = next; }
        return root;
      };
      for (const e of g.edges) {
        const p = PAIR_EDGE(e);
        if (!p || !g.nodes.contains(p[0]) || !g.nodes.contains(p[1])) continue;
        const x = find(key(p[0])), y = find(key(p[1]));
        if (x !== y) parent.set(y, x);
      }
      const comps = new Map<string, Value[]>();
      for (const n of nodes) {
        const rep = find(key(n));
        const c = comps.get(rep);
        if (c) c.push(n); else comps.set(rep, [n]);
      }
      return mkSet([...comps.values()].map(c => new SetV(c)));
    }],
  },
  Json: {
    ToJson: [(_, a) => jsonNode(a[0])],
    ToJsonArray: [(_, a) => jsonArrayNode(a[0])],
    ToJsonObject: [(_, a) => jsonObjectNode(a[0])],
    JsonSerialize: [(ev, a) => {
      const path = str(a[0], 'JsonSerialize', 0);
      if (!(a[1] instanceof TupleV) && !(a[1] instanceof RecordV)) argErr(1, 'JsonSerialize', 'sequence or record', a[1]);
      const text = jsonNode(a[1]);
      hostWrite(() => io(ev).writeFile(path, text), path);
      return true;
    }],
    ndJsonSerialize: [(ev, a) => {
      const path = str(a[0], 'ndJsonSerialize', 0);
      if (!(a[1] instanceof TupleV)) argErr(1, 'ndJsonSerialize', 'sequence', a[1]);
      const text = (a[1].e as Value[]).map(v => jsonNode(v) + '\n').join('');
      hostWrite(() => io(ev).writeFile(path, text), path);
      return true;
    }],
    JsonDeserialize: [(ev, a) => new JsonReader(readText(ev, str(a[0], 'JsonDeserialize', 0))).document()],
    ndJsonDeserialize: [(ev, a) => {
      const out: Value[] = [];
      for (const line of readText(ev, str(a[0], 'ndJsonDeserialize', 0)).split(/\r\n|\n|\r/)) {
        const t = line.trim();
        if (t !== '') out.push(new JsonReader(t).document());
      }
      return tupleOf(out);
    }],
  },
  CSV: {
    // Appends the record's values (and, if `headers`, first its field names) joined by `delim`.
    CSVWriteRecord: [(ev, a) => {
      if (!(a[0] instanceof RecordV)) oneArgErr('CSVWriteRecord', 'record', a[0]);
      const rec: RecordV = a[0], delim = str(a[1], 'CSVWriteRecord', 1), path = str(a[3], 'CSVWriteRecord', 3);
      if (typeof a[2] !== 'boolean') argErr(2, 'CSVWriteRecord', 'boolean', a[2]);
      let text = '';
      if (a[2]) text += rec.names.join(delim) + '\n';
      text += rec.vals.map(fmt).join(delim) + '\n';
      hostWrite(() => io(ev).appendFile(path, text), path);
      return true;
    }],
    // Appends String.format(template, values printed as TLA+ values) as one line.
    CSVWrite: [(ev, a) => {
      const template = str(a[0], 'CSVWrite', 0), path = str(a[2], 'CSVWrite', 2);
      if (!(a[1] instanceof TupleV)) oneArgErr('CSVWrite', 'sequence', a[1]);
      const text = javaFormat(template, (a[1].e as Value[]).map(fmt)) + '\n';
      hostWrite(() => io(ev).appendFile(path, text), path);
      return true;
    }],
    CSVRead: [(ev, a) => {
      if (!(a[0] instanceof TupleV)) oneArgErr('CSVRead', 'sequence', a[0]);
      const names = (a[0].e as Value[]).map((n, i) => (typeof n === 'string' ? n : fail(`Column name ${i + 1} of CSVRead should be a string, but instead it is:\n${fmt(n)}`)));
      const delim = str(a[1], 'CSVRead', 1), path = str(a[2], 'CSVRead', 2);
      if (!io(ev).exists(path)) return EMPTY_TUPLE;
      let re: RegExp;
      try { re = new RegExp(delim); } catch { re = new RegExp(delim.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')); }
      return tupleOf(splitLines(readText(ev, path)).map(line => {
        const cells = line.split(re); // Java's String.split: a regex, trailing empty strings removed
        while (cells.length > 1 && cells[cells.length - 1] === '') cells.pop();
        for (const c of cells) strId(c);
        if (cells.length !== names.length) fail(`CSVRead: a line of ${path} has ${cells.length} fields, but ${names.length} columns were given:\n${line}`);
        return makeFcnFromPairs(names.map((n, i): [Value, Value] => [n, cells[i]]));
      }));
    }],
    CSVRecords: [(ev, a) => {
      const path = str(a[0], 'CSVRecords', 0);
      return io(ev).exists(path) ? splitLines(readText(ev, path)).length : 0;
    }],
  },
  IOUtils: {
    IOEnv: [ev => {
      const env = io(ev).env;
      const names = Object.keys(env);
      return names.length ? makeRecord(names, names.map(n => env[n])) : EMPTY_TUPLE;
    }],
    atoi: [(_, a) => {
      const s = a[0];
      if (typeof s === 'string' && /^[+-]?[0-9]+$/.test(s)) {
        const n = Number(s);
        if (n >= -2147483648 && n <= 2147483647) return n === 0 ? 0 : n;
      }
      return oneArgErr('atoi', 'string', s);
    }],
    // TLC's binary value format (uncompressed only).
    IOSerialize: [(ev, a) => {
      const path = str(a[1], 'IOSerialize', 1), h = io(ev);
      if (a[2] !== false) fail('IOSerialize: compressed (gzip) output is not supported; pass FALSE as the third argument.');
      if (!h.writeBytes) fail('IOSerialize is not supported: this host does not provide binary file output.');
      const bytes = encodeValue(a[0]);
      hostWrite(() => h.writeBytes!(path, bytes), path);
      return true;
    }],
    IODeserialize: [(ev, a) => {
      const path = str(a[0], 'IODeserialize', 0), h = io(ev);
      if (a[1] !== false) fail('IODeserialize: compressed (gzip) input is not supported; pass FALSE as the second argument.');
      if (!h.readBytes) fail('IODeserialize is not supported: this host does not provide binary file input.');
      if (!h.exists(path)) fail(`${path} (No such file or directory)`);
      return decodeValue(h.readBytes!(path));
    }],
    // Serialize(value, dest, options) / Deserialize(src, options): only the plain-text format is implemented (as in TLC).
    Serialize: [(ev, a) => {
      const opts = a[2];
      if (!(opts instanceof RecordV) || opts.get('format') !== 'TXT') fail('Serialize: only [format |-> "TXT", charset |-> ..., openOptions |-> ...] is supported.');
      const oo = opts.get('openOptions'), cs = opts.get('charset');
      if (typeof a[0] !== 'string' || typeof a[1] !== 'string' || !(oo instanceof TupleV) || typeof cs !== 'string' || oo.e.some((x: Value) => typeof x !== 'string')) {
        return execResult(1, '', 'Serialize error invalid parameters: payload and file must be strings, charset a string and openOptions a sequence of strings');
      }
      const h = io(ev), o: string[] = oo.e;
      try {
        const bad = o.find(x => !['READ', 'WRITE', 'APPEND', 'TRUNCATE_EXISTING', 'CREATE', 'CREATE_NEW', 'DELETE_ON_CLOSE', 'SPARSE', 'SYNC', 'DSYNC'].includes(x));
        if (bad !== undefined) throw new Error(`java.lang.IllegalArgumentException: No enum constant java.nio.file.StandardOpenOption.${bad}`);
        const exists = h.exists(a[1]);
        if (o.includes('CREATE_NEW') && exists) throw new Error(`java.nio.file.FileAlreadyExistsException: ${a[1]}`);
        if (o.length > 0 && !o.includes('CREATE') && !o.includes('CREATE_NEW') && !exists) throw new Error(`java.nio.file.NoSuchFileException: ${a[1]}`);
        if (o.includes('APPEND')) h.appendFile(a[1], a[0]); else h.writeFile(a[1], a[0]);
        return execResult(0, 'Finish writing to the file with success!', '');
      } catch (e) {
        return execResult(1, '', 'Serialize error writing to the file: ' + (e as Error).message);
      }
    }],
    Deserialize: [(ev, a) => {
      const opts = a[1];
      if (!(opts instanceof RecordV) || opts.get('format') !== 'TXT') fail('Deserialize: only [format |-> "TXT", charset |-> ...] is supported.');
      if (typeof a[0] !== 'string' || typeof opts.get('charset') !== 'string') return execResult(1, '', 'Deserialize error invalid parameters: file and charset must be strings');
      const h = io(ev);
      try {
        if (!h.exists(a[0])) throw new Error(`java.nio.file.NoSuchFileException: ${a[0]}`);
        return execResult(0, h.readFile(a[0]), '');
      } catch (e) {
        return execResult(1, '', 'Deserialize error reading from the file: ' + (e as Error).message);
      }
    }],
    IOExec: [(ev, a) => runProcess(ev, 'IOExec', cmdStrings(a[0], 'IOExec'))],
    IOEnvExec: [(ev, a) => { const env = envRecord(a[0], 'IOEnvExec'); return runProcess(ev, 'IOEnvExec', cmdStrings(a[1], 'IOEnvExec'), env); }],
    IOExecTemplate: [(ev, a) => {
      const cmd = cmdStrings(a[0], 'IOExecTemplate'), params = cmdStrings(a[1], 'IOExecTemplate');
      return runProcess(ev, 'IOExecTemplate', cmd.map(c => javaFormat(c, params)));
    }],
    IOEnvExecTemplate: [(ev, a) => {
      const env = envRecord(a[0], 'IOEnvExecTemplate');
      const cmd = cmdStrings(a[1], 'IOEnvExecTemplate'), params = cmdStrings(a[2], 'IOEnvExecTemplate');
      return runProcess(ev, 'IOEnvExecTemplate', cmd.map(c => javaFormat(c, params)), env);
    }],
  },
};
