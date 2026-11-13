// Expression evaluator and action (next-state / initial-state) enumerator.
import type { Node, Bound, Param } from './parser.ts';
import { LOCAL, tailFn, defLevel } from './modules.ts';
import type { Def, Decl } from './modules.ts';
import {
  EvalError, SetBase, SetV, IntervalV, SubsetV, DerivedSetV, FcnSetV, RecSetV, CrossV, LazySetV, TupleV, RecordV, FcnV,
  ModelValue, valEq, compare, bsearch, sortDedup, mkSet, makeFcn, makeRecord, domainOf, fmt, strId, EMPTY_SET,
} from './values.ts';
import type { Value } from './values.ts';
import { TlaError } from './lexer.ts';
import { ppr } from './pprint.ts';

export class Ctx {
  name: string;
  val: any;
  next: Ctx | null;
  base: Ctx | null; // head of the enclosing instance environment (substitutions), or null at the root
  constructor(name: string, val: any, next: Ctx | null) {
    this.name = name;
    this.val = val;
    this.next = next;
    this.base = next === null ? null : next.base;
  }
}
const cons = (name: string, val: any, next: Ctx | null) => new Ctx(name, val, next);

// A delayed expression (operator argument, LET definition, instance substitution).
export class Lazy {
  e: Node;
  ctx: Ctx | null;
  v: Value = undefined;
  st: any = null; // state the cached value is valid for; ANY = constant
  constructor(e: Node, ctx: Ctx | null) { this.e = e; this.ctx = ctx; }
}
const ANY = { any: true };

export class Closure {
  params: Param[];
  body: Node;
  ctx: Ctx | null;
  name: string;
  constructor(params: Param[], body: Node, ctx: Ctx | null, name = 'LAMBDA') { this.params = params; this.body = body; this.ctx = ctx; this.name = name; }
  describe(): string { return `<operator ${this.name}>`; }
}
export class DefRef {
  def: Def;
  base: Ctx | null;
  constructor(def: Def, base: Ctx | null) { this.def = def; this.base = base; }
  describe(): string { return `<operator ${this.def.name}>`; }
}
export type Op = Closure | DefRef;

// A lazily evaluated function (recursive function definitions, functions over non-enumerable domains).
export class LazyFcn {
  node: Node;
  ctx: Ctx | null;
  ev: Evaluator;
  memo = new Map<any, Value>();
  forced: Value = undefined;
  constructor(node: Node, ctx: Ctx | null, ev: Evaluator) {
    this.node = node;
    this.ev = ev;
    this.ctx = node.recname ? cons(node.recname, this, ctx) : ctx;
  }
  describe(): string { return '<lazy function>'; }
  show(): string {
    try { const f = this.force(); if (f !== this) return ppr(fmt(f)); } catch (e) { if (!(e instanceof TlaError)) throw e; }
    return this.describe();
  }
  bind(arg: Value): Ctx | null {
    const ev = this.ev;
    const bounds = this.node.bounds as Bound[];
    let c = this.ctx;
    const one = bounds.length === 1 && (bounds[0].tuple !== null || bounds[0].names!.length === 1);
    if (one) {
      const b = bounds[0];
      const s = ev.evalSet(b.set!, this.ctx);
      if (!s.contains(arg)) throw new EvalError(`In applying the function\n${this.show()},\nthe first argument is:\n${ppr(fmt(arg))}\nwhich is not in its domain.\n`);
      c = b.tuple ? ev.bindTuple(b.tuple, arg, c) : cons(b.names![0], arg, c);
    } else {
      if (!(arg instanceof TupleV)) throw new EvalError(`Attempted to apply function to argument ${fmt(arg)}, which is not in the domain of the function.`);
      let i = 0;
      for (const b of bounds) {
        const s = ev.evalSet(b.set!, this.ctx);
        const cnt = b.tuple ? 1 : b.names!.length;
        for (let j = 0; j < cnt; j++) {
          const a = arg.e[i++];
          if (a === undefined || !s.contains(a)) throw new EvalError(`Attempted to apply function to argument ${fmt(arg)}, which is not in the domain of the function.`);
          c = b.tuple ? ev.bindTuple(b.tuple, a, c) : cons(b.names![j], a, c);
        }
      }
      if (i !== arg.e.length) throw new EvalError(`Attempted to apply function to argument ${fmt(arg)}, which is not in the domain of the function.`);
    }
    return c;
  }
  // [f EXCEPT ![k] = v] on a function that is not enumerated: later entries win
  over: [Value, Value][] | null = null;
  withOverride(key: Value, val: Value): LazyFcn {
    const g = new LazyFcn(this.node, null, this.ev);
    g.ctx = this.ctx;
    g.memo = this.memo;
    g.over = this.over ? [...this.over, [key, val]] : [[key, val]];
    return g;
  }
  // `lazy`: the caller keeps a function-valued result unevaluated (it is applied right away)
  apply(arg: Value, lazy = false): Value {
    if (this.over !== null) {
      for (let i = this.over.length - 1; i >= 0; i--) if (valEq(this.over[i][0], arg)) return this.over[i][1];
    }
    const ev = this.ev;
    const key = typeof arg === 'number' || typeof arg === 'string' ? arg : '\u0001' + fmt(arg);
    const hit = this.memo.get(key);
    if (hit !== undefined) return hit;
    const c = this.bind(arg);
    const s0 = ev.stTouch, p0 = ev.prTouch;
    // like TLC, the body of a recursive function is evaluated in keep-lazy mode
    const v = lazy || this.node.isRec ? ev.evalLazy(this.node.body, c) : ev.eval(this.node.body, c);
    if (ev.stTouch === s0 && ev.prTouch === p0) this.memo.set(key, v);
    return v;
  }
  domain(): SetBase {
    const bounds = this.node.bounds as Bound[];
    const sets: SetBase[] = [];
    for (const b of bounds) {
      const s = this.ev.evalSet(b.set!, this.ctx);
      const cnt = b.tuple ? 1 : b.names!.length;
      for (let j = 0; j < cnt; j++) sets.push(s);
    }
    return sets.length === 1 ? sets[0] : new CrossV(sets);
  }
  force(): Value {
    if (this.forced !== undefined) return this.forced;
    const ev = this.ev;
    const s0 = ev.stTouch, p0 = ev.prTouch;
    const ds = this.domain();
    if (!ds.enumerable()) return this; // stays lazy: only application and EXCEPT are possible
    const dom = ds.elems();
    const vals = dom.map(d => { const v = this.apply(d); return typeof v === 'object' && v instanceof LazyFcn ? v.force() : v; });
    const f = makeFcn(dom, vals);
    if (ev.stTouch === s0 && ev.prTouch === p0) this.forced = f;
    return f;
  }
}

const KINDS = ['num', 'str', 'bool', 'app', 'and', 'or', 'not', 'imp', 'eqv', 'eq', 'ne', 'in', 'notin', 'subseteq',
  'cup', 'cap', 'diff', 'powerset', 'bigunion', 'domain', 'prime', 'enabled', 'unchanged', 'cross', 'if', 'case',
  'let', 'quant', 'choose', 'setenum', 'setfilter', 'setmap', 'fndef', 'fnset', 'rec', 'recset', 'except', 'tuple',
  'fnapp', 'dot', 'boxact', 'angleact', 'lambda', 'at', 'always', 'eventually', 'leadsto', 'guarantee', 'wf', 'sf',
  'tquant', 'cdot', 'stepref'] as const;
const OP: Record<string, number> = {};
KINDS.forEach((k, i) => { OP[k] = i; });
const O = OP as Record<(typeof KINDS)[number], number>;
const O_num = O.num, O_str = O.str, O_bool = O.bool, O_app = O.app, O_and = O.and, O_or = O.or, O_not = O.not,
  O_imp = O.imp, O_eqv = O.eqv, O_eq = O.eq, O_ne = O.ne, O_in = O.in, O_notin = O.notin, O_subseteq = O.subseteq,
  O_cup = O.cup, O_cap = O.cap, O_diff = O.diff, O_powerset = O.powerset, O_bigunion = O.bigunion,
  O_domain = O.domain, O_prime = O.prime, O_enabled = O.enabled, O_unchanged = O.unchanged, O_cross = O.cross,
  O_if = O.if, O_case = O.case, O_let = O.let, O_quant = O.quant, O_choose = O.choose, O_setenum = O.setenum,
  O_setfilter = O.setfilter, O_setmap = O.setmap, O_fndef = O.fndef, O_fnset = O.fnset, O_rec = O.rec,
  O_recset = O.recset, O_except = O.except, O_tuple = O.tuple, O_fnapp = O.fnapp, O_dot = O.dot,
  O_boxact = O.boxact, O_angleact = O.angleact, O_lambda = O.lambda, O_at = O.at;

const ENABLED_MARK = '\u0000enabled';
const reducible = (s: SetBase) => s instanceof SetV || s instanceof IntervalV;

class Found extends Error {}
const FOUND = new Found();

export class Evaluator {
  nvars = 0;
  varNames: string[] = [];
  cur: Value[] = []; // current state (unprimed variables)
  nxt: Value[] | null = null; // next state (primed variables); may be partial during enumeration
  initMode = false; // enumerating initial states: `cur` is partial and mutable
  primeDepth = 0;
  stTouch = 0;
  prTouch = 0;
  hooks: { [k: string]: any } = { random: Math.random };
  callDepth = 0;
  nAssigned = 0; // number of target variables assigned during enumeration
  inEnabled = 0;
  extraGenerated = 0; // intermediate states of action compositions (TLC counts them as generated)
  scratch = new Map<Decl, number>(); // ENABLED: primed variables of instantiated modules are existentially bound

  fail(msg: string, n?: Node): never {
    const e = new EvalError(msg);
    if (n) { e.loc = n.loc; e.module = n.mod; }
    throw e;
  }

  // ---------- context helpers ----------
  lookup(ctx: Ctx | null, name: string): any {
    for (let c = ctx; c !== null; c = c.next) if (c.name === name) return c.val;
    return this.fail(`Internal error: unbound local identifier ${name}`);
  }
  envLookup(base: Ctx | null, name: string): any {
    for (let c = base; c !== null; c = c.next) if (c.name === name) return c.val;
    return undefined;
  }
  bindTuple(names: string[], v: Value, ctx: Ctx | null): Ctx | null {
    if (!(v instanceof TupleV) || v.e.length !== names.length) {
      return this.fail(`Attempted to match the tuple pattern <<${names.join(', ')}>> against the value ${fmt(v)}`);
    }
    let c = ctx;
    for (let i = 0; i < names.length; i++) c = cons(names[i], v.e[i], c);
    return c;
  }

  force(lz: Lazy, lazy = false): Value {
    if (lz.v !== undefined) {
      if (lz.st === ANY) return lz.v;
      if (lz.st === this.cur && !this.initMode && this.primeDepth === 0) { this.stTouch++; return lz.v; }
    }
    const s0 = this.stTouch, p0 = this.prTouch;
    const v = lazy ? this.evalLazy(lz.e, lz.ctx) : this.eval(lz.e, lz.ctx);
    if (this.prTouch === p0) {
      if (this.stTouch === s0) { lz.v = v; lz.st = ANY; }
      else if (!this.initMode && this.primeDepth === 0) { lz.v = v; lz.st = this.cur; }
    }
    return v;
  }

  // Turn an argument expression into a thunk / value / operator.
  mkArg(n: Node, ctx: Ctx | null): any {
    switch (n.k) {
      case 'num': case 'str': case 'bool': return n.v;
      case 'lambda': return new Closure(n.params, n.body, ctx);
      case 'app':
        if (n.args.length === 0 && !n.sel) {
          const r = n.r as any;
          if (r === LOCAL) return this.lookup(ctx, n.name);
          if (r.k === 'def') {
            const d = r.override ?? r;
            if (d.params.length > 0) return new DefRef(d, ctx === null ? null : ctx.base);
          } else if (r.k === 'const') {
            const base = ctx === null ? null : ctx.base;
            if (base !== null) { const b = this.envLookup(base, n.name); if (b !== undefined) return b; }
            if (r.subst) return r.subst.params.length > 0 ? new DefRef(r.subst, null) : new Lazy(n, ctx);
            if (r.hasValue) return r.value;
          }
        }
    }
    return new Lazy(n, ctx);
  }

  unthunk(t: any): Value {
    if (t instanceof Lazy) {
      const v = this.force(t);
      return typeof v === 'object' && v instanceof LazyFcn ? v.force() : v;
    }
    return t;
  }

  buildEnv(def: Def, thunks: any[], callerBase: Ctx | null): Ctx | null {
    const inst = def.inst!;
    if (inst.nparams === 0 && callerBase === null && inst.envCache !== undefined) return inst.envCache;
    let pc = callerBase;
    for (let i = 0; i < inst.nparams; i++) pc = cons(def.params[i].name, thunks[i], pc);
    let head: Ctx | null = null;
    const nodes: Ctx[] = [];
    for (const s of inst.substs) {
      head = new Ctx(s.name, this.mkArg(s.e, pc), head);
      nodes.push(head);
    }
    for (const nd of nodes) nd.base = head;
    if (inst.nparams === 0 && callerBase === null) inst.envCache = head;
    return head;
  }

  // Expand a definition application into (body, context) without evaluating it.
  expandDef(def: Def, thunks: any[], base: Ctx | null, viaInstance = false): { body: Node; ctx: Ctx | null } | null {
    // A config override (Op <- Other) replaces references to Op itself; an instantiated copy (I!Op) keeps the
    // original body, as in TLC where the override is attached to the definition node, not to its body.
    if (def.override && !(viaInstance && !def.override.builtin)) def = def.override;
    if (def.builtin) return null;
    if (def.inst) {
      const env = this.buildEnv(def, thunks, base);
      const rest = def.inst.nparams ? thunks.slice(def.inst.nparams) : thunks;
      const r = this.expandDef(def.inst.orig, rest, env, true);
      return r;
    }
    const ps = def.params;
    if (ps.length !== thunks.length) this.fail(`The operator ${def.name} expects ${ps.length} arguments but was given ${thunks.length}.`);
    let c = base;
    for (let i = 0; i < ps.length; i++) c = cons(ps[i].name, thunks[i], c);
    return { body: def.body!, ctx: c };
  }

  // Expand an `app` node one step: returns the body/context it denotes, or null if it is a plain value or builtin.
  expandApp(n: Node, ctx: Ctx | null): { body: Node; ctx: Ctx | null } | null {
    const r = n.r as any;
    let res: { body: Node; ctx: Ctx | null } | null = null;
    if (r === LOCAL) {
      const b = this.lookup(ctx, n.name);
      if (b instanceof Lazy) res = { body: b.e, ctx: b.ctx };
      else if (b instanceof Closure || b instanceof DefRef) res = this.expandOp(b, n.args.map((a: Node) => this.mkArg(a, ctx)));
    } else if (r.k === 'def') {
      res = this.expandDef(r, n.args.length ? n.args.map((a: Node) => this.mkArg(a, ctx)) : NOARGS, ctx === null ? null : ctx.base);
    } else {
      const base = ctx === null ? null : ctx.base;
      const b = base !== null ? this.envLookup(base, n.name) : undefined;
      if (b !== undefined) {
        if (b instanceof Lazy) res = { body: b.e, ctx: b.ctx };
        else if (b instanceof Closure || b instanceof DefRef) res = this.expandOp(b, n.args.map((a: Node) => this.mkArg(a, ctx)));
      } else if (r.k === 'const' && r.subst) {
        res = this.expandDef(r.subst, n.args.map((a: Node) => this.mkArg(a, ctx)), null);
      }
    }
    if (res && n.sel) res = this.select(res, n);
    return res;
  }

  expandOp(op: Op, thunks: any[]): { body: Node; ctx: Ctx | null } | null {
    if (op instanceof DefRef) return this.expandDef(op.def, thunks, op.base);
    if (op.params.length !== thunks.length) this.fail(`The operator ${op.name} expects ${op.params.length} arguments but was given ${thunks.length}.`);
    let c = op.ctx;
    for (let i = 0; i < op.params.length; i++) c = cons(op.params[i].name, thunks[i], c);
    return { body: op.body, ctx: c };
  }

  // Subexpression selectors: Op!1, Op!<<, Op!>> ...
  select(res: { body: Node; ctx: Ctx | null }, n: Node): { body: Node; ctx: Ctx | null } {
    let body = res.body;
    for (const s of n.sel) {
      const kids: Node[] | undefined = body.a ?? body.args ?? (body.body ? [body.body] : undefined);
      if (s === ':') continue;
      const i = s === '<<' ? 0 : s === '>>' ? 1 : typeof s === 'number' ? s - 1 : -1;
      if (!kids || i < 0 || i >= kids.length) this.fail(`Unsupported subexpression selector in ${n.name}`, n);
      body = kids![i];
    }
    return { body, ctx: res.ctx };
  }

  applyOp(op: any, args: any[]): Value {
    if (op instanceof DefRef) {
      const d = op.def.override ?? op.def;
      if (d.builtin) return d.builtin.lazy ? d.builtin.fn(this, args) : d.builtin.fn(this, args.map(a => this.unthunk(a)));
    } else if (!(op instanceof Closure)) return this.fail(`Attempted to apply a non-operator value ${fmt(op)} as an operator.`);
    const r = this.expandOp(op, args);
    if (r === null) {
      // instance of a builtin operator (e.g. LET T == INSTANCE TLC IN T!PrintT(x))
      let d = (op as DefRef).def;
      d = d.override ?? d;
      while (d.inst) { args = d.inst.nparams ? args.slice(d.inst.nparams) : args; d = d.inst.orig; d = d.override ?? d; }
      const bi = d.builtin!;
      return bi.lazy ? bi.fn(this, args) : bi.fn(this, args.map((a, i) => bi.ops && bi.ops.includes(i) ? a : this.unthunk(a)));
    }
    return this.eval(r.body, r.ctx);
  }

  applyDef(def: Def, n: Node, ctx: Ctx | null): Value {
    if (def.override) def = def.override;
    const bi = def.builtin;
    if (bi) {
      const args: any[] = new Array(n.args.length);
      if (bi.lazy) for (let i = 0; i < args.length; i++) args[i] = this.mkArg(n.args[i], ctx);
      else if (bi.ops) for (let i = 0; i < args.length; i++) args[i] = bi.ops.includes(i) ? this.mkArg(n.args[i], ctx) : this.eval(n.args[i], ctx);
      else for (let i = 0; i < args.length; i++) args[i] = this.eval(n.args[i], ctx);
      return bi.fn(this, args);
    }
    const base = ctx === null ? null : ctx.base;
    if (def.params.length === 0 && !def.inst) {
      if (base === null) {
        if (def.cached) return def.cache;
        const s0 = this.stTouch, p0 = this.prTouch;
        const v = this.eval(def.body!, null);
        if (this.stTouch === s0 && this.prTouch === p0) { def.cached = true; def.cache = v; }
        return v;
      }
      return this.eval(def.body!, base);
    }
    const r = this.expandDef(def, n.args.length ? n.args.map((a: Node) => this.mkArg(a, ctx)) : NOARGS, base);
    if (r === null) {
      // instance of a builtin operator
      let d = def;
      while (d.inst) d = d.inst.orig;
      return this.applyDef(d, n, ctx);
    }
    if (++this.callDepth > 6000) {
      this.callDepth = 0;
      this.fail(`Evaluation of ${def.name} exceeded the maximum recursion depth; the definition is probably non-terminating.`);
    }
    const v = this.eval(r.body, r.ctx);
    this.callDepth--;
    return v;
  }

  evalApp(n: Node, ctx: Ctx | null): Value {
    const r = n.r as any;
    if (n.sel) {
      const x = this.expandApp(n, ctx);
      if (!x) return this.fail('Unsupported subexpression selector', n);
      return this.eval(x.body, x.ctx);
    }
    if (r === LOCAL) {
      const b = this.lookup(ctx, n.name);
      if (b instanceof Lazy) return this.force(b);
      if (b instanceof Closure || b instanceof DefRef) {
        if (n.args.length === 0 && (b instanceof Closure ? b.params.length : (b.def.override ?? b.def).params.length) > 0) return b;
        return this.applyOp(b, n.args.map((a: Node) => this.mkArg(a, ctx)));
      }
      return b;
    }
    if (r.k === 'def') return this.applyDef(r, n, ctx);
    const base = ctx === null ? null : ctx.base;
    if (base !== null) {
      const b = this.envLookup(base, n.name);
      if (b !== undefined) {
        if (this.inEnabled > 0 && this.primeDepth > 0 && r.k === 'var' && b instanceof Lazy) {
          const idx = this.asVar(n, ctx);
          if (idx >= 0) {
            const v = this.cur[idx];
            this.prTouch++;
            if (v === undefined) return this.fail(`In evaluation, the identifier ${r.name} is either undefined or not an operator.`, n);
            return v;
          }
        }
        if (b instanceof Lazy) return this.force(b);
        if (b instanceof Closure || b instanceof DefRef) return this.applyOp(b, n.args.map((a: Node) => this.mkArg(a, ctx)));
        return b;
      }
    }
    if (r.k === 'var') {
      const v = this.cur[r.idx];
      if (this.primeDepth > 0) this.prTouch++; else this.stTouch++;
      if (v === undefined) {
        return this.fail(this.primeDepth > 0
          ? `In evaluation, the identifier ${r.name} is either undefined or not an operator.` // primed variable not yet assigned
          : `In evaluation, the identifier ${r.name} is either undefined or not an operator.`, n);
      }
      return v;
    }
    // constant
    if (r.subst) {
      const d = r.subst;
      if (d.params.length === 0 && n.args.length === 0) return this.applyDef(d, n, null);
      const x = this.expandDef(d, n.args.map((a: Node) => this.mkArg(a, ctx)), null);
      if (!x) return this.applyDef(d, n, ctx);
      return this.eval(x.body, x.ctx);
    }
    if (r.hasValue) return r.value;
    return this.fail(`The constant parameter ${r.name} is not assigned a value by the configuration file.`, n);
  }

  // ---------- evaluation ----------
  evalBool(n: Node, ctx: Ctx | null): boolean {
    const v = this.eval(n, ctx);
    if (typeof v !== 'boolean') return this.fail(`Attempted to evaluate an expression as a boolean, but it was the non-boolean value:\n${fmt(v)}`, n);
    return v;
  }
  evalSet(n: Node, ctx: Ctx | null): SetBase {
    const v = this.eval(n, ctx);
    if (!(v instanceof SetBase)) return this.fail(`Attempted to use the non-set value:\n${fmt(v)}\nas a set.`, n);
    return v;
  }
  evalElems(n: Node, ctx: Ctx | null): Value[] {
    const s = this.evalSet(n, ctx);
    try {
      return s.elems();
    } catch (e) {
      if (e instanceof TlaError && !e.loc) { e.loc = n.loc; e.module = n.mod; }
      throw e;
    }
  }

  // Iterate over all bindings of a list of bounds; f returns true to stop. Returns true if stopped.
  forBindings(bounds: Bound[], ctx: Ctx | null, f: (c: Ctx | null) => boolean): boolean {
    if (bounds.length === 1) {
      const b = bounds[0];
      if (b.set === null) return this.fail('TLC cannot handle unbounded quantification.');
      const es = this.evalElems(b.set, ctx);
      if (b.tuple) {
        for (let i = 0; i < es.length; i++) if (f(this.bindTuple(b.tuple, es[i], ctx))) return true;
        return false;
      }
      if (b.names!.length === 1) {
        const name = b.names![0];
        for (let i = 0; i < es.length; i++) if (f(new Ctx(name, es[i], ctx))) return true;
        return false;
      }
    }
    const sets = bounds.map(b => {
      if (b.set === null) return this.fail('TLC cannot handle unbounded quantification.');
      return this.evalElems(b.set, ctx);
    });
    // TLC varies the FIRST bound variable fastest, so the last one is the outermost loop.
    const flat: { name: string | null; tuple: string[] | null; es: Value[] }[] = [];
    bounds.forEach((b, i) => {
      if (b.tuple) flat.push({ name: null, tuple: b.tuple, es: sets[i] });
      else for (const nm of b.names!) flat.push({ name: nm, tuple: null, es: sets[i] });
    });
    const rec = (i: number, c: Ctx | null): boolean => {
      if (i < 0) return f(c);
      const b = flat[i];
      for (const v of b.es) if (rec(i - 1, b.tuple ? this.bindTuple(b.tuple, v, c) : cons(b.name!, v, c))) return true;
      return false;
    };
    return rec(flat.length - 1, ctx);
  }

  bindLet(defs: Node[], ctx: Ctx | null): Ctx | null {
    let c = ctx;
    const made: (Lazy | Closure | DefRef)[] = [];
    for (const d of defs) {
      if (d.k !== 'def') {
        for (const def of d.instDefs as Def[]) { const x = new DefRef(def, null); made.push(x); c = cons(def.name, x, c); }
        continue;
      }
      const x = d.params.length === 0 ? new Lazy(d.body, null) : new Closure(d.params, d.body, null, d.name);
      made.push(x);
      c = cons(d.name, x, c);
    }
    for (const x of made) { if (x instanceof DefRef) x.base = c; else x.ctx = c; }
    return c;
  }

  eval(n: Node, ctx: Ctx | null): Value {
    let o = n.o;
    if (o === undefined) o = n.o = OP[n.k];
    switch (o) {
      case O_num: case O_str: case O_bool: return n.v;
      case O_app: {
        const v = this.evalApp(n, ctx);
        if (typeof v === 'object' && v instanceof LazyFcn) return v.force();
        return v;
      }
      case O_and: {
        const a = n.a;
        for (let i = 0; i < a.length; i++) if (!this.evalBool(a[i], ctx)) return false;
        return true;
      }
      case O_or: {
        const a = n.a;
        for (let i = 0; i < a.length; i++) if (this.evalBool(a[i], ctx)) return true;
        return false;
      }
      case O_not: return !this.evalBool(n.a[0], ctx);
      case O_imp: return !this.evalBool(n.a[0], ctx) || this.evalBool(n.a[1], ctx);
      case O_eqv: return this.evalBool(n.a[0], ctx) === this.evalBool(n.a[1], ctx);
      case O_eq: return valEq(this.eval(n.a[0], ctx), this.eval(n.a[1], ctx));
      case O_ne: return !valEq(this.eval(n.a[0], ctx), this.eval(n.a[1], ctx));
      case O_in: {
        const x = this.eval(n.a[0], ctx);
        return this.evalSet(n.a[1], ctx).contains(x);
      }
      case O_notin: {
        const x = this.eval(n.a[0], ctx);
        return !this.evalSet(n.a[1], ctx).contains(x);
      }
      case O_subseteq: {
        let a = this.evalSet(n.a[0], ctx), b = this.evalSet(n.a[1], ctx);
        // SUBSET A \subseteq SUBSET B  iff  A \subseteq B
        while (a instanceof SubsetV && b instanceof SubsetV) { a = a.base; b = b.base; }
        if (!a.enumerable()) return this.fail(`Attempted to check if the non-enumerable set ${fmt(a)} is a subset of ${fmt(b)}`, n);
        if (a instanceof IntervalV && b instanceof IntervalV) return a.hi < a.lo || (a.lo >= b.lo && a.hi <= b.hi);
        for (const x of a.elems()) if (!b.contains(x)) return false;
        return true;
      }
      case O_cup: return this.setUnion(this.evalSet(n.a[0], ctx), this.evalSet(n.a[1], ctx));
      case O_cap: {
        const a = this.evalSet(n.a[0], ctx), b = this.evalSet(n.a[1], ctx);
        if (reducible(a) && reducible(b)) return new SetV(a.elems().filter(x => b.contains(x)));
        const gen = a.enumerable() ? () => a.elems().filter(x => b.contains(x)) : b.enumerable() ? () => b.elems().filter(x => a.contains(x)) : null;
        return new DerivedSetV(`${fmt(a)} \\cap ${fmt(b)}`, v => a.contains(v) && b.contains(v), gen);
      }
      case O_diff: {
        const a = this.evalSet(n.a[0], ctx), b = this.evalSet(n.a[1], ctx);
        if (reducible(a)) return new SetV(a.elems().filter(x => !b.contains(x)));
        return new DerivedSetV(`${fmt(a)} \\ ${fmt(b)}`, v => a.contains(v) && !b.contains(v), a.enumerable() ? () => a.elems().filter(x => !b.contains(x)) : null);
      }
      case O_powerset: return new SubsetV(this.evalSet(n.a[0], ctx));
      case O_bigunion: {
        const s = this.evalElems(n.a[0], ctx);
        const all: Value[] = [];
        let lazy = false;
        for (const x of s) {
          if (!(x instanceof SetBase)) return this.fail(`Attempted to apply UNION to a set containing the non-set value ${fmt(x)}`, n);
          if (!(x instanceof SetV)) { lazy = true; break; }
          for (const y of x.elems()) all.push(y);
        }
        if (lazy) {
          // like TLC's UnionValue: membership is tested against the member sets, enumeration is on demand
          const sets = s as SetBase[];
          return new DerivedSetV("UNION ...", v => { for (const x of sets) if (x.contains(v)) return true; return false; },
            sets.every(x => x.enumerable()) ? () => { const out: Value[] = []; for (const x of sets) for (const y of x.elems()) out.push(y); return out; } : null);
        }
        return mkSet(all);
      }
      case O_domain: {
        const f = tailFn(n.a[0]) ? this.evalLazy(n.a[0], ctx) : n.a[0].k === 'app' ? this.evalApp(n.a[0], ctx) : this.eval(n.a[0], ctx);
        if (f instanceof LazyFcn) return f.domain();
        const d = domainOf(f);
        if (d === null) return this.fail(`Attempted to apply the operator DOMAIN to the non-function value\n${fmt(f)}`, n);
        return d;
      }
      case O_prime: {
        if (this.nxt === null) return this.fail('Attempted to evaluate a primed expression where no next state is available (the expression is not a state-level expression).', n);
        const sc = this.cur, sn = this.nxt, im = this.initMode;
        this.cur = sn; this.nxt = null; this.primeDepth++; this.initMode = false;
        try {
          return this.eval(n.a[0], ctx);
        } finally {
          this.cur = sc; this.nxt = sn; this.primeDepth--; this.initMode = im;
        }
      }
      case O_enabled: return this.enabled(n.a[0], ctx);
      case O_unchanged: {
        const e = n.a[0];
        const v0 = this.eval(e, ctx);
        if (this.nxt === null) return this.fail('Attempted to evaluate UNCHANGED where no next state is available.', n);
        const sc = this.cur, sn = this.nxt;
        this.cur = sn; this.nxt = null; this.primeDepth++;
        try {
          return valEq(this.eval(e, ctx), v0);
        } finally {
          this.cur = sc; this.nxt = sn; this.primeDepth--;
        }
      }
      case O_cross: return new CrossV(n.a.map((x: Node) => this.evalSet(x, ctx)));
      case O_if: return this.evalBool(n.a[0], ctx) ? this.eval(n.a[1], ctx) : this.eval(n.a[2], ctx);
      case O_case: {
        for (const arm of n.arms) if (this.evalBool(arm.c, ctx)) return this.eval(arm.e, ctx);
        if (n.other) return this.eval(n.other, ctx);
        return this.fail('Attempted to evaluate a CASE expression in which none of the conditions were true.', n);
      }
      case O_let: return this.eval(n.body, this.bindLet(n.defs, ctx));
      case O_quant: {
        const body = n.body;
        if (n.q === 'A') return !this.forBindings(n.bounds, ctx, c => !this.evalBool(body, c));
        return this.forBindings(n.bounds, ctx, c => this.evalBool(body, c));
      }
      case O_choose: {
        const b = n.bound as Bound;
        if (b.set === null) return this.fail('TLC attempted to evaluate an unbounded CHOOSE.\nMake sure that the expression is of form CHOOSE x \\in S: P(x).', n);
        const es = this.evalElems(b.set, ctx);
        for (let i = 0; i < es.length; i++) {
          const c = b.tuple ? this.bindTuple(b.tuple, es[i], ctx) : new Ctx(b.names![0], es[i], ctx);
          if (this.evalBool(n.body, c)) return es[i];
        }
        return this.fail(`Attempted to compute the value of an expression of form\nCHOOSE x \\in S: P, but no element of S satisfied P.`, n);
      }
      case O_setenum: {
        const a = n.a;
        const out: Value[] = new Array(a.length);
        for (let i = 0; i < a.length; i++) out[i] = this.eval(a[i], ctx);
        return mkSet(out);
      }
      case O_setfilter: {
        const b = n.bound as Bound;
        const s = this.evalSet(b.set!, ctx);
        const pred = n.pred;
        if (!reducible(s)) {
          const test = (v: Value) => this.evalBool(pred, b.tuple ? this.bindTuple(b.tuple, v, ctx) : cons(b.names![0], v, ctx));
          // the predicate may depend on the state: capture it for later (lazy) evaluation
          const sc = this.cur, sn = this.nxt;
          const inState = <T>(f: () => T): T => {
            const c0 = this.cur, n0 = this.nxt;
            this.cur = sc; this.nxt = sn;
            try { return f(); } finally { this.cur = c0; this.nxt = n0; }
          };
          return new DerivedSetV(`{x \\in ${fmt(s)} : ...}`, v => s.contains(v) && inState(() => test(v)),
            s.enumerable() ? () => inState(() => s.elems().filter(test)) : null);
        }
        const es = s.elems();
        const out: Value[] = [];
        for (let i = 0; i < es.length; i++) {
          const c = b.tuple ? this.bindTuple(b.tuple, es[i], ctx) : new Ctx(b.names![0], es[i], ctx);
          if (this.evalBool(pred, c)) out.push(es[i]);
        }
        return new SetV(out);
      }
      case O_setmap: {
        const out: Value[] = [];
        const e = n.e;
        this.forBindings(n.bounds, ctx, c => { out.push(this.eval(e, c)); return false; });
        return mkSet(out);
      }
      case O_fndef: return this.evalFnDef(n, ctx);
      case O_fnset: return new FcnSetV(this.evalSet(n.a[0], ctx), this.evalSet(n.a[1], ctx));
      case O_rec: {
        const fs = n.fields;
        const names: string[] = new Array(fs.length), vals: Value[] = new Array(fs.length);
        for (let i = 0; i < fs.length; i++) { names[i] = fs[i].name; vals[i] = this.eval(fs[i].e, ctx); }
        return this.mkRecord(n, names, vals);
      }
      case O_recset: {
        const fs = n.fields as { name: string; e: Node }[];
        const idx = fs.map((_, i) => i).sort((i, j) => strId(fs[i].name) - strId(fs[j].name));
        return new RecSetV(idx.map(i => fs[i].name), idx.map(i => this.evalSet(fs[i].e, ctx)));
      }
      case O_except: {
        let f = this.eval(n.base, ctx);
        for (const u of n.updates) {
          const path: Value[] = u.path.map((p: Node) => this.eval(p, ctx));
          f = this.exceptUpdate(f, path, 0, u.val, ctx, n);
        }
        return f;
      }
      case O_tuple: {
        const a = n.a;
        const out: Value[] = new Array(a.length);
        for (let i = 0; i < a.length; i++) out[i] = this.eval(a[i], ctx);
        return new TupleV(out);
      }
      case O_fnapp: {
        const fn = n.f;
        let tf = fn.tf;
        if (tf === undefined) tf = tailFn(fn);
        const f = tf ? this.evalLazy(fn, ctx) : fn.k === 'app' ? this.evalApp(fn, ctx) : this.eval(fn, ctx);
        let arg: Value;
        if (n.args.length === 1) arg = this.eval(n.args[0], ctx);
        else arg = new TupleV(n.args.map((a: Node) => this.eval(a, ctx)));
        const v = this.applyFcn(f, arg, n);
        if (typeof v === 'object' && v instanceof LazyFcn) return v.force();
        return v;
      }
      case O_dot: {
        const r = this.eval(n.e, ctx);
        if (r instanceof RecordV) {
          const v = r.get(n.field);
          if (v === undefined) return this.fail(`Attempted to access nonexistent field '${n.field}' of record\n${fmt(r)}`, n);
          return v;
        }
        return this.fail(`Attempted to select field '${n.field}' from the non-record value ${fmt(r)}`, n);
      }
      case O_boxact: return this.evalBool(n.a[0], ctx) || this.unchangedVal(n.a[1], ctx);
      case O_angleact: return this.evalBool(n.a[0], ctx) && !this.unchangedVal(n.a[1], ctx);
      case O_lambda: return new Closure(n.params, n.body, ctx);
      case O_at: return this.lookup(ctx, '@');
    }
    if (n.k === 'cdot') {
      try {
        this.enumerate(n, ctx, () => { throw FOUND; });
        return false;
      } catch (e) {
        if (e === FOUND) return true;
        throw e;
      }
    }
    if (n.k === 'always' || n.k === 'eventually' || n.k === 'leadsto' || n.k === 'wf' || n.k === 'sf' || n.k === 'guarantee' || n.k === 'tquant') {
      return this.fail('TLC attempted to evaluate a temporal formula where a state or action-level expression was expected.', n);
    }
    return this.fail(`TLC does not support the construct '${n.k}' here.`, n);
  }

  // Evaluate in TLC's "keep lazy" mode: a function constructor reached through IF/CASE/LET/definitions is
  // returned as an unevaluated LazyFcn (the caller applies it, takes its DOMAIN or enumerates its body).
  evalLazy(n: Node, ctx: Ctx | null): Value {
    switch (n.k) {
      case 'fndef': return new LazyFcn(n, ctx, this);
      case 'if': return this.evalBool(n.a[0], ctx) ? this.evalLazy(n.a[1], ctx) : this.evalLazy(n.a[2], ctx);
      case 'case': {
        for (const arm of n.arms) if (this.evalBool(arm.c, ctx)) return this.evalLazy(arm.e, ctx);
        if (n.other) return this.evalLazy(n.other, ctx);
        return this.fail('Attempted to evaluate a CASE expression in which none of the conditions were true.', n);
      }
      case 'let': return this.evalLazy(n.body, this.bindLet(n.defs, ctx));
      case 'fnapp': {
        if (!tailFn(n)) break;
        const f = this.evalLazy(n.f, ctx);
        const arg = n.args.length === 1 ? this.eval(n.args[0], ctx) : new TupleV(n.args.map((a: Node) => this.eval(a, ctx)));
        return f instanceof LazyFcn ? f.apply(arg, true) : this.applyFcn(f, arg, n);
      }
      case 'app': {
        if (!tailFn(n)) return this.evalApp(n, ctx);
        const r = n.r as any;
        if (r === LOCAL) {
          const b = this.lookup(ctx, n.name);
          return b instanceof Lazy ? this.force(b, true) : this.evalApp(n, ctx);
        }
        let def: Def = r.override ?? r;
        if (def.builtin) break;
        const top = def.params.length === 0 && !def.inst && (ctx === null || ctx.base === null);
        if (top && def.cached) return def.cache;
        const x = this.expandApp(n, ctx);
        if (!x) break;
        const s0 = this.stTouch, p0 = this.prTouch;
        const v = this.evalLazy(x.body, x.ctx);
        if (top && defLevel(def) === 0 && this.stTouch === s0 && this.prTouch === p0) {
          // a constant: evaluate it completely once (TLC precomputes constant definitions), unless that fails
          let w = v;
          if (v instanceof LazyFcn) {
            try { w = v.force(); } catch (e) { if (!(e instanceof TlaError)) throw e; }
            if (this.stTouch !== s0 || this.prTouch !== p0) return v;
          }
          def.cached = true; def.cache = w;
          return w;
        }
        return v;
      }
    }
    return this.eval(n, ctx);
  }

  mkRecord(_n: Node, names: string[], vals: Value[]): Value {
    return makeRecord(names, vals);
  }

  unchangedVal(e: Node, ctx: Ctx | null): boolean {
    const v0 = this.eval(e, ctx);
    if (this.nxt === null) return this.fail('Attempted to evaluate an action where no next state is available.', e);
    const sc = this.cur, sn = this.nxt;
    this.cur = sn; this.nxt = null; this.primeDepth++;
    try {
      return valEq(this.eval(e, ctx), v0);
    } finally {
      this.cur = sc; this.nxt = sn; this.primeDepth--;
    }
  }

  setUnion(a: SetBase, b: SetBase): SetBase {
    if (!reducible(a) || !reducible(b)) {
      return new DerivedSetV(`${fmt(a)} \\cup ${fmt(b)}`, v => a.contains(v) || b.contains(v), a.enumerable() && b.enumerable() ? () => a.elems().concat(b.elems()) : null);
    }
    const x = a.elems(), y = b.elems();
    if (x.length === 0) return b;
    if (y.length === 0) return a;
    const out: Value[] = [];
    let i = 0, j = 0;
    while (i < x.length && j < y.length) {
      const c = compare(x[i], y[j]);
      if (c < 0) out.push(x[i++]);
      else if (c > 0) out.push(y[j++]);
      else { out.push(x[i++]); j++; }
    }
    while (i < x.length) out.push(x[i++]);
    while (j < y.length) out.push(y[j++]);
    return new SetV(out);
  }

  evalFnDef(n: Node, ctx: Ctx | null): Value {
    const bounds = n.bounds as Bound[];
    if (n.isRec) return new LazyFcn(n, ctx, this);
    if (bounds.length === 1 && (bounds[0].tuple || bounds[0].names!.length === 1)) {
      const b = bounds[0];
      const s = this.evalSet(b.set!, ctx);
      if (!s.enumerable()) return new LazyFcn(n, ctx, this);
      const dom = s.elems();
      const vals: Value[] = new Array(dom.length);
      const body = n.body;
      if (b.tuple) for (let i = 0; i < dom.length; i++) vals[i] = this.eval(body, this.bindTuple(b.tuple, dom[i], ctx));
      else {
        const name = b.names![0];
        for (let i = 0; i < dom.length; i++) vals[i] = this.eval(body, new Ctx(name, dom[i], ctx));
      }
      return makeFcn(dom, vals);
    }
    const dom: Value[] = [], vals: Value[] = [];
    const sets: Value[][] = [];
    const bsets: SetBase[] = [];
    for (const b of bounds) {
      const bs = this.evalSet(b.set!, ctx);
      if (!bs.enumerable()) return new LazyFcn(n, ctx, this);
      bsets.push(bs);
    }
    for (let bi = 0; bi < bounds.length; bi++) {
      const b = bounds[bi];
      const es = bsets[bi].elems();
      const cnt = b.tuple ? 1 : b.names!.length;
      for (let j = 0; j < cnt; j++) sets.push(es);
    }
    const names: (string | string[])[] = [];
    for (const b of bounds) { if (b.tuple) names.push(b.tuple); else names.push(...b.names!); }
    const cur: Value[] = [];
    const rec = (i: number, c: Ctx | null) => {
      if (i === sets.length) { dom.push(new TupleV(cur.slice())); vals.push(this.eval(n.body, c)); return; }
      const nm = names[i];
      for (const v of sets[i]) {
        cur.push(v);
        rec(i + 1, typeof nm === 'string' ? cons(nm, v, c) : this.bindTuple(nm, v, c));
        cur.pop();
      }
    };
    rec(0, ctx);
    return makeFcn(dom, vals);
  }

  applyFcn(f: Value, arg: Value, n?: Node): Value {
    if (f instanceof TupleV) {
      if (typeof arg === 'number' && arg >= 1 && arg <= f.e.length && Number.isInteger(arg)) return f.e[arg - 1];
      return this.fail(typeof arg === 'number' ? `Attempted to apply tuple\n${fmt(f)}\nto integer ${arg} which is out of domain.` : `Attempted to apply tuple\n${fmt(f)}\nto non-integer argument ${fmt(arg)}`, n);
    }
    if (f instanceof RecordV) {
      if (typeof arg === 'string') {
        const v = f.get(arg);
        if (v !== undefined) return v;
      }
      return this.fail(`Attempted to apply function:\n${fmt(f)}\nto argument ${fmt(arg)}, which is not in the domain of the function.`, n);
    }
    if (f instanceof FcnV) {
      const i = bsearch(f.dom, arg);
      if (i >= 0) return f.vals[i];
      return this.fail(`Attempted to apply function:\n${fmt(f)}\nto argument ${fmt(arg)}, which is not in the domain of the function.`, n);
    }
    if (f instanceof LazyFcn) return f.apply(arg);
    if (f instanceof Closure || f instanceof DefRef) return this.fail('Attempted to apply an operator as if it were a function (use parentheses, not brackets).', n);
    return this.fail(`A non-function (${fmt(f)}) was applied as a function.`, n);
  }

  exceptUpdate(f: Value, path: Value[], i: number, valNode: Node, ctx: Ctx | null, n: Node): Value {
    const key = path[i];
    const last = i === path.length - 1;
    const upd = (old: Value) => last ? this.eval(valNode, cons('@', old, ctx)) : this.exceptUpdate(old, path, i + 1, valNode, ctx, n);
    if (f instanceof TupleV) {
      if (typeof key !== 'number' || key < 1 || key > f.e.length) return f;
      const e = f.e.slice();
      e[key - 1] = upd(e[key - 1]);
      return new TupleV(e);
    }
    if (f instanceof RecordV) {
      const k = typeof key === 'string' ? f.names.indexOf(key) : -1;
      if (k < 0) return f;
      const vals = f.vals.slice();
      vals[k] = upd(vals[k]);
      return new RecordV(f.names, vals);
    }
    if (f instanceof FcnV) {
      const k = bsearch(f.dom, key);
      if (k < 0) return f;
      const vals = f.vals.slice();
      vals[k] = upd(vals[k]);
      return new FcnV(f.dom, vals);
    }
    if (f instanceof LazyFcn) {
      const d = f.domain();
      if (d.enumerable()) return this.exceptUpdate(f.force(), path, i, valNode, ctx, n);
      if (!d.contains(key)) return f;
      return f.withOverride(key, upd(f.apply(key)));
    }
    return this.fail(`Attempted to apply EXCEPT to the non-function value\n${fmt(f)}`, n);
  }

  // ---------- ENABLED ----------
  enabled(a: Node, ctx: Ctx | null): boolean {
    const sn = this.nxt, im = this.initMode, na = this.nAssigned, cd = this.callDepth;
    if (ctx !== null && ctx.base !== null && ctx.base.name !== ENABLED_MARK) {
      // mark the instance environment the ENABLED is evaluated in (see asVar)
      const env = new Ctx(ENABLED_MARK, true, ctx.base);
      env.base = env;
      ctx = new Ctx(ENABLED_MARK, true, ctx);
      ctx.base = env;
    }
    this.nxt = new Array(this.nvars);
    this.initMode = false;
    this.nAssigned = -1e9; // no all-assigned shortcut inside ENABLED
    this.inEnabled++;
    try {
      this.enumerate(a, ctx, () => { throw FOUND; });
      return false;
    } catch (e) {
      if (e === FOUND) return true;
      throw e;
    } finally {
      this.nxt = sn; this.initMode = im; this.nAssigned = na; this.callDepth = cd; this.inEnabled--;
    }
  }

  // ---------- action / initial-predicate enumeration ----------
  // Resolve an expression to a variable index if it denotes a variable (possibly through substitutions).
  asVar(e: Node, ctx: Ctx | null): number {
    for (let guard = 0; guard < 100; guard++) {
      if (e.k === 'let') { ctx = this.bindLet(e.defs, ctx); e = e.body; continue; }
      if (e.k !== 'app' || e.args.length !== 0 || e.sel) return -1;
      const r = e.r as any;
      if (r === LOCAL) {
        const b = this.lookup(ctx, e.name);
        if (b instanceof Lazy) { e = b.e; ctx = b.ctx; continue; }
        return -1;
      }
      if (r.k === 'def') {
        const x = this.expandApp(e, ctx);
        if (!x) return -1;
        e = x.body; ctx = x.ctx; continue;
      }
      if (r.k !== 'var') return -1;
      const base = ctx === null ? null : ctx.base;
      if (base !== null) {
        const b = this.envLookup(base, e.name);
        if (b instanceof Lazy) {
          if (base.name === ENABLED_MARK) {
            // Like TLC's context cut-off: a variable of an instantiated module that is reached from inside an
            // ENABLED evaluated in that module stands for itself, not for the expression substituted for it.
            let si = this.scratch.get(r);
            if (si === undefined) { si = this.nvars + this.scratch.size; this.scratch.set(r, si); }
            return si;
          }
          e = b.e; ctx = b.ctx; continue;
        }
        if (b !== undefined) return -1;
      }
      return (r as Decl).idx;
    }
    return -1;
  }

  // Enumerate all ways of satisfying `e`, assigning unassigned target variables (primed variables in
  // next-state mode, unprimed variables in init mode). Calls k for each satisfying (partial) assignment.
  enumerate(e: Node, ctx: Ctx | null, k: () => void): void {
    // Like TLC: once every variable is assigned, the remaining conjuncts are plain predicates.
    if (this.nAssigned === this.nvars && e.k !== 'cdot') { if (this.evalBool(e, ctx)) k(); return; }
    switch (e.k) {
      case 'cdot': {
        // s -(A \cdot B)-> u  iff  there is a t with  s -A-> t  and  t -B-> u
        if (this.initMode) break;
        const sc = this.cur, sn = this.nxt, na = this.nAssigned;
        const mids: Value[][] = [];
        const mid: Value[] = new Array(this.nvars);
        this.nxt = mid; this.nAssigned = 0;
        try {
          this.enumerate(e.a[0], ctx, () => {
            for (let i = 0; i < this.nvars; i++) if (mid[i] === undefined) this.fail('The first action of an action composition (\\cdot) does not completely specify the intermediate state.', e);
            mids.push(mid.slice());
          });
        } finally { this.nxt = sn; this.nAssigned = na; }
        if (this.inEnabled === 0) this.extraGenerated += mids.length;
        for (const t of mids) {
          this.cur = t;
          try {
            this.enumerate(e.a[1], ctx, () => {
              const c = this.cur;
              this.cur = sc;
              try { k(); } finally { this.cur = c; }
            });
          } finally { this.cur = sc; }
        }
        return;
      }
      case 'and': this.enumConj(e.a, 0, ctx, k); return;
      case 'or': for (const d of e.a) this.enumerate(d, ctx, k); return;
      case 'quant':
        if (e.q === 'E') {
          this.forBindings(e.bounds, ctx, c => { this.enumerate(e.body, c, k); return false; });
          return;
        }
        {
          // \A is a conjunction over all bindings
          const ctxs: (Ctx | null)[] = [];
          this.forBindings(e.bounds, ctx, c => { ctxs.push(c); return false; });
          const go = (i: number): void => {
            if (i === ctxs.length) { k(); return; }
            this.enumerate(e.body, ctxs[i], () => go(i + 1));
          };
          go(0);
          return;
        }
      case 'imp':
        if (!this.evalBool(e.a[0], ctx)) k(); else this.enumerate(e.a[1], ctx, k);
        return;
      case 'subseteq': {
        const tgt = this.targetVar(e.a[0], ctx);
        if (tgt >= 0) {
          const arr = this.initMode ? this.cur : this.nxt!;
          if (arr[tgt] === undefined) {
            const es = new SubsetV(this.evalSet(e.a[1], ctx)).elems();
            this.nAssigned++;
            try {
              for (let i = 0; i < es.length; i++) { arr[tgt] = es[i]; k(); }
            } finally { arr[tgt] = undefined; this.nAssigned--; }
            return;
          }
        }
        break;
      }
      case 'if':
        if (this.evalBool(e.a[0], ctx)) this.enumerate(e.a[1], ctx, k); else this.enumerate(e.a[2], ctx, k);
        return;
      case 'case': {
        for (const arm of e.arms) if (this.evalBool(arm.c, ctx)) { this.enumerate(arm.e, ctx, k); return; }
        if (e.other) { this.enumerate(e.other, ctx, k); return; }
        this.fail('Attempted to evaluate a CASE expression in which none of the conditions were true.', e);
        return;
      }
      case 'let': this.enumerate(e.body, this.bindLet(e.defs, ctx), k); return;
      case 'app': {
        const x = this.expandApp(e, ctx);
        if (x) { this.enumerate(x.body, x.ctx, k); return; }
        break;
      }
      case 'eq': {
        const tgt = this.targetVar(e.a[0], ctx);
        if (tgt >= 0) {
          const arr = this.initMode ? this.cur : this.nxt!;
          if (arr[tgt] === undefined) {
            const v = this.eval(e.a[1], ctx);
            arr[tgt] = v;
            this.nAssigned++;
            try { k(); } finally { arr[tgt] = undefined; this.nAssigned--; }
            return;
          }
        }
        break;
      }
      case 'in': {
        const tgt = this.targetVar(e.a[0], ctx);
        if (tgt >= 0) {
          const arr = this.initMode ? this.cur : this.nxt!;
          if (arr[tgt] === undefined) {
            const s = this.evalSet(e.a[1], ctx);
            const es = s.elems();
            this.nAssigned++;
            try {
              for (let i = 0; i < es.length; i++) { arr[tgt] = es[i]; k(); }
            } finally { arr[tgt] = undefined; this.nAssigned--; }
            return;
          }
        }
        break;
      }
      case 'unchanged':
        if (!this.initMode) { this.enumUnchanged(e.a[0], ctx, k); return; }
        break;
      case 'fnapp': {
        // TLC enters the body of a lazily evaluated (recursive) function
        const f = tailFn(e.f) ? this.evalLazy(e.f, ctx) : e.f.k === 'app' ? this.evalApp(e.f, ctx) : this.eval(e.f, ctx);
        if (f instanceof LazyFcn) {
          const arg = e.args.length === 1 ? this.eval(e.args[0], ctx) : new TupleV(e.args.map((a: Node) => this.eval(a, ctx)));
          this.enumerate(f.node.body, f.bind(arg), k);
          return;
        }
        break;
      }
      case 'boxact':
        if (!this.initMode) {
          this.enumerate(e.a[0], ctx, k);
          this.enumUnchanged(e.a[1], ctx, k);
          return;
        }
        break;
      case 'angleact':
        if (!this.initMode) {
          this.enumerate(e.a[0], ctx, () => { if (!this.unchangedVal(e.a[1], ctx)) k(); });
          return;
        }
        break;
    }
    if (this.evalBool(e, ctx)) k();
  }

  enumConj(items: Node[], i: number, ctx: Ctx | null, k: () => void): void {
    if (i === items.length) { k(); return; }
    if (i === items.length - 1) { this.enumerate(items[i], ctx, k); return; }
    this.enumerate(items[i], ctx, () => this.enumConj(items, i + 1, ctx, k));
  }

  targetVar(lhs: Node, ctx: Ctx | null): number {
    if (this.initMode) return lhs.k === 'app' ? this.asVar(lhs, ctx) : -1;
    if (this.nxt === null || this.primeDepth > 0) return -1;
    // look through operator parameters bound to primed variables, e.g. Send(p, d, mem, mem')
    for (let guard = 0; guard < 100; guard++) {
      if (lhs.k === 'let') { ctx = this.bindLet(lhs.defs, ctx); lhs = lhs.body; continue; }
      if (lhs.k !== 'app' || lhs.args.length !== 0) break;
      if (lhs.r === LOCAL) {
        const b = this.lookup(ctx, lhs.name);
        if (!(b instanceof Lazy)) return -1;
        lhs = b.e; ctx = b.ctx;
      } else if (lhs.r.k === 'def' && !lhs.sel) {
        // a definition whose body is a primed variable (a == x')
        const x = this.expandApp(lhs, ctx);
        if (!x) return -1;
        lhs = x.body; ctx = x.ctx;
      } else return -1;
    }
    if (lhs.k !== 'prime') return -1;
    return this.asVar(lhs.a[0], ctx);
  }

  enumUnchanged(e: Node, ctx: Ctx | null, k: () => void): void {
    const nxt = this.nxt!;
    if (e.k === 'tuple') {
      const items = e.a as Node[];
      const go = (i: number): void => {
        if (i === items.length) { k(); return; }
        this.enumUnchanged(items[i], ctx, () => go(i + 1));
      };
      go(0);
      return;
    }
    if (e.k === 'app') {
      const idx = this.asVar(e, ctx);
      if (idx >= 0) {
        if (nxt[idx] === undefined) {
          const v = idx >= this.nvars ? this.eval(e, ctx) : this.cur[idx];
          this.stTouch++;
          if (v === undefined) this.fail(`In evaluation, the identifier ${this.varNames[idx]} is either undefined or not an operator.`, e);
          nxt[idx] = v;
          this.nAssigned++;
          try { k(); } finally { nxt[idx] = undefined; this.nAssigned--; }
        } else if (valEq(nxt[idx], idx >= this.nvars ? this.eval(e, ctx) : this.cur[idx])) k();
        return;
      }
      const x = this.expandApp(e, ctx);
      if (x) { this.enumUnchanged(x.body, x.ctx, k); return; }
    }
    if (this.unchangedVal(e, ctx)) k();
  }
}

const NOARGS: any[] = [];
export { cons, TlaError, EMPTY_SET, IntervalV, sortDedup, ModelValue };
