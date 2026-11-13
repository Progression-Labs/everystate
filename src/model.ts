// Builds a checkable model from a root module and a configuration.
import type { Node } from './parser.ts';
import { TlaError } from './lexer.ts';
import type { Loc } from './lexer.ts';
import { Loader, levelOf, defLevel, LOCAL } from './modules.ts';
import type { ModuleInfo, Def, Decl, SourceResolver } from './modules.ts';
import { Evaluator, Ctx, Lazy, Closure, DefRef } from './eval.ts';
import { buildStdlib, globalDefs } from './stdlib.ts';
import { OVERRIDES } from './community.ts';
import type { Config } from './cfg.ts';
import { EvalError, SetBase, ModelValue, isFcn, domainElems, fcnValues, fmt, strId, valEq } from './values.ts';
import type { Value } from './values.ts';

export interface Pred { name: string; e: Node; ctx: Ctx | null }
export interface Action { name: string; params: string; loc: Loc; module: string; e: Node; ctx: Ctx | null }
export interface Model {
  rootName: string;
  root: ModuleInfo;
  loader: Loader;
  ev: Evaluator;
  vars: Decl[];
  inits: Pred[];
  actions: Action[];
  invariants: Pred[];
  impliedInits: Pred[];
  impliedActions: Pred[];
  constraints: Pred[];
  actionConstraints: Pred[];
  fairness: Pred[];
  liveProps: Pred[];
  symmetry: Map<ModelValue, ModelValue>[] | null;
  view: Pred | null;
  alias: Pred | null;
  postconditions: (Pred & { possible?: boolean; loc: Loc; module: string })[];
  checkDeadlock: boolean;
  warnings: string[];
}

export class ConfigError extends TlaError {
  constructor(msg: string) { super(msg, undefined, undefined, 'config'); }
}

export function locStr(loc: Loc, module: string): string {
  return `line ${loc[0]}, col ${loc[1]} to line ${loc[2]}, col ${loc[3]} of module ${module}`;
}

export function buildModel(rootName: string, resolve: SourceResolver, cfg: Config, io: { print: (s: string) => void }): Model {
  const loader = new Loader(resolve, buildStdlib(io));
  loader.globals = globalDefs();
  const root = loader.load(rootName);
  // native overrides for bundled modules
  for (const [mname, ops] of Object.entries(OVERRIDES)) {
    const m = loader.modules.get(mname);
    if (!m) continue;
    for (const [name, [fn, opts]] of Object.entries(ops)) {
      const d = m.syms.get(name);
      if (d && d.k === 'def') d.builtin = { fn, ...opts };
    }
  }
  const ev = new Evaluator();
  const vars = tlcVariableOrder(root);
  vars.forEach((v, i) => { v.idx = i; });
  ev.nvars = vars.length;
  ev.varNames = vars.map(v => v.name);
  const warnings: string[] = [];

  const mkApp = (name: string, def: Def | Decl): Node => ({ k: 'app', loc: (def as Def).loc ?? [0, 0, 0, 0], name, args: [], r: def });
  const getDef = (name: string, what: string): Def => {
    const s = root.syms.get(name);
    if (!s) throw new ConfigError(`The ${what} ${name} specified in the configuration file\nis not defined in the specification.`);
    if (s.k === 'var') throw new ConfigError(`The ${what} ${name} specified in the configuration file\nis not a defined operator.`);
    return s as Def;
  };

  // ---- constants ----
  const opTables = new Map<Decl, { args: Value[]; value: Value }[]>();
  for (const c of cfg.constants) {
    const scope = c.module ? loader.modules.get(c.module) : root;
    const s = scope?.syms.get(c.name);
    if (!s) {
      if (c.subst !== undefined) throw new ConfigError(`The constant parameter ${c.name} is not a constant or operator of the specification.`);
      continue; // e.g. `a = a` just declares a model value
    }
    if (c.args) {
      // F(v1, ..., vn) = value lines define a constant operator by a table
      if (s.k !== 'const') throw new ConfigError(`The constant parameter ${c.name} is not a constant operator of the specification.`);
      let tbl = opTables.get(s);
      if (!tbl) {
        tbl = [];
        opTables.set(s, tbl);
        const rows = tbl, nm = c.name;
        const params = c.args.map((_, i) => ({ name: `p${i}`, arity: 0 }));
        s.subst = { k: 'def', name: nm, params, body: null, module: s.module, local: false, loc: [0, 0, 0, 0], builtin: { fn: (_ev: any, a: any[]) => {
          for (const r of rows) if (r.args.every((x, i) => valEq(x, a[i]))) return r.value;
          throw new EvalError(`Attempted to apply the operator ${nm} to arguments (${a.map(x => fmt(x)).join(', ')}) for which the configuration file gives no value.`);
        } } };
      } else if (tbl[0].args.length !== c.args.length) throw new ConfigError(`The constant ${c.name} is given values with inconsistent arities in the configuration file.`);
      tbl.push({ args: c.args, value: c.value });
      continue;
    }
    if (c.subst !== undefined) {
      const target = root.syms.get(c.subst);
      if (!target || target.k !== 'def') throw new ConfigError(`The configuration file substitutes for ${c.name} with the undefined identifier ${c.subst}.`);
      if (s.k === 'const') s.subst = target;
      else if (s.k === 'def') s.override = target;
    } else if (s.k === 'const') {
      if (s.arity > 0) throw new ConfigError(`The constant operator ${c.name} cannot be assigned a value; use <- to substitute an operator.`);
      s.value = c.value;
      s.hasValue = true;
    } else if (s.k === 'def') {
      const value = c.value;
      s.override = { k: 'def', name: s.name, params: [], body: null, module: s.module, local: false, loc: s.loc, builtin: { fn: () => value } };
    }
  }
  // A constant replaced by a definition that is not constant-level (TLC evaluates the replacement at startup).
  for (const c of cfg.constants) {
    if (c.subst === undefined) continue;
    const s = (c.module ? loader.modules.get(c.module) : root)?.syms.get(c.name);
    if (!s || s.k !== 'const' || !s.subst || s.subst.params.length !== 0 || s.subst.builtin) continue;
    const s0 = ev.stTouch;
    try {
      ev.cur = []; ev.nxt = null; ev.initMode = false;
      ev.eval(mkApp(c.subst, s.subst), null);
    } catch (e) {
      if (!(e instanceof TlaError)) { if (e instanceof RangeError) continue; throw e; }
      if (defLevel(s.subst) > 0 || ev.stTouch !== s0) {
        throw new ConfigError(`The configuration file substitutes constant ${c.name} with non-constant ${c.subst} - specifically: ${e.message}`);
      }
    }
  }
  for (const c of root.consts) {
    if (!c.hasValue && !c.subst) {
      throw new ConfigError(`The constant parameter ${c.name} is not assigned a value by the configuration file.`);
    }
  }

  // SANY's level check: a temporal operator may not be applied to an action (no "raw TLA")
  {
    const errs: string[] = [];
    const walk = (x: any): void => {
      if (!x || typeof x !== 'object') return;
      if (Array.isArray(x)) { for (const y of x) walk(y); return; }
      if ((x.k === 'always' || x.k === 'eventually' || x.k === 'leadsto' || x.k === 'guarantee') && x.loc) {
        for (const a of x.a as Node[]) {
          if (a.k !== 'boxact' && a.k !== 'angleact' && levelOf(a) === 2) {
            errs.push(`line ${a.loc[0]}, col ${a.loc[1]} to line ${a.loc[2]}, col ${a.loc[3]} of module ${a.mod ?? rootName}\n\nAction used where only temporal formula or state predicate allowed.`);
          }
        }
      }
      for (const key in x) {
        if (key === 'r' || key === 'loc' || key === 'instDefs' || key === 'ld') continue;
        const v = x[key];
        if (v && typeof v === 'object') walk(v);
      }
    };
    for (const name of loader.loadOrder) for (const d of loader.modules.get(name)!.ownDefs) if (d.body) walk(d.body);
    if (errs.length) throw new TlaError(`Semantic errors:\n\n*** Errors: ${errs.length}\n\n${errs.join('\n\n\n')}`, undefined, rootName, 'semantic');
  }

  const model: Model = {
    rootName, root, loader, ev, vars, inits: [], actions: [], invariants: [], impliedInits: [], impliedActions: [],
    constraints: [], actionConstraints: [], fairness: [], liveProps: [], symmetry: null, view: null, alias: null,
    postconditions: [], checkDeadlock: cfg.checkDeadlock ?? true, warnings,
  };

  // ---- invariants / constraints ----
  for (const n of cfg.invariants) {
    const d = getDef(n, 'invariant');
    if (d.k === 'def' && d.params.length) throw new ConfigError(`The invariant ${n} cannot take arguments.`);
    if (d.k === 'def' && defLevel(d) >= 2) throw new ConfigError(`The invariant ${n} is not a state predicate (it has primed variables or temporal operators).`);
    model.invariants.push({ name: n, e: mkApp(n, d), ctx: null });
  }
  for (const n of cfg.constraints) model.constraints.push({ name: n, e: mkApp(n, getDef(n, 'constraint')), ctx: null });
  for (const n of cfg.actionConstraints) model.actionConstraints.push({ name: n, e: mkApp(n, getDef(n, 'action constraint')), ctx: null });
  if (cfg.view) model.view = { name: cfg.view, e: mkApp(cfg.view, getDef(cfg.view, 'view')), ctx: null };
  if (cfg.alias) model.alias = { name: cfg.alias, e: mkApp(cfg.alias, getDef(cfg.alias, 'alias')), ctx: null };
  const bodyLoc = (d: Def): { loc: Loc; module: string } => {
    let o = d.override ?? d;
    while (o.inst) o = o.inst.orig;
    return { loc: o.body?.loc ?? o.loc, module: o.body?.mod ?? o.module };
  };
  for (const n of cfg.postconditions) {
    const d = getDef(n, 'post condition');
    model.postconditions.push({ name: n, e: mkApp(n, d), ctx: null, ...bodyLoc(d) });
  }
  // _POSSIBLE P: count how often P holds (state predicates: per generated state; actions: per transition) and
  // require a non-zero count once model checking has finished.
  if (cfg.possible.length) {
    const pm = loader.load('_Possible');
    const track = pm.syms.get('_Track') as Def, check = pm.syms.get('_CheckName') as Def;
    const str = (v: string): Node => ({ k: 'str', loc: [0, 0, 0, 0], v });
    for (const n of cfg.possible) {
      const s = root.syms.get(n);
      if (!s) throw new ConfigError(`The possible ${n} specified in the configuration file\nis not defined in the specification.`);
      if (s.k !== 'def') throw new ConfigError(`The possible ${n} specified in the configuration file\nis not a defined operator.`);
      if (s.params.length) throw new ConfigError(`The possible ${n} specified in the configuration file\nrequires arguments.`);
      const lv = defLevel(s);
      if (lv >= 3) throw new ConfigError(`The possible ${n} specified in the configuration file\nis a temporal formula; only state- and action-level predicates are supported.`);
      strId(n);
      const e: Node = { k: 'app', loc: s.loc, name: '_Track', args: [mkApp(n, s), str(n)], r: track };
      (lv <= 1 ? model.constraints : model.actionConstraints).push({ name: n, e, ctx: null });
      model.postconditions.push({ name: n, e: { k: 'app', loc: s.loc, name: '_CheckName', args: [str(n)], r: check }, ctx: null, possible: true, ...bodyLoc(s) });
    }
  }

  // ---- behaviour spec ----
  let nextPred: { e: Node; ctx: Ctx | null; name: string } | null = null;
  const lvl = (e: Node, ctx: Ctx | null): number => exprLevel(ev, e, ctx);

  const processSpec = (e: Node, ctx: Ctx | null, name: string): void => {
    switch (e.k) {
      case 'let': processSpec(e.body, ev.bindLet(e.defs, ctx), name); return;
      case 'app': {
        const x = ev.expandApp(e, ctx);
        if (x) {
          const nm = e.args.length === 0 && e.r !== LOCAL ? e.name : name;
          if (lvl(x.body, x.ctx) <= 1) { model.inits.push({ name: nm, e: x.body, ctx: x.ctx }); return; }
          processSpec(x.body, x.ctx, nm);
          return;
        }
        break;
      }
      case 'and': for (const c of e.a) processSpec(c, ctx, name); return;
      case 'always': {
        const arg = e.a[0];
        if (arg.k === 'boxact') {
          if (nextPred) throw new ConfigError('TLC cannot handle a specification with more than one next-state relation ([][Next]_v conjunct).');
          nextPred = { e: arg.a[0], ctx, name: '' };
          return;
        }
        if (lvl(arg, ctx) <= 1) throw new ConfigError('TLC cannot handle the temporal formula ' + name + ': a []P conjunct with a state predicate P in a specification is not supported (use an INVARIANT instead).');
        model.fairness.push({ name, e, ctx });
        return;
      }
    }
    const l = lvl(e, ctx);
    if (l <= 1) model.inits.push({ name, e, ctx });
    else if (l === 3) model.fairness.push({ name, e, ctx });
    else throw new ConfigError('TLC cannot handle a conjunct of the specification that is an action formula outside [][...]_v.');
  };

  if (cfg.spec !== undefined) {
    if (cfg.init !== undefined || cfg.next !== undefined) throw new ConfigError('The configuration file cannot specify both INIT/NEXT and SPECIFICATION fields.');
    const d = getDef(cfg.spec, 'specification');
    processSpec(mkApp(cfg.spec, d), null, cfg.spec);
  } else {
    if (cfg.init !== undefined) {
      const d = getDef(cfg.init, 'initial predicate');
      model.inits.push({ name: cfg.init, e: mkApp(cfg.init, d), ctx: null });
    }
    if (cfg.next !== undefined) {
      const d = getDef(cfg.next, 'next state action');
      nextPred = { e: mkApp(cfg.next, d), ctx: null, name: cfg.next };
    }
  }
  // a specification without variables has no behaviours to explore: TLC only checks the assumptions
  if (vars.length === 0) { model.inits.length = 0; nextPred = null; }
  const noBehavior = (cfg.spec === undefined && cfg.init === undefined && cfg.next === undefined) || vars.length === 0;
  if (model.inits.length === 0 && !noBehavior) throw new ConfigError('The configuration file did not specify the initial state predicate.');
  if (!nextPred && cfg.spec === undefined && !noBehavior) throw new ConfigError('The configuration file did not specify the next state predicate.');

  // ---- split Next into actions ----
  const paramStr = (def: Def | null, ctx: Ctx | null): string => {
    if (!def || def.params.length === 0) return '';
    const vals: string[] = [];
    for (const p of def.params) {
      try {
        const b = ev.lookup(ctx, p.name);
        vals.push(fmt(ev.unthunk(b)));
      } catch { vals.push('?'); }
    }
    return `(${vals.join(',')})`;
  };
  const split = (e: Node, ctx: Ctx | null, name: string, def: Def | null, module: string): void => {
    const leaf = () => model.actions.push({ name, params: paramStr(def, ctx), loc: e.loc, module, e, ctx });
    switch (e.k) {
      case 'let': split(e.body, ev.bindLet(e.defs, ctx), name, def, module); return;
      case 'app': {
        const r = e.r as any;
        if (r !== LOCAL && r.k === 'def' && !e.sel) {
          let d: Def = r.override ?? r;
          if (!d.builtin) {
            if (e.args.every((a: Node) => lvl(a, ctx) === 0)) {
              try {
                const x = ev.expandApp(e, ctx);
                if (x) {
                  let orig = d;
                  while (orig.inst) orig = orig.inst.orig;
                  split(x.body, x.ctx, e.name, orig, orig.module);
                  return;
                }
              } catch (err) { if (!(err instanceof TlaError)) throw err; }
            }
            model.actions.push({ name: e.name, params: '', loc: e.loc, module, e, ctx });
            return;
          }
          void d;
        }
        break;
      }
      case 'quant':
        if (e.q === 'E') {
          try {
            const ctxs: (Ctx | null)[] = [];
            ev.forBindings(e.bounds, ctx, c => { ctxs.push(c); return false; });
            if (ctxs.length > 0) {
              for (const c of ctxs) split(e.body, c, name, def, module);
              return;
            }
          } catch (err) { if (!(err instanceof TlaError)) throw err; }
        }
        break;
      case 'or': for (const d of e.a) split(d, ctx, name, def, module); return;
    }
    leaf();
  };
  if (nextPred) {
    const np = nextPred as { e: Node; ctx: Ctx | null; name: string };
    split(np.e, np.ctx, np.name || 'Action', null, rootName);
  }

  // ---- properties ----
  const processProp = (e: Node, ctx: Ctx | null, name: string): void => {
    switch (e.k) {
      case 'let': processProp(e.body, ev.bindLet(e.defs, ctx), name); return;
      case 'app': {
        const x = ev.expandApp(e, ctx);
        if (x) { processProp(x.body, x.ctx, e.args.length === 0 && e.r !== LOCAL ? e.name : name); return; }
        break;
      }
      case 'quant':
        if (e.q === 'A' && lvl(e, ctx) === 3) {
          try {
            const ctxs: (Ctx | null)[] = [];
            ev.forBindings(e.bounds, ctx, c => { ctxs.push(c); return false; });
            for (const c of ctxs) processProp(e.body, c, name);
            return;
          } catch (err) { if (!(err instanceof TlaError)) throw err; }
        }
        break;
      case 'and': for (const c of e.a) processProp(c, ctx, name); return;
      case 'always': {
        const arg = e.a[0];
        if (arg.k === 'boxact') { model.impliedActions.push({ name, e: arg, ctx }); return; }
        if (lvl(arg, ctx) < 2) {
          const nm = arg.k === 'app' && arg.args.length === 0 && arg.r !== LOCAL ? arg.name : name;
          model.invariants.push({ name: nm, e: arg, ctx });
          return;
        }
        model.liveProps.push({ name, e, ctx });
        return;
      }
    }
    const l = lvl(e, ctx);
    if (l <= 1) model.impliedInits.push({ name, e, ctx });
    else if (l === 3) model.liveProps.push({ name, e, ctx });
    else throw new ConfigError(`The property ${name} is an action-level formula; TLC can only check action properties of the form [][A]_v.`);
  };
  for (const n of cfg.properties) processProp(mkApp(n, getDef(n, 'property')), null, n);

  // ---- symmetry ----
  if (cfg.symmetry) {
    const d = getDef(cfg.symmetry, 'symmetry function');
    ev.cur = []; ev.nxt = null;
    const v = ev.eval(mkApp(cfg.symmetry, d), null);
    if (!(v instanceof SetBase)) throw new ConfigError(`The symmetry operator ${cfg.symmetry} must evaluate to a set of permutations.`);
    const perms: Map<ModelValue, ModelValue>[] = [];
    for (const f of v.elems()) {
      if (!isFcn(f)) throw new ConfigError('Symmetry function must have model values as domain and range.');
      const dom = domainElems(f), rng = fcnValues(f);
      const m = new Map<ModelValue, ModelValue>();
      let identity = true;
      for (let i = 0; i < dom.length; i++) {
        if (!(dom[i] instanceof ModelValue) || !(rng[i] instanceof ModelValue)) throw new ConfigError('Symmetry function must have model values as domain and range.');
        m.set(dom[i], rng[i]);
        if (dom[i] !== rng[i]) identity = false;
      }
      if (!identity) perms.push(m);
    }
    // close the generators under composition (TLC computes the generated group)
    const key = (m: Map<ModelValue, ModelValue>) => [...m.entries()].filter(([a, b]) => a !== b).map(([a, b]) => `${a.id}>${b.id}`).sort().join(',');
    const seenPerms = new Set<string>(['']);
    const group: Map<ModelValue, ModelValue>[] = [];
    for (const g of perms) { const k = key(g); if (!seenPerms.has(k)) { seenPerms.add(k); group.push(g); } }
    const gens = group.slice();
    for (let i = 0; i < group.length; i++) {
      for (const g of gens) {
        const c = new Map<ModelValue, ModelValue>();
        for (const [a, b] of group[i]) c.set(a, g.get(b) ?? b);
        for (const [a, b] of g) if (!c.has(a)) c.set(a, b);
        const k = key(c);
        if (!seenPerms.has(k)) { seenPerms.add(k); group.push(c); }
      }
    }
    model.symmetry = group.length ? group : null;
  }
  void EvalError; void Lazy; void Closure; void DefRef;
  return model;
}

// Level of an expression in a context: like levelOf, but looks through locally bound thunks.
export function exprLevel(ev: Evaluator, e: Node, ctx: Ctx | null): number {
  const seen = new Set<Node>();
  const go = (n: Node, c: Ctx | null): number => {
    let l = levelOf(n);
    if (l >= 3) return l;
    // local references may be bound to higher-level thunks
    const visit = (x: Node, cc: Ctx | null): void => {
      if (l >= 3 || !x || typeof x !== 'object') return;
      if (x.k === 'app') {
        if (x.r === LOCAL) {
          let b: any;
          try { b = ev.lookup(cc, x.name); } catch { b = undefined; }
          if (b instanceof Lazy && !seen.has(b.e)) { seen.add(b.e); l = Math.max(l, go(b.e, b.ctx)); }
        } else if (x.r && x.r.k !== 'def' && cc && cc.base) {
          const b = ev.envLookup(cc.base, x.name);
          if (b instanceof Lazy && !seen.has(b.e)) { seen.add(b.e); l = Math.max(l, go(b.e, b.ctx)); }
        } else if (x.r && x.r.k === 'def' && cc && cc.base && !x.r.builtin && x.r.body && !seen.has(x.r.body)) {
          seen.add(x.r.body);
          visit(x.r.body, cc.base);
        }
      }
      for (const key of ['a', 'args']) if (Array.isArray(x[key])) for (const y of x[key]) visit(y, cc);
      for (const key of ['body', 'e', 'f', 'base', 'pred', 'other']) if (x[key] && typeof x[key] === 'object' && x[key].k) visit(x[key], cc);
      if (x.arms) for (const arm of x.arms) { visit(arm.c, cc); visit(arm.e, cc); }
      if (x.fields) for (const f of x.fields) visit(f.e, cc);
      if (x.bounds) for (const b of x.bounds) if (b.set) visit(b.set, cc);
      if (x.bound && x.bound.set) visit(x.bound.set, cc);
      if (x.defs) for (const d of x.defs) visit(d.body, cc);
      if (x.updates) for (const u of x.updates) { for (const p of u.path) visit(p, cc); visit(u.val, cc); }
    };
    visit(n, c);
    return l;
  };
  return go(e, ctx);
}

// TLC lists variables in the iteration order of SANY's symbol Hashtable for the root module, so the
// order depends on Java's String.hashCode of each name and on the table capacity, which in turn
// depends on how many symbols the module context holds. Reproduced here so that printed states match.
const STD_SYMBOLS: Record<string, number> = {
  Naturals: 12, Integers: 2, Reals: 3, Sequences: 8, FiniteSets: 2, TLC: 14, Bags: 12, TLCExt: 14, Randomization: 4,
};
function javaHash(s: string): number {
  let h = 0;
  for (let i = 0; i < s.length; i++) h = (Math.imul(h, 31) + s.charCodeAt(i)) | 0;
  return h & 0x7fffffff;
}
export function tlcVariableOrder(root: ModuleInfo): Decl[] {
  let count = 72; // built-in operators in SANY's initial context
  const std = new Set<string>();
  for (const sym of new Set(root.syms.values())) {
    if (sym.k === 'def' && sym.builtin && STD_SYMBOLS[sym.module] !== undefined) std.add(sym.module);
    else count++;
  }
  for (const m of std) count += STD_SYMBOLS[m];
  let cap = 11;
  while (count > Math.floor(cap * 0.75)) cap = cap * 2 + 1;
  return root.vars.map((v, i) => ({ v, b: javaHash(v.name) % cap, i })).sort((x, y) => x.b - y.b || x.i - y.i).map(x => x.v);
}
