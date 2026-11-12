// Module loading, symbol tables and static name resolution.
import { parseModule } from './parser.ts';
import type { Node, Param, DefNode, ModuleNode, Bound } from './parser.ts';
import { TlaError } from './lexer.ts';
import type { Loc } from './lexer.ts';
import type { Value } from './values.ts';
import { strId } from './values.ts';

export interface Decl {
  k: 'const' | 'var';
  name: string;
  arity: number;
  idx: number; // variable index (vars only; assigned for the root module)
  module: string;
  value?: Value; // constants: value from the config
  subst?: Def; // constants: replaced by a definition (C <- Def)
  hasValue?: boolean;
}
export interface Builtin {
  fn: (ev: any, args: any[]) => Value;
  ops?: number[]; // indices of operator-valued arguments
  lazy?: boolean; // receives unevaluated thunks
}
export interface Def {
  k: 'def';
  name: string;
  params: Param[];
  body: Node | null;
  module: string;
  local: boolean;
  loc: Loc;
  builtin?: Builtin;
  inst?: { orig: Def; substs: { name: string; e: Node; arity: number }[]; nparams: number; envCache?: any };
  cached?: boolean;
  cache?: Value;
  level?: number;
  override?: Def; // config replacement (Op <- Other)
}
export type Sym = Decl | Def;
export const LOCAL = { k: 'local' } as const;

export interface ModuleInfo {
  name: string;
  syms: Map<string, Sym>;
  exports: Map<string, Sym>;
  consts: Decl[];
  vars: Decl[];
  assumes: { e: Node; name: string | null; module: string }[];
  ownDefs: Def[];
  order: string[]; // names of own definitions in source order
}

export type SourceResolver = (name: string) => string | null;

interface Scope { names: Map<string, { used: boolean }>; parent: Scope | null }

export class Loader {
  modules = new Map<string, ModuleInfo>();
  builtins: Map<string, ModuleInfo>;
  resolveSource: SourceResolver;
  loadOrder: string[] = [];
  loading = new Set<string>();
  globals = new Map<string, Def>();
  constructor(resolveSource: SourceResolver, builtins: Map<string, ModuleInfo>) {
    this.resolveSource = resolveSource;
    this.builtins = builtins;
  }

  load(name: string, from?: string): ModuleInfo {
    const have = this.modules.get(name);
    if (have) return have;
    const b = this.builtins.get(name);
    if (b) { this.modules.set(name, b); return b; }
    if (this.loading.has(name)) throw new TlaError(`Circular dependency among modules involving ${name}`, undefined, name, 'semantic');
    const src = this.resolveSource(name);
    if (src === null) {
      throw new TlaError(`Cannot find source file for module ${name}${from ? ` imported in module ${from}` : ''}.`, undefined, from, 'semantic');
    }
    this.loading.add(name);
    const ast = parseModule(src, name);
    if (ast.name !== name) throw new TlaError(`File name '${name}' does not match the name '${ast.name}' of the top level module it contains.`, undefined, name, 'semantic');
    const info = this.process(ast, null);
    this.loading.delete(name);
    this.modules.set(name, info);
    this.loadOrder.push(name);
    return info;
  }

  process(ast: ModuleNode, outer: ModuleInfo | null): ModuleInfo {
    const info: ModuleInfo = {
      name: ast.name, syms: new Map(), exports: new Map(), consts: [], vars: [], assumes: [], ownDefs: [], order: [],
    };
    if (outer) for (const [k, v] of outer.syms) info.syms.set(k, v);
    const inner = new Map<string, ModuleInfo>();
    const pendingInst: { def: Def; scopeParams: Param[] }[] = [];
    const add = (name: string, sym: Sym, local: boolean) => {
      const prev = info.syms.get(name);
      if (prev && prev !== sym) {
        const own = sym.module === ast.name && !(sym.k === 'def' && sym.inst);
        const prevOwn = prev.module === ast.name && !(prev.k === 'def' && prev.inst);
        if (!own) return; // imported symbols: first one wins
        if (prevOwn && !(outer && outer.syms.get(name) === prev)) {
          throw new TlaError(`Multiply-defined symbol '${name}' in module ${ast.name}`, (sym as Def).loc, ast.name, 'semantic');
        }
      }
      info.syms.set(name, sym);
      if (!local) info.exports.set(name, sym);
    };
    for (const m of ast.extends) {
      const ext = this.load(m, ast.name);
      for (const [k, v] of ext.exports) add(k, v, false);
      for (const c of ext.consts) if (!info.consts.includes(c)) info.consts.push(c);
      for (const v of ext.vars) if (!info.vars.includes(v)) info.vars.push(v);
      for (const a of ext.assumes) if (!info.assumes.includes(a)) info.assumes.push(a);
    }
    const importInstance = (u: Node, prefix: string | null, params: Param[], local: boolean) => {
      const m = inner.get(u.module) ?? this.load(u.module, ast.name);
      const explicit = new Map<string, Node>();
      for (const s of u.substs as { name: string; e: Node }[]) {
        if (!m.consts.some(c => c.name === s.name) && !m.vars.some(v => v.name === s.name)) {
          throw new TlaError(`Substitution target '${s.name}' is not a CONSTANT or VARIABLE of module ${u.module}`, u.loc, ast.name, 'semantic');
        }
        explicit.set(s.name, s.e);
      }
      const substs: { name: string; e: Node; arity: number }[] = [];
      for (const d of [...m.consts, ...m.vars]) {
        const e = explicit.get(d.name) ?? { k: 'app', loc: u.loc, name: d.name, args: [], implicit: true };
        substs.push({ name: d.name, e, arity: d.arity });
      }
      for (const [name, sym] of m.exports) {
        if (sym.k !== 'def') continue;
        if (sym.builtin && !prefix) { add(name, sym, local); continue; }
        const def: Def = {
          k: 'def', name: prefix ? `${prefix}!${name}` : name, params: [...params, ...sym.params], body: null,
          module: ast.name, local, loc: sym.loc, inst: { orig: sym, substs, nparams: params.length },
        };
        if (!substs.length && !params.length && !prefix) { add(name, sym, local); continue; }
        add(def.name, def, local);
        pendingInst.push({ def, scopeParams: params });
      }
      return substs;
    };
    const resolveLater: (() => void)[] = [];
    for (const u of ast.units) {
      switch (u.k) {
        case 'variables':
          for (const n of u.names) { const d: Decl = { k: 'var', name: n, arity: 0, idx: -1, module: ast.name }; info.vars.push(d); add(n, d, false); }
          break;
        case 'constants':
          for (const p of u.decls as Param[]) { const d: Decl = { k: 'const', name: p.name, arity: p.arity, idx: -1, module: ast.name }; info.consts.push(d); add(p.name, d, false); }
          break;
        case 'def': {
          const dn = u as DefNode;
          const def: Def = { k: 'def', name: dn.name, params: dn.params, body: dn.body, module: ast.name, local: dn.local, loc: dn.loc };
          add(dn.name, def, dn.local);
          info.ownDefs.push(def);
          info.order.push(dn.name);
          break;
        }
        case 'instance': {
          const substs = importInstance(u, u.name, u.params, u.local);
          const seen = new Set<Node>();
          resolveLater.push(() => {
            const scope: Scope | null = u.params.length ? { names: new Map(u.params.map((p: Param) => [p.name, { used: false }])), parent: null } : null;
            for (const s of substs) if (!seen.has(s.e)) { seen.add(s.e); this.resolve(s.e, scope, info); }
          });
          break;
        }
        case 'assume': info.assumes.push({ e: u.e, name: u.name, module: ast.name });
          if (u.name) {
            const def: Def = { k: 'def', name: u.name, params: [], body: u.e, module: ast.name, local: false, loc: u.loc };
            add(u.name, def, false);
          }
          break;
        case 'theorem':
          if (u.name && u.e.k !== 'assumeprove') {
            const def: Def = { k: 'def', name: u.name, params: [], body: u.e, module: ast.name, local: false, loc: u.loc };
            add(u.name, def, false);
            info.ownDefs.push(def);
          }
          break;
        case 'module': inner.set(u.name, this.process(u as ModuleNode, info)); break;
        case 'recursive': break;
      }
    }
    // pass 2: resolve names
    for (const d of info.ownDefs) {
      const scope: Scope | null = d.params.length ? { names: new Map(d.params.map(p => [p.name, { used: false }])), parent: null } : null;
      try {
        this.resolve(d.body!, scope, info);
      } catch (e) {
        // Theorems may mention things we do not model (proof-only constructs); ignore them.
        if (!(e instanceof TlaError) || !ast.units.some(u => u.k === 'theorem' && u.e === d.body)) throw e;
        d.body = { k: 'bool', loc: d.loc, v: true };
      }
    }
    for (const a of info.assumes) if (a.module === ast.name) this.resolve(a.e, null, info);
    for (const f of resolveLater) f();
    for (const str of (ast.strings ?? []) as string[]) strId(str);
    return info;
  }

  lookupScope(scope: Scope | null, name: string): { used: boolean } | null {
    for (let s = scope; s; s = s.parent) {
      const e = s.names.get(name);
      if (e) return e;
    }
    return null;
  }

  resolve(n: Node, scope: Scope | null, mod: ModuleInfo): void {
    const R = (x: Node | null | undefined, s: Scope | null = scope) => { if (x) this.resolve(x, s, mod); };
    const push = (names: string[]): Scope => ({ names: new Map(names.map(x => [x, { used: false }])), parent: scope });
    const boundNames = (bs: Bound[]) => bs.flatMap(b => b.names ?? b.tuple ?? []);
    n.mod = mod.name;
    switch (n.k) {
      case 'num': case 'str': case 'bool': case 'at': case 'stepref': return;
      case 'app': {
        const loc = this.lookupScope(scope, n.name);
        if (loc) { loc.used = true; n.r = LOCAL; }
        else {
          const sym = mod.syms.get(n.name) ?? this.globals.get(n.name);
          if (!sym) {
            throw new TlaError(`Unknown operator: \`${n.name}'.`, n.loc, mod.name, 'semantic');
          }
          n.r = sym;
        }
        for (const a of n.args) R(a);
        if (n.sel) for (const s of n.sel) if (Array.isArray(s)) for (const a of s) R(a);
        return;
      }
      case 'quant': case 'setmap': case 'fndef': {
        for (const b of n.bounds as Bound[]) R(b.set);
        const names = boundNames(n.bounds);
        if (n.k === 'fndef' && n.recname) names.push(n.recname);
        const s = push(names);
        R(n.k === 'setmap' ? n.e : n.body, s);
        if (n.k === 'fndef' && n.recname) n.isRec = s.names.get(n.recname)!.used;
        return;
      }
      case 'choose': case 'setfilter': {
        const b = n.bound as Bound;
        R(b.set);
        R(n.k === 'choose' ? n.body : n.pred, push(b.names ?? b.tuple ?? []));
        return;
      }
      case 'tquant': R(n.body, push(n.names)); return;
      case 'lambda': R(n.body, push(n.params.map((p: Param) => p.name))); return;
      case 'let': {
        const names: string[] = [];
        for (const d of n.defs as Node[]) {
          if (d.k === 'def') names.push(d.name);
          else if (!d.instDefs) {
            const m = this.load(d.module, mod.name);
            const explicit = new Map<string, Node>((d.substs as { name: string; e: Node }[]).map(x => [x.name, x.e]));
            const substs = [...m.consts, ...m.vars].map(c => ({ name: c.name, arity: c.arity,
              e: explicit.get(c.name) ?? ({ k: 'app', loc: d.loc, name: c.name, args: [], implicit: true } as Node) }));
            d.instSubsts = substs;
            d.instDefs = [];
            for (const [name, sym] of m.exports) {
              if (sym.k !== 'def') continue;
              const def: Def = { k: 'def', name: `${d.name}!${name}`, params: [...d.params, ...sym.params], body: null,
                module: mod.name, local: true, loc: sym.loc, inst: { orig: sym, substs, nparams: d.params.length } };
              d.instDefs.push(def);
            }
          }
          if (d.instDefs) for (const x of d.instDefs as Def[]) names.push(x.name);
        }
        const s = push(names);
        for (const d of n.defs as any[]) {
          if (d.k !== 'def') {
            const ds: Scope = d.params.length ? { names: new Map(d.params.map((p: Param) => [p.name, { used: false }])), parent: s } : s;
            for (const x of d.instSubsts) this.resolve(x.e, ds, mod);
            continue;
          }
          const ds: Scope = d.params.length ? { names: new Map(d.params.map((p: Param) => [p.name, { used: false }])), parent: s } : s;
          this.resolve(d.body, ds, mod);
        }
        R(n.body, s);
        return;
      }
      case 'case':
        for (const a of n.arms) { R(a.c); R(a.e); }
        R(n.other);
        return;
      case 'rec': case 'recset': for (const f of n.fields) R(f.e); return;
      case 'except':
        R(n.base);
        for (const u of n.updates) { for (const p of u.path) R(p); R(u.val); }
        return;
      case 'fnapp': R(n.f); for (const a of n.args) R(a); return;
      case 'dot': R(n.e); return;
      case 'assumeprove': return;
      default:
        if (n.a) { for (const x of n.a) R(x); return; }
        throw new TlaError(`Internal error: cannot resolve node kind ${n.k}`, n.loc, mod.name, 'semantic');
    }
  }
}

// ---- expression levels: 0 constant, 1 state, 2 action, 3 temporal ----
export function levelOf(n: Node): number {
  if (n.lvl !== undefined) return n.lvl;
  let l = 0;
  const up = (x: Node | null | undefined) => { if (x) { const v = levelOf(x); if (v > l) l = v; } };
  switch (n.k) {
    case 'num': case 'str': case 'bool': case 'at': case 'stepref': break;
    case 'app': {
      const r = n.r as Sym | typeof LOCAL | undefined;
      if (r && r !== LOCAL) {
        if (r.k === 'var') l = 1;
        else if (r.k === 'def') l = defLevel(r);
        else if (r.k === 'const' && r.subst) l = defLevel(r.subst);
      }
      for (const a of n.args) up(a);
      break;
    }
    case 'prime': case 'unchanged': case 'boxact': case 'angleact': case 'cdot':
      l = 2; break;
    case 'enabled': l = 1; break;
    case 'always': case 'eventually': case 'leadsto': case 'guarantee': case 'wf': case 'sf': case 'tquant':
      l = 3; break;
    case 'quant': case 'setmap': case 'fndef':
      for (const b of n.bounds) up(b.set);
      up(n.k === 'setmap' ? n.e : n.body);
      break;
    case 'choose': case 'setfilter': up(n.bound.set); up(n.k === 'choose' ? n.body : n.pred); break;
    case 'lambda': up(n.body); break;
    case 'let': for (const d of n.defs) up(d.body); up(n.body); break;
    case 'case': for (const a of n.arms) { up(a.c); up(a.e); } up(n.other); break;
    case 'rec': case 'recset': for (const f of n.fields) up(f.e); break;
    case 'except': up(n.base); for (const u of n.updates) { for (const p of u.path) up(p); up(u.val); } break;
    case 'fnapp': up(n.f); for (const a of n.args) up(a); break;
    case 'dot': up(n.e); break;
    default: if (n.a) for (const x of n.a) up(x);
  }
  n.lvl = l;
  return l;
}
export function defLevel(d: Def): number {
  if (d.override) return defLevel(d.override);
  if (d.level !== undefined) return d.level;
  d.level = 0; // recursion guard
  let l = 0;
  if (d.inst) {
    l = defLevel(d.inst.orig);
    const refs = declRefs(d.inst.orig);
    for (const s of d.inst.substs) if (refs.has(s.name)) l = Math.max(l, levelOf(s.e));
  } else if (d.body) l = levelOf(d.body);
  d.level = l;
  return l;
}

// Names of CONSTANT/VARIABLE declarations a definition (transitively) depends on.
const refCache = new Map<Def, Set<string>>();
export function declRefs(d: Def): Set<string> {
  const have = refCache.get(d);
  if (have) return have;
  const out = new Set<string>();
  refCache.set(d, out);
  if (d.inst) {
    const inner = declRefs(d.inst.orig);
    for (const s of d.inst.substs) if (inner.has(s.name)) collectRefs(s.e, out);
  } else if (d.body) collectRefs(d.body, out);
  return out;
}
function collectRefs(n: any, out: Set<string>): void {
  if (!n || typeof n !== 'object') return;
  if (Array.isArray(n)) { for (const x of n) collectRefs(x, out); return; }
  if (n.k === 'app') {
    const r = n.r;
    if (r && r !== LOCAL) {
      if (r.k === 'def') for (const x of declRefs(r)) out.add(x);
      else out.add(r.name);
    }
  }
  for (const key in n) {
    if (key === 'r' || key === 'loc' || key === 'instDefs') continue;
    const v = n[key];
    if (v && typeof v === 'object') collectRefs(v, out);
  }
}
