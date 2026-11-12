// Liveness checking: temporal formula normalisation, tableau construction, and SCC search over the
// product of the state graph and the tableau (same approach as TLC: possible error models made of
// []<> (AE) and <>[] (EA) constraints plus a particle tableau for everything else).
import type { Node } from './parser.ts';
import type { Model, Pred, Action } from './model.ts';
import { exprLevel, ConfigError } from './model.ts';
import { Checker } from './checker.ts';
import type { CheckResult, TraceStep, CheckOptions } from './checker.ts';
import type { Ctx } from './eval.ts';
import { TlaError } from './lexer.ts';

// ---- live expressions ----
interface LE {
  t: 'bool' | 'atom' | 'not' | 'and' | 'or' | 'always' | 'eventually';
  lvl: number; // 0..3
  v?: boolean;
  e?: Node;
  ctx?: Ctx | null;
  id?: number; // atoms / interned predicates
  as?: LE[];
  a?: LE;
}
const TRUE: LE = { t: 'bool', lvl: 0, v: true };
const FALSE: LE = { t: 'bool', lvl: 0, v: false };
const mkNot = (a: LE): LE => a.t === 'bool' ? (a.v ? FALSE : TRUE) : a.t === 'not' ? a.a! : { t: 'not', lvl: a.lvl, a };
function mkJunc(t: 'and' | 'or', items: LE[]): LE {
  const out: LE[] = [];
  for (const x of items) {
    if (x.t === 'bool') {
      if (x.v === (t === 'or')) return x; // TRUE in or / FALSE in and
      continue;
    }
    if (x.t === t) out.push(...x.as!); else out.push(x);
  }
  if (out.length === 0) return t === 'and' ? TRUE : FALSE;
  if (out.length === 1) return out[0];
  return { t, lvl: Math.max(...out.map(x => x.lvl)), as: out };
}
const mkAlways = (a: LE): LE => a.t === 'bool' ? a : { t: 'always', lvl: 3, a };
const mkEventually = (a: LE): LE => a.t === 'bool' ? a : { t: 'eventually', lvl: 3, a };

export class Liveness {
  model: Model;
  checker: Checker;
  atomIds = new Map<Node, Map<Ctx | null, number>>();
  atoms: LE[] = [];
  constructor(model: Model, checker: Checker) { this.model = model; this.checker = checker; }

  atom(e: Node, ctx: Ctx | null, lvl: number): LE {
    let m = this.atomIds.get(e);
    if (!m) { m = new Map(); this.atomIds.set(e, m); }
    let id = m.get(ctx);
    if (id === undefined) {
      id = this.atoms.length;
      m.set(ctx, id);
      this.atoms.push({ t: 'atom', lvl: Math.max(lvl, 1), e, ctx, id });
    }
    return this.atoms[id];
  }

  toLive(e: Node, ctx: Ctx | null): LE {
    const ev = this.model.ev;
    const lvl = exprLevel(ev, e, ctx);
    if (lvl === 0) {
      try {
        ev.cur = []; ev.nxt = null; ev.initMode = false;
        const v = ev.eval(e, ctx);
        if (typeof v === 'boolean') return v ? TRUE : FALSE;
      } catch (err) { if (!(err instanceof TlaError)) throw err; }
      return this.atom(e, ctx, 1);
    }
    if (lvl <= 2) return this.atom(e, ctx, lvl);
    const syn = (k: string, a: Node[]): Node => ({ k, loc: e.loc, a, mod: e.mod });
    switch (e.k) {
      case 'app': {
        const x = ev.expandApp(e, ctx);
        if (x) return this.toLive(x.body, x.ctx);
        break;
      }
      case 'let': return this.toLive(e.body, ev.bindLet(e.defs, ctx));
      case 'quant': {
        const parts: LE[] = [];
        ev.cur = []; ev.nxt = null;
        ev.forBindings(e.bounds, ctx, c => { parts.push(this.toLive(e.body, c)); return false; });
        return mkJunc(e.q === 'A' ? 'and' : 'or', parts);
      }
      case 'and': return mkJunc('and', e.a.map((x: Node) => this.toLive(x, ctx)));
      case 'or': return mkJunc('or', e.a.map((x: Node) => this.toLive(x, ctx)));
      case 'not': return mkNot(this.toLive(e.a[0], ctx));
      case 'imp': return mkJunc('or', [mkNot(this.toLive(e.a[0], ctx)), this.toLive(e.a[1], ctx)]);
      case 'eqv': {
        const a = this.toLive(e.a[0], ctx), b = this.toLive(e.a[1], ctx);
        return mkJunc('or', [mkJunc('and', [a, b]), mkJunc('and', [mkNot(a), mkNot(b)])]);
      }
      case 'if': {
        const g = this.toLive(e.a[0], ctx);
        return mkJunc('or', [mkJunc('and', [g, this.toLive(e.a[1], ctx)]), mkJunc('and', [mkNot(g), this.toLive(e.a[2], ctx)])]);
      }
      case 'always': return mkAlways(this.toLive(e.a[0], ctx));
      case 'eventually': return mkEventually(this.toLive(e.a[0], ctx));
      case 'leadsto': return mkAlways(mkJunc('or', [mkNot(this.toLive(e.a[0], ctx)), mkEventually(this.toLive(e.a[1], ctx))]));
      case 'wf': case 'sf': {
        const act = syn('angleact', [e.a[1], e.a[0]]);
        const en = this.atom(syn('enabled', [act]), ctx, 1);
        const a = this.atom(act, ctx, 2);
        if (e.k === 'wf') return mkAlways(mkEventually(mkJunc('or', [mkNot(en), a])));
        return mkJunc('or', [mkEventually(mkAlways(mkNot(en))), mkAlways(mkEventually(a))]);
      }
    }
    throw new ConfigError(`TLC cannot handle the temporal formula at line ${e.loc[0]}, col ${e.loc[1]} to line ${e.loc[2]}, col ${e.loc[3]} of module ${e.mod ?? '?'}`);
  }

  // Push negations inward; non-temporal subtrees stay as (possibly negated) predicates.
  pushNeg(x: LE, neg: boolean): LE {
    if (x.lvl <= 2) return neg ? mkNot(x) : x;
    switch (x.t) {
      case 'not': return this.pushNeg(x.a!, !neg);
      case 'and': case 'or': {
        const t = (x.t === 'and') !== neg ? 'and' : 'or';
        return mkJunc(t, x.as!.map(y => this.pushNeg(y, neg)));
      }
      case 'always': return neg ? mkEventually(this.pushNeg(x.a!, true)) : mkAlways(this.pushNeg(x.a!, false));
      case 'eventually': return neg ? mkAlways(this.pushNeg(x.a!, true)) : mkEventually(this.pushNeg(x.a!, false));
    }
    return x;
  }

  simp(x: LE): LE {
    if (x.lvl <= 2) return x;
    switch (x.t) {
      case 'and': case 'or': return mkJunc(x.t, x.as!.map(y => this.simp(y)));
      case 'always': {
        const a = this.simp(x.a!);
        if (a.t === 'always') return a;
        if (a.t === 'and' && a.lvl === 3) return mkJunc('and', a.as!.map(y => this.simp(mkAlways(y))));
        if (a.t === 'eventually' && a.a!.t === 'always') return a; // []<>[]p = <>[]p
        if (a.t === 'eventually' && a.a!.t === 'or' && a.a!.lvl === 3) return mkJunc('or', a.a!.as!.map(y => this.simp(mkAlways(mkEventually(y)))));
        return mkAlways(a);
      }
      case 'eventually': {
        const a = this.simp(x.a!);
        if (a.t === 'eventually') return a;
        if (a.t === 'or' && a.lvl === 3) return mkJunc('or', a.as!.map(y => this.simp(mkEventually(y))));
        if (a.t === 'always' && a.a!.t === 'eventually') return a; // <>[]<>p = []<>p
        if (a.t === 'always' && a.a!.t === 'and' && a.a!.lvl === 3) return mkJunc('and', a.a!.as!.map(y => this.simp(mkEventually(mkAlways(y)))));
        return mkEventually(a);
      }
    }
    return x;
  }

  dnf(x: LE): LE[][] {
    if (x.t === 'or' && x.lvl === 3) return x.as!.flatMap(y => this.dnf(y));
    if (x.t === 'and' && x.lvl === 3) {
      let acc: LE[][] = [[]];
      for (const y of x.as!) {
        const d = this.dnf(y);
        const next: LE[][] = [];
        for (const a of acc) for (const b of d) next.push([...a, ...b]);
        acc = next;
        if (acc.length > 100000) throw new ConfigError('The temporal formula is too large to check (DNF blow-up).');
      }
      return acc;
    }
    if (x.t === 'bool') return x.v ? [[]] : [];
    return [[x]];
  }

  key(x: LE): string {
    switch (x.t) {
      case 'bool': return x.v ? 'T' : 'F';
      case 'atom': return 'a' + x.id;
      case 'not': return '!' + this.key(x.a!);
      case 'always': return '[]' + this.key(x.a!);
      case 'eventually': return '<>' + this.key(x.a!);
      default: return (x.t === 'and' ? '&(' : '|(') + x.as!.map(y => this.key(y)).join(',') + ')';
    }
  }

  // ---- graph ----
  S = 0;
  eStart!: Int32Array; eTo!: Int32Array; eAct!: Int32Array;
  stateCache = new Map<string, Uint8Array>();
  edgeCache = new Map<string, Uint8Array>();

  buildGraph(): void {
    const c = this.checker;
    const S = this.S = c.states.length;
    let E = S;
    for (let i = 0; i < S; i++) E += c.succ[i].length;
    this.eStart = new Int32Array(S + 1);
    this.eTo = new Int32Array(E);
    this.eAct = new Int32Array(E);
    let p = 0;
    for (let i = 0; i < S; i++) {
      this.eStart[i] = p;
      const su = c.succ[i], sa = c.succAct[i];
      const seen = new Set<number>();
      for (let j = 0; j < su.length; j++) {
        if (seen.has(su[j])) continue;
        seen.add(su[j]);
        this.eTo[p] = su[j]; this.eAct[p] = sa[j]; p++;
      }
      if (!seen.has(i)) { this.eTo[p] = i; this.eAct[p] = -1; p++; } // stuttering self-loop
    }
    this.eStart[S] = p;
  }

  // Evaluate a non-temporal live expression at a state (and, for action level, along edge `e`).
  evalLE(x: LE, s: number, e: number): boolean {
    switch (x.t) {
      case 'bool': return x.v!;
      case 'not': return !this.evalLE(x.a!, s, e);
      case 'and': for (const y of x.as!) if (!this.evalLE(y, s, e)) return false; return true;
      case 'or': for (const y of x.as!) if (this.evalLE(y, s, e)) return true; return false;
      case 'atom': {
        const c = this.checker;
        if (x.lvl <= 1) {
          let cache = this.stateCache.get('a' + x.id);
          if (!cache) { cache = new Uint8Array(this.S); this.stateCache.set('a' + x.id, cache); }
          if (cache[s] === 0) cache[s] = c.evalPred(x as unknown as Pred, c.states[s], null) ? 2 : 1;
          return cache[s] === 2;
        }
        if (e < 0) throw new ConfigError('TLC cannot handle a temporal formula with an action in a state-level position.');
        let cache = this.edgeCache.get('a' + x.id);
        if (!cache) { cache = new Uint8Array(this.eTo.length); this.edgeCache.set('a' + x.id, cache); }
        if (cache[e] === 0) cache[e] = c.evalPred(x as unknown as Pred, c.states[s], c.states[this.eTo[e]]) ? 2 : 1;
        return cache[e] === 2;
      }
    }
    throw new Error('temporal operator in evalLE');
  }

  check(): CheckResult | null {
    const m = this.model;
    if (m.liveProps.length === 0) return null;
    const fair = mkJunc('and', m.fairness.map(f => this.toLive(f.e, f.ctx)));
    const props = m.liveProps.map(p => this.toLive(p.e, p.ctx));
    const formula = mkJunc('and', [fair, mkJunc('or', props.map(p => mkNot(p)))]);
    const nf = this.simp(this.pushNeg(formula, false));
    const disjuncts = this.dnf(nf);
    if (disjuncts.length === 0) return null;
    this.buildGraph();
    // group disjuncts by tableau formula
    interface PEM { aeState: LE[]; aeAction: LE[]; ea: LE[] }
    const groups = new Map<string, { tf: LE; pems: PEM[] }>();
    for (const d of disjuncts) {
      const pem: PEM = { aeState: [], aeAction: [], ea: [] };
      const tfs: LE[] = [];
      for (const c of d) {
        if (c.t === 'always' && c.a!.t === 'eventually' && c.a!.a!.lvl <= 2) {
          (c.a!.a!.lvl <= 1 ? pem.aeState : pem.aeAction).push(c.a!.a!);
        } else if (c.t === 'eventually' && c.a!.t === 'always' && c.a!.a!.lvl <= 2) pem.ea.push(c.a!.a!);
        else {
          if (this.hasAction(c)) throw new ConfigError('TLC cannot handle the temporal formula: an action appears outside of a []<> or <>[] context.');
          tfs.push(c);
        }
      }
      const tf = mkJunc('and', tfs);
      const k = this.key(tf);
      let g = groups.get(k);
      if (!g) { g = { tf, pems: [] }; groups.set(k, g); }
      g.pems.push(pem);
    }
    for (const g of groups.values()) {
      const r = this.checkGroup(g.tf, g.pems);
      if (r) return r;
    }
    return null;
  }

  hasAction(x: LE): boolean {
    if (x.t === 'atom') return x.lvl === 2;
    if (x.a) return this.hasAction(x.a);
    if (x.as) return x.as.some(y => this.hasAction(y));
    return false;
  }

  // ---- tableau ----
  buildTableau(tf: LE): { init: number[]; parts: { preds: LE[]; succ: number[]; set: Set<number> }[]; promises: { ev: number; body: number }[] } {
    // intern formulas
    const ids = new Map<string, number>();
    const forms: { le: LE; kind: 'pred' | 'and' | 'or' | 'always' | 'eventually'; kids: number[] }[] = [];
    const intern = (x: LE): number => {
      const k = this.key(x);
      const have = ids.get(k);
      if (have !== undefined) return have;
      const id = forms.length;
      ids.set(k, id);
      const f = { le: x, kind: 'pred' as 'pred' | 'and' | 'or' | 'always' | 'eventually', kids: [] as number[] };
      forms.push(f);
      if (x.lvl === 3) {
        if (x.t === 'and' || x.t === 'or') { f.kind = x.t; f.kids = x.as!.map(intern); }
        else if (x.t === 'always' || x.t === 'eventually') { f.kind = x.t; f.kids = [intern(x.a!)]; }
      }
      return id;
    };
    const root = intern(tf);
    const promises: { ev: number; body: number }[] = [];
    forms.forEach((f, i) => { if (f.kind === 'eventually') promises.push({ ev: i, body: f.kids[0] }); });
    // particles: closed sets of formula ids plus the set of formulas required in the next state
    interface Part { set: Set<number>; next: Set<number> }
    const cover = (start: number[]): Part[] => {
      const out: Part[] = [];
      const rec = (todo: number[], set: Set<number>, next: Set<number>): void => {
        if (todo.length === 0) { out.push({ set, next }); return; }
        const f = todo[todo.length - 1];
        const rest = todo.slice(0, -1);
        if (set.has(f)) { rec(rest, set, next); return; }
        const s2 = new Set(set); s2.add(f);
        const F = forms[f];
        switch (F.kind) {
          case 'pred': rec(rest, s2, next); return;
          case 'and': rec([...rest, ...F.kids], s2, next); return;
          case 'or': for (const k of F.kids) rec([...rest, k], s2, next); return;
          case 'always': { const n2 = new Set(next); n2.add(f); rec([...rest, F.kids[0]], s2, n2); return; }
          case 'eventually': {
            rec([...rest, F.kids[0]], s2, next);
            const n2 = new Set(next); n2.add(f);
            rec(rest, s2, n2);
            return;
          }
        }
      };
      rec(start, new Set(), new Set());
      return out;
    };
    const partIds = new Map<string, number>();
    const parts: { preds: LE[]; succ: number[]; set: Set<number>; next: Set<number> }[] = [];
    const add = (p: Part): number => {
      const k = [...p.set].sort((a, b) => a - b).join(',') + '|' + [...p.next].sort((a, b) => a - b).join(',');
      const have = partIds.get(k);
      if (have !== undefined) return have;
      const id = parts.length;
      partIds.set(k, id);
      parts.push({ preds: [...p.set].filter(f => forms[f].kind === 'pred').map(f => forms[f].le), succ: [], set: p.set, next: p.next });
      return id;
    };
    const init = [...new Set(cover([root]).map(add))];
    for (let i = 0; i < parts.length; i++) {
      parts[i].succ = [...new Set(cover([...parts[i].next]).map(add))];
      if (parts.length > 20000) throw new ConfigError('The temporal formula is too large to check (tableau blow-up).');
    }
    return { init, parts, promises };
  }

  checkGroup(tf: LE, pems: { aeState: LE[]; aeAction: LE[]; ea: LE[] }[]): CheckResult | null {
    const c = this.checker;
    const tb = this.buildTableau(tf);
    const P = tb.parts.length;
    const S = this.S;
    // product nodes: reachable (state, particle) pairs
    const nodeId = new Map<number, number>();
    const nState: number[] = [], nPart: number[] = [];
    const adj: number[][] = [], adjEdge: number[][] = [];
    const consistent = (s: number, p: number): boolean => {
      for (const pr of tb.parts[p].preds) if (!this.evalLE(pr, s, -1)) return false;
      return true;
    };
    const consCache = new Int8Array(S * P);
    const cons = (s: number, p: number): boolean => {
      const k = s * P + p;
      if (consCache[k] === 0) consCache[k] = consistent(s, p) ? 2 : 1;
      return consCache[k] === 2;
    };
    const getNode = (s: number, p: number): number => {
      const k = s * P + p;
      let id = nodeId.get(k);
      if (id === undefined) { id = nState.length; nodeId.set(k, id); nState.push(s); nPart.push(p); adj.push([]); adjEdge.push([]); }
      return id;
    };
    const initNodes: number[] = [];
    for (const s of c.inits) for (const p of tb.init) if (cons(s, p)) initNodes.push(getNode(s, p));
    for (let n = 0; n < nState.length; n++) {
      const s = nState[n], p = nPart[n];
      for (let e = this.eStart[s]; e < this.eStart[s + 1]; e++) {
        const t = this.eTo[e];
        for (const q of tb.parts[p].succ) {
          if (!cons(t, q)) continue;
          adj[n].push(getNode(t, q));
          adjEdge[n].push(e);
        }
      }
    }
    const N = nState.length;
    // group PEMs by their EA constraints
    const byEA = new Map<string, { ea: LE[]; pems: typeof pems }>();
    for (const pem of pems) {
      const k = pem.ea.map(x => this.key(x)).sort().join(';');
      let g = byEA.get(k);
      if (!g) { g = { ea: pem.ea, pems: [] }; byEA.set(k, g); }
      g.pems.push(pem);
    }
    for (const g of byEA.values()) {
      const edgeOk = (n: number, j: number): boolean => {
        for (const x of g.ea) if (!this.evalLE(x, nState[n], adjEdge[n][j])) return false;
        return true;
      };
      // iterative Tarjan
      const index = new Int32Array(N).fill(-1), low = new Int32Array(N), onStack = new Uint8Array(N);
      const comp = new Int32Array(N).fill(-1);
      const stack: number[] = [];
      let idx = 0, ncomp = 0;
      const callN: number[] = [], callJ: number[] = [];
      for (let root = 0; root < N; root++) {
        if (index[root] !== -1) continue;
        callN.push(root); callJ.push(0);
        index[root] = low[root] = idx++; stack.push(root); onStack[root] = 1;
        while (callN.length) {
          const n = callN[callN.length - 1];
          let j = callJ[callJ.length - 1];
          let pushed = false;
          const a = adj[n];
          while (j < a.length) {
            const w = a[j];
            if (!edgeOk(n, j)) { j++; continue; }
            if (index[w] === -1) {
              callJ[callJ.length - 1] = j + 1;
              index[w] = low[w] = idx++; stack.push(w); onStack[w] = 1;
              callN.push(w); callJ.push(0);
              pushed = true;
              break;
            }
            if (onStack[w] && index[w] < low[n]) low[n] = index[w];
            j++;
          }
          if (pushed) continue;
          callN.pop(); callJ.pop();
          if (callN.length) { const par = callN[callN.length - 1]; if (low[n] < low[par]) low[par] = low[n]; }
          if (low[n] === index[n]) {
            const members: number[] = [];
            for (;;) { const w = stack.pop()!; onStack[w] = 0; comp[w] = ncomp; members.push(w); if (w === n) break; }
            const r = this.checkComponent(members, comp, ncomp, g.pems, edgeOk, tb, nState, nPart, adj, adjEdge, initNodes);
            ncomp++;
            if (r) return r;
          }
        }
      }
    }
    return null;
  }

  checkComponent(members: number[], comp: Int32Array, cid: number, pems: { aeState: LE[]; aeAction: LE[]; ea: LE[] }[],
    edgeOk: (n: number, j: number) => boolean, tb: ReturnType<Liveness['buildTableau']>, nState: number[], nPart: number[],
    adj: number[][], adjEdge: number[][], initNodes: number[]): CheckResult | null {
    // must contain at least one internal edge
    let hasEdge = false;
    for (const n of members) {
      for (let j = 0; j < adj[n].length && !hasEdge; j++) if (comp[adj[n][j]] === cid && edgeOk(n, j)) hasEdge = true;
      if (hasEdge) break;
    }
    if (!hasEdge) return null;
    // promises
    const promiseNodes: number[] = [];
    for (const pr of tb.promises) {
      let found = -1;
      for (const n of members) {
        const set = tb.parts[nPart[n]].set;
        if (!set.has(pr.ev) || set.has(pr.body)) { found = n; break; }
      }
      if (found < 0) return null;
      promiseNodes.push(found);
    }
    for (const pem of pems) {
      const targets: { node: number; edge: number }[] = promiseNodes.map(n => ({ node: n, edge: -1 }));
      let ok = true;
      for (const x of pem.aeState) {
        let found = -1;
        for (const n of members) if (this.evalLE(x, nState[n], -1)) { found = n; break; }
        if (found < 0) { ok = false; break; }
        targets.push({ node: found, edge: -1 });
      }
      if (!ok) continue;
      for (const x of pem.aeAction) {
        let fn = -1, fj = -1;
        outer: for (const n of members) {
          for (let j = 0; j < adj[n].length; j++) {
            if (comp[adj[n][j]] === cid && edgeOk(n, j) && this.evalLE(x, nState[n], adjEdge[n][j])) { fn = n; fj = j; break outer; }
          }
        }
        if (fn < 0) { ok = false; break; }
        targets.push({ node: fn, edge: fj });
      }
      if (!ok) continue;
      return this.counterexample(members, comp, cid, targets, edgeOk, nState, adj, adjEdge, initNodes);
    }
    return null;
  }

  counterexample(members: number[], comp: Int32Array, cid: number, targets: { node: number; edge: number }[],
    edgeOk: (n: number, j: number) => boolean, nState: number[], adj: number[][], adjEdge: number[][], initNodes: number[]): CheckResult {
    const c = this.checker;
    const N = nState.length;
    // BFS helper: shortest path from `from` to a node satisfying `goal`; `inside` restricts to the component.
    const bfs = (from: number[], goal: (n: number) => boolean, inside: boolean, minLen: number): { nodes: number[]; edges: number[] } | null => {
      const prev = new Int32Array(N).fill(-2), prevE = new Int32Array(N).fill(-1);
      const q: number[] = [];
      if (minLen === 0) {
        for (const f of from) { if (prev[f] === -2) { prev[f] = -1; q.push(f); } }
      } else {
        // paths of length >= 1: seed with successors
        for (const f of from) {
          for (let j = 0; j < adj[f].length; j++) {
            const w = adj[f][j];
            if (inside && (comp[w] !== cid || !edgeOk(f, j))) continue;
            if (prev[w] === -2) { prev[w] = -3 - f; prevE[w] = adjEdge[f][j]; q.push(w); }
          }
        }
      }
      for (let h = 0; h < q.length; h++) {
        const n = q[h];
        if (goal(n)) {
          const nodes: number[] = [], edges: number[] = [];
          let x = n;
          for (;;) {
            nodes.push(x);
            const p = prev[x];
            if (p === -1) break;
            edges.push(prevE[x]);
            if (p <= -3) { nodes.push(-3 - p); break; }
            x = p;
          }
          return { nodes: nodes.reverse(), edges: edges.reverse() };
        }
        for (let j = 0; j < adj[n].length; j++) {
          const w = adj[n][j];
          if (inside && (comp[w] !== cid || !edgeOk(n, j))) continue;
          if (prev[w] === -2) { prev[w] = n; prevE[w] = adjEdge[n][j]; q.push(w); }
        }
      }
      return null;
    };
    const inComp = (n: number) => comp[n] === cid;
    const prefix = bfs(initNodes, inComp, false, 0)!;
    const entry = prefix.nodes[prefix.nodes.length - 1];
    // cycle through all targets and back to entry
    const cycNodes: number[] = [entry], cycEdges: number[] = [];
    let cur = entry;
    for (const t of targets) {
      if (cur !== t.node) {
        const p = bfs([cur], n => n === t.node, true, 0)!;
        cycNodes.push(...p.nodes.slice(1)); cycEdges.push(...p.edges);
        cur = t.node;
      }
      if (t.edge >= 0) {
        cycNodes.push(adj[cur][t.edge]); cycEdges.push(adjEdge[cur][t.edge]);
        cur = adj[cur][t.edge];
      }
    }
    if (cur !== entry || cycEdges.length === 0) {
      const p = bfs([cur], n => n === entry, true, cur === entry ? 1 : 0)!;
      cycNodes.push(...p.nodes.slice(1)); cycEdges.push(...p.edges);
    }
    // project onto states
    const steps: TraceStep[] = [];
    const actOf = (e: number): Action | null => (this.eAct[e] >= 0 ? this.model.actions[this.eAct[e]] : null);
    let last = -1;
    prefix.nodes.forEach((n, i) => {
      const s = nState[n];
      if (s === last) return;
      steps.push({ state: c.states[s], action: i === 0 ? null : actOf(prefix.edges[i - 1]), id: s });
      last = s;
    });
    const loopStart = steps.length - 1;
    let loopAction: Action | null = null;
    for (let i = 1; i < cycNodes.length; i++) {
      const s = nState[cycNodes[i]];
      if (s === last) continue;
      if (i === cycNodes.length - 1) { loopAction = actOf(cycEdges[i - 1]); break; } // returns to the entry state
      steps.push({ state: c.states[s], action: actOf(cycEdges[i - 1]), id: s });
      last = s;
    }
    if (loopAction === null && steps.length - 1 > loopStart && steps[steps.length - 1].id === steps[loopStart].id) {
      loopAction = steps.pop()!.action;
    }
    const stutter = steps.length - 1 === loopStart && loopAction === null;
    const names = this.model.liveProps.map(p => p.name);
    return c.result('liveness', { name: names.length === 1 ? names[0] : undefined, trace: steps, loopTo: stutter ? -1 : loopStart, loopAction });
  }
}

// Run safety checking, then (if there are temporal properties) liveness checking.
export function modelCheck(model: Model, opts: CheckOptions): { result: CheckResult; checker: Checker } {
  const needLive = model.liveProps.length > 0;
  const checker = new Checker(model, { ...opts, recordGraph: opts.recordGraph || needLive });
  let result = checker.run();
  if (result.status === 'ok' && needLive) {
    try {
      const r = new Liveness(model, checker).check();
      if (r) { r.outdegree = result.outdegree; result = r; }
    } catch (e) {
      if (!(e instanceof TlaError)) throw e;
      result = checker.result('error', { message: checker.describeErr(e) });
    }
  }
  return { result, checker };
}
