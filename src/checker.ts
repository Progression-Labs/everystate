// Explicit-state breadth-first model checker.
import type { Model, Pred, Action } from './model.ts';
import { locStr } from './model.ts';
import type { Evaluator } from './eval.ts';
import { TlaError } from './lexer.ts';
import {
  Hasher, SetBase, SetV, TupleV, RecordV, FcnV, ModelValue, compare, mkSet, makeFcnFromPairs, IntervalV, makeRecord,
} from './values.ts';
import type { Value } from './values.ts';

export type State = Value[];
export interface TraceStep { state: State; action: Action | null; id: number }
export interface CheckResult {
  status: 'ok' | 'invariant' | 'invariant-init' | 'deadlock' | 'action-property' | 'implied-init' | 'liveness'
    | 'error' | 'assumption' | 'incomplete' | 'init-error';
  name?: string;
  message?: string;
  trace?: TraceStep[];
  loopTo?: number; // liveness: index (0-based) of the state the lasso returns to; -1 = stuttering
  loopAction?: Action | null;
  errorLoc?: string;
  generated: number;
  distinct: number;
  queue: number;
  depth: number;
  initGenerated: number;
  initDistinct: number;
  printSummary: boolean;
  outdegree?: { min: number; avg: number; p95: number; max: number };
}
export interface CheckOptions {
  checkDeadlock: boolean;
  recordGraph?: boolean;
  onProgress?: (generated: number, distinct: number, queue: number) => void;
  maxDepth?: number;
  onChecker?: (c: Checker) => void;
}

// Open-addressing hash set of 64-bit fingerprints (two int32 halves) mapping to state ids.
export class FpSet {
  cap = 1 << 16;
  k1 = new Int32Array(this.cap);
  k2 = new Int32Array(this.cap);
  ids = new Int32Array(this.cap); // id + 1; 0 = empty
  size = 0;
  // Returns the existing id, or -1 after inserting `id`.
  put(h1: number, h2: number, id: number): number {
    if (this.size * 2 >= this.cap) this.grow();
    const mask = this.cap - 1;
    let i = (h1 ^ Math.imul(h2, 0x9e3779b1)) & mask;
    for (;;) {
      const v = this.ids[i];
      if (v === 0) { this.k1[i] = h1; this.k2[i] = h2; this.ids[i] = id + 1; this.size++; return -1; }
      if (this.k1[i] === h1 && this.k2[i] === h2) return v - 1;
      i = (i + 1) & mask;
    }
  }
  grow(): void {
    const ok1 = this.k1, ok2 = this.k2, oids = this.ids, ocap = this.cap;
    this.cap = ocap * 2;
    this.k1 = new Int32Array(this.cap);
    this.k2 = new Int32Array(this.cap);
    this.ids = new Int32Array(this.cap);
    const mask = this.cap - 1;
    for (let j = 0; j < ocap; j++) {
      if (oids[j] === 0) continue;
      let i = (ok1[j] ^ Math.imul(ok2[j], 0x9e3779b1)) & mask;
      while (this.ids[i] !== 0) i = (i + 1) & mask;
      this.k1[i] = ok1[j]; this.k2[i] = ok2[j]; this.ids[i] = oids[j];
    }
  }
}

export function permute(v: Value, m: Map<ModelValue, ModelValue>): Value {
  if (typeof v !== 'object') return v;
  if (v instanceof ModelValue) return m.get(v) ?? v;
  if (v instanceof TupleV) return new TupleV(v.e.map(x => permute(x, m)));
  if (v instanceof RecordV) return new RecordV(v.names, v.vals.map(x => permute(x, m)));
  if (v instanceof FcnV) return makeFcnFromPairs(v.dom.map((d, i) => [permute(d, m), permute(v.vals[i], m)] as [Value, Value]));
  if (v instanceof IntervalV) return v;
  if (v instanceof SetBase) return mkSet(v.elems().map(x => permute(x, m)));
  return v;
}

export class CheckError extends Error {
  result: CheckResult;
  constructor(result: CheckResult) { super(result.message ?? result.status); this.result = result; }
}

export class Checker {
  model: Model;
  ev: Evaluator;
  opts: CheckOptions;
  states: State[] = [];
  parent: number[] = [];
  level: number[] = [];
  act: number[] = [];
  succ: number[][] = []; // recorded graph: successor ids per state (if recordGraph)
  succAct: number[][] = [];
  inits: number[] = [];
  fps = new FpSet();
  hasher = new Hasher();
  generated = 0;
  initGenerated = 0;
  initDistinct = 0;
  head = 0;
  depth = 0;
  nvars: number;
  outdeg: number[] = [];

  constructor(model: Model, opts: CheckOptions) {
    this.model = model;
    this.ev = model.ev;
    this.opts = opts;
    this.nvars = model.vars.length;
    this.ev.hooks.tlcGet = (k: string) => this.tlcGet(k);
    if (!this.ev.hooks.random) this.ev.hooks.random = Math.random;
  }

  curLevel = 1;
  tlcGet(k: string): Value {
    switch (k) {
      case 'level': return this.curLevel;
      case 'distinct': return this.states.length;
      case 'generated': return this.generated;
      case 'queue': return this.states.length - this.head;
      case 'diameter': return this.depth;
      case 'duration': return 0;
      case 'config': return makeRecord(['mode', 'depth', 'deadlock', 'worker', 'traces', 'seed', 'fingerprint'],
        ['bfs', -1, this.opts.checkDeadlock, 1, 0, 0, 0]);
      case 'stats': return makeRecord(['distinct', 'generated', 'queue', 'diameter', 'duration'],
        [this.states.length, this.generated, this.states.length - this.head, this.depth, 0]);
    }
    if (k.startsWith('-D')) return 'FALSE';
    return undefined;
  }

  fingerprint(s: State): void {
    const h = this.hasher;
    h.reset();
    const m = this.model;
    let t = s;
    if (m.symmetry) {
      for (const p of m.symmetry) {
        const u = s.map(v => permute(v, p));
        if (this.stateLess(u, t)) t = u;
      }
    }
    if (m.view) {
      this.ev.cur = t; this.ev.nxt = null; this.ev.initMode = false;
      h.value(this.ev.eval(m.view.e, m.view.ctx));
    } else {
      for (let i = 0; i < t.length; i++) h.value(t[i]);
    }
    h.finish();
  }
  stateLess(a: State, b: State): boolean {
    for (let i = 0; i < a.length; i++) {
      const c = compare(a[i], b[i]);
      if (c !== 0) return c < 0;
    }
    return false;
  }

  result(status: CheckResult['status'], extra: Partial<CheckResult> = {}): CheckResult {
    return {
      status, generated: this.generated, distinct: this.states.length, queue: Math.max(0, this.states.length - this.head),
      depth: this.depth, initGenerated: this.initGenerated, initDistinct: this.initDistinct, printSummary: true,
      outdegree: this.outdegree(), ...extra,
    };
  }

  outdegree(): CheckResult['outdegree'] {
    if (!this.outdeg.length) return undefined;
    const d = this.outdeg.slice().sort((x, y) => x - y);
    return { min: d[0], avg: Math.round(d.reduce((x, y) => x + y, 0) / d.length), p95: d[Math.min(d.length - 1, Math.ceil(d.length * 0.95) - 1)], max: d[d.length - 1] };
  }

  traceTo(id: number): TraceStep[] {
    const out: TraceStep[] = [];
    for (let i = id; i >= 0; i = this.parent[i]) {
      out.push({ state: this.states[i], action: this.act[i] >= 0 ? this.model.actions[this.act[i]] : null, id: i });
    }
    return out.reverse();
  }

  evalPred(p: Pred, s: State, t: State | null): boolean {
    const ev = this.ev;
    ev.cur = s; ev.nxt = t; ev.initMode = false; ev.primeDepth = 0; ev.callDepth = 0; ev.nAssigned = 0;
    return ev.evalBool(p.e, p.ctx);
  }

  checkAssumptions(): CheckResult | null {
    const ev = this.ev;
    for (const a of this.model.root.assumes) {
      ev.cur = []; ev.nxt = null; ev.initMode = false;
      let ok: Value;
      try {
        ok = ev.eval(a.e, null);
      } catch (e) {
        if (e instanceof TlaError) return this.result('error', { message: `Evaluating assumption ${locStr(a.e.loc, a.module)} failed.\n${e.message}`, printSummary: false });
        throw e;
      }
      if (typeof ok !== 'boolean') return this.result('error', { message: `The assumption ${locStr(a.e.loc, a.module)} was not a boolean.`, printSummary: false });
      if (!ok) return this.result('assumption', { message: `Assumption ${locStr(a.e.loc, a.module)} is false.`, printSummary: false });
    }
    return null;
  }

  describeErr(e: unknown): string {
    if (e instanceof RangeError) return 'Stack overflow while evaluating the specification (recursion too deep). Re-run with a larger stack.';
    if (e instanceof TlaError) {
      let m = e.message;
      if (e.loc && e.loc[0] > 0) m += `\n(evaluating the expression at line ${e.loc[0]}, col ${e.loc[1]} to line ${e.loc[2]}, col ${e.loc[3]} of module ${e.module ?? '?'})`;
      return m;
    }
    throw e;
  }

  // Enumerate initial states.
  computeInit(): CheckResult | null {
    const ev = this.ev, m = this.model;
    const found: State[] = [];
    ev.cur = new Array(this.nvars); ev.nxt = null; ev.initMode = true; ev.primeDepth = 0; ev.nAssigned = 0;
    const preds = m.inits;
    if (preds.length === 0) return null;
    const go = (i: number): void => {
      if (i === preds.length) {
        const s = ev.cur;
        for (let k = 0; k < this.nvars; k++) {
          if (s[k] === undefined) {
            const missing = m.vars.filter((_, j) => s[j] === undefined).map(v => v.name).sort();
            throw new CheckError(this.result('init-error', { message: `current state is not a legal state\nWhile working on the initial state:\n` + `The variable${missing.length > 1 ? 's' : ''} ${missing.join(', ')} ${missing.length > 1 ? 'are' : 'is'} not assigned a value by the initial predicate.` }));
          }
        }
        found.push(s.slice());
        return;
      }
      ev.enumerate(preds[i].e, preds[i].ctx, () => go(i + 1));
    };
    try {
      go(0);
    } catch (e) {
      ev.initMode = false;
      if (e instanceof CheckError) return e.result;
      return this.result('error', { message: this.describeErr(e) });
    }
    ev.initMode = false;
    for (const s of found) {
      this.generated++;
      this.initGenerated++;
      let inModel: boolean, unseen = true, id = -1;
      try {
        inModel = m.constraints.every(c => this.evalPred(c, s, null));
        if (inModel) {
          this.fingerprint(s);
          id = this.states.length;
          unseen = this.fps.put(this.hasher.h1, this.hasher.h2, id) < 0;
          if (unseen) {
            this.states.push(s); this.parent.push(-1); this.level.push(1); this.act.push(-1); this.inits.push(id);
            if (this.opts.recordGraph) { this.succ.push([]); this.succAct.push([]); }
            this.depth = Math.max(this.depth, 1);
            this.initDistinct++;
          }
        }
      } catch (e) {
        return this.result('error', { message: this.describeErr(e), trace: [{ state: s, action: null, id: -1 }] });
      }
      if (unseen) {
        for (const inv of m.invariants) {
          let ok: boolean;
          try { ok = this.evalPred(inv, s, null); } catch (e) {
            return this.result('error', { message: `Evaluating invariant ${inv.name} failed.\n${this.describeErr(e)}`, trace: [{ state: s, action: null, id: -1 }] });
          }
          if (!ok) return this.result('invariant-init', { name: inv.name, trace: [{ state: s, action: null, id }], printSummary: false });
        }
        for (const p of m.impliedInits) {
          let ok: boolean;
          try { ok = this.evalPred(p, s, null); } catch (e) {
            return this.result('error', { message: `Evaluating property ${p.name} failed.\n${this.describeErr(e)}`, trace: [{ state: s, action: null, id: -1 }] });
          }
          if (!ok) return this.result('implied-init', { name: p.name, trace: [{ state: s, action: null, id }], printSummary: false });
        }
      }
    }
    return null;
  }

  // Successors of one state, as (state, action index) pairs in action order.
  successors(s: State, out: State[], outAct: number[]): void {
    const ev = this.ev, m = this.model, n = this.nvars;
    const actions = m.actions;
    for (let ai = 0; ai < actions.length; ai++) {
      const a = actions[ai];
      ev.cur = s; ev.nxt = new Array(n); ev.initMode = false; ev.primeDepth = 0; ev.callDepth = 0; ev.nAssigned = 0;
      const nxt = ev.nxt;
      ev.enumerate(a.e, a.ctx, () => {
        for (let k = 0; k < n; k++) {
          if (nxt[k] === undefined) {
            const missing = m.vars.filter((_, j) => nxt[j] === undefined).map(v => v.name).sort();
            const which = actions.length === 1 ? 'the next-state action' : `action ${a.name} of the next-state relation`;
            throw new CheckError(this.result('incomplete', {
              message: `Successor state is not completely specified by ${which}. The following variable${missing.length > 1 ? 's are' : ' is'} not defined: ${missing.join(', ')}.`,
            }));
          }
        }
        out.push(nxt.slice());
        outAct.push(ai);
      });
    }
  }

  run(): CheckResult {
    const m = this.model;
    const a0 = this.checkAssumptions();
    if (a0) return a0;
    const i0 = this.computeInit();
    if (i0) return i0;
    this.opts.onProgress?.(-1, this.initDistinct, 0);
    const succs: State[] = [], succAct: number[] = [];
    const record = !!this.opts.recordGraph;
    let lastProgress = Date.now();
    if (m.actions.length === 0 || m.inits.length === 0) return this.result('ok');
    while (this.head < this.states.length) {
      const sid = this.head++;
      const s = this.states[sid];
      this.curLevel = this.level[sid];
      succs.length = 0; succAct.length = 0;
      try {
        this.successors(s, succs, succAct);
      } catch (e) {
        if (e instanceof CheckError) { e.result.trace = this.traceTo(sid); e.result.queue = this.states.length - this.head; return e.result; }
        return this.result('error', { message: this.describeErr(e), trace: this.traceTo(sid) });
      }
      let fresh = 0;
      for (let i = 0; i < succs.length; i++) {
        const t = succs[i];
        this.generated++;
        let inModel = true, unseen = true, id = -1;
        try {
          for (const c of m.constraints) if (!this.evalPred(c, t, null)) { inModel = false; break; }
          if (inModel) for (const c of m.actionConstraints) if (!this.evalPred(c, s, t)) { inModel = false; break; }
          if (inModel) {
            this.fingerprint(t);
            const nid = this.states.length;
            const ex = this.fps.put(this.hasher.h1, this.hasher.h2, nid);
            if (ex < 0) {
              id = nid;
              this.states.push(t); this.parent.push(sid); this.level.push(this.level[sid] + 1); this.act.push(succAct[i]);
              if (record) { this.succ.push([]); this.succAct.push([]); }
              if (this.level[sid] + 1 > this.depth) this.depth = this.level[sid] + 1;
              fresh++;
            } else { unseen = false; id = ex; }
            if (record) { this.succ[sid].push(id); this.succAct[sid].push(succAct[i]); }
          }
        } catch (e) {
          return this.result('error', { message: this.describeErr(e), trace: [...this.traceTo(sid), { state: t, action: m.actions[succAct[i]], id: -1 }] });
        }
        if (unseen) {
          for (const inv of m.invariants) {
            let ok: boolean;
            try { ok = this.evalPred(inv, t, null); } catch (e) {
              return this.result('error', { message: `Evaluating invariant ${inv.name} failed.\n${this.describeErr(e)}`, trace: [...this.traceTo(sid), { state: t, action: m.actions[succAct[i]], id }] });
            }
            if (!ok) {
              const r = this.result('invariant', { name: inv.name, trace: [...this.traceTo(sid), { state: t, action: m.actions[succAct[i]], id }] });
              if (inModel) r.queue = Math.max(0, r.queue - 1);
              return r;
            }
          }
        }
        for (const p of m.impliedActions) {
          let ok: boolean;
          try { ok = this.evalPred(p, s, t); } catch (e) {
            return this.result('error', { message: `Evaluating action property ${p.name} failed.\n${this.describeErr(e)}`, trace: [...this.traceTo(sid), { state: t, action: m.actions[succAct[i]], id }] });
          }
          if (!ok) {
            const r = this.result('action-property', { name: p.name, trace: [...this.traceTo(sid), { state: t, action: m.actions[succAct[i]], id }] });
            if (inModel && unseen) r.queue = Math.max(0, r.queue - 1);
            return r;
          }
        }
      }
      this.outdeg.push(fresh);
      if (succs.length === 0 && this.opts.checkDeadlock) {
        return this.result('deadlock', { trace: this.traceTo(sid) });
      }
      if (this.opts.onProgress && (sid & 1023) === 0) {
        const now = Date.now();
        if (now - lastProgress > 60000) { lastProgress = now; this.opts.onProgress(this.generated, this.states.length, this.states.length - this.head); }
      }
    }
    const r = this.result('ok');
    return r;
  }
}
export { SetV };
