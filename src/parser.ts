// TLA+ parser: tokens -> AST. Hand-written recursive descent with precedence climbing and
// column-sensitive junction lists.
import { lex, TlaError } from './lexer.ts';
import type { Tok, Loc } from './lexer.ts';
import { strId } from './values.ts';

export interface Node {
  k: string;
  loc: Loc;
  [key: string]: any;
}
export interface Param { name: string; arity: number }
export interface Bound { names: string[] | null; tuple: string[] | null; set: Node | null }
export interface DefNode extends Node {
  k: 'def';
  name: string;
  params: Param[];
  body: Node;
  local: boolean;
}
export interface ModuleNode extends Node {
  k: 'module';
  name: string;
  extends: string[];
  units: Node[];
}

// [lo, hi, leftAssoc]
const INFIX: Record<string, [number, number, boolean]> = {
  '=>': [1, 1, false], '-+->': [2, 2, false], '<=>': [2, 2, false], '~>': [2, 2, false],
  '\\/': [3, 3, true], '/\\': [3, 3, true],
  '\\cdot': [5, 14, true], '@@': [6, 6, true], ':>': [7, 7, false], '<:': [7, 7, false],
  '\\': [8, 8, false], '\\cap': [8, 8, true], '\\cup': [8, 8, true],
  '..': [9, 9, false], '...': [9, 9, false],
  '!!': [9, 13, false], '##': [9, 13, true], '$': [9, 13, true], '$$': [9, 13, true], '??': [9, 13, true],
  '\\sqcap': [9, 13, true], '\\sqcup': [9, 13, true], '\\uplus': [9, 13, true], '\\wr': [9, 14, false],
  '\\oplus': [10, 10, true], '+': [10, 10, true], '++': [10, 10, true],
  '%': [10, 11, false], '%%': [10, 11, true], '|': [10, 11, true], '||': [10, 11, true],
  '\\X': [10, 13, false],
  '-': [11, 11, true], '--': [11, 11, true], '\\ominus': [11, 11, true],
  '&': [13, 13, true], '&&': [13, 13, true], '*': [13, 13, true], '**': [13, 13, true], '/': [13, 13, false],
  '//': [13, 13, false], '\\div': [13, 13, false], '\\odot': [13, 13, true], '\\oslash': [13, 13, false],
  '\\otimes': [13, 13, true], '\\bigcirc': [13, 13, true], '\\bullet': [13, 13, true], '\\o': [13, 13, true],
  '\\star': [13, 13, true], '^': [14, 14, false], '^^': [14, 14, false],
};
for (const r of ['=', '/=', '<', '>', '<=', '>=', '\\in', '\\notin', '\\subseteq', '\\subset', '\\supseteq',
  '\\supset', '\\prec', '\\preceq', '\\succ', '\\succeq', '\\ll', '\\gg', '\\sim', '\\simeq', '\\approx',
  '\\cong', '\\doteq', '\\asymp', '\\propto', '\\sqsubset', '\\sqsubseteq', '\\sqsupset', '\\sqsupseteq',
  '::=', ':=', '|-', '|=', '-|', '=|']) INFIX[r] = [5, 5, false];

const PREFIX: Record<string, [number, number]> = {
  '~': [4, 4], '[]': [4, 15], '<>': [4, 15], 'ENABLED': [4, 15], 'UNCHANGED': [4, 15],
  'SUBSET': [8, 8], 'UNION': [8, 8], 'DOMAIN': [8, 8], '-': [12, 12],
};
const POSTFIX = new Set(["'", '^+', '^*', '^#']);

// Operators with fixed (non user-definable) meaning get their own node kinds.
const FIXED: Record<string, string> = {
  '/\\': 'and', '\\/': 'or', '~': 'not', '=>': 'imp', '<=>': 'eqv', '=': 'eq', '/=': 'ne', '\\in': 'in',
  '\\notin': 'notin', '\\subseteq': 'subseteq', '\\cup': 'cup', '\\cap': 'cap', '\\': 'diff',
  'SUBSET': 'powerset', 'UNION': 'bigunion', 'DOMAIN': 'domain', "'": 'prime', 'ENABLED': 'enabled',
  'UNCHANGED': 'unchanged', '[]': 'always', '<>': 'eventually', '~>': 'leadsto', '-+->': 'guarantee',
  '\\cdot': 'cdot',
};

const THEOREM_KW = new Set(['THEOREM', 'LEMMA', 'PROPOSITION', 'COROLLARY']);
const UNIT_START_KW = new Set(['VARIABLE', 'VARIABLES', 'CONSTANT', 'CONSTANTS', 'RECURSIVE', 'LOCAL', 'INSTANCE',
  'ASSUME', 'ASSUMPTION', 'AXIOM', 'THEOREM', 'LEMMA', 'PROPOSITION', 'COROLLARY', 'USE', 'HIDE']);

class Parser {
  toks: Tok[];
  p = 0;
  js: number[] = []; // junction column stack; -1 = unconstrained
  last: Tok;
  mod: string;
  noArgs = false;
  constructor(toks: Tok[], mod: string) {
    this.toks = toks;
    this.last = toks[0];
    this.mod = mod;
  }
  static STOP: Tok = { t: 'eof', v: '<end of junction item>', line: 0, col: 0, ec: 0 };

  raw(): Tok { return this.toks[this.p]; }
  peek(): Tok {
    const t = this.toks[this.p];
    const n = this.js.length;
    if (n > 0 && t.col <= this.js[n - 1] && t.t !== 'eof') return Parser.STOP;
    return t;
  }
  peekAt(k: number): Tok { return this.toks[Math.min(this.p + k, this.toks.length - 1)]; }
  next(): Tok {
    const t = this.peek();
    if (t === Parser.STOP) this.fail('Unexpected end of junction list item');
    this.last = t;
    this.p++;
    return t;
  }
  isOp(v: string): boolean { const t = this.peek(); return t.t === 'op' && t.v === v; }
  isKw(v: string): boolean { const t = this.peek(); return t.t === 'kw' && t.v === v; }
  eatOp(v: string): boolean { if (this.isOp(v)) { this.next(); return true; } return false; }
  eatKw(v: string): boolean { if (this.isKw(v)) { this.next(); return true; } return false; }
  expectOp(v: string): Tok { if (!this.isOp(v)) this.fail(`Expected '${v}'`); return this.next(); }
  expectKw(v: string): Tok { if (!this.isKw(v)) this.fail(`Expected ${v}`); return this.next(); }
  expectId(): Tok { const t = this.peek(); if (t.t !== 'id') this.fail('Expected identifier'); return this.next(); }
  fail(msg: string): never {
    const t = this.raw();
    throw new TlaError(`${msg} but found '${t.v}' at line ${t.line}, col ${t.col} of module ${this.mod}`,
      [t.line, t.col, t.line, t.ec], this.mod, 'parse');
  }
  node(k: string, start: Tok | Node, props: object = {}): Node {
    const bl = 'loc' in start ? (start as Node).loc[0] : (start as Tok).line;
    const bc = 'loc' in start ? (start as Node).loc[1] : (start as Tok).col;
    return { k, loc: [bl, bc, this.last.line, this.last.ec], ...props };
  }

  // ---------- module level ----------
  parseModule(): ModuleNode {
    const start = this.raw();
    if (start.t !== 'sep') this.fail('Expected module header');
    this.next();
    this.expectKw('MODULE');
    const name = this.expectId().v;
    this.mod = name;
    if (this.raw().t !== 'sep') this.fail('Expected ---- after module name');
    this.next();
    const ext: string[] = [];
    if (this.eatKw('EXTENDS')) {
      do ext.push(this.expectId().v); while (this.eatOp(','));
    }
    const units: Node[] = [];
    for (;;) {
      const t = this.raw();
      if (t.t === 'end') { this.next(); break; }
      if (t.t === 'eof') this.fail('Unexpected end of file; module not terminated by ====');
      if (t.t === 'sep') {
        if (this.peekAt(1).t === 'kw' && this.peekAt(1).v === 'MODULE') {
          const inner = this.parseModule();
          this.mod = name;
          units.push(inner);
        } else this.next();
        continue;
      }
      const u = this.parseUnit();
      if (u) units.push(u);
    }
    return this.node('module', start, { name, extends: ext, units }) as ModuleNode;
  }

  parseUnit(): Node | null {
    const t = this.peek();
    if (t.t === 'kw') {
      switch (t.v) {
        case 'VARIABLE': case 'VARIABLES': {
          this.next();
          const names: string[] = [];
          do names.push(this.expectId().v); while (this.eatOp(','));
          return this.node('variables', t, { names });
        }
        case 'CONSTANT': case 'CONSTANTS': {
          this.next();
          const decls: Param[] = [];
          do decls.push(this.parseOpDecl()); while (this.eatOp(','));
          return this.node('constants', t, { decls });
        }
        case 'RECURSIVE': {
          this.next();
          const decls: Param[] = [];
          do decls.push(this.parseOpDecl()); while (this.eatOp(','));
          return this.node('recursive', t, { decls });
        }
        case 'LOCAL': {
          this.next();
          if (this.isKw('INSTANCE')) { const i = this.parseInstance(); i.local = true; return i; }
          const d = this.parseDef();
          d.local = true;
          return d;
        }
        case 'INSTANCE': return this.parseInstance();
        case 'ASSUME': case 'ASSUMPTION': case 'AXIOM': {
          this.next();
          let name: string | null = null;
          if (this.peek().t === 'id' && this.peekAt(1).t === 'op' && this.peekAt(1).v === '==') {
            name = this.next().v;
            this.next();
          }
          const e = this.parseExpr();
          return this.node('assume', t, { name, e });
        }
        case 'USE': case 'HIDE': this.next(); this.parseUseBody(); return null;
      }
      if (THEOREM_KW.has(t.v)) {
        this.next();
        let name: string | null = null;
        if (this.peek().t === 'id' && this.peekAt(1).t === 'op' && this.peekAt(1).v === '==') {
          name = this.next().v;
          this.next();
        }
        const e = this.isKw('ASSUME') ? this.parseAssumeProve() : this.parseExpr();
        const th = this.node('theorem', t, { name, e });
        this.parseProofOpt();
        return th;
      }
    }
    return this.parseDef();
  }

  parseOpDecl(): Param {
    const t = this.peek();
    if (t.t === 'id') {
      this.next();
      let arity = 0;
      if (this.eatOp('(')) {
        do { this.expectOp('_'); arity++; } while (this.eatOp(','));
        this.expectOp(')');
      }
      return { name: t.v, arity };
    }
    if (t.t === 'op' && t.v === '_') {
      this.next();
      const op = this.next();
      if (this.eatOp('_')) return { name: op.v, arity: 2 };
      return { name: op.v, arity: 1 }; // postfix
    }
    if (t.t === 'op' || t.t === 'kw') {
      this.next();
      this.expectOp('_');
      return { name: t.v === '-' ? '-.' : t.v, arity: 1 };
    }
    this.fail('Expected operator declaration');
  }

  parseInstance(): Node {
    const t = this.expectKw('INSTANCE');
    const module = this.expectId().v;
    const substs: { name: string; e: Node }[] = [];
    if (this.eatKw('WITH')) {
      do {
        const nt = this.next();
        if (nt.t !== 'id' && nt.t !== 'op') this.fail('Expected substitution target');
        this.expectOp('<-');
        substs.push({ name: nt.v, e: this.parseOpArg() });
      } while (this.eatOp(','));
    }
    return this.node('instance', t, { module, substs, local: false, name: null, params: [] });
  }

  // Definition: operator, function, or module (instance) definition.
  parseDef(): DefNode | Node {
    const t = this.peek();
    let name: string;
    let params: Param[] = [];
    let fnBounds: Bound[] | null = null;
    const nx = this.peekAt(1);
    if (t.t === 'op' && (PREFIX[t.v] || t.v === '-.') && nx.t === 'id') {
      // prefix operator definition
      this.next();
      name = t.v === '-' ? '-.' : t.v;
      params = [{ name: this.expectId().v, arity: 0 }];
    } else if (t.t === 'kw' && PREFIX[t.v] && nx.t === 'id') {
      this.fail(`Cannot redefine ${t.v}`);
    } else if (t.t === 'id') {
      this.next();
      name = t.v;
      const n1 = this.peek();
      if (n1.t === 'op' && n1.v === '(') {
        this.next();
        do params.push(this.parseOpDecl()); while (this.eatOp(','));
        this.expectOp(')');
      } else if (n1.t === 'op' && n1.v === '[') {
        this.next();
        this.js.push(-1);
        fnBounds = this.parseBounds();
        this.js.pop();
        this.expectOp(']');
      } else if (n1.t === 'op' && INFIX[n1.v] && this.peekAt(1).t === 'id') {
        this.next();
        params = [{ name: t.v, arity: 0 }, { name: this.expectId().v, arity: 0 }];
        name = n1.v;
      } else if (n1.t === 'op' && POSTFIX.has(n1.v)) {
        this.next();
        params = [{ name: t.v, arity: 0 }];
        name = n1.v;
      }
    } else this.fail('Expected a definition or declaration');
    const defTok = this.expectOp('==');
    if (this.isKw('INSTANCE')) {
      const inst = this.parseInstance();
      inst.name = name;
      inst.params = params;
      inst.loc = [t.line, t.col, this.last.line, this.last.ec];
      return inst;
    }
    void defTok;
    let body = this.parseExpr();
    if (fnBounds) body = { k: 'fndef', loc: body.loc, bounds: fnBounds, body, recname: name };
    return this.node('def', t, { name, params, body, local: false }) as DefNode;
  }

  // ---------- proofs (parsed and discarded) ----------
  parseAssumeProve(): Node {
    const t = this.expectKw('ASSUME');
    do {
      if (this.isKw('ASSUME')) { this.parseAssumeProve(); continue; }
      if (this.isKw('NEW') || this.isKw('CONSTANT') || this.isKw('VARIABLE') || this.isKw('STATE') ||
        this.isKw('ACTION') || this.isKw('TEMPORAL')) {
        this.eatKw('NEW');
        const lvl = this.peek();
        if (lvl.t === 'kw' && ['CONSTANT', 'VARIABLE', 'STATE', 'ACTION', 'TEMPORAL'].includes(lvl.v)) this.next();
        this.parseOpDecl();
        if (this.eatOp('\\in')) this.parseExpr();
        continue;
      }
      this.parseExpr();
    } while (this.eatOp(','));
    this.expectKw('PROVE');
    const e = this.parseExpr();
    return this.node('assumeprove', t, { e });
  }

  parseUseBody(): void {
    // [ONLY] facts [DEF(S) names]
    this.eatKw('ONLY');
    const isDef = () => this.isKw('DEF') || this.isKw('DEFS');
    if (!isDef()) {
      do {
        if (this.eatKw('MODULE')) { this.expectId(); continue; }
        this.parseExpr();
      } while (this.eatOp(','));
    }
    if (isDef()) {
      this.next();
      do {
        if (this.eatKw('MODULE')) { this.expectId(); continue; }
        if (this.peek().t === 'op' && this.peek().v !== '(') { this.next(); continue; }
        this.parseOpArg();
      } while (this.eatOp(','));
    }
  }

  parseProofOpt(): void {
    const t = this.peek();
    if (t.t === 'kw') {
      if (t.v === 'PROOF') {
        this.next();
        this.parseProofOpt();
        return;
      }
      if (t.v === 'OBVIOUS' || t.v === 'OMITTED') { this.next(); return; }
      if (t.v === 'BY') { this.next(); this.parseUseBody(); return; }
    }
    if (t.t === 'step') this.parseSteps();
  }

  stepLevel(t: Tok): string { return /^<(\d+|\*|\+)>/.exec(t.v)![1]; }

  parseSteps(): void {
    // All steps at this level until QED.
    for (;;) {
      const t = this.peek();
      if (t.t !== 'step') return;
      this.next();
      const k = this.peek();
      if (k.t === 'kw') {
        switch (k.v) {
          case 'QED': this.next(); this.parseProofOpt(); return;
          case 'USE': case 'HIDE': this.next(); this.parseUseBody(); continue;
          case 'DEFINE': this.next(); this.parseStepDefs(); continue;
          case 'HAVE': this.next(); this.parseExpr(); continue;
          case 'WITNESS': this.next(); do this.parseExpr(); while (this.eatOp(',')); continue;
          case 'TAKE': this.next(); this.parseTakeBounds(); continue;
          case 'PICK': this.next(); this.parseTakeBounds(); this.expectOp(':'); this.parseExpr(); this.parseProofOpt(); continue;
          case 'CASE': this.next(); this.parseExpr(); this.parseProofOpt(); continue;
          case 'SUFFICES':
            this.next();
            if (this.isKw('ASSUME')) this.parseAssumeProve(); else this.parseExpr();
            this.parseProofOpt();
            continue;
          case 'ASSUME': this.parseAssumeProve(); this.parseProofOpt(); continue;
          case 'INSTANCE': this.parseInstance(); continue;
        }
      }
      // definition step without DEFINE, or an assertion
      if (this.looksLikeDef()) { this.parseStepDefs(); continue; }
      this.parseExpr();
      this.parseProofOpt();
    }
  }

  looksLikeDef(): boolean {
    const save = this.p, saveLast = this.last, js = this.js.slice();
    try {
      const t = this.peek();
      if (t.t !== 'id' && !(t.t === 'op' && PREFIX[t.v])) return false;
      this.parseDef();
      return true;
    } catch {
      return false;
    } finally {
      this.p = save; this.last = saveLast; this.js = js;
    }
  }

  parseStepDefs(): void {
    do this.parseDef(); while (this.peek().t === 'id' && this.looksLikeDef());
  }

  parseTakeBounds(): void {
    // x, y  |  x \in S, y \in T
    const save = this.p;
    try {
      const b = this.parseBounds();
      if (b.length) return;
    } catch { /* fall through */ }
    this.p = save;
    do this.expectId(); while (this.eatOp(','));
  }

  // ---------- expressions ----------
  parseExpr(): Node { return this.parseBin(0); }

  parseBin(minPrec: number): Node {
    let left = this.parsePrefix(minPrec);
    for (;;) {
      const t = this.peek();
      if (t.t !== 'op') break;
      const info = INFIX[t.v];
      if (!info) break;
      if (info[0] < minPrec) break;
      this.next();
      const op = t.v;
      if (op === '\\X') {
        const items = [left, this.parseBin(info[1] + 1)];
        while (this.isOp('\\X')) { this.next(); items.push(this.parseBin(info[1] + 1)); }
        left = this.node('cross', left, { a: items });
        continue;
      }
      const right = this.parseBin(info[1] + 1);
      const fixed = FIXED[op];
      if (fixed === 'and' || fixed === 'or') {
        if (left.k === fixed && !left.junction && !left.paren) { left.a.push(right); left.loc = [left.loc[0], left.loc[1], this.last.line, this.last.ec]; }
        else left = this.node(fixed, left, { a: [left, right] });
      } else if (fixed) left = this.node(fixed, left, { a: [left, right] });
      else left = this.node('app', left, { name: op, args: [left, right] });
    }
    return left;
  }

  parsePrefix(minPrec: number): Node {
    const t = this.peek();
    if ((t.t === 'op' || t.t === 'kw') && PREFIX[t.v]) {
      // "-" followed by nothing useful, or operator used as argument, are handled by parseOpArg.
      const info = PREFIX[t.v];
      this.next();
      const arg = this.parseBin(info[1] + 1);
      let e: Node;
      if (t.v === '-') e = this.node('app', t, { name: '-.', args: [arg] });
      else e = this.node(FIXED[t.v], t, { a: [arg] });
      return this.parsePostfixOps(e, minPrec);
    }
    return this.parsePostfixOps(this.parsePrimary(), minPrec);
  }

  parsePostfixOps(e: Node, minPrec: number): Node {
    for (;;) {
      const t = this.peek();
      if (t.t !== 'op') break;
      if (t.v === '[') {
        this.next();
        this.js.push(-1);
        const args = [this.parseExpr()];
        while (this.eatOp(',')) args.push(this.parseExpr());
        this.js.pop();
        this.expectOp(']');
        e = this.node('fnapp', e, { f: e, args });
      } else if (t.v === '.') {
        this.next();
        const f = this.next();
        if (f.t !== 'id' && f.t !== 'kw') this.fail('Expected field name');
        e = this.node('dot', e, { e, field: f.v });
      } else if (t.v === "'") {
        this.next();
        e = this.node('prime', e, { a: [e] });
      } else if (POSTFIX.has(t.v)) {
        this.next();
        e = this.node('app', e, { name: t.v, args: [e] });
      } else break;
    }
    void minPrec;
    return e;
  }

  // An operator argument: expression, or a bare operator symbol (e.g. F(+, 1)), or LAMBDA.
  parseOpArg(): Node {
    const t = this.peek();
    if ((t.t === 'op' && (INFIX[t.v] || POSTFIX.has(t.v) || t.v === '-.' || PREFIX[t.v])) || (t.t === 'kw' && PREFIX[t.v])) {
      const n = this.peekAt(1);
      if (n.t === 'op' && (n.v === ',' || n.v === ')') || n.t === 'eof' || n.t === 'end' || n.t === 'sep' ||
        (n.t === 'kw' && UNIT_START_KW.has(n.v))) {
        this.next();
        return this.opRef(t);
      }
    }
    return this.parseExpr();
  }

  // A bare operator symbol used as an operator argument. Built-in (non-definable) operators become LAMBDAs.
  opRef(t: Tok): Node {
    const fixed = FIXED[t.v];
    if (!fixed) return this.node('app', t, { name: t.v, args: [] });
    const loc: Loc = [t.line, t.col, t.line, t.ec];
    const arg = (name: string): Node => ({ k: 'app', loc, name, args: [] });
    if (PREFIX[t.v] || t.v === "'") return { k: 'lambda', loc, params: [{ name: '_a', arity: 0 }], body: { k: fixed, loc, a: [arg('_a')] } };
    return { k: 'lambda', loc, params: [{ name: '_a', arity: 0 }, { name: '_b', arity: 0 }], body: { k: fixed, loc, a: [arg('_a'), arg('_b')] } };
  }

  // Non-fix application of an infix/postfix operator symbol: +(a, b), \in(x, S), ^+(a), -.(a)
  prefixApply(t: Tok): Node {
    this.next();
    this.next();
    const args = this.parseArgs();
    const fixed = FIXED[t.v];
    const want = POSTFIX.has(t.v) || t.v === '-.' ? 1 : 2;
    if (args.length !== want) this.fail(`The operator ${t.v} requires ${want} arguments`);
    if (fixed) return this.node(fixed, t, { a: args });
    return this.node('app', t, { name: t.v, args });
  }

  parseArgs(): Node[] {
    // after '('
    this.js.push(-1);
    const args: Node[] = [];
    do args.push(this.parseOpArg()); while (this.eatOp(','));
    this.js.pop();
    this.expectOp(')');
    return args;
  }

  parseJunction(bullet: string): Node {
    const first = this.peek();
    const col = first.col;
    const items: Node[] = [];
    for (;;) {
      const r = this.raw();
      if (!(r.t === 'op' && r.v === bullet && r.col === col)) break;
      // the bullet must itself be visible to the enclosing junction context
      if (this.peek() === Parser.STOP) break;
      this.next();
      this.js.push(col);
      items.push(this.parseExpr());
      this.js.pop();
    }
    const kind = bullet === '/\\' ? 'and' : 'or';
    if (items.length === 1) {
      const it = items[0];
      return it.k === 'and' || it.k === 'or' ? { ...it, junction: true } : it;
    }
    return this.node(kind, first, { a: items, junction: true });
  }

  // names (\in set)? groups separated by commas. Returns [] if no bound parsed.
  parseBounds(): Bound[] {
    const out: Bound[] = [];
    for (;;) {
      const t = this.peek();
      if (t.t === 'op' && t.v === '<<') {
        this.next();
        const tuple: string[] = [];
        if (!this.isOp('>>')) do tuple.push(this.expectId().v); while (this.eatOp(','));
        this.expectOp('>>');
        this.expectOp('\\in');
        out.push({ names: null, tuple, set: this.parseExpr() });
      } else {
        const names = [this.expectId().v];
        while (this.eatOp(',')) names.push(this.expectId().v);
        if (this.eatOp('\\in')) out.push({ names, tuple: null, set: this.parseExpr() });
        else out.push({ names, tuple: null, set: null });
      }
      if (!this.eatOp(',')) break;
    }
    return out;
  }

  attempt<T>(f: () => T): T | null {
    const save = this.p, saveLast = this.last, js = this.js.slice();
    try {
      return f();
    } catch (e) {
      if (!(e instanceof TlaError)) throw e;
      this.p = save; this.last = saveLast; this.js = js;
      return null;
    }
  }

  parsePrimary(): Node {
    const t = this.peek();
    switch (t.t) {
      case 'num': this.next(); return this.node('num', t, { v: t.n });
      case 'str': this.next(); return this.node('str', t, { v: t.v });
      case 'step':
        this.next();
        while (this.isOp('!')) { this.next(); this.next(); }
        return this.node('stepref', t, { v: t.v });
      case 'id': return this.parseIdent();
      case 'kw': return this.parseKeywordExpr(t);
      case 'op': break;
      default: this.fail('Expected expression');
    }
    switch (t.v) {
      case '(': {
        this.next();
        this.js.push(-1);
        const e = this.parseExpr();
        this.js.pop();
        this.expectOp(')');
        // mark parenthesised junctions so they do not merge with neighbours
        return e.k === 'and' || e.k === 'or' ? { ...e, paren: true } : e;
      }
      case '/\\': case '\\/': return this.parseJunction(t.v);
      case '<<': {
        this.next();
        this.js.push(-1);
        const items: Node[] = [];
        if (!this.isOp('>>') && !this.isOp('>>_')) do items.push(this.parseExpr()); while (this.eatOp(','));
        this.js.pop();
        if (this.eatOp('>>_')) {
          const v = this.parseSubscript();
          if (items.length !== 1) this.fail('<<A>>_v requires exactly one action');
          return this.node('angleact', t, { a: [items[0], v] });
        }
        this.expectOp('>>');
        return this.node('tuple', t, { a: items });
      }
      case '{': return this.parseSet(t);
      case '[': return this.parseBracket(t);
      case '\\A': case '\\E': {
        this.next();
        const bounds = this.parseBounds();
        this.expectOp(':');
        const body = this.parseExpr();
        return this.node('quant', t, { q: t.v === '\\A' ? 'A' : 'E', bounds, body });
      }
      case '\\AA': case '\\EE': {
        this.next();
        const names = [this.expectId().v];
        while (this.eatOp(',')) names.push(this.expectId().v);
        this.expectOp(':');
        const body = this.parseExpr();
        return this.node('tquant', t, { q: t.v, names, body });
      }
      case '@': this.next(); return this.node('at', t);
    }
    {
      const n1 = this.peekAt(1);
      if ((INFIX[t.v] || POSTFIX.has(t.v) || t.v === '-.') && t.v !== '-' && n1.t === 'op' && n1.v === '(') return this.prefixApply(t);
    }
    this.fail('Expected expression');
  }

  parseSubscript(): Node {
    // subscript of [A]_v, <<A>>_v, WF_v, SF_v: an identifier-ish expression or parenthesised/tuple expr
    let e: Node;
    if (this.peek().t === 'id') {
      const t = this.next();
      let name = t.v;
      while (this.isOp('!') && this.peekAt(1).t === 'id') { this.next(); name += '!' + this.next().v; }
      e = this.node('app', t, { name, args: [] });
    } else e = this.parsePrimary();
    while (this.isOp('.') || this.isOp('[')) {
      if (this.eatOp('.')) { const f = this.next(); e = this.node('dot', e, { e, field: f.v }); }
      else {
        this.next(); this.js.push(-1);
        const args = [this.parseExpr()];
        while (this.eatOp(',')) args.push(this.parseExpr());
        this.js.pop(); this.expectOp(']');
        e = this.node('fnapp', e, { f: e, args });
      }
    }
    return e;
  }

  parseIdent(): Node {
    const t = this.next();
    let name = t.v;
    let args: Node[] = [];
    if (this.isOp('(')) { this.next(); args = this.parseArgs(); }
    // label:  lab:: expr
    if (this.isOp('::')) { this.next(); return this.parseExpr(); }
    // instance path: A!B(x)!C, and subexpression selectors Op!2, Op!<<, Op!(x)
    let sel: any[] | null = null;
    while (this.isOp('!')) {
      const n1 = this.peekAt(1);
      const n2 = this.peekAt(2);
      if (!sel && (n1.t === 'id' || (n1.t === 'op' && INFIX[n1.v] !== undefined && ((n1.v !== '<' && n1.v !== ':>') || (n2.t === 'op' && n2.v === '('))) ||
        (n1.t === 'op' && (n1.v === '-.' || (POSTFIX.has(n1.v) && n1.v !== "'")) && n2.t === 'op' && n2.v === '(')) && !(n1.t === 'op' && n1.v === '<<')) {
        this.next();
        const part = this.next();
        name += '!' + part.v;
        if (this.isOp('(')) { this.next(); args = args.concat(this.parseArgs()); }
      } else if (n1.t === 'num' || (n1.t === 'op' && (n1.v === '<<' || n1.v === '>>' || n1.v === ':' || n1.v === '@' || n1.v === '('))) {
        this.next();
        sel = sel ?? [];
        const s1 = this.next();
        if (s1.v === '(') sel.push(this.parseArgs());
        else sel.push(s1.t === 'num' ? s1.n : s1.v);
      } else break;
    }
    if (sel) return this.node('app', t, { name, args, sel });
    return this.node('app', t, { name, args });
  }

  parseKeywordExpr(t: Tok): Node {
    switch (t.v) {
      case 'TRUE': this.next(); return this.node('bool', t, { v: true });
      case 'FALSE': this.next(); return this.node('bool', t, { v: false });
      case 'IF': {
        this.next();
        const c = this.parseExpr();
        this.expectKw('THEN');
        const a = this.parseExpr();
        this.expectKw('ELSE');
        const b = this.parseExpr();
        return this.node('if', t, { a: [c, a, b] });
      }
      case 'CASE': {
        this.next();
        const arms: { c: Node; e: Node }[] = [];
        let other: Node | null = null;
        for (;;) {
          if (this.eatKw('OTHER')) {
            this.expectOp('->');
            other = this.parseExpr();
            break; // OTHER is always the last arm; a following [] belongs to an enclosing CASE
          } else {
            const c = this.parseExpr();
            this.expectOp('->');
            arms.push({ c, e: this.parseExpr() });
          }
          if (!this.eatOp('[]')) break;
        }
        return this.node('case', t, { arms, other });
      }
      case 'LET': {
        this.next();
        const defs: Node[] = [];
        this.js.push(-1);
        while (!this.isKw('IN')) {
          if (this.isKw('RECURSIVE')) {
            this.next();
            do this.parseOpDecl(); while (this.eatOp(','));
            continue;
          }
          defs.push(this.parseDef());
        }
        this.js.pop();
        this.expectKw('IN');
        const body = this.parseExpr();
        return this.node('let', t, { defs, body });
      }
      case 'CHOOSE': {
        this.next();
        const b = this.parseBounds();
        if (b.length !== 1 || (b[0].names && b[0].names.length !== 1)) this.fail('CHOOSE takes one bound variable');
        this.expectOp(':');
        const body = this.parseExpr();
        return this.node('choose', t, { bound: b[0], body });
      }
      case 'LAMBDA': {
        this.next();
        const params: Param[] = [];
        do params.push({ name: this.expectId().v, arity: 0 }); while (this.eatOp(','));
        this.expectOp(':');
        const body = this.parseExpr();
        return this.node('lambda', t, { params, body });
      }
      case 'WF_': case 'SF_': {
        this.next();
        const v = this.parseSubscript();
        this.expectOp('(');
        this.js.push(-1);
        const a = this.parseExpr();
        this.js.pop();
        this.expectOp(')');
        return this.node(t.v === 'WF_' ? 'wf' : 'sf', t, { a: [v, a] });
      }
    }
    this.fail('Expected expression');
  }

  parseSet(t: Tok): Node {
    this.next();
    this.js.push(-1);
    try {
      if (this.eatOp('}')) return this.node('setenum', t, { a: [] });
      // {x \in S : P}
      const p0 = this.peek();
      const p1 = this.peekAt(1);
      if ((p0.t === 'id' && p1.t === 'op' && p1.v === '\\in') || (p0.t === 'op' && p0.v === '<<')) {
        const r = this.attempt(() => {
          let bound: Bound;
          if (p0.t === 'id') {
            this.next(); this.next();
            bound = { names: [p0.v], tuple: null, set: this.parseExpr() };
          } else {
            this.next();
            const tuple: string[] = [];
            do tuple.push(this.expectId().v); while (this.eatOp(','));
            this.expectOp('>>');
            this.expectOp('\\in');
            bound = { names: null, tuple, set: this.parseExpr() };
          }
          this.expectOp(':');
          const pred = this.parseExpr();
          this.expectOp('}');
          return this.node('setfilter', t, { bound, pred });
        });
        if (r) return r;
      }
      const first = this.parseExpr();
      if (this.eatOp(':')) {
        const bounds = this.parseBounds();
        this.expectOp('}');
        return this.node('setmap', t, { e: first, bounds });
      }
      const items = [first];
      while (this.eatOp(',')) items.push(this.parseExpr());
      this.expectOp('}');
      return this.node('setenum', t, { a: items });
    } finally {
      this.js.pop();
    }
  }

  parseBracket(t: Tok): Node {
    this.next();
    this.js.push(-1);
    try {
      const p0 = this.peek();
      const p1 = this.peekAt(1);
      if ((p0.t === 'id' || p0.t === 'kw') && p1.t === 'op' && (p1.v === '|->' || p1.v === ':')) {
        const isRec = p1.v === '|->';
        const fields: { name: string; e: Node }[] = [];
        do {
          const f = this.next();
          this.expectOp(isRec ? '|->' : ':');
          fields.push({ name: f.v, e: this.parseExpr() });
        } while (this.eatOp(','));
        this.expectOp(']');
        return this.node(isRec ? 'rec' : 'recset', t, { fields });
      }
      // [x \in S |-> e]
      if (p0.t === 'id' || (p0.t === 'op' && p0.v === '<<')) {
        const r = this.attempt(() => {
          const bounds = this.parseBounds();
          if (bounds.some(b => !b.set)) this.fail('Expected bound');
          this.expectOp('|->');
          const body = this.parseExpr();
          this.expectOp(']');
          return this.node('fndef', t, { bounds, body });
        });
        if (r) return r;
      }
      const e = this.parseExpr();
      if (this.eatOp('->')) {
        const rng = this.parseExpr();
        this.expectOp(']');
        return this.node('fnset', t, { a: [e, rng] });
      }
      if (this.eatKw('EXCEPT')) {
        const updates: { path: Node[]; val: Node }[] = [];
        do {
          this.expectOp('!');
          const path: Node[] = [];
          for (;;) {
            if (this.eatOp('.')) {
              const f = this.next();
              path.push({ k: 'str', loc: [f.line, f.col, f.line, f.ec], v: f.v });
            } else if (this.isOp('[')) {
              this.next();
              const idx = [this.parseExpr()];
              while (this.eatOp(',')) idx.push(this.parseExpr());
              this.expectOp(']');
              path.push(idx.length === 1 ? idx[0] : { k: 'tuple', loc: idx[0].loc, a: idx });
            } else break;
          }
          if (!path.length) this.fail('Expected EXCEPT path');
          this.expectOp('=');
          updates.push({ path, val: this.parseExpr() });
        } while (this.eatOp(','));
        this.expectOp(']');
        return this.node('except', t, { base: e, updates });
      }
      if (this.eatOp(']_')) {
        this.js.pop();
        this.js.push(this.js.length ? this.js[this.js.length - 1] : -1);
        const v = this.parseSubscript();
        return this.node('boxact', t, { a: [e, v] });
      }
      this.fail("Expected ']', '->', 'EXCEPT' or ']_'");
    } finally {
      this.js.pop();
    }
  }
}

export function parseModule(src: string, nameHint = '?'): ModuleNode {
  const toks = lex(src, nameHint, strId);
  const p = new Parser(toks, nameHint);
  const m = p.parseModule();
  m.strings = toks.filter(t => t.t === 'str').map(t => t.v);
  return m;
}

// Parse a standalone expression (used for config values and tests).
export function parseExpression(src: string): Node {
  const toks = lex(src, '<expr>');
  const p = new Parser(toks, '<expr>');
  const e = p.parseExpr();
  if (p.raw().t !== 'eof') p.fail('Unexpected trailing input');
  return e;
}
