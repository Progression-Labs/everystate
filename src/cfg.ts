// TLC configuration (.cfg) file parser.
import { TlaError } from './lexer.ts';
import { modelValue, mkSet, strId } from './values.ts';
import type { Value } from './values.ts';

export interface Config {
  constants: { name: string; value?: Value; subst?: string; module?: string }[];
  init?: string;
  next?: string;
  spec?: string;
  invariants: string[];
  properties: string[];
  constraints: string[];
  actionConstraints: string[];
  symmetry?: string;
  view?: string;
  alias?: string;
  postcondition?: string;
  checkDeadlock?: boolean;
}

const SECTIONS = new Set(['CONSTANT', 'CONSTANTS', 'INIT', 'NEXT', 'SPECIFICATION', 'INVARIANT', 'INVARIANTS',
  'PROPERTY', 'PROPERTIES', 'CONSTRAINT', 'CONSTRAINTS', 'ACTION_CONSTRAINT', 'ACTION_CONSTRAINTS', 'SYMMETRY',
  'VIEW', 'CHECK_DEADLOCK', 'ALIAS', 'POSTCONDITION', 'TYPE', 'TYPE_CONSTRAINT']);

interface CTok { t: 'id' | 'num' | 'str' | 'sym' | 'eof'; v: string; line: number }

function tokenize(src: string): CTok[] {
  const out: CTok[] = [];
  let i = 0, line = 1;
  const n = src.length;
  while (i < n) {
    const c = src[i];
    if (c === '\n') { line++; i++; continue; }
    if (/\s/.test(c)) { i++; continue; }
    if (c === '\\' && src[i + 1] === '*') { while (i < n && src[i] !== '\n') i++; continue; }
    if (c === '(' && src[i + 1] === '*') {
      let depth = 1; i += 2;
      while (i < n && depth > 0) {
        if (src[i] === '\n') line++;
        if (src[i] === '(' && src[i + 1] === '*') { depth++; i += 2; }
        else if (src[i] === '*' && src[i + 1] === ')') { depth--; i += 2; }
        else i++;
      }
      continue;
    }
    if (c === '"') {
      let j = i + 1, s = '';
      while (j < n && src[j] !== '"') { if (src[j] === '\\') { j++; } s += src[j++]; }
      out.push({ t: 'str', v: s, line });
      i = j + 1;
      continue;
    }
    let m = /^-?\d+(?![A-Za-z_])/.exec(src.slice(i, i + 40));
    if (m) { out.push({ t: 'num', v: m[0], line }); i += m[0].length; continue; }
    m = /^[A-Za-z0-9_!]+/.exec(src.slice(i, i + 400));
    if (m) { out.push({ t: 'id', v: m[0], line }); i += m[0].length; continue; }
    if (src.startsWith('<-', i)) { out.push({ t: 'sym', v: '<-', line }); i += 2; continue; }
    out.push({ t: 'sym', v: c, line });
    i++;
  }
  out.push({ t: 'eof', v: '<EOF>', line });
  return out;
}

export function parseConfig(src: string): Config {
  const toks = tokenize(src);
  let p = 0;
  const cfg: Config = { constants: [], invariants: [], properties: [], constraints: [], actionConstraints: [] };
  const fail = (msg: string): never => {
    throw new TlaError(`TLC found an error in the configuration file at line ${toks[p].line}\n${msg}`, undefined, undefined, 'config');
  };
  const isSection = () => toks[p].t === 'id' && SECTIONS.has(toks[p].v);
  const parseValue = (): Value => {
    const t = toks[p++];
    if (t.t === 'num') return Number(t.v);
    if (t.t === 'str') { strId(t.v); return t.v; }
    if (t.t === 'id') {
      if (t.v === 'TRUE') return true;
      if (t.v === 'FALSE') return false;
      return modelValue(t.v);
    }
    if (t.t === 'sym' && t.v === '{') {
      const items: Value[] = [];
      if (toks[p].v === '}' && toks[p].t === 'sym') { p++; return mkSet(items); }
      for (;;) {
        items.push(parseValue());
        const s = toks[p++];
        if (s.t === 'sym' && s.v === '}') break;
        if (!(s.t === 'sym' && s.v === ',')) { p--; fail(`Expected ',' or '}' but found '${s.v}'`); }
      }
      return mkSet(items);
    }
    p--;
    return fail(`Unexpected token '${t.v}' in a constant value`);
  };
  const names = (into: string[]) => { while (toks[p].t === 'id' && !isSection()) into.push(toks[p++].v); };
  const one = (what: string): string => {
    if (toks[p].t !== 'id' || isSection()) fail(`Expected an identifier after ${what}`);
    return toks[p++].v;
  };
  while (toks[p].t !== 'eof') {
    const t = toks[p];
    if (!isSection()) fail(`Unexpected token '${t.v}'; expected a configuration keyword`);
    p++;
    switch (t.v) {
      case 'CONSTANT': case 'CONSTANTS':
        while (toks[p].t === 'id' && !isSection()) {
          const name = toks[p++].v;
          const op = toks[p++];
          if (op.t === 'sym' && op.v === '=') {
            let module: string | undefined;
            if (toks[p].t === 'sym' && toks[p].v === '[') { p++; module = toks[p++].v; p++; }
            cfg.constants.push({ name, value: parseValue(), module });
          } else if (op.t === 'sym' && op.v === '<-') {
            let module: string | undefined;
            if (toks[p].t === 'sym' && toks[p].v === '[') { p++; module = toks[p++].v; p++; }
            cfg.constants.push({ name, subst: toks[p++].v, module });
          } else { p--; fail(`Expected '=' or '<-' after constant ${name} but found '${op.v}'`); }
        }
        break;
      case 'INIT': cfg.init = one('INIT'); break;
      case 'NEXT': cfg.next = one('NEXT'); break;
      case 'SPECIFICATION': cfg.spec = one('SPECIFICATION'); break;
      case 'INVARIANT': case 'INVARIANTS': names(cfg.invariants); break;
      case 'PROPERTY': case 'PROPERTIES': names(cfg.properties); break;
      case 'CONSTRAINT': case 'CONSTRAINTS': names(cfg.constraints); break;
      case 'ACTION_CONSTRAINT': case 'ACTION_CONSTRAINTS': names(cfg.actionConstraints); break;
      case 'SYMMETRY': cfg.symmetry = one('SYMMETRY'); break;
      case 'VIEW': cfg.view = one('VIEW'); break;
      case 'ALIAS': cfg.alias = one('ALIAS'); break;
      case 'POSTCONDITION': cfg.postcondition = one('POSTCONDITION'); break;
      case 'CHECK_DEADLOCK': {
        const v = one('CHECK_DEADLOCK');
        cfg.checkDeadlock = v === 'TRUE';
        break;
      }
      default: names([]);
    }
  }
  return cfg;
}
