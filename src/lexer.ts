// TLA+ lexer. Produces a flat token array for one source file.

export type Loc = [number, number, number, number]; // begin line, begin col, end line, end col (inclusive, 1-based)

export class TlaError extends Error {
  loc?: Loc;
  module?: string;
  kind: string;
  constructor(msg: string, loc?: Loc, module?: string, kind = 'error') {
    super(msg);
    this.loc = loc;
    this.module = module;
    this.kind = kind;
  }
}

export type TokType = 'id' | 'num' | 'str' | 'op' | 'kw' | 'step' | 'sep' | 'end' | 'eof' | 'bad';
export interface Tok {
  t: TokType;
  v: string;
  line: number;
  col: number;
  ec: number; // end column (inclusive)
  n?: number;
}

const KEYWORDS = new Set([
  'ASSUME', 'ASSUMPTION', 'AXIOM', 'CASE', 'CHOOSE', 'CONSTANT', 'CONSTANTS', 'DOMAIN', 'ELSE', 'ENABLED',
  'EXCEPT', 'EXTENDS', 'IF', 'IN', 'INSTANCE', 'LET', 'LOCAL', 'MODULE', 'OTHER', 'SUBSET', 'THEN', 'THEOREM',
  'UNCHANGED', 'UNION', 'VARIABLE', 'VARIABLES', 'WITH', 'LAMBDA', 'RECURSIVE', 'PROPOSITION', 'LEMMA',
  'COROLLARY', 'BY', 'OBVIOUS', 'OMITTED', 'PROOF', 'QED', 'HAVE', 'TAKE', 'WITNESS', 'PICK', 'SUFFICES',
  'PROVE', 'DEFINE', 'DEF', 'DEFS', 'USE', 'HIDE', 'ONLY', 'NEW', 'STATE', 'ACTION', 'TEMPORAL', 'TRUE', 'FALSE',
]);

// Symbol tokens, longest first.
const SYMBOLS = [
  '-+->', '(\\X)', '<=>', '...', '::=', '|->', '(+)', '(-)', '(.)', '(/)', '>>_',
  '=>', '~>', '->', '<-', '==', '=<', '<=', '>=', '/=', '/\\', '..', ':=', '::', ':>', '<:', '@@', '!!', '##',
  '$$', '??', '%%', '&&', '**', '++', '--', '//', '^^', '||', '|-', '|=', '-|', '=|', '<<', '>>', ']_', '[]',
  '<>', '^+', '^*', '^#', '-.',
  '~', '=', '<', '>', '#', '$', '%', '&', '*', '+', '-', '/', '^', '|', '(', ')', '[', ']', '{', '}', ',', ':',
  ';', '.', '!', '@', '_', "'",
];
const SYM_BY_CHAR = new Map<string, string[]>();
for (const s of SYMBOLS) {
  const l = SYM_BY_CHAR.get(s[0]) ?? [];
  l.push(s);
  SYM_BY_CHAR.set(s[0], l);
}

// Canonical spellings for operator synonyms.
const CANON: Record<string, string> = {
  '\\land': '/\\', '\\lor': '\\/', '\\lnot': '~', '\\neg': '~', '\\equiv': '<=>', '#': '/=', '\\neq': '/=',
  '=<': '<=', '\\leq': '<=', '\\geq': '>=', '\\union': '\\cup', '\\intersect': '\\cap', '\\times': '\\X',
  '\\circ': '\\o', '(+)': '\\oplus', '(-)': '\\ominus', '(.)': '\\odot', '(/)': '\\oslash', '(\\X)': '\\otimes',
  '\\notin': '\\notin', '\\forall': '\\A', '\\exists': '\\E', '\\mod': '%',
};

const UNICODE: Record<string, string> = {
  '∧': '/\\', '∨': '\\/', '¬': '~', '∈': '\\in', '∉': '\\notin', '⇒': '=>', '≡': '<=>', '⇔': '<=>', '≠': '/=', '≤': '<=',
  '≥': '>=', '∪': '\\cup', '∩': '\\cap', '⊆': '\\subseteq', '×': '\\X', '∀': '\\A', '∃': '\\E', '□': '[]', '◇': '<>',
  '↦': '|->', '→': '->', '←': '<-', '≜': '==', '⟨': '<<', '⟩': '>>', '∘': '\\o', '÷': '\\div', '⊂': '\\subset',
  '⊃': '\\supset', '⊇': '\\supseteq', '↝': '~>', '‥': '..', '⋅': '\\cdot',
};

const isAlpha = (c: number) => (c >= 65 && c <= 90) || (c >= 97 && c <= 122);
const isDigit = (c: number) => c >= 48 && c <= 57;
const isIdChar = (c: number) => isAlpha(c) || isDigit(c) || c === 95;

export function lex(src: string, moduleName?: string, intern?: (s: string) => void): Tok[] {
  const toks: Tok[] = [];
  if (src.includes('\t')) {
    // expand tabs to 8-column tab stops so that junction-list alignment works
    src = src.split('\n').map(l => {
      if (!l.includes('\t')) return l;
      let o = '';
      for (const ch of l) o += ch === '\t' ? ' '.repeat(8 - (o.length % 8)) : ch;
      return o;
    }).join('\n');
  }
  let i = 0;
  let line = 1;
  let lineStart = 0;
  const n = src.length;
  // Skip any prelude before the first module header.
  const m = /-{4,}[ \t]*MODULE\b/.exec(src);
  if (m) {
    for (let k = 0; k < m.index; k++) if (src.charCodeAt(k) === 10) { line++; lineStart = k + 1; }
    i = m.index;
  }
  const push = (t: TokType, v: string, start: number, end: number, num?: number) => {
    toks.push({ t, v, line, col: start - lineStart + 1, ec: end - lineStart, n: num });
  };
  while (i < n) {
    const c = src.charCodeAt(i);
    if (c === 10) { i++; line++; lineStart = i; continue; }
    if (c === 32 || c === 9 || c === 13 || c === 12) { i++; continue; }
    const ch = src[i];
    // comments
    if (ch === '\\' && src[i + 1] === '*') {
      while (i < n && src.charCodeAt(i) !== 10) i++;
      continue;
    }
    if (ch === '(' && src[i + 1] === '*') {
      let depth = 1;
      i += 2;
      while (i < n && depth > 0) {
        const d = src.charCodeAt(i);
        if (d === 10) { line++; lineStart = i + 1; i++; }
        else if (d === 40 && src[i + 1] === '*') { depth++; i += 2; }
        else if (d === 42 && src[i + 1] === ')') { depth--; i += 2; }
        else i++;
      }
      continue;
    }
    const start = i;
    // separators / end
    if (ch === '-' && src.startsWith('----', i)) {
      while (i < n && src[i] === '-') i++;
      push('sep', '----', start, i);
      continue;
    }
    if (ch === '=' && src.startsWith('====', i)) {
      while (i < n && src[i] === '=') i++;
      push('end', '====', start, i);
      continue;
    }
    // strings
    if (ch === '"') {
      i++;
      let s = '';
      while (i < n && src[i] !== '"') {
        if (src[i] === '\\') {
          const e = src[i + 1];
          s += e === 'n' ? '\n' : e === 't' ? '\t' : e === 'r' ? '\r' : e === 'f' ? '\f' : e;
          i += 2;
        } else if (src.charCodeAt(i) === 10) {
          throw new TlaError('Unterminated string', [line, start - lineStart + 1, line, i - lineStart], moduleName, 'parse');
        } else s += src[i++];
      }
      i++;
      push('str', s, start, i);
      continue;
    }
    // numbers and identifiers
    if (isIdChar(c)) {
      while (i < n && isIdChar(src.charCodeAt(i))) i++;
      let word = src.slice(start, i);
      if (/^\d+$/.test(word)) {
        // decimal?
        if (src[i] === '.' && isDigit(src.charCodeAt(i + 1))) {
          i++;
          while (i < n && isDigit(src.charCodeAt(i))) i++;
          word = src.slice(start, i);
          push('num', word, start, i, Number(word));
        } else push('num', word, start, i, Number(word));
        continue;
      }
      if ((word.startsWith('WF_') || word.startsWith('SF_'))) {
        i = start + 3;
        push('kw', word.slice(0, 3), start, i);
        continue;
      }
      if (word === '_') { push('op', '_', start, i); continue; }
      if (intern) intern(word);
      push(KEYWORDS.has(word) ? 'kw' : 'id', word, start, i);
      continue;
    }
    if (ch === '\\') {
      const nx = src[i + 1];
      if (nx === '/') { i += 2; push('op', '\\/', start, i); continue; }
      if ((nx === 'b' || nx === 'B' || nx === 'o' || nx === 'O' || nx === 'h' || nx === 'H') && /[0-9a-fA-F]/.test(src[i + 2] ?? '')) {
        const radix = nx === 'b' || nx === 'B' ? 2 : nx === 'o' || nx === 'O' ? 8 : 16;
        const re = radix === 2 ? /[01]/ : radix === 8 ? /[0-7]/ : /[0-9a-fA-F]/;
        let j = i + 2;
        while (j < n && re.test(src[j])) j++;
        if (j > i + 2 && !isIdChar(src.charCodeAt(j))) {
          const v = parseInt(src.slice(i + 2, j), radix);
          i = j;
          push('num', String(v), start, i, v);
          continue;
        }
      }
      if (nx && isAlpha(nx.charCodeAt(0))) {
        i++;
        while (i < n && isAlpha(src.charCodeAt(i))) i++;
        const w = src.slice(start, i);
        push('op', CANON[w] ?? w, start, i);
        continue;
      }
      i++;
      push('op', '\\', start, i);
      continue;
    }
    // proof step tokens: <1>, <1>2., <*>, <+>
    if (ch === '<') {
      const sm = /^<(\d+|\*|\+)>[A-Za-z0-9_]*\.*/.exec(src.slice(i, i + 80));
      if (sm) {
        i += sm[0].length;
        push('step', sm[0], start, i);
        continue;
      }
    }
    const cands = SYM_BY_CHAR.get(ch);
    let matched = false;
    if (cands) {
      for (const s of cands) {
        if (src.startsWith(s, i)) {
          i += s.length;
          push('op', CANON[s] ?? s, start, i);
          matched = true;
          break;
        }
      }
    }
    if (matched) continue;
    const u = UNICODE[ch];
    if (u) { i++; push('op', u, start, i); continue; }
    i++;
    push('bad', ch, start, i);
  }
  toks.push({ t: 'eof', v: '<EOF>', line, col: 0, ec: 0 });
  return toks;
}
