// Command-line driver. Accepts TLC's flags and prints TLC-compatible output (including -tool mode).
import { parseConfig } from './cfg.ts';
import { buildModel } from './model.ts';
import { Loader, defLevel } from './modules.ts';
import { buildStdlib, globalDefs } from './stdlib.ts';
import type { Model, Action } from './model.ts';
import { modelCheck } from './liveness.ts';
import type { CheckResult, Checker, State } from './checker.ts';
import { BUNDLED } from './bundled.ts';
import { TlaError } from './lexer.ts';
import { fmt, resetInterning } from './values.ts';
import { ppr } from './pprint.ts';

export const VERSION = '0.1.0';

export interface Host {
  fs: {
    readFileSync(p: string, enc: 'utf8'): string;
    existsSync(p: string): boolean;
    writeFileSync(p: string, s: string): void;
    appendFileSync?(p: string, s: string): void;
  };
  path: { dirname(p: string): string; join(...p: string[]): string; basename(p: string, ext?: string): string; resolve(...p: string[]): string };
  stdout: (s: string) => void;
  exit: (code: number) => void;
  env?: Record<string, string | undefined>;
  libraryPaths?: string[];
}

const pad = (n: number) => String(n).padStart(2, '0');
function now(): string {
  const d = new Date();
  return `${d.getFullYear()}-${pad(d.getMonth() + 1)}-${pad(d.getDate())} ${pad(d.getHours())}:${pad(d.getMinutes())}:${pad(d.getSeconds())}`;
}
const commas = (n: number) => String(Math.round(n)).replace(/\B(?=(\d{3})+(?!\d))/g, ',');

export function stateText(model: Model, s: State): string {
  const vars = model.vars;
  if (vars.length === 1) return `${vars[0].name} = ${ppr(fmt(s[0]))}\n`;
  let out = '';
  for (let i = 0; i < vars.length; i++) out += `/\\ ${vars[i].name} = ${ppr(fmt(s[i]))}\n`;
  return out;
}
export function actionLabel(a: Action | null): string {
  if (!a) return '<Initial predicate>';
  return `<${a.name}${a.params} line ${a.loc[0]}, col ${a.loc[1]} to line ${a.loc[2]}, col ${a.loc[3]} of module ${a.module}>`;
}

class Reporter {
  tool: boolean;
  out: (s: string) => void;
  constructor(tool: boolean, out: (s: string) => void) { this.tool = tool; this.out = out; }
  // cls: 0 none, 1 error, 2 bug, 3 warning, 4 state
  msg(code: number, cls: number, text: string): void {
    if (this.tool) this.out(`@!@!@STARTMSG ${code}:${cls} @!@!@\n${text}\n@!@!@ENDMSG ${code} @!@!@\n`);
    else this.out((cls === 1 ? 'Error: ' : cls === 3 ? 'Warning: ' : cls === 4 ? 'State ' : '') + text + '\n');
  }
  plain(text: string): void { this.out(text + '\n'); }
}

const EXIT: Record<string, number> = {
  ok: 0, assumption: 10, deadlock: 11, invariant: 12, 'invariant-init': 12, 'action-property': 13, 'implied-init': 13,
  liveness: 13, incomplete: 75, error: 255, 'init-error': 255,
};

const ARITY1 = new Set(['-workers', '-fp', '-lncheck', '-metadir', '-seed', '-depth', '-fpmem', '-coverage', '-checkpoint',
  '-maxSetSize', '-fpbits', '-userFile', '-recover', '-aril', '-dfid', '-suppressMessages', '-messagesAsErrors', '-inv',
  '-invlevel', '-postCondition', '-teSpecOutDir']);

export function runCli(argv: string[], host: Host): void {
  let spec: string | null = null, config: string | null = null, deadlock = true, tool = false, json = false;
  let dump: { file: string; dot: boolean; opts: string } | null = null;
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === '-config') config = argv[++i];
    else if (a === '-deadlock') deadlock = false;
    else if (a === '-tool') tool = true;
    else if (a === '-json') json = true;
    else if (a === '-dump') {
      const x = argv[++i];
      if (x === 'dot' || x.startsWith('dot,')) dump = { file: argv[++i], dot: true, opts: x.toLowerCase() };
      else dump = { file: x, dot: false, opts: '' };
    } else if (a === '-dumpTrace' || a === '-loadTrace') i += 2;
    else if (a === '-simulate' || a === '-generate') {
      host.stdout('Error: simulation mode is not supported by verify.js yet.\n');
      host.exit(1);
      return;
    } else if (a === '-h' || a === '-help' || a === '--help') { host.stdout(USAGE); host.exit(0); return; }
    else if (a === '-version' || a === '--version') { host.stdout(`verify.js ${VERSION}\n`); host.exit(0); return; }
    else if (ARITY1.has(a)) i++;
    else if (a.startsWith('-')) { /* flag without effect here (-cleanup, -nowarning, -terse, -noTE, ...) */ }
    else if (spec !== null) { host.stdout(`Error: more than one input files: ${spec} and ${a}\n`); host.exit(1); return; }
    else spec = a;
  }
  if (!spec) { host.stdout('Error: Missing input TLA+ module.\n' + USAGE); host.exit(1); return; }
  const specPath = spec.endsWith('.tla') ? spec : spec + '.tla';
  const dir = host.path.dirname(host.path.resolve(specPath));
  const rootName = host.path.basename(specPath, '.tla');
  let cfgPath = config ?? rootName + '.cfg';
  if (!cfgPath.endsWith('.cfg') && !host.fs.existsSync(cfgPath) && !host.fs.existsSync(host.path.join(dir, cfgPath))) cfgPath += '.cfg';
  if (!host.fs.existsSync(cfgPath) || config === null) {
    const inDir = host.path.join(dir, cfgPath);
    if (host.fs.existsSync(inDir)) cfgPath = inDir;
  }
  const rep = new Reporter(tool, host.stdout);
  const t0 = Date.now();
  const parsed: string[] = [];
  const libs = [dir, ...(host.libraryPaths ?? [])];
  const resolve = (name: string): string | null => {
    for (const d of libs) {
      const p = host.path.join(d, name + '.tla');
      if (host.fs.existsSync(p)) { parsed.push(p); return host.fs.readFileSync(p, 'utf8'); }
    }
    return BUNDLED[name] ?? null;
  };
  const finish = (code: number) => {
    const ms = Date.now() - t0;
    const s = Math.floor(ms / 1000);
    const dur = tool ? `${ms}ms` : s < 60 ? `${pad(s)}s` : s < 3600 ? `${pad(Math.floor(s / 60))}min ${pad(s % 60)}s` : `${pad(Math.floor(s / 3600))}h ${pad(Math.floor((s % 3600) / 60))}min`;
    if (!json) rep.msg(2186, 0, `Finished in ${dur} at (${now()})`);
    host.exit(code);
  };
  resetInterning();
  if (!json) {
    rep.msg(2262, 0, `TLC2 Version 2.19 of 08 August 2024 (verify.js ${VERSION})`);
    rep.msg(2187, 0, `Running breadth-first search Model-Checking with fp 0 and seed 0 with 1 worker on 1 cores with 0MB heap and 0MB offheap memory (verify.js ${VERSION}, pure TypeScript, HashFPSet, MemStateQueue).`);
  }
  let model: Model;
  try {
    if (!host.fs.existsSync(cfgPath)) throw new TlaError(`TLC encountered the following error reading the configuration file ${cfgPath}:\nFile not found.`, undefined, undefined, 'config');
    const cfg = parseConfig(host.fs.readFileSync(cfgPath, 'utf8'));
    if (!json && tool) rep.msg(2220, 0, 'Starting SANY...');
    try {
      model = buildModel(rootName, resolve, cfg, { print: s => host.stdout(s + '\n') });
    } finally {
      if (!json) {
        for (const p of parsed) rep.plain(`Parsing file ${p}`);
      }
    }
    if (!json) {
      for (const m of model.loader.loadOrder) rep.plain(`Semantic processing of module ${m}`);
      if (tool) rep.msg(2219, 0, 'SANY finished.');
    }
  } catch (e) {
    if (!(e instanceof TlaError)) throw e;
    if (json) { host.stdout(JSON.stringify({ status: 'setup-error', kind: e.kind, message: e.message }) + '\n'); host.exit(e.kind === 'config' ? 151 : 150); return; }
    if (e.kind === 'config') { rep.msg(1000, 1, e.message); finish(151); return; }
    rep.plain(e.message);
    rep.msg(3002, 1, 'Parsing or semantic analysis failed.');
    finish(150);
    return;
  }
  model.ev.hooks.io = {
    readFile: (p: string) => host.fs.readFileSync(p, 'utf8'),
    writeFile: (p: string, d: string) => host.fs.writeFileSync(p, d),
    appendFile: (p: string, d: string) => (host.fs.appendFileSync ? host.fs.appendFileSync(p, d) : host.fs.writeFileSync(p, (host.fs.existsSync(p) ? host.fs.readFileSync(p, 'utf8') : '') + d)),
    exists: (p: string) => host.fs.existsSync(p),
    env: host.env ?? {},
  };
  if (!json) rep.msg(2185, 0, `Starting... (${now()})`);
  let first = true;
  const { result: res, checker } = modelCheck(model, {
    checkDeadlock: deadlock && model.checkDeadlock,
    recordGraph: dump !== null,
    onProgress: (gen, distinct, queue) => {
      if (json) return;
      if (first) {
        first = false;
        const c = checker0();
        rep.msg(2189, 0, 'Computing initial states...');
        if (c.initGenerated === c.initDistinct) rep.msg(2190, 0, `Finished computing initial states: ${c.initDistinct} distinct state${c.initDistinct === 1 ? '' : 's'} generated at ${now()}.`);
        else rep.msg(2191, 0, `Finished computing initial states: ${c.initGenerated} state${c.initGenerated === 1 ? '' : 's'} generated, with ${c.initDistinct} of them distinct at ${now()}.`);
        return;
      }
      rep.msg(2200, 0, `Progress(${checker0().depth}) at ${now()}: ${commas(gen)} states generated, ${commas(distinct)} distinct states found, ${commas(queue)} states left on queue.`);
    },
    onChecker: (c: Checker) => { theChecker = c; },
    onLiveness: (phase, branches) => {
      if (json) return;
      const c = checker0();
      if (phase === 'branches') rep.msg(2212, 0, `Implied-temporal checking--satisfiability problem has ${branches} branches.`);
      else if (phase === 'start') {
        if (!rep.tool) rep.msg(2200, 0, `Progress(${c.depth}) at ${now()}: ${commas(c.generated)} states generated, ${commas(c.states.length)} distinct states found, 0 states left on queue.`);
        rep.msg(2192, 0, `Checking ${branches > 1 ? branches + ' branches of ' : ''}temporal properties for the complete state space with ${c.states.length * branches} total distinct states at (${now()})`);
      } else rep.msg(2267, 0, `Finished checking temporal properties in 00s at ${now()}`);
    },
  });
  if (dump) {
    try { writeDump(model, checker, dump, host); } catch (e) { rep.msg(1000, 1, `Failed to write the state dump: ${(e as Error).message}`); }
  }
  if (json) {
    host.stdout(JSON.stringify({
      status: res.status, name: res.name, message: res.message, generated: res.generated, distinct: res.distinct, queue: res.queue,
      depth: res.depth, loopTo: res.loopTo,
      trace: res.trace?.map(t => ({ action: t.action?.name ?? null, state: Object.fromEntries(model.vars.map((v, i) => [v.name, fmt(t.state[i])])) })),
    }) + '\n');
    host.exit(EXIT[res.status] ?? 255);
    return;
  }
  if (first) rep.msg(2189, 0, 'Computing initial states...');
  report(rep, model, res, t0);
  finish(res.callStack ? 75 : res.code === 2111 ? 76 : EXIT[res.status] ?? 255);
}

let theChecker: Checker | null = null;
const checker0 = (): Checker => theChecker!;

function printTrace(rep: Reporter, model: Model, res: CheckResult): void {
  const tr = res.trace ?? [];
  tr.forEach((t, i) => {
    rep.msg(2217, 4, `${i + 1}: ${actionLabel(i === 0 ? null : t.action)}\n${stateText(model, t.state)}`);
  });
}

function report(rep: Reporter, model: Model, res: CheckResult, t0: number): void {
  const summary = () => {
    if (rep.tool) {
      const mins = Math.max((Date.now() - t0) / 60000, 1e-6);
      rep.msg(2200, 0, `Progress(${res.depth}) at ${now()}: ${commas(res.generated)} states generated (${commas(res.generated / mins)} s/min), ${commas(res.distinct)} distinct states found (${commas(res.distinct / mins)} ds/min), ${commas(res.queue)} states left on queue.`);
    }
    rep.msg(2199, 0, `${res.generated} states generated, ${res.distinct} distinct states found, ${res.queue} states left on queue.`);
    rep.msg(2194, 0, `The depth of the complete state graph search is ${res.depth}.`);
    if (res.outdegree && (res.status === 'ok' || rep.tool)) {
      const o = res.outdegree;
      rep.msg(2268, 0, `The average outdegree of the complete state graph is ${o.avg} (minimum is ${o.min}, the maximum ${o.max} and the 95th percentile is ${o.p95}).`);
    }
  };
  switch (res.status) {
    case 'ok': {
      const p = res.distinct * ((res.generated - res.distinct) / 18446744073709551616);
      const ps = p === 0 ? '0.0' : p.toExponential(1).replace('e', 'E').replace('E+', 'E');
      rep.msg(2193, 0, `Model checking completed. No error has been found.\n  Estimates of the probability that TLC did not check all reachable states\n  because two distinct states had the same fingerprint:\n  calculated (optimistic):  val = ${ps}`);
      summary();
      return;
    }
    case 'assumption': rep.msg(2104, 1, res.message!.replace(/^Assumption /, 'Assumption ').replace(/\.$/, '.')); return;
    case 'invariant-init':
      rep.msg(2107, 1, `Invariant ${res.name} is violated by the initial state:\n${stateText(model, res.trace![0].state)}`);
      return;
    case 'implied-init':
      rep.msg(2108, 1, `Property ${res.name} is violated by the initial state:\n${stateText(model, res.trace![0].state)}`);
      return;
    case 'invariant': rep.msg(2110, 1, `Invariant ${res.name} is violated.`); break;
    case 'action-property': rep.msg(2112, 1, `Action property ${res.name} is violated.`); break;
    case 'deadlock': rep.msg(2114, 1, 'Deadlock reached.'); break;
    case 'liveness': {
      rep.msg(2116, 1, res.name ? `Temporal properties were violated.\n` : 'Temporal properties were violated.\n');
      rep.msg(2264, 1, 'The following behavior constitutes a counter-example:\n');
      printTrace(rep, model, res);
      const n = res.trace!.length;
      if (res.loopTo === undefined || res.loopTo < 0) rep.msg(2218, 4, `${n + 1}: Stuttering`);
      else if (rep.tool) rep.msg(2122, 4, `${res.loopTo + 1}: Back to state: ${actionLabel(res.loopAction ?? null)}\n`);
      else rep.out(`Back to state ${res.loopTo + 1}: ${actionLabel(res.loopAction ?? null)}\n\n`);
      rep.msg(2267, 0, `Finished checking temporal properties in 00s at ${now()}`);
      if (rep.tool) {
        const mins = Math.max((Date.now() - t0) / 60000, 1e-6);
        rep.msg(2200, 0, `Progress(${res.depth}) at ${now()}: ${commas(res.generated)} states generated (${commas(res.generated / mins)} s/min), ${commas(res.distinct)} distinct states found (${commas(res.distinct / mins)} ds/min), ${commas(res.queue)} states left on queue.`);
      }
      rep.msg(2199, 0, `${res.generated} states generated, ${res.distinct} distinct states found, ${res.queue} states left on queue.`);
      return;
    }
    case 'incomplete': rep.msg(2109, 1, res.message! + '\n'); break;
    default: {
      const m = res.message ?? 'unknown error';
      if (res.code) { rep.msg(res.code, 1, m); break; }
      if (res.trace && res.trace.length === 1 && res.trace[0].id === -1 && res.trace[0].action === null) {
        rep.msg(2102, 1, `${m}\nWhile working on the initial state:\n${stateText(model, res.trace[0].state)}`);
        if (res.printSummary) summary();
        return;
      }
      rep.msg(1000, 1, `TLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nSee the User Output or TLC Console for clues to what happened.\nThe exception was a java.lang.RuntimeException\n: ${m}`);
    }
  }
  if (res.trace && res.trace.length) {
    rep.msg(2121, 1, 'The behavior up to this point is:');
    printTrace(rep, model, res);
  }
  if (res.callStack) rep.msg(2103, 1, `The error occurred when TLC was evaluating the nested\nexpressions at the following positions:\n${res.callStack}`);
  if (res.printSummary) summary();
}

function fpString(checker: Checker, s: State): string {
  checker.fingerprint(s);
  const h = checker.hasher;
  return BigInt.asIntN(64, (BigInt(h.h1 >>> 0) << 32n) | BigInt(h.h2 >>> 0)).toString();
}

function writeDump(model: Model, checker: Checker, dump: { file: string; dot: boolean; opts: string }, host: Host): void {
  const states = checker.states;
  if (!dump.dot) {
    let out = '';
    states.forEach((s, i) => { out += `State ${i + 1}:\n${stateText(model, s)}\n`; });
    host.fs.writeFileSync(dump.file.endsWith('.dump') ? dump.file : dump.file + '.dump', out);
    return;
  }
  const labels = dump.opts.includes('actionlabels');
  const esc = (s: string) => s.replace(/\\/g, '\\\\').replace(/"/g, '\\"').trim().replace(/\n/g, '\\n');
  const ids = states.map(s => fpString(checker, s));
  const lines: string[] = ['strict digraph DiskGraph {', 'nodesep=0.35;', 'subgraph cluster_graph {', 'color="white";'];
  const ranks = new Map<number, Set<number>>();
  const rank = (i: number) => { let r = ranks.get(checker.level[i]); if (!r) { r = new Set(); ranks.set(checker.level[i], r); } r.add(i); };
  const written = new Set<number>();
  for (const i of checker.inits) {
    lines.push(`${ids[i]} [label="${esc(stateText(model, states[i]))}",style = filled]`);
    written.add(i);
    rank(i);
  }
  for (let s = 0; s < states.length; s++) {
    const su = checker.succ[s] ?? [], sa = checker.succAct[s] ?? [];
    for (let j = 0; j < su.length; j++) {
      const t = su[j];
      const a = model.actions[sa[j]];
      lines.push(`${ids[s]} -> ${ids[t]} [label="${labels ? esc(a.name) : ''}",color="black",fontcolor="black"];`);
      rank(s);
      if (!written.has(t)) { written.add(t); lines.push(`${ids[t]} [label="${esc(stateText(model, states[t]))}"];`); }
    }
  }
  for (const [, set] of [...ranks.entries()].sort((a, b) => a[0] - b[0])) lines.push(`{rank = same; ${[...set].map(i => ids[i] + ';').join('')}}`);
  lines.push('}', '}');
  host.fs.writeFileSync(dump.file.endsWith('.dot') ? dump.file : dump.file + '.dot', lines.join('\n') + '\n');
}

const USAGE = `verify.js ${VERSION} - a TLA+ model checker in pure TypeScript (TLC-compatible command line)

Usage: verify [options] SPEC[.tla]

  -config FILE        configuration file (default: SPEC.cfg)
  -deadlock           do not check for deadlock
  -tool               machine-readable output (TLC's -tool message framing)
  -dump [dot[,actionlabels]] FILE   write the reachable state graph
  -json               print a single JSON result object instead of TLC-style output
  -workers N, -fp N, -lncheck S, -metadir DIR, -seed N, ...   accepted for compatibility

Exit status: 0 success, 10 assumption, 11 deadlock, 12 safety, 13 liveness, 150 parse error, 151 config error.
`;

// Emulates `java ... tla2sany.xml.XMLExporter [-o] [-I dir] SPEC`: a minimal XML description of the
// root module (variables, definitions and their levels), enough for tools that only need the symbol table.
export function runXmlExporter(argv: string[], host: Host): void {
  let spec: string | null = null;
  const libs: string[] = [];
  for (let i = 0; i < argv.length; i++) {
    if (argv[i] === '-I') libs.push(argv[++i]);
    else if (!argv[i].startsWith('-')) spec = argv[i];
  }
  if (!spec) { host.stdout('Usage: XMLExporter [-o] [-I dir] SPEC\n'); host.exit(1); return; }
  const specPath = spec.endsWith('.tla') ? spec : spec + '.tla';
  const dir = host.path.dirname(host.path.resolve(specPath));
  const rootName = host.path.basename(specPath, '.tla');
  const dirs = [dir, ...libs, ...(host.libraryPaths ?? [])];
  const resolve = (name: string): string | null => {
    for (const d of dirs) {
      const p = host.path.join(d, name + '.tla');
      if (host.fs.existsSync(p)) return host.fs.readFileSync(p, 'utf8');
    }
    return BUNDLED[name] ?? null;
  };
  resetInterning();
  try {
    const loader = new Loader(resolve, buildStdlib({ print: () => {} }));
    loader.globals = globalDefs();
    const root = loader.load(rootName);
    const escXml = (t: string) => t.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
    let uid = 1;
    const entries: string[] = [];
    const refs: string[] = [];
    for (const v of root.vars) {
      const id = ++uid;
      refs.push(`<OpDeclNodeRef><UID>${id}</UID></OpDeclNodeRef>`);
      entries.push(`<entry><UID>${id}</UID><OpDeclNode><uniquename>${escXml(v.name)}</uniquename><level>1</level><arity>0</arity><kind>3</kind></OpDeclNode></entry>`);
    }
    for (const c of root.consts) {
      const id = ++uid;
      refs.push(`<OpDeclNodeRef><UID>${id}</UID></OpDeclNodeRef>`);
      entries.push(`<entry><UID>${id}</UID><OpDeclNode><uniquename>${escXml(c.name)}</uniquename><level>0</level><arity>${c.arity}</arity><kind>2</kind></OpDeclNode></entry>`);
    }
    for (const [name, sym] of root.syms) {
      if (sym.k !== 'def' || sym.builtin) continue;
      const id = ++uid;
      refs.push(`<UserDefinedOpKindRef><UID>${id}</UID></UserDefinedOpKindRef>`);
      entries.push(`<entry><UID>${id}</UID><UserDefinedOpKind><uniquename>${escXml(name)}</uniquename><level>${defLevel(sym)}</level><arity>${sym.params.length}</arity></UserDefinedOpKind></entry>`);
    }
    host.stdout(`<?xml version="1.0" encoding="UTF-8"?>\n<modules><RootModule>${escXml(rootName)}</RootModule><context>` +
      `<entry><UID>1</UID><ModuleNode><uniquename>${escXml(rootName)}</uniquename>${refs.join('')}</ModuleNode></entry>${entries.join('')}</context></modules>\n`);
    host.exit(0);
  } catch (e) {
    if (!(e instanceof TlaError)) throw e;
    host.stdout(`${e.message}\n*** Errors: 1\n`);
    host.exit(1);
  }
}

// Emulates the `java` command line of the TLA+ tools, so that scripts which shell out to
// `java -cp tla2tools.jar tlc2.TLC ...` can run on verify.js unchanged.
export function runJavaShim(argv: string[], host: Host): void {
  const libs: string[] = [...(host.libraryPaths ?? [])];
  let i = 0;
  for (; i < argv.length; i++) {
    const a = argv[i];
    if (a.startsWith('-DTLA-Library=')) libs.push(...a.slice('-DTLA-Library='.length).split(/[:;]/).filter(Boolean));
    else if (a === '-cp' || a === '-classpath' || a === '-jar') i++;
    else if (!a.startsWith('-')) break;
  }
  const main = argv[i];
  const rest = argv.slice(i + 1);
  const h = { ...host, libraryPaths: libs };
  if (main === 'tlc2.TLC') runCli(rest, h);
  else if (main === 'tla2sany.xml.XMLExporter') runXmlExporter(rest, h);
  else if (main === 'tla2sany.SANY') runXmlExporter(['-quiet', ...rest], { ...h, stdout: () => {} });
  else { host.stdout(`verify.js java shim: unsupported main class ${main ?? '(none)'}\n`); host.exit(1); }
}
