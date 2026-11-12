// Command-line driver (TLC-compatible flags).
import { parseConfig } from './cfg.ts';
import { buildModel } from './model.ts';
import { modelCheck } from './liveness.ts';
import type { CheckResult } from './checker.ts';
import { BUNDLED } from './bundled.ts';
import { TlaError } from './lexer.ts';
import { fmt } from './values.ts';

export interface Host {
  fs: { readFileSync(p: string, enc: 'utf8'): string; existsSync(p: string): boolean; writeFileSync?(p: string, s: string): void };
  path: { dirname(p: string): string; join(...p: string[]): string; basename(p: string, ext?: string): string; resolve(...p: string[]): string };
  stdout: (s: string) => void;
  exit: (code: number) => void;
}

export function runCli(argv: string[], host: Host): void {
  let spec: string | null = null, config: string | null = null, deadlock = true, json = false;
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === '-config') config = argv[++i];
    else if (a === '-deadlock') deadlock = false;
    else if (a === '-json') json = true;
    else if (['-workers', '-fp', '-lncheck', '-metadir', '-seed', '-depth', '-fpmem', '-coverage', '-checkpoint', '-maxSetSize', '-fpbits', '-userFile', '-dumpTrace'].includes(a)) i++;
    else if (a === '-dump') { i++; if (argv[i].includes(',') || argv[i] === 'dot') i++; }
    else if (a.startsWith('-')) { /* ignored flag */ }
    else spec = a;
  }
  if (!spec) { host.stdout('Usage: verify [-config FILE] [-deadlock] SPEC\n'); host.exit(1); return; }
  const specPath = spec.endsWith('.tla') ? spec : spec + '.tla';
  const dir = host.path.dirname(host.path.resolve(specPath));
  const rootName = host.path.basename(specPath, '.tla');
  const cfgPath = config ? (host.fs.existsSync(config) ? config : host.path.join(dir, config)) : host.path.join(dir, rootName + '.cfg');
  const resolve = (name: string): string | null => {
    const p = host.path.join(dir, name + '.tla');
    if (host.fs.existsSync(p)) return host.fs.readFileSync(p, 'utf8');
    return BUNDLED[name] ?? null;
  };
  let res: CheckResult;
  try {
    const cfg = parseConfig(host.fs.readFileSync(cfgPath, 'utf8'));
    const model = buildModel(rootName, resolve, cfg, { print: s => host.stdout(s + '\n') });
    res = modelCheck(model, { checkDeadlock: deadlock && model.checkDeadlock }).result;
    if (json) {
      host.stdout(JSON.stringify({ status: res.status, name: res.name, message: res.message, generated: res.generated, distinct: res.distinct, queue: res.queue, depth: res.depth,
        loopTo: res.loopTo, trace: res.trace?.map(t => ({ action: t.action?.name ?? null, state: Object.fromEntries(model.vars.map((v, i) => [v.name, fmt(t.state[i])])) })) }) + '\n');
    } else {
      host.stdout(`${res.status}${res.name ? ' ' + res.name : ''}${res.message ? ': ' + res.message : ''}\n`);
      for (const t of res.trace ?? []) host.stdout(`  ${t.action?.name ?? 'Init'}: ` + model.vars.map((v, i) => `${v.name}=${fmt(t.state[i])}`).join(' ') + '\n');
      host.stdout(`${res.generated} states generated, ${res.distinct} distinct states found, ${res.queue} states left on queue. depth ${res.depth}\n`);
    }
  } catch (e) {
    if (e instanceof TlaError) {
      if (json) host.stdout(JSON.stringify({ status: 'setup-error', kind: e.kind, message: e.message }) + '\n');
      else host.stdout(`Error (${e.kind}): ${e.message}\n`);
      host.exit(150);
      return;
    }
    throw e;
  }
  host.exit(res.status === 'ok' ? 0 : 12);
}
