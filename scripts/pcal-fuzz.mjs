// Random mutations of the PlusCal algorithms of the corpora (tokens deleted, duplicated, replaced,
// lines dropped, swapped, cut): `everystate pcal` must end with exit status 0 or 255 on each (never
// crash or hang), and, with --java, must agree with `java pcal.trans` on the exit status, the
// messages and the resulting file.
//
// usage: node scripts/pcal-fuzz.mjs [N] [SEED] [--java] [--tlaplus DIR] [--examples DIR] [--jar tla2tools.jar]
//   N     mutations per file (default 10)
//   SEED  of the pseudo-random generator (default 1); a failure is reported with the mutated file
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { spawnSync } from 'node:child_process';

const args = process.argv.slice(2);
const opt = (name, dflt) => (args.includes(name) ? args[args.indexOf(name) + 1] : dflt);
const numbers = args.filter(a => /^\d+$/.test(a)).map(Number);
const N = numbers[0] ?? 10;
let seed = numbers[1] ?? 1;
const withJava = args.includes('--java');
const tlaplus = path.resolve(opt('--tlaplus', '/home/user/refs/tlaplus'));
const examples = path.resolve(opt('--examples', '/home/user/refs/Examples'));
const jar = path.resolve(opt('--jar', '/home/user/refs/tla2tools.jar'));
const bin = process.env.EVERYSTATE_CMD ?? path.resolve(import.meta.dirname, '../target/release/everystate');

const rnd = () => {
  seed = (seed * 1103515245 + 12345) & 0x7fffffff;
  return seed / 0x7fffffff;
};
const pick = a => a[Math.floor(rnd() * a.length)];
const TOKENS = [';', 'end', 'if', '(', ')', 'begin', ':=', '||', 'while', 'do', '{', '}', 'with', 'either', 'or', 'call', 'return', 'goto', 'macro', 'procedure', 'process', ',', '"', '(*', '*)', '\\*',
  'define', 'fair', '+', '-', ':', 'then', 'else', 'elsif', 'skip', 'print', 'assert', 'await', 'variables', '=', '\\in', '[', ']', '<<', '>>', 'x', 'self', 'Done', '\\E', '\\A', 'algorithm', '--algorithm',
  'TRUE', '.', '!', '@', '`', '====', '----', "'"];

function walk(dir, out = []) {
  if (!fs.existsSync(dir)) return out;
  for (const e of fs.readdirSync(dir, { withFileTypes: true })) {
    const p = path.join(dir, e.name);
    if (e.isDirectory()) walk(p, out);
    else if (e.name.endsWith('.tla')) out.push(p);
  }
  return out;
}
const files = [
  ...walk(path.join(tlaplus, 'tlatools/org.lamport.tlatools/test-model/pcal')),
  ...walk(path.resolve(import.meta.dirname, '../test/pcal')),
  ...walk(path.join(examples, 'specifications')).filter(f => /--algorithm|--fair/.test(fs.readFileSync(f, 'latin1'))),
];

function mutate(text) {
  const lines = text.split('\n');
  const a = lines.findIndex(l => l.includes('--algorithm') || l.includes('--fair'));
  if (a < 0) return text;
  let b = lines.findIndex((l, i) => i > a && l.includes('BEGIN TRANSLATION'));
  if (b < 0) b = Math.min(lines.length, a + 60);
  const line = () => a + Math.floor(rnd() * Math.max(1, b - a));
  for (let k = 1 + Math.floor(rnd() * 3); k > 0; k--) {
    const i = line();
    const toks = (lines[i] ?? '').split(/( +)/);
    const j = Math.floor(rnd() * toks.length);
    switch (Math.floor(rnd() * 8)) {
      case 0: toks.splice(j, 1); lines[i] = toks.join(''); break;
      case 1: toks.splice(j, 0, toks[j] ?? ''); lines[i] = toks.join(''); break;
      case 2: toks[j] = pick(TOKENS); lines[i] = toks.join(''); break;
      case 3: toks.splice(j, 0, ` ${pick(TOKENS)} `); lines[i] = toks.join(''); break;
      case 4: lines.splice(i, 1); break;
      case 5: { const i2 = line(); [lines[i], lines[i2]] = [lines[i2] ?? '', lines[i] ?? '']; break; }
      case 6: lines[i] = (lines[i] ?? '').slice(0, Math.floor(rnd() * ((lines[i] ?? '').length + 1))); break;
      case 7: lines.splice(i, 0, lines[line()] ?? ''); break;
    }
  }
  return lines.join('\n');
}

const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'everystate-pcal-fuzz-'));
const javaEnv = { ...process.env };
delete javaEnv.JAVA_TOOL_OPTIONS;
let runs = 0, crashes = 0, translated = 0, diffs = 0;
for (const f of files) {
  const text = fs.readFileSync(f, 'utf8');
  const base = path.basename(f);
  for (let k = 0; k < N; k++) {
    const mutated = mutate(text);
    const opts = ['-nocfg', '-noold', ...(rnd() < 0.5 ? ['-label'] : [])];
    const keep = () => {
      const p = path.join(os.tmpdir(), `everystate-pcal-fuzz-${crashes + diffs}-${base}`);
      fs.writeFileSync(p, mutated);
      return p;
    };
    fs.writeFileSync(path.join(dir, base), mutated);
    const e = spawnSync(bin, ['pcal', ...opts, base], { cwd: dir, encoding: 'utf8', timeout: 10000 });
    runs++;
    if (e.status === 0) translated++;
    if (e.status !== 0 && e.status !== 255) {
      crashes++;
      console.log(`CRASH ${f} [${opts.join(' ')}]: status ${e.status}, signal ${e.signal}; input kept in ${keep()}`);
      continue;
    }
    if (!withJava) continue;
    const ours = fs.readFileSync(path.join(dir, base), 'utf8');
    fs.writeFileSync(path.join(dir, base), mutated);
    const j = spawnSync('java', ['-cp', jar, 'pcal.trans', ...opts, base], { cwd: dir, encoding: 'utf8', timeout: 120000, env: javaEnv });
    if (j.status !== e.status || j.stdout !== e.stdout || fs.readFileSync(path.join(dir, base), 'utf8') !== ours) {
      diffs++;
      const brief = s => s.split('\n').slice(1, 6).join(' | ').slice(0, 300);
      console.log(`DIFF ${f} [${opts.join(' ')}]: java exit ${j.status}, everystate exit ${e.status}; input kept in ${keep()}\n  java: ${brief(j.stdout)}${j.stderr ? ` (stderr: ${j.stderr.split('\n')[0].slice(0, 200)})` : ''}\n  ours: ${brief(e.stdout)}`);
    }
  }
}
fs.rmSync(dir, { recursive: true, force: true });
console.log(JSON.stringify({ files: files.length, runs, translated, crashes, comparedWithJava: withJava ? runs - crashes : 0, diffs }));
process.exit(crashes || diffs ? 1 : 0);
