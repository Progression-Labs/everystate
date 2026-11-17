// Compares `everystate pcal` with the Java PlusCal translator (`java pcal.trans`) on two corpora:
// the translator's own test models (tlatools test-model/pcal, with the options the Java tests pass)
// and every specification of tlaplus/Examples that contains a PlusCal algorithm.  Each file is
// copied to a scratch directory, translated by both, and the resulting .tla and .cfg, the exit
// status and the messages are compared.  The Java results are cached.
//
// usage: node scripts/pcal-corpus.mjs [--tlaplus DIR] [--examples DIR] [--jar tla2tools.jar]
//          [--cache DIR] [--filter STR] [--show] [--check N] [--check-timeout SECONDS]
//   --tlaplus   a checkout of tlaplus/tlaplus (default /home/user/refs/tlaplus)
//   --examples  a checkout of tlaplus/Examples (default /home/user/refs/Examples)
//   --show      print a diff for each mismatch
//   --variants  also translate every file with each of a set of other option combinations
//   --extra DIR more modules to compare (default test/pcal of this repository); a file Name.opts
//               next to Name.tla holds the options for it, one set of options per line
//   --validate  also compare what SANY says about changed algorithms and translations (the warning
//               TLC prints when it loads a module) with `everystate pcal --check`, on the translated
//               modules and on mutations of them
//   --check N   also model-check up to N Examples specs before and after re-translating them with
//               everystate, and compare the state counts
// EVERYSTATE_CMD: the binary to test (default target/release/everystate)
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import crypto from 'node:crypto';
import { spawn, spawnSync } from 'node:child_process';

const args = process.argv.slice(2);
const opt = (name, dflt) => (args.includes(name) ? args[args.indexOf(name) + 1] : dflt);
const tlaplus = path.resolve(opt('--tlaplus', '/home/user/refs/tlaplus'));
const examples = path.resolve(opt('--examples', '/home/user/refs/Examples'));
const jar = path.resolve(opt('--jar', '/home/user/refs/tla2tools.jar'));
const cacheDir = path.resolve(opt('--cache', path.join(os.tmpdir(), 'everystate-pcal-cache')));
const filter = opt('--filter', '');
const show = args.includes('--show');
const checkN = Number(opt('--check', '0'));
const checkTimeout = Number(opt('--check-timeout', '30')) * 1000;
const bin = process.env.EVERYSTATE_CMD ?? path.resolve(import.meta.dirname, '../target/release/everystate');
fs.mkdirSync(cacheDir, { recursive: true });
const scratch = fs.mkdtempSync(path.join(os.tmpdir(), 'everystate-pcal-'));
const javaEnv = { ...process.env };
delete javaEnv.JAVA_TOOL_OPTIONS;

function walk(dir, out = []) {
  for (const e of fs.readdirSync(dir, { withFileTypes: true })) {
    const p = path.join(dir, e.name);
    if (e.isDirectory()) walk(p, out);
    else if (e.name.endsWith('.tla')) out.push(p);
  }
  return out;
}

// the options of the Java tests: super("Name", "pcal", new String[] {"-wf", "-termination"})
function testOptions() {
  const map = new Map();
  const dir = path.join(tlaplus, 'tlatools/org.lamport.tlatools/test/pcal');
  if (!fs.existsSync(dir)) return map;
  for (const f of fs.readdirSync(dir)) {
    if (!f.endsWith('.java')) continue;
    const m = /super\(\s*"([^"]+)"\s*,\s*"pcal"\s*(?:,\s*new String\[\]\s*\{([^}]*)\})?/.exec(fs.readFileSync(path.join(dir, f), 'utf8'));
    if (m) map.set(m[1], m[2] ? [...m[2].matchAll(/"([^"]*)"/g)].map(x => x[1]) : []);
  }
  return map;
}

const cases = [];
{
  const dir = path.join(tlaplus, 'tlatools/org.lamport.tlatools/test-model/pcal');
  const opts = testOptions();
  for (const f of fs.readdirSync(dir).sort()) {
    if (!f.endsWith('.tla')) continue;
    const name = f.slice(0, -4);
    cases.push({ corpus: 'test-model', id: `test-model/${f}`, file: path.join(dir, f), options: ['-unixEOL', ...(opts.get(name) ?? [])] });
  }
  const root = path.join(examples, 'specifications');
  for (const f of walk(root).sort()) {
    const text = fs.readFileSync(f, 'latin1');
    if (!text.includes('--algorithm') && !text.includes('--fair')) continue;
    cases.push({ corpus: 'examples', id: `examples/${path.relative(root, f)}`, file: f, options: [] });
  }
}

function run(cmd, argv, cwd, env) {
  return new Promise(resolve => {
    const p = spawn(cmd, argv, { cwd, env, stdio: ['ignore', 'pipe', 'pipe'] });
    let out = '', err = '';
    p.stdout.on('data', d => (out += d));
    p.stderr.on('data', d => (err += d));
    p.on('close', code => resolve({ status: code, stdout: out, stderr: err }));
    p.on('error', e => resolve({ status: -1, stdout: out, stderr: String(e) }));
  });
}

// Copies the module (and its .cfg) to a fresh directory, runs the translator there and collects
// what it left behind.
async function translate(c, which) {
  const dir = fs.mkdtempSync(path.join(scratch, `${which}-`));
  const base = path.basename(c.file);
  const name = base.slice(0, -4);
  fs.copyFileSync(c.file, path.join(dir, base));
  const cfg = c.file.slice(0, -4) + '.cfg';
  if (fs.existsSync(cfg)) fs.copyFileSync(cfg, path.join(dir, `${name}.cfg`));
  const r = which === 'java' ? await run('java', ['-cp', jar, 'pcal.trans', ...c.options, base], dir, javaEnv) : await run(bin, ['pcal', ...c.options, base], dir, process.env);
  const read = f => (fs.existsSync(path.join(dir, f)) ? fs.readFileSync(path.join(dir, f)).toString('base64') : null);
  const res = { status: r.status, stdout: r.stdout, stderr: r.stderr, tla: read(base), cfg: read(`${name}.cfg`), old: read(`${name}.old`) };
  fs.rmSync(dir, { recursive: true, force: true });
  return res;
}

const jarStamp = fs.existsSync(jar) ? `${fs.statSync(jar).size}:${fs.statSync(jar).mtimeMs}` : 'nojar';
async function javaResult(c) {
  const h = crypto.createHash('sha256');
  h.update(jarStamp).update('\0').update(c.options.join(' ')).update('\0').update(path.basename(c.file)).update('\0').update(fs.readFileSync(c.file));
  const cfg = c.file.slice(0, -4) + '.cfg';
  if (fs.existsSync(cfg)) h.update('\0').update(fs.readFileSync(cfg));
  const key = path.join(cacheDir, h.digest('hex') + '.json');
  if (fs.existsSync(key)) return JSON.parse(fs.readFileSync(key, 'utf8'));
  const r = await translate(c, 'java');
  fs.writeFileSync(key, JSON.stringify(r));
  return r;
}

function diff(a, b) {
  const fa = path.join(scratch, '_java'), fb = path.join(scratch, '_everystate');
  fs.writeFileSync(fa, a ?? '');
  fs.writeFileSync(fb, b ?? '');
  return spawnSync('diff', [fa, fb], { encoding: 'utf8' }).stdout.split('\n').slice(0, 40).join('\n');
}
const text = b64 => (b64 == null ? null : Buffer.from(b64, 'base64').toString('utf8'));

{
  const dir = path.resolve(opt('--extra', path.resolve(import.meta.dirname, '../test/pcal')));
  if (fs.existsSync(dir)) {
    for (const f of fs.readdirSync(dir).sort()) {
      if (!f.endsWith('.tla')) continue;
      const o = path.join(dir, f.slice(0, -4) + '.opts');
      // a blank line stands for "no options"
      const sets = fs.existsSync(o) ? fs.readFileSync(o, 'utf8').replace(/\n$/, '').split('\n') : [''];
      for (const set of sets) cases.push({ corpus: 'extra', id: `extra/${f}`, file: path.join(dir, f), options: set.trim() ? set.trim().split(/\s+/) : [] });
    }
  }
}
if (args.includes('--variants')) {
  const variants = [['-label'], ['-sf'], ['-wf'], ['-wfNext'], ['-nof'], ['-noDoneDisjunct'], ['-termination'], ['-nof', '-termination'], ['-lineWidth', '60'], ['-lineWidth', '130'],
    ['-label', '-labelRoot', 'L'], ['-version', '1.4'], ['-reportLabels'], ['-nocfg', '-noold'], ['-debug'], ['-sf', '-label', '-termination', '-lineWidth', '70']];
  for (const c of [...cases]) {
    if (c.corpus === 'extra') continue;
    for (const v of variants) cases.push({ ...c, corpus: `${c.corpus}+variants`, options: v });
  }
}
const selected = cases.filter(c => !filter || c.id.includes(filter));
const results = new Array(selected.length);
let next = 0;
async function worker() {
  while (next < selected.length) {
    const i = next++;
    const c = selected[i];
    const [j, e] = await Promise.all([javaResult(c), translate(c, 'everystate')]);
    const problems = [];
    if (j.status !== e.status) problems.push('exit');
    if (j.tla !== e.tla) problems.push('tla');
    if (j.cfg !== e.cfg) problems.push('cfg');
    if (j.old !== e.old) problems.push('old');
    if (j.stdout !== e.stdout) problems.push('messages');
    results[i] = { c, j, e, problems };
  }
}
await Promise.all(Array.from({ length: Math.max(1, Math.min(8, os.cpus().length)) }, worker));

const summary = {};
const categories = {};
let pass = 0;
for (const { c, j, e, problems } of results) {
  const s = (summary[c.corpus] ??= { total: 0, pass: 0, javaOk: 0, javaRejects: 0, identicalTla: 0, bothReject: 0 });
  s.total++;
  if (j.status === 0) s.javaOk++;
  else s.javaRejects++;
  if (j.status === 0 && e.status === 0 && j.tla === e.tla) s.identicalTla++;
  if (j.status !== 0 && e.status !== 0) s.bothReject++;
  if (problems.length === 0) {
    s.pass++;
    pass++;
    continue;
  }
  for (const p of problems) (categories[p] ??= []).push(c.id);
  console.log(`FAIL ${c.id} [${c.options.join(' ')}]: ${problems.join(', ')} (java exit ${j.status}, everystate exit ${e.status})`);
  if (show) {
    if (problems.includes('tla')) console.log(diff(text(j.tla), text(e.tla)));
    if (problems.includes('cfg')) console.log(diff(text(j.cfg), text(e.cfg)));
    if (problems.includes('messages') || problems.includes('exit')) console.log(diff(j.stdout + j.stderr, e.stdout + e.stderr));
  }
}
for (const [name, s] of Object.entries(summary)) {
  console.log(`${name}: ${s.pass} of ${s.total} identical in every respect; Java translates ${s.javaOk} (byte-identical .tla: ${s.identicalTla}), Java rejects ${s.javaRejects} (also rejected: ${s.bothReject})`);
}
for (const [k, v] of Object.entries(categories)) console.log(`mismatch in ${k}: ${v.length}`);

// ---- the warnings about changed algorithms and translations ----
let validateFail = 0;
if (args.includes('--validate')) {
  // what a tool printed about module `name`: the translator's errors and the warning, if any
  const digest = (out, name) => {
    const errors = [...out.matchAll(/\nUnrecoverable error:\n -- [^]*?\.\n\n/g)].map(m => m[0].trim());
    // the block of warnings ends where the semantic analysis (or the list of errors) begins
    const start = out.indexOf('Warnings (');
    const block = start < 0 ? '' : out.slice(start).split(/^(?:Semantic processing|Semantic errors|\*\*\* Errors|Fatal errors|Abort messages|Linting)/m)[0];
    const w = new RegExp(`In module ${name}\\n\\n([^\\n]*)\\n`).exec(block);
    return JSON.stringify({ errors: [...new Set(errors)], warning: w ? w[1] : null });
  };
  const mutations = {
    same: t => t,
    // white space and comments are not part of the algorithm
    space: t => t.replace(/(--algorithm|--fair algorithm)([^\n]*)\n/, '$1$2  \n(* a comment *)\n'),
    // a change of the algorithm (which may also make it unparsable)
    algorithm: t => t.replace(/:=/, ':= 0 +'),
    broken: t => t.replace(/:=/, ':= ('),
    translation: t => t.replace(/(\\\* BEGIN TRANSLATION[^\n]*\n)/, '$1\n'),
    both: t => t.replace(/:=/, ':= 0 +').replace(/(\\\* BEGIN TRANSLATION[^\n]*\n)/, '$1\n'),
  };
  const jobs = [];
  for (const { c, j } of results) {
    if (j.status !== 0 || j.tla == null || c.corpus.includes('variants')) continue;
    for (const [mname, mutate] of Object.entries(mutations)) jobs.push({ c, mname, text: mutate(text(j.tla)) });
  }
  let n = 0, same = 0, skipped = 0;
  const kinds = {};
  async function vworker() {
    while (n < jobs.length) {
      const job = jobs[n++];
      const base = path.basename(job.c.file);
      const name = base.slice(0, -4);
      const h = crypto.createHash('sha256').update(jarStamp).update('\0sany\0').update(base).update('\0').update(job.text).digest('hex');
      const key = path.join(cacheDir, h + '.sany.json');
      const dir = fs.mkdtempSync(path.join(scratch, 'sany-'));
      // the other modules of the specification are needed for SANY to get as far as the warnings
      for (const f of fs.readdirSync(path.dirname(job.c.file))) if (f.endsWith('.tla') && f !== base) fs.copyFileSync(path.join(path.dirname(job.c.file), f), path.join(dir, f));
      fs.writeFileSync(path.join(dir, base), job.text);
      let jout;
      if (fs.existsSync(key)) jout = JSON.parse(fs.readFileSync(key, 'utf8'));
      else {
        jout = (await run('java', ['-cp', jar, 'tla2sany.SANY', base], dir, javaEnv)).stdout;
        fs.writeFileSync(key, JSON.stringify(jout));
      }
      const eout = (await run(bin, ['pcal', '--check', base], dir, process.env)).stdout;
      fs.rmSync(dir, { recursive: true, force: true });
      const k = (kinds[job.mname] ??= { total: 0, same: 0, warned: 0, skipped: 0 });
      // SANY prints the warnings only when it could load the module and everything it imports
      if (/Could not parse module|Cannot find source file|Fatal errors while parsing/.test(jout)) {
        k.skipped++;
        skipped++;
        continue;
      }
      const [dj, de] = [digest(jout, name), digest(eout, name)];
      k.total++;
      if (JSON.parse(dj).warning) k.warned++;
      if (dj === de) {
        same++;
        k.same++;
      } else {
        validateFail++;
        console.log(`VALIDATE FAIL ${job.c.id} (${job.mname}): SANY ${dj}, everystate ${de}`);
      }
    }
  }
  await Promise.all(Array.from({ length: Math.max(1, Math.min(8, os.cpus().length)) }, vworker));
  for (const [k, v] of Object.entries(kinds)) console.log(`validate ${k}: ${v.same} of ${v.total} agree with SANY (${v.warned} with a warning; ${v.skipped} skipped because SANY cannot load the module)`);
  console.log(`VALIDATE ${same} of ${jobs.length - skipped}`);
}

// ---- model-check a sample of the Examples before and after re-translation ----
let checkFail = 0;
if (checkN > 0) {
  const check = (dir, name) => {
    const r = spawnSync(bin, ['-json', `${name}.tla`], { cwd: dir, encoding: 'utf8', timeout: checkTimeout, maxBuffer: 1 << 28 });
    if (r.error || r.status === null) return null;
    try {
      const o = JSON.parse(r.stdout.trim().split('\n').pop());
      return { status: o.status, generated: o.generated, distinct: o.distinct };
    } catch {
      return null;
    }
  };
  let done = 0, same = 0;
  for (const { c, e } of results) {
    if (done >= checkN) break;
    if (c.corpus !== 'examples' || e.status !== 0) continue;
    const name = path.basename(c.file, '.tla');
    const src = path.dirname(c.file);
    // the models of this module: Name.cfg, and M.cfg for each module M that extends or instantiates it
    const uses = new RegExp(`\\b(EXTENDS|INSTANCE)\\b[^\\n]*\\b${name}\\b`);
    const models = fs.readdirSync(src).filter(f => f.endsWith('.cfg')).map(f => f.slice(0, -4))
      .filter(m => fs.existsSync(path.join(src, `${m}.tla`)) && (m === name || uses.test(fs.readFileSync(path.join(src, `${m}.tla`), 'latin1'))));
    if (models.length === 0) continue;
    const dir = fs.mkdtempSync(path.join(scratch, 'check-'));
    fs.cpSync(src, dir, { recursive: true });
    const t = spawnSync(bin, ['pcal', '-nocfg', `${name}.tla`], { cwd: dir, encoding: 'utf8' });
    for (const m of models) {
      if (done >= checkN) break;
      const before = check(src, m);
      if (!before || before.status === 'setup-error') continue;
      const after = t.status === 0 ? check(dir, m) : null;
      done++;
      if (after && JSON.stringify(before) === JSON.stringify(after)) {
        same++;
        if (show) console.log(`CHECK ok ${c.id} with ${m}.cfg: ${JSON.stringify(after)}`);
      } else {
        checkFail++;
        console.log(`CHECK FAIL ${c.id} with ${m}.cfg: before ${JSON.stringify(before)}, after ${JSON.stringify(after)}`);
      }
    }
    fs.rmSync(dir, { recursive: true, force: true });
  }
  console.log(`model-checked ${done} models of re-translated Examples specs: ${same} with unchanged status and state counts`);
}
fs.rmSync(scratch, { recursive: true, force: true });
console.log(`PASS ${pass} of ${results.length}`);
process.exit(pass === results.length && checkFail === 0 && validateFail === 0 ? 0 : 1);
