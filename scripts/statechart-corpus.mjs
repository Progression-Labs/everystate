// Runs the (unmodified) pstack `statechart` skill script on its own test corpus, but with everystate
// standing in for Java+TLC, and compares the chart and report with the committed expectations.
// usage: node scripts/statechart-corpus.mjs /path/to/pstack/skills/statechart/scripts [--filter STR] [--show]
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
const args = process.argv.slice(2);
const sc = path.resolve(args[0]);
const filter = args.includes('--filter') ? args[args.indexOf('--filter') + 1] : '';
const corpus = path.join(sc, 'test/corpus');
const shimDir = fs.mkdtempSync(path.join(os.tmpdir(), 'verify-shim-'));
const shim = path.join(shimDir, 'java');
// EVERYSTATE_JAVA_CMD: an alternative java shim (e.g. "/path/to/everystate java" for the Rust binary)
const tsJava = path.resolve(import.meta.dirname, '../src/java.ts');
const javaCmd = process.env.EVERYSTATE_JAVA_CMD ?? (fs.existsSync(tsJava) ? undefined : `${path.resolve(import.meta.dirname, '../target/release/everystate')} java`) ?? `${process.execPath} --experimental-strip-types --no-warnings --stack-size=30000 ${path.resolve(import.meta.dirname, '../src/java.ts')}`;
fs.writeFileSync(shim, `#!/bin/sh\nexec ${javaCmd} "$@"\n`, { mode: 0o755 });
let pass = 0, fail = 0;
for (const name of fs.readdirSync(corpus).sort()) {
  if (filter && !name.includes(filter)) continue;
  const dir = path.join(corpus, name);
  const out = path.join(fs.mkdtempSync(path.join(os.tmpdir(), 'verify-sc-')), 'out');
  const view = path.join(dir, 'view.mjs');
  const r = spawnSync(process.execPath, ['--experimental-strip-types', '--no-warnings', path.join(sc, 'statechart.ts'), path.join(dir, `${name}.tla`),
    ...(fs.existsSync(view) ? ['--view', view] : []), '--out', out], { encoding: 'utf8', env: { ...process.env, JAVA: shim, TLA2TOOLS: '/nonexistent/tla2tools.jar' } });
  const read = f => (fs.existsSync(f) ? fs.readFileSync(f, 'utf8') : null);
  const firstExit = read(path.join(dir, 'verdict-1.exit'));
  const plain = firstExit ? Number(firstExit) : 0;
  const expStatus = plain === 0 ? 0 : [11, 12, 13].includes(plain) ? 1 : 2;
  const problems = [];
  if (r.status !== expStatus) problems.push(`exit ${r.status} != ${expStatus}`);
  for (const f of ['report.md', 'chart.mmd']) if (read(path.join(out, f)) !== read(path.join(dir, f))) problems.push(f);
  if (problems.length === 0) { pass++; continue; }
  fail++;
  console.log(`FAIL ${name}: ${problems.join(', ')}${r.stderr ? ' | stderr: ' + r.stderr.trim().split('\n').slice(0, 3).join(' / ').slice(0, 300) : ''}`);
  if (args.includes('--show')) {
    for (const f of ['report.md', 'chart.mmd']) {
      const a = read(path.join(out, f)), b = read(path.join(dir, f));
      if (a !== b) { fs.writeFileSync('/tmp/_a', a ?? ''); fs.writeFileSync('/tmp/_b', b ?? ''); console.log(spawnSync('diff', ['/tmp/_b', '/tmp/_a'], { encoding: 'utf8' }).stdout.split('\n').slice(0, 30).join('\n')); }
    }
  }
}
console.log(JSON.stringify({ pass, fail }));
process.exit(fail ? 1 : 0);
