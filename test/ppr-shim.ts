// Stand-in for src/pprint.ts that calls the Rust pretty-printer, so that test/pprint.test.ts
// (337 cases produced by the real Java implementation) can be reused unchanged.
import { spawnSync } from 'node:child_process';
import path from 'node:path';
const bin = path.resolve(import.meta.dirname, '../target/release/everystate');
export function ppr(value: string, width = 80): string {
  const r = spawnSync(bin, ['--ppr', String(width)], { input: value, encoding: 'utf8' });
  return r.stdout;
}
