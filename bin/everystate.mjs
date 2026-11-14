#!/usr/bin/env node
// Launcher: runs the prebuilt native binary for this platform (installed as an optional dependency),
// or falls back to the WebAssembly build, which only prints a JSON result.
import { spawnSync } from 'node:child_process';
import { createRequire } from 'node:module';
import path from 'node:path';

const require = createRequire(import.meta.url);
const exe = process.platform === 'win32' ? 'everystate.exe' : 'everystate';

function nativeBinary() {
  if (process.env.EVERYSTATE_BINARY) return process.env.EVERYSTATE_BINARY;
  try {
    return require.resolve(`everystate-${process.platform}-${process.arch}/bin/${exe}`);
  } catch {
    return null;
  }
}

// `everystate-java ...` is `everystate java ...`: the stand-in for `java -cp tla2tools.jar tlc2.TLC`.
const asJava = path.basename(process.argv[1] ?? '').startsWith('everystate-java');
const args = asJava ? ['java', ...process.argv.slice(2)] : process.argv.slice(2);

const bin = nativeBinary();
if (bin) {
  const r = spawnSync(bin, args, { stdio: 'inherit' });
  if (r.error) { console.error(`everystate: cannot run ${bin}: ${r.error.message}`); process.exit(1); }
  if (r.signal) process.kill(process.pid, r.signal);
  process.exit(r.status ?? 1);
} else if (asJava) {
  console.error(`everystate: no prebuilt binary for ${process.platform}-${process.arch}; the Java stand-in needs one (cargo install everystate).`);
  process.exit(1);
} else {
  console.error(`everystate: no prebuilt binary for ${process.platform}-${process.arch}; using the WebAssembly build (JSON output only).`);
  process.argv = [process.argv[0], process.argv[1], ...args];
  await import('../wasm/cli.mjs');
}
