#!/usr/bin/env node
// Launcher: runs the prebuilt native binary for this platform (shipped in ../native/<platform>-<arch>/),
// or falls back to the WebAssembly build, which only prints a JSON result.
import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';

const exe = process.platform === 'win32' ? 'everystate.exe' : 'everystate';

function nativeBinary() {
  if (process.env.EVERYSTATE_BINARY) return process.env.EVERYSTATE_BINARY;
  const file = path.join(import.meta.dirname, '..', 'native', `${process.platform}-${process.arch}`, exe);
  if (!fs.existsSync(file)) return null;
  try { fs.accessSync(file, fs.constants.X_OK); } catch { try { fs.chmodSync(file, 0o755); } catch {} }
  return file;
}

const args = process.argv.slice(2);

const bin = nativeBinary();
if (bin) {
  const r = spawnSync(bin, args, { stdio: 'inherit' });
  if (r.error) { console.error(`everystate: cannot run ${bin}: ${r.error.message}`); process.exit(1); }
  if (r.signal) process.kill(process.pid, r.signal);
  process.exit(r.status ?? 1);
} else {
  console.error(`everystate: no prebuilt binary for ${process.platform}-${process.arch}; using the WebAssembly build (JSON output only).`);
  process.argv = [process.argv[0], process.argv[1], ...args];
  await import('../wasm/cli.mjs');
}
