// Runs a CLI entry point. Under Node the work is done in a worker thread with a large stack, because
// evaluating deeply recursive TLA+ definitions needs far more stack than the 1 MB main-thread default.
import { Worker, isMainThread, parentPort, workerData } from 'node:worker_threads';
import * as os from 'node:os';
import { nodeHost } from './node-host.ts';
import type { Host } from './main.ts';

export function runEntry(entryUrl: string, main: (argv: string[], host: Host) => void): void {
  const isNode = !(process.versions as Record<string, string>).bun && !(globalThis as Record<string, unknown>).Deno;
  if (!isMainThread && workerData && workerData.verifyEntry) {
    const host = nodeHost();
    let code = 0;
    host.exit = c => { code = c; };
    try {
      main(workerData.argv, host);
    } finally {
      parentPort!.postMessage({ exit: code });
    }
    return;
  }
  if (!isNode || process.env.VERIFY_NO_WORKER) { main(process.argv.slice(2), nodeHost()); return; }
  const heapMb = Math.max(2048, Math.min(16384, Math.floor(os.totalmem() / 1048576 * 0.75)));
  const w = new Worker(new URL(entryUrl), {
    workerData: { verifyEntry: true, argv: process.argv.slice(2) },
    resourceLimits: { stackSizeMb: 256, maxOldGenerationSizeMb: heapMb },
    stdout: false, stderr: false,
  });
  w.on('message', m => { if (m && typeof m.exit === 'number') process.exitCode = m.exit; });
  w.on('error', e => {
    const msg = (e as { code?: string }).code === 'ERR_WORKER_OUT_OF_MEMORY'
      ? 'Error: verify.js ran out of memory while exploring the state space.'
      : `Error: ${e && (e as Error).stack ? (e as Error).stack : e}`;
    process.stdout.write(msg + '\n');
    process.exitCode = 255;
  });
}
