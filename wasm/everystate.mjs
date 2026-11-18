// everystate as WebAssembly: `conform(...)` for trace conformance, and the same
// `check({ root, modules, config, deadlock?, simulate?, print? })` API as the
// TypeScript package's index.ts, backed by the Rust engine. Works in Node and Bun out of the box (the
// .wasm file next to this module is read synchronously); in a browser or worker call `init()` first
// with the compiled module, its bytes, or a fetch() Response.
//
// Differences from the TypeScript API: a trace state is an array of already formatted values (one
// string per variable, in `model.vars` order), so `fmt` is the identity on them; `model` only carries
// `vars`. Every call runs in a fresh WebAssembly instance (string ordering starts from scratch, as
// `resetInterning()` does in TypeScript) and its memory is released afterwards.

let compiled = null;

/** Optional: provide the compiled module (WebAssembly.Module, bytes, or a Response / Promise of one). */
export async function init(source) {
  source = await source;
  if (source instanceof WebAssembly.Module) compiled = source;
  else if (typeof Response !== 'undefined' && source instanceof Response) compiled = await WebAssembly.compile(await source.arrayBuffer());
  else if (source) compiled = await WebAssembly.compile(source);
  else compiled = load();
  return compiled;
}

function load() {
  if (compiled) return compiled;
  const url = new URL('./everystate.wasm', import.meta.url);
  let bytes;
  if (typeof process !== 'undefined' && process.getBuiltinModule) bytes = process.getBuiltinModule('node:fs').readFileSync(url);
  else if (typeof Bun !== 'undefined' || typeof process !== 'undefined') bytes = globalThis.require?.('node:fs').readFileSync(url);
  if (!bytes) throw new Error('everystate: call `await init(wasmModuleOrBytes)` before check() in this environment.');
  compiled = new WebAssembly.Module(bytes);
  return compiled;
}

const enc = new TextEncoder(), dec = new TextDecoder();

export class TlaError extends Error {
  constructor(message, kind) { super(message); this.kind = kind; }
}

/** Formats a value of a trace state (they are already strings in TLC syntax). */
export const fmt = v => String(v);

/** A fresh instance with the module sources loaded; `put` copies a string into its memory. */
function instantiate(input) {
  const module = load();
  let memory;
  const print = input.print ?? (() => {});
  const instance = new WebAssembly.Instance(module, {
    env: {
      es_print: (ptr, len) => print(dec.decode(new Uint8Array(memory.buffer, ptr, len))),
      es_now: () => Date.now(),
    },
  });
  const ex = instance.exports;
  memory = ex.memory;
  const put = s => {
    const b = enc.encode(s);
    const p = ex.es_alloc(b.length);
    new Uint8Array(memory.buffer, p, b.length).set(b);
    return [p, b.length];
  };
  for (const [name, src] of Object.entries(input.modules)) ex.es_add_module(...put(name), ...put(src));
  const result = p => JSON.parse(dec.decode(new Uint8Array(memory.buffer, p, ex.es_result_len())));
  return { ex, put, result };
}

// The engine's call stack (RangeError) or the 64 MiB linear-memory stack (RuntimeError) ran out.
const isStackOverflow = e => e instanceof RangeError || (typeof WebAssembly !== 'undefined' && e instanceof WebAssembly.RuntimeError);
const STACK_MESSAGE = 'Stack overflow while evaluating the specification (recursion too deep). Re-run with a larger stack.';

/**
 * Model-check a specification held in memory. With `simulate` (true, or `{ traces?, depth?, seed?, aril? }`)
 * random behaviours are generated and checked instead of the whole state space, as TLC's -simulate does:
 * by default 1000 behaviours of at most 100 steps; `result.seed` repeats the run.
 * @param {{root: string, modules: Record<string,string>, config: string, deadlock?: boolean, simulate?: boolean | {traces?: number, depth?: number, seed?: number, aril?: number}, print?: (line: string) => void}} input
 */
export function check(input) {
  const { ex, put, result: read } = instantiate(input);
  let json;
  try {
    const deadlock = (input.deadlock ?? true) ? 1 : 0;
    const sim = input.simulate === true ? {} : input.simulate;
    const num = v => (typeof v === 'number' ? Math.trunc(v) : NaN);
    json = read(sim
      ? ex.es_simulate(...put(input.root), ...put(input.config), deadlock, num(sim.traces) || 0, Number.isNaN(num(sim.depth)) ? -1 : Math.max(0, Math.min(num(sim.depth), 2 ** 31 - 1)), num(sim.seed), num(sim.aril))
      : ex.es_check(...put(input.root), ...put(input.config), deadlock));
  } catch (e) {
    if (isStackOverflow(e)) {
      return {
        result: { status: 'error', message: STACK_MESSAGE, generated: 0, distinct: 0, queue: 0, depth: 0 },
        model: { vars: [] },
      };
    }
    throw e;
  }
  if (json.status === 'setup-error') throw new TlaError(json.message, json.kind);
  const vars = json.vars ?? [];
  const act = name => (name === null || name === undefined ? null : { name });
  const result = {
    status: json.status, name: json.name, message: json.message, code: json.code,
    generated: json.generated, distinct: json.distinct, queue: json.queue, depth: json.depth,
    loopTo: json.loopTo, loopAction: json.status === 'liveness' ? act(json.loopAction) : undefined,
    ...(json.mode === 'simulate' ? { mode: json.mode, traces: json.traces, seed: json.seed, aril: json.aril } : {}),
    trace: json.trace?.map(t => ({ action: act(t.action), state: vars.map(v => t.state[v]) })),
  };
  return { result, model: { vars: vars.map(name => ({ name })) } };
}

const PCAL_FLAGS = ['label', 'termination', 'noDoneDisjunct', 'reportLabels'];

/**
 * Translate the PlusCal algorithm in the text of a module to TLA+, as `java pcal.trans` does (same
 * output, including the checksums in the BEGIN TRANSLATION line). Pure: nothing is read or written.
 * @param {string} source the text of the module
 * @param {string[] | {fairness?: 'wf'|'sf'|'wfNext'|'nof', label?: boolean, labelRoot?: string, termination?: boolean, noDoneDisjunct?: boolean, lineWidth?: number, version?: string}} [options]
 *   the translator's command-line options (e.g. `['-wf', '-termination']`) or their object form
 * @returns {{output: string | null, errors: string[], messages: string[]}} the new text of the module
 *   (lines end with "\n"), or `null` with the reasons in `errors`
 */
export function translatePlusCal(source, options = []) {
  let opts = options;
  if (!Array.isArray(options)) {
    opts = [];
    if (options.fairness) opts.push(`-${options.fairness}`);
    for (const f of PCAL_FLAGS) if (options[f]) opts.push(`-${f}`);
    if (options.labelRoot !== undefined) opts.push('-labelRoot', String(options.labelRoot));
    if (options.lineWidth !== undefined) opts.push('-lineWidth', String(options.lineWidth));
    if (options.version !== undefined) opts.push('-version', String(options.version));
  }
  let memory;
  const instance = new WebAssembly.Instance(load(), { env: { es_print: () => {}, es_now: () => Date.now() } });
  const ex = instance.exports;
  memory = ex.memory;
  const put = s => {
    const b = enc.encode(s);
    const p = ex.es_alloc(b.length);
    new Uint8Array(memory.buffer, p, b.length).set(b);
    return [p, b.length];
  };
  const p = ex.es_pcal(...put(String(source)), ...put(opts.join('\n')));
  const json = JSON.parse(dec.decode(new Uint8Array(memory.buffer, p, ex.es_result_len())));
  const errors = [];
  for (const m of json.messages) {
    const e = /^\nUnrecoverable error:\n -- ([^]*)\.\n$/.exec(m);
    if (e) errors.push(e[1]);
  }
  if (json.output === null && errors.length === 0) errors.push(json.messages.join('\n') || 'The translation failed.');
  return { output: json.output, errors, messages: json.messages };
}

/**
 * Trace conformance: is a recorded run of the real system a behaviour of the specification?
 * `trace` is JSON Lines text, the text of a JSON array, or an array of observation objects
 * `{ action?, params?, state? }`. Returns the same object as `everystate conform -json`.
 * @param {{root: string, modules: Record<string,string>, config: string, trace: string | object[], hidden?: number, stutter?: boolean, behavior?: boolean, constraints?: boolean, limit?: number, print?: (line: string) => void}} input
 */
export function conform(input) {
  const { ex, put, result: read } = instantiate(input);
  const trace = typeof input.trace === 'string' ? input.trace : input.trace.map(o => JSON.stringify(o)).join('\n');
  const flags = (input.stutter ? 1 : 0) | (input.behavior ? 2 : 0) | (input.constraints === false ? 4 : 0);
  let json;
  try {
    json = read(ex.es_conform(...put(input.root), ...put(input.config), ...put(trace), input.hidden ?? 0, input.limit ?? 0, flags));
  } catch (e) {
    if (isStackOverflow(e)) return { status: 'error', message: STACK_MESSAGE, observations: 0, ignored: 0, matched: 0, candidates: 0 };
    throw e;
  }
  if (json.status === 'setup-error') throw new TlaError(json.message, json.kind);
  return json;
}

/**
 * Like `check`, but (under Node) runs in a worker thread with a large call stack, because WebAssembly
 * recursion uses the JavaScript engine's stack: the default ~1 MB allows roughly 500-1000 nested TLA+
 * operator applications, 256 MB allows the evaluator's own limit of 6000. Elsewhere it falls back to `check`.
 */
export async function checkAsync(input, { stackSizeMb = 256 } = {}) {
  const isNode = typeof process !== 'undefined' && process.versions?.node && !process.versions.bun && typeof Deno === 'undefined';
  if (!isNode) return check(input);
  const { Worker } = await import('node:worker_threads');
  const { print, ...plain } = input;
  const code = `
    import { parentPort, workerData } from 'node:worker_threads';
    const { check } = await import(workerData.url);
    const out = check({ ...workerData.input, print: line => parentPort.postMessage({ line }) });
    parentPort.postMessage({ out });`;
  return new Promise((resolve, reject) => {
    const w = new Worker(code, { eval: true, type: 'module', workerData: { url: import.meta.url, input: plain }, resourceLimits: { stackSizeMb } });
    w.on('message', m => { if (m.line !== undefined) print?.(m.line); else resolve(m.out); });
    w.on('error', reject);
  });
}
