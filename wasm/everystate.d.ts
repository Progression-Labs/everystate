export interface CheckInput {
  /** Name of the root module. */
  root: string;
  /** Module sources by module name (the root and any modules it EXTENDS/INSTANCEs that are not bundled). */
  modules: Record<string, string>;
  /** Contents of the TLC configuration (.cfg) file. */
  config: string;
  /** Check for deadlock (default: true unless the config says CHECK_DEADLOCK FALSE). */
  deadlock?: boolean;
  /** Receives output of Print/PrintT. */
  print?: (line: string) => void;
}
export interface TraceStep { action: { name: string } | null; state: string[] }
export interface CheckResult {
  status: 'ok' | 'invariant' | 'invariant-init' | 'deadlock' | 'action-property' | 'implied-init' | 'liveness' | 'error' | 'assumption' | 'incomplete' | 'init-error';
  name?: string;
  message?: string;
  code?: number;
  generated: number;
  distinct: number;
  queue: number;
  depth: number;
  /** liveness: index (0-based) of the state the lasso returns to; -1 = stuttering */
  loopTo?: number;
  loopAction?: { name: string } | null;
  trace?: TraceStep[];
}
export class TlaError extends Error { kind: string }
export function init(source?: WebAssembly.Module | BufferSource | Response | Promise<Response>): Promise<WebAssembly.Module>;
export function check(input: CheckInput): { result: CheckResult; model: { vars: { name: string }[] } };
export function fmt(value: unknown): string;
/** Under Node: runs `check` in a worker thread with a `stackSizeMb` call stack (default 256). */
export function checkAsync(input: CheckInput, options?: { stackSizeMb?: number }): Promise<{ result: CheckResult; model: { vars: { name: string }[] } }>;

export interface PlusCalOptions {
  /** Fairness of the generated Spec: `wf`/`sf` (of each process), `wfNext` (of Next) or `nof` (none). */
  fairness?: 'wf' | 'sf' | 'wfNext' | 'nof';
  /** Add missing labels (required when the algorithm has some labels but not all it needs). */
  label?: boolean;
  /** Prefix of added labels (default `Lbl_`). */
  labelRoot?: string;
  /** Translate for checking termination: the default fairness becomes `wf`. */
  termination?: boolean;
  /** Do not add the disjunct that allows stuttering after termination. */
  noDoneDisjunct?: boolean;
  /** Preferred width of the generated lines (default 78, at least 60). */
  lineWidth?: number;
  /** Translate as an earlier PlusCal version did (e.g. `'1.4'`). */
  version?: string;
}
export interface PlusCalTranslation {
  /** The text of the module with the new translation (lines end with "\n"), or null if the translation failed. */
  output: string | null;
  /** Why the translation failed (the translator's error messages, with line and column). */
  errors: string[];
  /** Everything the translator printed. */
  messages: string[];
}
/**
 * Translates the PlusCal algorithm in the text of a module to TLA+ between its BEGIN TRANSLATION and
 * END TRANSLATION lines (added after the algorithm if missing), with the output of `java pcal.trans`.
 * `options` are the translator's command-line options (`['-wf', '-termination']`) or their object form.
 * Pure: no file is read or written (so no .cfg and no .old file).
 */
export function translatePlusCal(source: string, options?: string[] | PlusCalOptions): PlusCalTranslation;
