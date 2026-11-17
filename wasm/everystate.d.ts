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

/** One recorded step of the real system. Other keys (timestamps, messages) are ignored. */
export interface Observation {
  /** Name of the spec action that happened. Omit it to allow any action. */
  action?: string | null;
  /** The action's arguments: in order, or by parameter name. */
  params?: unknown[] | Record<string, unknown>;
  /** Values of some or all spec variables after the step. Variables left out are unconstrained. */
  state?: Record<string, unknown>;
  [key: string]: unknown;
}
export interface ConformInput {
  root: string;
  modules: Record<string, string>;
  config: string;
  /** JSON Lines text, the text of a JSON array, or the observations themselves. */
  trace: string | Observation[];
  /** Up to this many unlogged steps may happen before each observation (default 0). */
  hidden?: number;
  /** An observation without an action may also be a snapshot of an unchanged state (default false). */
  stutter?: boolean;
  /** Include one full-state behaviour of the spec that matches the trace. */
  behavior?: boolean;
  /** Apply the CONSTRAINT bounds of the configuration (default true). */
  constraints?: boolean;
  /** Stop when more than this many spec states are consistent with the trace (default 100000). */
  limit?: number;
  print?: (line: string) => void;
}
export interface ConformResult {
  /** `conforms`; `mismatch`: an observation the spec does not allow; `invariant`: the recorded behaviour
   *  is allowed by the spec but violates an invariant of the configuration; `limit`: no verdict;
   *  `trace-error`: the trace is malformed. */
  status: 'conforms' | 'mismatch' | 'invariant' | 'limit' | 'trace-error' | 'assumption' | 'error';
  message?: string;
  /** invariant: its name */
  name?: string;
  /** Trace line (for an array of objects: 1-based element position) of the failing observation. */
  line?: number;
  observations: number;
  /** Trace entries without `action` and `state`. */
  ignored: number;
  matched: number;
  /** Number of spec states consistent with the matched observations. */
  candidates: number;
  /** `index` is the 1-based position among the observations. */
  failed?: { index: number; line: number; observation: Observation };
  lastMatched?: { index: number; line: number; candidates: number } | null;
  /** mismatch: the observed variables before the failing step (JSON form of the spec's values). */
  before?: Record<string, unknown>[];
  /** mismatch: the closest steps the spec allows, and how they differ from the observation. */
  nearest?: { action: string | null; differs: { var: string; observed: unknown; expected: unknown }[] }[];
  /** mismatch: the steps the spec allows at that point, with the observed variables after each. */
  enabled?: { action: string; produces: Record<string, unknown>; matchesState: boolean }[];
  enabledMore?: number;
  hints?: string[];
  notes?: string[];
  vars?: string[];
  /** One behaviour of the spec that matches the trace; values are TLA+ text. */
  behavior?: { line: number | null; action: string | null; state: Record<string, string> }[];
}
/** Checks that a recorded run is a behaviour of the specification. Throws `TlaError` if the spec or config does not parse. */
export function conform(input: ConformInput): ConformResult;
