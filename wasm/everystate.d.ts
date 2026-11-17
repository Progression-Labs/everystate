export interface CheckInput {
  /** Name of the root module. */
  root: string;
  /** Module sources by module name (the root and any modules it EXTENDS/INSTANCEs that are not bundled). */
  modules: Record<string, string>;
  /** Contents of the TLC configuration (.cfg) file. */
  config: string;
  /** Check for deadlock (default: true unless the config says CHECK_DEADLOCK FALSE). */
  deadlock?: boolean;
  /**
   * Random simulation (TLC's `-simulate`) instead of exhaustive checking: generate random behaviours
   * and check each of them. For models too large to enumerate; `status: 'ok'` then only means that no
   * generated behaviour violates a property. `true` uses the defaults.
   */
  simulate?: boolean | SimulateOptions;
  /** Receives output of Print/PrintT. */
  print?: (line: string) => void;
}
export interface SimulateOptions {
  /** Number of behaviours to generate (default 1000; a run is always bounded). */
  traces?: number;
  /** Maximal number of steps of a behaviour (default 100, as TLC's `-depth`). */
  depth?: number;
  /** Seed of the random choices; the same seed repeats the run. Default: taken from the clock. */
  seed?: number;
  /** A second number mixed into the seed (TLC's `-aril`, default 0). */
  aril?: number;
}
export interface TraceStep { action: { name: string } | null; state: string[] }
export interface CheckResult {
  status: 'ok' | 'invariant' | 'invariant-init' | 'deadlock' | 'action-property' | 'implied-init' | 'liveness' | 'error' | 'assumption' | 'incomplete' | 'init-error';
  name?: string;
  message?: string;
  code?: number;
  /** States generated. In a simulation: the initial states plus every successor computed. */
  generated: number;
  /** Distinct states found (-1 in a simulation, which does not count them). */
  distinct: number;
  /** States left unexplored (-1 in a simulation). */
  queue: number;
  /** Depth of the search. In a simulation: the number of states of the longest behaviour. */
  depth: number;
  /** Present, with the three fields below, when the result comes from a simulation. */
  mode?: 'simulate';
  /** Simulation: behaviours generated (including the one that ended in an error). */
  traces?: number;
  /** Simulation: the seed used; pass it as `simulate.seed` to repeat the run. */
  seed?: number;
  aril?: number;
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
