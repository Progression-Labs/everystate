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
