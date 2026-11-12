// Programmatic API.
export { runCli, runJavaShim, runXmlExporter, stateText, actionLabel, VERSION } from './main.ts';
export type { Host } from './main.ts';
export { parseConfig } from './cfg.ts';
export type { Config } from './cfg.ts';
export { buildModel } from './model.ts';
export type { Model, Action, Pred } from './model.ts';
export { modelCheck } from './liveness.ts';
export { Checker } from './checker.ts';
export type { CheckResult, CheckOptions, TraceStep, State } from './checker.ts';
export { parseModule, parseExpression } from './parser.ts';
export { fmt } from './values.ts';
export { ppr } from './pprint.ts';
export { TlaError } from './lexer.ts';
export { BUNDLED } from './bundled.ts';

import { parseConfig } from './cfg.ts';
import { buildModel } from './model.ts';
import { modelCheck } from './liveness.ts';
import { BUNDLED } from './bundled.ts';
import { resetInterning } from './values.ts';
import type { CheckResult } from './checker.ts';
import type { Model } from './model.ts';

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

/** Model-check a specification held in memory. Works in any JavaScript runtime (no file system needed). */
export function check(input: CheckInput): { result: CheckResult; model: Model } {
  resetInterning();
  const cfg = parseConfig(input.config);
  const model = buildModel(input.root, name => input.modules[name] ?? BUNDLED[name] ?? null, cfg, { print: input.print ?? (() => {}) });
  const { result } = modelCheck(model, { checkDeadlock: (input.deadlock ?? true) && model.checkDeadlock });
  return { result, model };
}
