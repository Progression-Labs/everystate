# everystate

## 0.4.0

### Minor Changes

- f0ebc18: Actions and invariants are now compiled once into closures over a frame of slots, with the tree-walking evaluator as the automatic fallback: about 30% less CPU on actor-style models and 6% on the benchmark set, with identical results. `EVERYSTATE_EVAL=tree` selects the tree-walker alone. An experimental bounded cache of local steps is available with `EVERYSTATE_STEP_CACHE=on` (off by default; `EVERYSTATE_STEP_CACHE_MB` sets its fixed size, default 32, per worker).
- b9a2e9d: Faster transitions: bag updates by merge, an additive content-based state fingerprint probed before a successor state is allocated, and less work per step in the evaluator; `EVERYSTATE_CACHE_STATS=1` reports how often a cache of local steps would hit.
- 4527826: `-workers N` (and `-workers auto`) runs the breadth-first search on N threads in the native binary; state counts, depth, verdict and counterexample are identical to a one-worker run.
- c375290: Add a PlusCal translator, `everystate pcal [options] File.tla` (also `java pcal.trans` through the Java stand-in, and `translatePlusCal` in the WebAssembly API), whose output is byte-identical to the Java translator's; the model checker now warns, like TLC, when an algorithm or its translation changed since it was translated.
- c912576: Remove the `everystate-java` command from the npm package.
- 416d264: Simulation mode: `-simulate [num=N]` with `-depth`, `-seed` and `-aril` generates and checks random behaviours as TLC does, for models too large to enumerate; also `check({ simulate })` in the WebAssembly API.
- 975ba5d: Trace conformance: `everystate conform -trace run.jsonl Spec.tla` (and `conform()` in the WebAssembly API) checks that a recorded run of the real system is a behaviour of the spec, and reports the first step the spec does not allow.

### Patch Changes

- 2d4202d: The WebAssembly fallback of the command now exits with the same status as the native binary (12 for an invariant violation, and so on) instead of always 0.

## 0.3.1

### Patch Changes

- f3d05fa: Add the `formal-verification` agent skill (`skills/formal-verification`), with a worked example, and ship it in the npm package.
- 8aa9fbd: Releases now go through changesets, and the crate is published from CI with trusted publishing. No change to the engine.
