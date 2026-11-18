# Conformance

Real TLC (`tla2tools.jar`) is the reference. Results below are for the Rust engine.

## tlaplus/Examples manifest

`npm run conformance:examples -- /path/to/Examples --max-runtime 5` (run from the Examples checkout)

Models whose upstream runtime is 5 seconds or less: **122 of 122** match on result kind and exact
generated and distinct state counts.

- State depth is not compared: the upstream numbers were recorded with several workers.
- The script passes `-Dtlc2.tool.impl.Tool.cdot=true`, as the Examples CI does for TLC; two models
  need action composition.
- Models up to 60 seconds: 161 of 161, measured before the last round of fixes and not repeated.

## TLC's own `test-model` directory

`npm run conformance:tlc -- /path/to/test-model`

Each model is run with live TLC and with everystate; outcome, state counts and trace length are
compared. **383 of 414** match. 4 are skipped because TLC itself times out. `pcal/Detlefs` sits at
the 60-second limit and can pass or time out.

| Reason for mismatch | Count | Specs |
|---|---|---|
| Result depends on TLC's random seed | 5 | `RandomElement`, `RandomElementXandY`, `RandomSubsetNext`, `SpanTreeRandom`, `Github648` |
| TLC fingerprints strings by low byte, so distinct states collide (not copied: it drops reachable states) | 3 | `Unicode*Fingerprint` |
| Java class module override | 1 | `UserModuleOverride` |
| Labels and full subexpression selectors | 4 | `suite/test206`, `209`, `219`, `219a` |
| SANY-only semantic errors | 4 | `suite/test212`, `213`, `214`, `217` |
| Large assumption suites on TLC value internals | 3 | `EmptySetEqAssume`, `ValueSemanticsAssume`, `KSubsetAssume` |
| TLC normalizes sets lazily | 3 | `NormalizationAssume`, `NormalizationLiveness`, `NormalizationTLCSet` |
| TLC checks safety-shaped temporal properties during the search | 3 | `Github710b`, `Github710d`, `InitialLivenessEvaluationError` |

## pstack `statechart` corpus

`npm run conformance:statechart -- /path/to/pstack/skills/statechart/scripts`

The unmodified script runs with `everystate java` standing in for Java: **33 of 33** charts and
reports are byte-identical to those recorded from TLC 2.19.

## Self-contained tests

`npm test`: the WebAssembly API (6 cases), the value pretty-printer against 337 outputs recorded
from the Java implementation, and the community-module operators (21 of 21 runnable fixtures).

## Known differences from TLC

- A liveness violation prints "Temporal properties were violated." as TLC 2.19 does; newer TLC
  names the violated properties.
- TLC's warnings and the "Trace exploration spec path" line are not printed.
- `RandomElement` and the `Randomization` module use a different generator.
- Reproductions of behaviours fixed during the port are in `repro/`.
