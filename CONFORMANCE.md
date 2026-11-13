# Conformance

Real TLC is the specification. Numbers below are from 2026-11-13, commit `3c73470`, against
`tla2tools.jar` 1.8.0 (and TLC 2.19 output for the statechart corpus).

## tlaplus/Examples manifest

`npm run conformance:examples -- /path/to/Examples --max-runtime 5`

Models whose upstream runtime is 5 seconds or less, exhaustive mode: **121 of 122** match on result
kind and on exact generated and distinct state counts.

- The one failure, `ewd998/EWD998ChanTrace.cfg`, reads a data file by a path relative to the
  Examples checkout; it passes when the script is run from that directory.
- State depth is not compared: the upstream numbers were recorded with several workers, which makes
  depth nondeterministic. Single-worker TLC agrees with verify.js on the cases checked by hand.
- The manifest labels action-property violations "liveness failure" (TLC exit code 13); the script
  maps them the same way.

## TLC's own `test-model` directory

`npm run conformance:tlc -- /path/to/tlaplus/tlatools/org.lamport.tlatools/test-model`

Every `X.tla` with an `X.cfg` is run through real TLC and through verify.js; outcome class, violated
invariant name, generated/distinct counts and trace length are compared.

**377 of 414 match.** 8 are skipped because TLC itself does not finish in the time limit.
The 29 mismatches:

| Reason | Count | Specs |
|---|---|---|
| Result depends on a random seed | 4 | `RandomElement`, `RandomSubsetNext`, `SpanTreeRandom`, `RandomElementXandY` |
| Out of scope: fingerprint-collision tests, Java module override | 4 | `Unicode*Fingerprint` (3), `UserModuleOverride` |
| Deliberate: TLC rejects `\cdot` unless a flag is set, verify.js implements it | 3 | `cdot/*` |
| Labels and the full subexpression-selector syntax | 4 | `suite/test206`, `test209`, `test219`, `test219a` |
| Errors only SANY reports (non-Leibniz substitution, level errors, `HIDE`) | 4 | `suite/test212`–`214`, `test217` |
| Suites of hundreds of assumptions on exact TLC internals and message text | 4 | `EmptySetEqAssume`, `ValueSemanticsAssume`, `NormalizationAssume`, `KSubsetAssume` |
| TLC keeps mixed-type sets unsorted until needed | 2 | `NormalizationLiveness`, `NormalizationTLCSet` |
| TLC checks some temporal properties during the search, verify.js only at the end | 3 | `InitialLivenessEvaluationError`, `Github710b`, `Github710d` |
| `ALIAS` trace formatting | 1 | `PrintTraceException` |

## pstack `statechart` corpus

`npm run conformance:statechart -- /path/to/pstack/skills/statechart/scripts`

The unmodified script, with `verify-java` in place of Java and no `tla2tools.jar`:
**33 of 33** cases produce a byte-identical `chart.mmd` and `report.md`.

## Self-contained tests

`npm test` — 34 pass, 0 fail, 4 todo. No Java needed.

## Known behavioural differences from TLC

- Liveness is checked once, after the state space is complete (TLC's `-lncheck final`).
- Fingerprints are 64-bit but not TLC's, so node ids in `-dump dot` output differ.
- Sets are kept sorted from construction; TLC sorts lazily. A set mixing incomparable values fails
  earlier than in TLC.
- `\cdot` (action composition) works without a flag.
