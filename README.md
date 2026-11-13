# verify.js

A TLA+ model checker written in pure TypeScript. No Java, no native code, no runtime dependencies.

It reads ordinary TLA+ modules and TLC configuration files, explores the state space the way TLC
does, and prints results in TLC's format, so tools written against TLC keep working.

```sh
npx verify.js Spec.tla                 # uses Spec.cfg next to the spec
npx verify.js -config MC.cfg -deadlock Spec.tla
```

```
Error: Invariant NotSolved is violated.
Error: The behavior up to this point is:
State 1: <Initial predicate>
/\ big = 0
/\ small = 0

State 2: <FillBig line 16, col 12 to line 16, col 37 of module DieHard>
/\ big = 5
/\ small = 0
...
73 states generated, 14 distinct states found, 1 states left on queue.
```

Runs on Node 20+ and Bun. It uses only `node:fs`, `node:path`, `node:worker_threads` and
`node:child_process` in its CLI host; the checker itself (`import { check } from 'verify.js'`) needs
no host APIs at all and runs anywhere JavaScript does.

## What it does

- **Language**: the full TLA+ expression language as TLC supports it — modules, `EXTENDS`,
  `INSTANCE ... WITH` (named, parameterised, `LOCAL`, inside `LET`), recursive operators and
  functions, higher-order operators, `LAMBDA`, `CASE`, `CHOOSE`, `EXCEPT`, junction lists, action
  operators (`'`, `UNCHANGED`, `ENABLED`, `[A]_v`, `<<A>>_v`, `\cdot`), temporal operators, proofs
  (parsed and ignored).
- **Checking**: invariants, deadlock, state and action constraints, `[][A]_v` action properties,
  refinement (`PROPERTY OtherSpec`), and liveness under weak and strong fairness
  (`[]<>`, `<>[]`, `~>`, `WF_`, `SF_`) with lasso counterexamples.
- **Configuration**: `SPECIFICATION`, `INIT`/`NEXT`, `CONSTANT(S)` (values, model values, `<-`
  substitution), `INVARIANT(S)`, `PROPERTY/PROPERTIES`, `CONSTRAINT(S)`, `ACTION_CONSTRAINT(S)`,
  `SYMMETRY`, `VIEW`, `CHECK_DEADLOCK`.
- **Standard modules**, implemented natively: `Naturals`, `Integers`, `Reals` (integers only),
  `Sequences`, `FiniteSets`, `Bags`, `TLC`, `TLCExt`, `Randomization`.
- **Community modules**, bundled: `FiniteSetsExt`, `SequencesExt`, `Functions`, `Folds`, `Graphs`,
  `UndirectedGraphs`, `Relation`, `BagsExt`, `Bitwise`, `Combinatorics`, `Json`, `CSV`, `IOUtils`,
  `VectorClocks`, `DyadicRationals`, `Statistics`, and the TLAPS library modules (`TLAPS`,
  `FiniteSetTheorems`, `NaturalsInduction`, ...) so that specs with proofs load.
- **Output**: TLC's messages, `-tool` framing, exit codes, trace format with action names and
  source locations, 80-column value wrapping, and `-dump dot,actionlabels`.

## Using it where a tool expects Java + TLC

`verify-java` accepts the command line of `java -cp tla2tools.jar tlc2.TLC ...` (and of
`tla2sany.xml.XMLExporter`). Point a TLC-driving script at it instead of a JVM:

```sh
JAVA="$(npm root)/verify.js/dist/java.js" TLA2TOOLS=unused  some-tool-that-runs-tlc Spec.tla
```

The pstack `statechart` skill script runs unmodified this way.

## API

```ts
import { check, fmt } from 'verify.js';

const { result, model } = check({
  root: 'Spec',
  modules: { Spec: tlaSource },         // plus any modules it imports that are not bundled
  config: 'SPECIFICATION Spec\nINVARIANT TypeOK',
});
result.status;      // 'ok' | 'invariant' | 'deadlock' | 'liveness' | 'action-property' | ...
result.distinct;    // distinct states found
result.trace;       // counterexample: [{ state, action }]
```

## How it is verified

Real TLC is the specification. Three suites compare against it:

| Suite | What is compared | Command |
|---|---|---|
| [tlaplus/Examples](https://github.com/tlaplus/Examples) manifest | result kind and exact generated / distinct state counts recorded upstream | `npm run conformance:examples -- /path/to/Examples` |
| TLC's own `test-model` directory | outcome, state counts and trace length against a live run of `tla2tools.jar` | `npm run conformance:tlc -- /path/to/test-model` |
| pstack `statechart` corpus | byte-identical charts and reports produced by the real script with verify.js standing in for Java | `npm run conformance:statechart -- /path/to/statechart/scripts` |

`npm test` runs the self-contained tests (no Java needed): the checker API, the value
pretty-printer against 337 outputs recorded from the Java implementation, and the community-module
operators against fixtures validated with real TLC.

Current results are in [CONFORMANCE.md](CONFORMANCE.md).

## Not supported (yet)

- Simulation / generation mode (`-simulate`, `-generate`), depth-first iterative deepening.
- Multiple workers, disk-backed state queues and fingerprint sets, checkpointing: everything is in
  memory, so the practical limit is a few million distinct states.
- The PlusCal translator (specs that already contain their translation work).
- Trace-explorer spec generation, the debugger, coverage statistics, Java module overrides.
- TLAPS proofs are parsed and skipped, not checked.

## Rust port

`rust/` holds `verify-rs`, a Rust port of the safety checker (no liveness, `-tool` or `-dump`),
built to compare speed. It is about 2x faster than this TypeScript engine on Node and roughly level
with single-worker Java TLC; see `rust/BENCHMARK.md`. The TypeScript engine is the complete one.

## Layout

```
src/lexer.ts, parser.ts     TLA+ front end
src/modules.ts              module loading, name resolution, expression levels
src/values.ts               values and TLC's ordering
src/eval.ts                 evaluator and next-state enumeration
src/stdlib.ts, community.ts native standard and community module operators
src/model.ts, cfg.ts        configuration -> checkable model
src/checker.ts, liveness.ts breadth-first search, liveness (tableau + SCC)
src/main.ts                 CLI, TLC-compatible output, java shim
```

## License

MIT. Bundled TLA+ library modules keep their own (MIT / BSD) licenses.
