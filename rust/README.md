# everystate (Rust)

The Rust engine of everystate: a TLA+ model checker that is command-line and output compatible with
TLC. It is a port of the TypeScript engine in `../src`, which remains the reference oracle; real TLC
(`scripts/tlc.sh`) is the specification for both.

It covers safety and liveness checking, TLC's text and `-tool` output, state dumps, the `java`
command-line shim, the native standard and community modules, and it also builds as WebAssembly.

## Build and run

```
cd rust
cargo build --release
target/release/everystate [options] SPEC[.tla]
```

| option | meaning |
|---|---|
| `-config FILE` | configuration file (default `SPEC.cfg`) |
| `-deadlock` | do not check for deadlock |
| `-tool` | TLC's machine-readable message framing (`@!@!@STARTMSG ...`) |
| `-dump FILE`, `-dump dot[,actionlabels] FILE` | write the reachable states / the state graph |
| `-json` | one JSON line: `{"status","name","message","generated","distinct","queue","depth","loopTo","trace":[{"action","state":{var:"value"}}]}` |
| `-cdot`, `-Dtlc2.tool.impl.Tool.cdot=true` | enable action composition (`\cdot`), which is an error otherwise, as in TLC |
| `-workers N`, `-metadir DIR`, `-lncheck S`, ... | accepted and ignored |

Exit statuses are TLC's: 0 success, 10 assumption, 11 deadlock, 12 invariant, 13 property (action
property, implied init, liveness), 75/76 evaluation errors, 150 parse error, 151 config error, 255 other.

**Java shim.** `everystate java -cp tla2tools.jar tlc2.TLC ...` (or the same binary installed under
the name `everystate-java` or `java`) emulates the `java` command line of the TLA+ tools:
`tlc2.TLC`, `tla2sany.xml.XMLExporter` and `tla2sany.SANY`, with `-DTLA-Library=` as library path.

## WebAssembly

```
rust/wasm/build.sh          # cargo build --target wasm32-unknown-unknown, copies wasm/everystate.wasm (1.7 MB)
```

`wasm/everystate.mjs` (types in `everystate.d.ts`) exposes the same API as the TypeScript package:

```js
import { check, checkAsync, fmt } from './rust/wasm/everystate.mjs';
const { result, model } = check({ root: 'Spec', modules: { Spec: source }, config: 'INIT Init\nNEXT Next', deadlock: true, print: console.log });
```

- Target `wasm32-unknown-unknown`, no JS toolchain: a hand-written loader with two imports
  (`es_print`, `es_now`). Works in Node and Bun as is; in a browser call `await init(fetch(url))` first.
- The core has no direct file-system, clock or process access (`src/host.rs` is the only door), so
  file-based community operators report "not available" under WebAssembly.
- Differences from the TypeScript `check`: a trace state is an array of formatted values (strings, in
  `model.vars` order), `fmt` is the identity on them, and `model` only has `vars`. Setup errors throw.
- Each call runs in a fresh instance, so string ordering starts from scratch as `resetInterning()` does.
- **Recursion.** WebAssembly calls use the JavaScript engine's stack. With the default stack, Node
  evaluates between 500 and 1000 nested TLA+ operator applications and Bun between 1000 and 2000
  (measured with `Sum(n) == IF n = 0 THEN 0 ELSE n + Sum(n - 1)`); beyond that `check` returns
  `status: "error"` with the "Stack overflow ..." message instead of crashing, but without counts.
  `checkAsync` runs the check in a Node worker thread with a 256 MB stack, which reaches the
  evaluator's own limit of 6000 (as does `node --stack-size=30000`). The linear-memory stack is 64 MiB
  (`.cargo/config.toml`) and is guarded separately.
- `node rust/wasm/cli.mjs [-config FILE] SPEC.tla` is a small CLI on top of it (used by the benchmark).

## Verification

All of these are run against real TLC results or against the TypeScript engine:

| check | command | result |
|---|---|---|
| tlaplus/Examples manifest, runtime <= 5 s | `EVERYSTATE_CMD=rust/target/release/everystate node scripts/conformance.mjs <Examples> --max-runtime 5 --timeout 120` (from the Examples checkout) | 122 / 122 |
| TLC `test-model` differential against live `tla2tools.jar` | `EVERYSTATE_CMD=... node scripts/diff-tlc.mjs <test-model>` | 384 / 414, 4 skipped (TLC times out); the 26 mismatches and their reasons are in BENCHMARK.md |
| pstack statechart corpus through the Java shim | `EVERYSTATE_JAVA_CMD="rust/target/release/everystate java" node scripts/statechart-corpus.mjs <scripts>` | 33 / 33 byte-identical |
| complete text output vs the TypeScript engine (debugging aid only, TLC is the arbiter) | `node rust/scripts/diff-ts.mjs <test-model>` (also with `--tool`) | 398 of 408 identical before the Rust-only TLC fixes listed below |
| pretty-printer, 337 cases produced by Java | `node --experimental-strip-types --test rust/tests/pprint.test.ts` | all pass |
| community-module fixtures and upstream tests | `node rust/tests/community.mjs` | 21 / 21 |
| WebAssembly API | `node --experimental-strip-types --test rust/wasm/check.test.ts`, `bun test rust/wasm/check.test.ts` | 6 / 6 each |

## Layout

| file | ported from | contents |
|---|---|---|
| `src/intern.rs` | values.ts (`strId`) | identifier interner; string interner whose ids reproduce TLC's first-seen string order |
| `src/lexer.rs`, `src/parser.rs`, `src/ast.rs` | lexer.ts, parser.ts | tokens, column-sensitive junction lists, precedence climbing, proofs parsed and skipped |
| `src/modules.rs` | modules.ts | module loading, EXTENDS / INSTANCE, name resolution, arity checks, levels |
| `src/value.rs` | values.ts | values in canonical form, symbolic and lazy sets, TLC ordering, equality, hashing, printing |
| `src/eval.rs` | eval.ts | evaluator: thunks with state-keyed caching, keep-lazy functions, ENABLED, primes, action enumeration |
| `src/stdlib.rs`, `src/community.rs` | stdlib.ts, community.ts | standard modules and all native community-module operators |
| `src/cfg.rs`, `src/model.rs` | cfg.ts, model.ts | config, constants, substitution, spec / action splitting, properties, symmetry, VIEW, ALIAS, _POSSIBLE |
| `src/checker.rs`, `src/liveness.rs` | checker.ts, liveness.ts | BFS, counting rules, traces, tableau, product graph, SCC search, lasso counterexamples, POSTCONDITION |
| `src/pprint.rs` | pprint.ts | TLC's 80-column value pretty-printer |
| `src/cli.rs`, `src/main.rs` | main.ts, java.ts | TLC-compatible CLI, `-tool`, `-dump`, XMLExporter, Java shim |
| `src/tshash.rs` | values.ts (`Hasher`) | the TypeScript fingerprint, bit for bit, used only for node ids in `-dump dot` |
| `src/host.rs`, `src/wasm.rs`, `wasm/` | node-host.ts, index.ts | host abstraction, WebAssembly exports, JS wrapper |
| `lib/*.tla`, `src/bundled.rs` | bundled.ts | bundled community / TLAPS modules (`scripts/export-lib.mjs` regenerates them) |
| `repro/` | - | minimal specs for bugs found in the TypeScript engine |
| `scripts/diff-ts.mjs`, `tests/` | - | differential and reuse-the-TS-tests harnesses |

## Dependencies

- `mimalloc` (native builds only): the evaluator allocates many small reference-counted nodes; it was
  3-23 % faster than glibc malloc on the models tried. WebAssembly uses the standard allocator.
- Nothing else; no dependency at all for the WebAssembly build.

## Running without the TypeScript engine

`scripts/conformance.mjs`, `scripts/diff-tlc.mjs` and `scripts/statechart-corpus.mjs` use the Rust
binary when `EVERYSTATE_CMD` / `EVERYSTATE_JAVA_CMD` is set, and fall back to
`rust/target/release/everystate` when `src/cli.ts` (`src/java.ts`) does not exist. `rust/tests/*`,
`rust/wasm/check.test.ts` and `rust/bench.mjs` need only the binary, Node and (for the benchmark) TLC;
`rust/tests/community.mjs` reads the fixture specs in `test/community`. `rust/scripts/export-lib.mjs`
without an argument regenerates `src/bundled.rs` from `rust/lib/*.tla`. Only `rust/scripts/diff-ts.mjs`
and the files in `test/*.test.ts` need `src/`.

## Where the Rust engine follows TLC and the TypeScript engine does not

- Prefix operators followed by an infix operator of overlapping precedence (`SUBSET S \cup T`,
  `[]x = 1`) and unary minus after a tighter infix operator (`a * -b`, `2 ^ -x`) are SANY's
  "Precedence conflict" parse errors; `DOMAIN` has precedence 9-9.
- A step reference with arguments in a proof (`<1>4!1!(v)`) parses.
- `AXIOM` is not evaluated (only `ASSUME` / `ASSUMPTION`).
- `ALIAS` is applied to printed trace states, including `_format` and `_ALIASEvalError`.
- `\cdot` is rejected unless enabled (see the options).
- `kSubset(0, S)` is `{{}}` for any `S`; large `kSubset`s stay symbolic.
- Stack exhaustion is always reported as TLC-style "Stack overflow ..." (TypeScript can die with a raw
  `RangeError` while normalising temporal formulas, e.g. test-model `Github1389Loops`).

Repro specs for these are in `repro/`; BENCHMARK.md has the table.

## Other notes

- `RandomElement` / `Randomization` use a different generator than TLC and than the TypeScript engine,
  so runs that depend on random choices differ (as they do between two TLC runs).
- Timestamps are printed in UTC.
- Liveness is checked once, after the state space is complete (TLC's `-lncheck final`); TLC's
  detection of safety-shaped temporal properties during the search is not implemented.
- A liveness violation prints "Temporal properties were violated." (TLC 2.19 text); TLC 2026 names the
  properties.
- Runtime-created strings are interned when created rather than when first compared; this can only
  reorder two strings that never appear in the spec or config.
- Internals that do not change results: one 64-bit fingerprint with per-value hash caching, early-exit
  symmetry canonicalisation, copy-on-write permutation, no reference cycles for LET definitions.
