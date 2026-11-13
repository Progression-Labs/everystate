# everystate: benchmark and conformance status

Engines compared, one worker each, doing the same breadth-first check of the same model:

- **Rust**: `target/release/everystate` (native);
- **Rust/WASM (Node)**: the same core compiled to `wasm32-unknown-unknown`, run by `node wasm/cli.mjs`;
- **TS/Node**, **TS/Bun**: the TypeScript engine in `../src`;
- **TLC**: Java TLC (`tla2tools.jar`, `-workers 1`).

All engines must report the same generated / distinct state counts (`counts agree` column).

## Result (2026-11-13)

Median wall-clock seconds of 3 runs of the whole process (start-up, parsing and checking).
"Rust vs X" is X's time divided by Rust's time: above 1 means Rust is faster.

| model | distinct | generated | Rust s | Rust/WASM (Node) s | TS/Node s | TS/Bun s | TLC (1 worker) s | Rust states/s | TS/Node states/s | TLC states/s | Rust vs Node | Rust vs Bun | Rust vs TLC | RSS Rust MB | RSS Node MB | counts agree |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|
| TCommit (tiny (startup)) | 34 | 94 | 0.01 | 0.08 | 0.30 | 0.07 | 0.69 | 10,389 | 313 | 136 | 33.1x | 7.2x | 76.5x | 13 | 135 | yes |
| ACP_SB_TLC (sets, quantifiers) | 54944 | 218352 | 0.38 | 0.90 | 1.59 | 1.22 | 1.61 | 568,471 | 137,152 | 135,794 | 4.1x | 3.2x | 4.2x | 28 | 185 | yes |
| StaleShrinkV6Wait2x (records) | 43348 | 111445 | 0.44 | 1.07 | 1.53 | 1.44 | 1.70 | 251,507 | 72,842 | 65,437 | 3.5x | 3.2x | 3.8x | 27 | 190 | yes |
| Barriers (functions (PlusCal)) | 29279 | 104515 | 2.35 | 3.79 | 6.54 | 5.58 | 4.52 | 44,428 | 15,972 | 23,117 | 2.8x | 2.4x | 1.9x | 20 | 179 | yes |
| SimpleRegular (functions (PlusCal)) | 277726 | 1454776 | 4.71 | 9.86 | 11.42 | 9.44 | 6.10 | 309,034 | 127,437 | 238,578 | 2.4x | 2.0x | 1.3x | 178 | 343 | yes |
| Paxos (symmetry, sets of records) | 1207 | 13290 | 3.05 | 4.56 | 15.59 | 11.43 | 1.92 | 4,359 | 853 | 6,910 | 5.1x | 3.8x | 0.6x | 13 | 172 | yes |
| VoteProof (set heavy, quantifiers) | 6962 | 318877 | 7.23 | 13.60 | 16.36 | 15.36 | 13.55 | 44,128 | 19,493 | 23,541 | 2.3x | 2.1x | 1.9x | 15 | 182 | yes |
| MCNanoMedium (VIEW, records, sets) | 530587 | 1120079 | 15.94 | 35.45 | 62.16 | 36.75 | 21.26 | 70,281 | 18,019 | 52,677 | 3.9x | 2.3x | 1.3x | 615 | 1030 | yes |
| MCBakery (functions (PlusCal)) | 655200 | 3403584 | 10.07 | 18.19 | 26.93 | 20.82 | 11.58 | 337,950 | 126,386 | 293,963 | 2.7x | 2.1x | 1.1x | 214 | 429 | yes |
| MCLamportMutex (functions of sequences) | 724274 | 2729079 | 15.92 | 33.74 | 45.06 | 32.48 | 15.35 | 171,400 | 60,569 | 177,801 | 2.8x | 2.0x | 1.0x | 531 | 798 | yes |
| MCbtree (function / set heavy) | 374727 | 2820091 | 15.61 | 30.52 | 53.63 | 41.63 | 35.33 | 180,654 | 52,586 | 79,828 | 3.4x | 2.7x | 2.3x | 193 | 333 | yes |
| GameOfLife (recursive operators, functions) | 65536 | 131072 | 25.71 | 48.05 | 58.14 | 31.95 | 11.85 | 5,098 | 2,254 | 11,059 | 2.3x | 1.2x | 0.5x | 39 | 190 | yes |

The raw per-run times are in `bench-last.log`.

### Machine and versions

- Intel Xeon @ 2.10 GHz, 4 cores (1 thread per core), 15 GB RAM, Linux 6.18 (Firecracker VM).
- rustc 1.97.0, release profile with `lto = "fat"`, `codegen-units = 1`, `panic = "abort"`, mimalloc (native only).
- WebAssembly: `wasm32-unknown-unknown`, same profile, standard allocator, run under Node v22.23.4.
- Node v22.23.4 (`--experimental-strip-types`), Bun 1.4.4, OpenJDK 21.0.12 with `-XX:+UseParallelGC`,
  TLC 2026.11.06 (`tla2tools.jar` in `refs/`).

**Load caveat.** The machine was shared: other jobs used one to two cores during the run (load average
1.4 at the start, 1.0 at the end, on 4 cores), including a few short single-core jobs of the author of
this table. The benchmark itself ran strictly sequentially. Absolute times are 10-30 % slower than in
the first recorded run of these models, taken on a quieter machine; the ratios are what to read. The
three runs per cell mostly agree within 5 %, with outliers up to 40 % (see `bench-last.log`). Peak RSS
was measured in a separate fourth run through `getrusage(RUSAGE_CHILDREN)` (`/usr/bin/time` is not
installed here).

The table was measured with the binary as it was before the last correctness changes (AXIOM is not
evaluated, `\cdot` is opt-in, ALIAS is applied when printing traces, the second precedence-conflict
rule, symbolic `kSubset`). None of them touches the evaluation or search loops, but the table was not
re-measured after them.

### Commands

```
cd rust && cargo build --release && wasm/build.sh
node scripts/bench.mjs --runs 3            # prints the table; progress and raw times go to stderr
```

Per model `bench.mjs` runs, with `cwd = refs/Examples` for the first four:

```
target/release/everystate -json -config <cfg> <spec>
node wasm/cli.mjs -config <cfg> <spec>
node --experimental-strip-types --no-warnings src/cli.ts -json -config <cfg> <spec>
bun src/cli.ts -json -config <cfg> <spec>
# cwd = directory of the spec, JAVA_TOOL_OPTIONS unset:
java -XX:+UseParallelGC -DTLA-Library=refs/tlapm/library:refs/CommunityModules/modules \
     -cp refs/tla2tools.jar tlc2.TLC -workers 1 -metadir <tmp> -config <cfg> <spec>
```

The TypeScript columns are skipped automatically when `src/cli.ts` does not exist.

## Analysis

**Rust against the TypeScript engine.** On the nine models that run for more than two seconds Rust is
2.3x to 5.1x faster than the same algorithm under Node (median 2.8x) and 1.2x to 3.8x faster than
under Bun (median 2.1x). TCommit measures start-up only: about 10 ms for Rust, 70-80 ms for Bun and
for Rust/WASM under Node, 300 ms for the TypeScript engine under Node, 690 ms for TLC. Paxos (5.1x) is
an algorithmic difference: the Rust checker abandons a symmetry permutation at the first variable that
compares larger, the TypeScript one permutes and normalizes the whole state for each of the 143
permutations.

**WebAssembly.** The WASM build takes 1.5x to 2.4x the time of the native build (median 2.0x). It is
faster than the TypeScript engine under Node in every row, and faster than the TypeScript engine under
Bun except on SimpleRegular, MCLamportMutex (both within 5 %) and GameOfLife (1.5x slower). Known
contributors are the standard allocator instead of mimalloc and Node's start-up; the rest was not
broken down.

**Rust against TLC.** One worker each: Rust is ahead by 1.3x to 4.2x on seven of the eleven models
that are not pure start-up, level (1.0x to 1.1x) on MCBakery and MCLamportMutex, behind on Paxos
(0.6x) and GameOfLife (0.5x). TLC is a tree-walking interpreter too, but one with twenty years of
tuning under a JIT.

**Memory.** Rust uses 13 MB for small models against 135-190 MB for Node, and about half to two
thirds of Node's peak on the large ones (214 vs 429 MB for 655 k states, 531 vs 798 MB for 724 k).

**Where the time goes in Rust.** Instruction-count profiles (callgrind) of ACP_SB, Barriers,
SlidingPuzzles, VoucherIssue and GameOfLife are flat. Roughly: a third to a half in the tree walk
itself (`eval`, `eval_app`, `enumerate` and their continuations); 10-20 % in the allocator (context
nodes, thunks, result vectors); 3-17 % in `compare` (set normalization and binary search); 5-9 % in
fingerprinting; 5-6 % in reference-count traffic.

**Performance work done after parity:** a hash cached in every tuple, record, function and set (11 %
fewer instructions on Barriers), reuse of the successor buffer, no typed-model-value check on the fast
path, tracing moved out of the hot `eval` (4 %), early-exit symmetry canonicalisation.
**Not done:** resolving variables and locals to slots instead of name-keyed linked contexts. That is
the obvious next step and, together with one thunk per operator argument, the main structural cost
left. GameOfLife and Paxos, where TLC wins, are the cases that should profit most.

## Conformance status

Real TLC is the arbiter. Everything below was run with the final binary unless noted.

| check | command | result |
|---|---|---|
| tlaplus/Examples manifest, runtime <= 5 s | `EVERYSTATE_CMD=target/release/everystate node scripts/conformance.mjs . --max-runtime 5 --timeout 120` from the Examples checkout | **122 / 122** |
| the same, runtime <= 60 s (incl. liveness) | `... --max-runtime 60 --timeout 600` | 161 / 161 (run before the last correctness changes, not repeated) |
| TLC `test-model` against live `tla2tools.jar` | `EVERYSTATE_CMD=target/release/everystate node scripts/diff-tlc.mjs <test-model>` | **384 / 414**, 4 skipped because TLC itself times out, 26 mismatches (below) |
| pstack statechart corpus through the Java shim | `EVERYSTATE_JAVA_CMD="target/release/everystate java" node scripts/statechart-corpus.mjs <scripts>` | **33 / 33** byte-identical |
| pretty-printer, 337 cases produced by Java | `node --experimental-strip-types --test test/pprint.test.ts` | all pass |
| community-module fixtures and upstream tests | `node test/community.mjs` | 21 / 21 |
| WebAssembly API (the six cases of `test/check.test.ts`) | `node --experimental-strip-types --test test/wasm.test.ts`, `bun test test/wasm.test.ts` | 6 / 6 each |

Notes on these runs:

- `scripts/conformance.mjs` passes `-Dtlc2.tool.impl.Tool.cdot=true` to the engine named by
  `EVERYSTATE_CMD`, as the Examples CI does for TLC on models with action composition: two Examples
  models assert that the property is set.
- `diff-tlc.mjs`: every TLC result comes from a fresh run of `tla2tools.jar` in this session (60 s
  limit, 2 jobs). The first complete run gave 383 with `pcal/Detlefs` timing out on the Rust side; the
  run with the final binary gave 384 with Detlefs passing. Detlefs needs 55-75 s here depending on
  load (60 s measured alone, TLC 38 s), so it sits on the 60 s limit and can go either way.
- The classification regex in `diff-tlc.mjs` was fixed: TLC 2026 prints "Temporal properties A and B
  were violated", which the old pattern did not recognise (five false mismatches).

### The 26 remaining `test-model` mismatches

| reason | count | specs | fixable? |
|---|---:|---|---|
| Result depends on a random seed (TLC's own counts differ from run to run) | 5 | `RandomElement`, `RandomElementXandY`, `RandomSubsetNext`, `SpanTreeRandom`, `Github648` | no |
| TLC bug reproduced by a test: strings are fingerprinted by their low bytes, so two distinct states collide | 3 | `Unicode*Fingerprint` | deliberately not: it would drop reachable states |
| Java class module override | 1 | `UserModuleOverride` | no |
| Labels and the full subexpression-selector syntax (`Op!lab(1)!:!++`, `!@`, `!<<`) | 4 | `suite/test206`, `test209`, `test219`, `test219a` | yes, parser and resolver work |
| Errors only SANY reports: non-Leibniz substitution, level of instantiation arguments, `HIDE` facts | 4 | `suite/test212`, `test213`, `test214`, `test217` | yes, semantic-analysis work |
| Suites of hundreds of assumptions on TLC's value internals (issue 1407): `[{} -> Nat] = {<<>>}`, equality and cardinality of non-enumerable sets, symbolic `kSubset`, fingerprints of symbolic sets | 3 | `EmptySetEqAssume` (about 190 of 443 fail), `ValueSemanticsAssume` (about 70 of 510), `KSubsetAssume` (at least 13 of 228) | yes, one rule at a time |
| TLC normalizes sets lazily, so a set mixing incomparable values is accepted until it is compared | 3 | `NormalizationAssume`, `NormalizationLiveness`, `NormalizationTLCSet` | needs unsorted set values; a design change |
| TLC checks safety-shaped temporal properties (`[](P => []Q)`) while it explores and reports a finite counterexample; everystate checks liveness after the search | 3 | `Github710b` (infinite state space, so everystate does not terminate), `Github710d`, `InitialLivenessEvaluationError` | needs the tableau product built during the search |

Fixed in this round, all confirmed against TLC: `VoteProof/MC` (AXIOM, step reference with
arguments), `cdot/*` (3), `PrintTraceException` (ALIAS), and the five regex false mismatches.

### Output that still differs from TLC 2026 by design

- A liveness violation is reported as "Temporal properties were violated." TLC 2026.11 names the
  violated properties ("Temporal property P was violated."). The banner claims TLC 2.19, whose text
  this is, and the statechart corpus requires exactly the old line (its `tlc.ts` matches it).
- TLC's warnings (symmetry with liveness, record field named like a variable, state-level PROPERTY) and
  the "Trace exploration spec path" line are not printed.

## Where everystate (Rust) follows TLC and the TypeScript engine does not

Each was checked against Java TLC; repro specs are in `repro/`
(`everystate repro/<Name>.tla`, `scripts/tlc.sh $PWD/repro/<Name>.tla <Name>.cfg`).

| repro | TLC and Rust | TypeScript engine |
|---|---|---|
| `LazyCup` | membership in a lazy union of `SUBSET (1..30)` is answered | fixed in `src/` meanwhile |
| `LazyUnion` | `UNION` of a non-enumerable set stays lazy | fixed in `src/` meanwhile |
| `MCBase` + `Base` | `Op <- Replacement` does not replace `Op` inside its own instance | fixed in `src/` meanwhile |
| `PrecConflict` | `SUBSET S \cup T` is a parse error ("Precedence conflict between ops ...") | accepted |
| `PrecConflict2` | `2 * -x` is a parse error: unary minus as right operand of an infix operator of precedence 13 or more | accepted |
| `StepRef` | a step reference with arguments, `<1>1!(v)`, parses | parse error |
| `AxiomSkip` | `AXIOM` is parsed and resolved but never evaluated; only `ASSUME` / `ASSUMPTION` are | evaluated, so the model fails |
| `Alias` | `ALIAS` is applied to every printed trace state: constructor field order, `_format`, `_ALIASEvalError`, the successor state for primed variables | `ALIAS` is ignored |
| (test-model `cdot/*`) | `\cdot` is an error unless `-Dtlc2.tool.impl.Tool.cdot=true` or `-cdot` is given | always on |
| (test-model `KSubsetAssume`, partly) | `kSubset(0, Nat)` is `{{}}`; k-subsets of one infinite base are ordered by k; a `kSubset` with millions of elements stays symbolic | enumerates or fails |
