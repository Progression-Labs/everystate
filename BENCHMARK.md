# everystate: benchmark and conformance status

Engines compared, one worker each, doing the same breadth-first check of the same model:

- **Rust**: `target/release/everystate` (native);
- **Rust/WASM (Node)**: the same core compiled to `wasm32-unknown-unknown`, run by `node wasm/cli.mjs`;
- **TLC**: Java TLC (`tla2tools.jar`, `-workers 1`).

All engines must report the same generated / distinct state counts (`counts agree` column).

## Result (2026-11-14, after the performance pass)

Median wall-clock seconds of 3 runs of the whole process (start-up, parsing and checking).
"Rust vs TLC" is TLC's time divided by Rust's: above 1 means everystate is faster. It is faster than
single-worker TLC on every row.

| model | distinct | generated | Rust 0.2.0 s (before) | Rust s (after) | Rust/WASM (Node) s | TLC (1 worker) s | Rust states/s | TLC states/s | Rust vs TLC before | Rust vs TLC after | RSS Rust MB | counts agree |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|
| TCommit (tiny (startup)) | 34 | 94 | 0.01 | 0.01 | 0.08 | 0.63 | 7,626 | 150 | 76.5x | 51.0x | 12 | yes |
| ACP_SB_TLC (sets, quantifiers) | 54944 | 218352 | 0.40 | 0.33 | 0.73 | 1.43 | 658,700 | 152,281 | 4.2x | 4.3x | 28 | yes |
| StaleShrinkV6Wait2x (records) | 43348 | 111445 | 0.40 | 0.33 | 0.83 | 1.54 | 332,936 | 72,371 | 3.8x | 4.6x | 28 | yes |
| Barriers (functions (PlusCal)) | 29279 | 104515 | 2.15 | 2.10 | 3.16 | 3.64 | 49,857 | 28,745 | 1.9x | 1.7x | 20 | yes |
| SimpleRegular (functions (PlusCal)) | 277726 | 1454776 | 4.38 | 3.50 | 7.32 | 4.75 | 415,338 | 306,019 | 1.3x | 1.4x | 178 | yes |
| Paxos (symmetry, sets of records) | 1207 | 13290 | 2.62 | 0.75 | 1.37 | 1.69 | 17,735 | 7,860 | 0.6x | 2.3x | 52 | yes |
| VoteProof (set heavy, quantifiers) | 6962 | 318877 | 6.27 | 5.15 | 9.98 | 11.38 | 61,878 | 28,021 | 1.9x | 2.2x | 15 | yes |
| MCNanoMedium (VIEW, records, sets) | 530587 | 1120079 | 13.87 | 13.60 | 28.12 | 17.86 | 82,337 | 62,703 | 1.3x | 1.3x | 616 | yes |
| MCBakery (functions (PlusCal)) | 655200 | 3403584 | 9.32 | 7.98 | 13.49 | 9.24 | 426,394 | 368,306 | 1.1x | 1.2x | 212 | yes |
| MCLamportMutex (functions of sequences) | 724274 | 2729079 | 14.39 | 11.66 | 25.45 | 13.50 | 234,126 | 202,100 | 1.0x | 1.2x | 531 | yes |
| MCbtree (function / set heavy) | 374727 | 2820091 | 14.74 | 11.92 | 22.10 | 30.93 | 236,557 | 91,168 | 2.3x | 2.6x | 193 | yes |
| GameOfLife (recursive operators, functions) | 65536 | 131072 | 22.55 | 9.09 | 16.21 | 10.30 | 14,413 | 12,729 | 0.5x | 1.1x | 39 | yes |

- "before": the 0.2.0 binary (git HEAD before this pass), one run per model on the same machine on
  the same day. "Rust vs TLC before" is the ratio from the previous version of this table (2026-11-13).
- The raw per-run times are in `bench-last.log`.

### Machine and versions

- Intel Xeon @ 2.10 GHz, 4 cores (1 thread per core), 15 GB RAM, Linux 6.18 (Firecracker VM).
- rustc 1.97.0, release profile with `lto = "fat"`, `codegen-units = 1`, `panic = "abort"`, mimalloc (native only).
- WebAssembly: `wasm32-unknown-unknown`, same profile, standard allocator, run under Node v22.23.4.
- OpenJDK 21.0.12 with `-XX:+UseParallelGC`, TLC 2026.11.06 (`tla2tools.jar` in `refs/`).

**Load caveat.** The machine was shared: the load average was 0.7 at the start of the run (1.3 over
the preceding five minutes) on 4 cores. The benchmark itself ran strictly sequentially. Run-to-run
variation of one cell is up to about 10 % (see `bench-last.log`), so the 1.1x on GameOfLife and the
1.2x on MCBakery and MCLamportMutex are real but not large margins. A second complete run of the same
table half an hour earlier (same code except for the bound on the permutation memo) gave ratios
within 0.1x of these on every row that runs for more than two seconds. Peak RSS was measured in a
separate fourth run through `getrusage(RUSAGE_CHILDREN)`.

### Commands

```
npm run build                            # cargo build --release && wasm/build.sh
node scripts/bench.mjs --runs 3          # prints the table; progress and raw times go to stderr
```

Per model `bench.mjs` runs, with `cwd = refs/Examples` for the first two:

```
target/release/everystate -json -config <cfg> <spec>
node wasm/cli.mjs -config <cfg> <spec>
# cwd = directory of the spec, JAVA_TOOL_OPTIONS unset:
java -XX:+UseParallelGC -DTLA-Library=refs/tlapm/library:refs/CommunityModules/modules \
     -cp refs/tla2tools.jar tlc2.TLC -workers 1 -metadir <tmp> -config <cfg> <spec>
```

## The performance pass

Profiles first (callgrind instruction counts on the `profiling` cargo profile; `perf` is not
available here), then changes. What the profiles said:

- **Paxos** (0.6x before): 95 % of the instructions were in symmetry canonicalisation. Every
  generated state was permuted by all 143 permutations; the cost was permuting and re-sorting the
  set of messages, generic `compare`, a hash-map lookup per model value, and a thread-local access
  per model-value comparison.
- **GameOfLife** (0.5x before): nothing in the checker; all in the evaluator. `Sum(sc, points)`
  passed the function definition `sc` as an operator argument, and `f[x]` then built all of `sc`
  (36 CASE evaluations) to read one point; each application of a lazy function re-evaluated its
  domain expression; the constant `nbrs` set was rebuilt on every call of `score`.
- **MCBakery, MCLamportMutex, SimpleRegular, MCNanoMedium**: flat. 60-90 % is the tree walk
  (`eval`, `eval_app`, `enumerate` and their continuations), about 8 % the allocator, 5-16 % set
  membership and `compare` for the type invariants, 3-7 % fingerprinting. Identifier lookup in the
  linked contexts is only 3-5 %.

One line per optimisation, with what it bought (wall-clock of the named model on this machine, or
callgrind instructions of GameOfLife with N = 3):

| optimisation | effect |
|---|---|
| Symmetry: permutations as dense tables indexed by string id instead of hash maps; model-value comparison without thread-local access | Paxos 2.70 s -> 2.17 s |
| Symmetry: compare the cheapest variables first (by shallow size, which is the same for every state of an orbit), so most permutations are decided on a small function and the message set is never permuted | Paxos 2.17 s -> 1.75 s |
| Symmetry: memo of permuted compound values, keyed by (value hash, permutation) and confirmed by equality, bounded to 131072 entries | Paxos 1.75 s -> 0.64 s (0.7 s with the bound) |
| An operator parameter applied as a function (`Op(f, x) == f[x]`) is forced in keep-lazy mode, as TLC does: one point is computed, not the whole function. Also a correctness fix (`repro/LazyParam`) | GameOfLife 22.5 s -> 14.6 s |
| A lazy function evaluates its domain sets once | GameOfLife 14.6 s -> 13.1 s |
| A closed constant LET definition (no state, no free local name, only pure standard operators) is evaluated once per run; small filtered sets are stored enumerated | GameOfLife 13.1 s -> 11.9 s |
| Leaf fast paths in `eval`: state variable, constant, local bound to a plain value; scalar equality inline; tuples compared element-wise without recursion | GameOfLife 11.9 s -> 10.6 s (565 M -> 518 M instructions at N = 3) |
| Integer `+ - < > <= >=` computed inline instead of through the builtin call | 518 M -> 499 M |
| No memo for lazy functions that are not recursive; `f[x]` reads a state variable `f` directly | 499 M -> 477 M (9.4 s) |
| `CHOOSE x \in S : TRUE` returns the first element without binding | 477 M -> 468 M (8.9 s) |
| `S = {}` on an enumerated set without building an empty set | 468 M -> 447 M (8.7 s) |
| Scalar comparison inline in binary search; `f \in [D -> R]` compares the domain in place instead of building it as a set | SimpleRegular, MCBakery, MCLamportMutex: a few percent, within the noise when measured alone |

The mid rows moved by the generic items only: MCBakery 9.3 s -> 8.0 s, MCLamportMutex 14.4 s -> 11.7 s,
SimpleRegular 4.4 s -> 3.5 s, MCbtree 14.7 s -> 11.9 s, VoteProof 6.3 s -> 5.2 s, MCNanoMedium
13.9 s -> 13.6 s.

Tried without a measurable gain: the closed-LET cache alone did nothing for GameOfLife until the
filtered set was stored enumerated (a lazy filter keeps its context and was excluded from the
cache); interval fast paths in `for_bindings` and in function construction (earlier round).

**Not done.**

- *Slot-resolved identifiers.* The profiles put linked-context lookup at 3-5 %, so it would not
  have closed a row by itself; the leaf fast paths took the cheap part of it.
- *Avoiding a thunk per argument.* Literals and identifiers that are already bound are passed
  without a new thunk; other argument expressions still allocate one.
- *Compiling the AST to closures or bytecode.* This is what would move the flat rows (MCBakery,
  MCLamportMutex, MCNanoMedium, where the margin over TLC is 1.2-1.3x) substantially: per evaluated
  node the tree walk still costs 200-300 instructions including dispatch, result moves and
  reference counts.
- *Incremental fingerprints.* Compound values cache their hash, so an unchanged variable costs one
  addition per state already; fingerprinting is 3-7 %.

### Parallel BFS (`-workers N`): design note, not implemented

Values are `Rc`-based with `Cell` hash caches, the evaluator is a per-thread singleton, the AST
carries `Cell` / `RefCell` caches (resolution, levels, constant values, thunks), and string ids are
interned per thread in first-seen order, which also defines TLC's string ordering. Making all of
that `Arc` / atomic would slow the single-worker path (an estimate, not measured: 10-20 %) and is not
advisable. A sound design keeps the evaluator single-threaded and shares nothing but bytes:

1. One evaluator (interner, AST, caches) per worker thread, each parsing the spec itself.
2. A global string table (read-mostly lock) so that string ids, and with them value order and
   fingerprints, are the same in every worker; today fingerprints hash thread-local ids.
3. States cross threads in a serialized canonical form: a worker takes a serialized state from the
   shared queue, rebuilds its values locally, enumerates successors, fingerprints them, inserts into
   a sharded concurrent fingerprint set and pushes the new ones serialized.
4. Level-synchronized BFS (process one level in parallel, then a barrier), so that depth, the
   shortest counterexample and the state counts stay deterministic; parent pointers by fingerprint
   and trace reconstruction by re-execution, as TLC does.
5. Liveness needs the edge lists: per-worker buffers merged at the barrier. `TLCGet` / `TLCSet`
   registers, `Print` order and random choices become per-worker, as in TLC.
6. WebAssembly stays single-worker.

Cost: the serialization format, the global interner, id-independent fingerprints, the sharded set
and the driver; the evaluator is untouched. Scaling should be close to linear on evaluator-bound
models, less the (de)serialization per state.

## Conformance status

Real TLC is the arbiter. Everything below was run with the final binary unless noted.

| check | command | result |
|---|---|---|
| tlaplus/Examples manifest, runtime <= 5 s | `EVERYSTATE_CMD=target/release/everystate node scripts/conformance.mjs . --max-runtime 5 --timeout 120` from the Examples checkout | **122 / 122** |
| the same, runtime <= 60 s (incl. liveness) | `... --max-runtime 60 --timeout 600` | 161 / 161 (run before the last change of the performance pass, the bound on the permutation memo) |
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
| `LazyParam` | an operator parameter applied as a function is forced only at the point used | fixed in `src/` meanwhile |
| `MCBase` + `Base` | `Op <- Replacement` does not replace `Op` inside its own instance | fixed in `src/` meanwhile |
| `PrecConflict` | `SUBSET S \cup T` is a parse error ("Precedence conflict between ops ...") | accepted |
| `PrecConflict2` | `2 * -x` is a parse error: unary minus as right operand of an infix operator of precedence 13 or more | accepted |
| `StepRef` | a step reference with arguments, `<1>1!(v)`, parses | parse error |
| `AxiomSkip` | `AXIOM` is parsed and resolved but never evaluated; only `ASSUME` / `ASSUMPTION` are | evaluated, so the model fails |
| `Alias` | `ALIAS` is applied to every printed trace state: constructor field order, `_format`, `_ALIASEvalError`, the successor state for primed variables | `ALIAS` is ignored |
| (test-model `cdot/*`) | `\cdot` is an error unless `-Dtlc2.tool.impl.Tool.cdot=true` or `-cdot` is given | always on |
| (test-model `KSubsetAssume`, partly) | `kSubset(0, Nat)` is `{{}}`; k-subsets of one infinite base are ordered by k; a `kSubset` with millions of elements stays symbolic | enumerates or fails |
