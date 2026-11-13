# verify-rs

A Rust port of the safety-checking core of verify.js (the TypeScript reimplementation of the TLC
model checker in this repository). It exists so that the two implementations can be benchmarked head
to head on identical work: same parser, same evaluation semantics, same breadth-first search, same
counting rules, single-threaded.

It was ported from the frozen snapshot `refs/ts-snapshot/src` (lexer, parser, modules, values, eval,
stdlib, cfg, model, checker). Liveness checking is **not** ported.

## Build and run

```
cd rust
cargo build --release
target/release/verify-rs [-json] [-config FILE] [-deadlock] SPEC.tla
```

- `-json` prints exactly one line of JSON with the same fields as `verify -json`:
  `{"status","name","message","generated","distinct","queue","depth","trace":[{"action","state":{var:"value"}}]}`.
  Status strings are the TypeScript ones: `ok`, `invariant`, `invariant-init`, `deadlock`,
  `action-property`, `implied-init`, `assumption`, `error`, `incomplete`, `init-error`, `setup-error`.
- A model with a temporal (liveness) property is not checked at all; the answer is
  `{"status":"unsupported-liveness", ...}` (exit status 2).
- Without `-json` a short human-readable summary (and the error trace) is printed.
- Exit statuses follow the TypeScript CLI (0 ok, 10 assumption, 11 deadlock, 12 invariant,
  13 action property, 150/151 setup errors, 255 other errors).

Dependencies: `std` plus `mimalloc` (global allocator; 3-23 % faster than glibc malloc on the models
tried, because the evaluator allocates many small reference-counted nodes). `[profile.profiling]` in
`Cargo.toml` is a release build with debug info for callgrind.

## Layout

| file | ported from | contents |
|---|---|---|
| `src/intern.rs` | values.ts (`strId`) | identifier interner, and the string interner whose ids reproduce TLC's first-seen string order |
| `src/lexer.rs`, `src/parser.rs`, `src/ast.rs` | lexer.ts, parser.ts | tokens, column-sensitive junction lists, precedence climbing, proofs parsed and skipped |
| `src/modules.rs` | modules.ts | module loading, EXTENDS / INSTANCE (named, parameterised, LOCAL, in LET), name resolution, levels |
| `src/value.rs` | values.ts | values in canonical form, symbolic sets, TLC ordering, equality, fingerprint hashing, printing |
| `src/eval.rs` | eval.ts | evaluator, lazy thunks with state-keyed caching, ENABLED, primes, recursive functions, action enumeration |
| `src/stdlib.rs` | stdlib.ts, part of community.ts | Naturals, Integers, Reals, Sequences, FiniteSets, TLC, TLCExt, Bags, Randomization; native overrides for the hot community operators |
| `src/cfg.rs`, `src/model.rs` | cfg.ts, model.ts | config parsing, constants, substitution, SPECIFICATION splitting, action splitting, properties, symmetry group closure, VIEW |
| `src/checker.rs` | checker.ts | BFS, fingerprint set, counting rules, deadlock, trace reconstruction, POSTCONDITION |
| `repro/` | - | minimal specs for the TypeScript bugs found while porting |
| `lib/*.tla`, `src/bundled.rs` | bundled.ts | the bundled community / TLAPS modules, exported once by `scripts/export-lib.mjs` and embedded with `include_str!` |

`node scripts/export-lib.mjs /path/to/ts/src/bundled.ts` regenerates `lib/` and `src/bundled.rs`.

## How it differs from the TypeScript code (design, not behaviour)

- The AST is a typed enum, leaked once per module so the evaluator holds `&'static Node`.
- Identifiers are interned to integers; contexts are `Rc` linked lists compared by integer name.
- Values are a 16-byte enum; tuples, records, functions and sets are `Rc`-shared and immutable.
  Record field-name vectors and function domains are shared between values with the same shape.
- A state is one `Rc` buffer; the evaluator never copies a state to evaluate it.
- The fingerprint is a single 64-bit hash (folded multiply) stored in an open-addressing table.
- LET definitions are bound without the reference cycles the TypeScript version relies on the
  garbage collector for (a LET cell finds its group through the context walk); values that capture
  their context (lazy filtered sets, closures, lazy functions) are not cached in LET cells.
- Symmetry reduction permutes values copy-on-write (unchanged subtrees are shared).

## Known deviations from the TypeScript implementation

- No liveness (reported as `unsupported-liveness`), no `-tool` output, no `-dump`, no ALIAS, no
  `_POSSIBLE`, no simulation. TLCGet("config"/"stats"/"level"/...) and TLCSet("exit", TRUE) work.
- Only these community operators are native: FiniteSetsExt (FoldSet, Quantify, SumSet, ProductSet,
  Max, Min, kSubset), Functions (Range, IsInjective, AntiFunction, FoldFunction, FoldFunctionOnSet),
  Folds (MapThenFoldSet), SequencesExt (FoldSeq, FoldLeft, FoldRight, FoldLeftDomain, FoldRightDomain,
  ToSet, Reverse, Cons, Front, Last, IsSuffix, Contains, IsPrefix, SetToSeq, SetToSeqs, RemoveFirst),
  Bitwise (And, Or, Xor), IOUtils (IOEnv, atoi), Json (JsonDeserialize, ndJsonDeserialize),
  VectorClocks (CausalOrder). Everything else in those modules runs from its TLA+ definition in
  `lib/`; operators that are not executable from TLA+ (file output, CSV, SVG, process execution,
  serialization) are missing.
- Runtime-created strings (`\o`, ToString) are interned when created instead of when first compared.
  This can only change the relative order of two strings that never appeared in the spec or config.
- Descriptions of lazy sets are built only when an error message needs them. The TypeScript version
  formats them eagerly, which enumerates nested lazy sets (see BENCHMARK.md, "bugs found").
- Deep recursion is limited by a 1 GiB evaluation stack instead of Node's 256 MB.
- Three deliberate behaviour changes, each a bug in the TypeScript version confirmed against TLC
  (BENCHMARK.md, "Bugs found"; repro specs in `repro/`): `UNION` over sets that are not explicit
  stays lazy; a config replacement `Op <- Other` does not apply to `I!Op` inside an instance of the
  same module; lazy-set descriptions are not built eagerly.
- Symmetry canonicalisation stops permuting a state at the first variable that compares larger than
  the best candidate. The canonical state, and therefore every count, is unchanged.
- Enumerated function sets and record sets skip the "already sorted?" check (odometer order over
  normalized components is the normalized order).
