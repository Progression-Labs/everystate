# verify-rs vs verify.js (Node, Bun) vs TLC: single-core benchmark

All four engines do the same work: breadth-first safety checking of the same model with one
worker. All four must report the same generated / distinct state counts (`counts agree` column).

## Result (2026-11-13)

> Update after this table was recorded: the lazy-set description bug (TypeScript bug 1 below) is
> fixed in `src/`. MCNanoMedium on TS/Node now takes about 42 s instead of 269 s, so Rust is about
> 3x faster there, in line with the other rows. Bugs 2 and 3 were already fixed in `src/` after the
> snapshot the port was made from. The other rows were not re-measured.

Median wall-clock seconds of 3 runs of the whole process (start-up, parsing and checking).
"Rust vs X" is X's time divided by Rust's time: above 1 means Rust is faster.

| model | distinct | generated | Rust s | TS/Node s | TS/Bun s | TLC (1 worker) s | Rust states/s | TS/Node states/s | TLC states/s | Rust vs Node | Rust vs Bun | Rust vs TLC | RSS Rust MB | RSS Node MB | counts agree |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|
| TCommit (tiny (startup)) | 34 | 94 | 0.01 | 0.32 | 0.06 | 0.55 | 16,967 | 294 | 172 | 57.8x | 10.4x | 98.5x | 13 | 138 | yes |
| ACP_SB_TLC (sets, quantifiers) | 54944 | 218352 | 0.40 | 1.21 | 0.88 | 1.45 | 544,222 | 180,674 | 150,555 | 3.0x | 2.2x | 3.6x | 25 | 194 | yes |
| StaleShrinkV6Wait2x (records) | 43348 | 111445 | 0.38 | 1.21 | 1.10 | 1.46 | 290,727 | 91,941 | 76,424 | 3.2x | 2.9x | 3.8x | 27 | 194 | yes |
| Barriers (functions (PlusCal)) | 29279 | 104515 | 2.08 | 5.27 | 4.30 | 3.69 | 50,319 | 19,844 | 28,317 | 2.5x | 2.1x | 1.8x | 19 | 188 | yes |
| SimpleRegular (functions (PlusCal)) | 277726 | 1454776 | 3.51 | 8.45 | 7.74 | 4.92 | 413,961 | 172,210 | 295,575 | 2.4x | 2.2x | 1.4x | 165 | 340 | yes |
| Paxos (symmetry, sets of records) | 1207 | 13290 | 2.16 | 10.89 | 9.19 | 1.62 | 6,141 | 1,221 | 8,208 | 5.0x | 4.2x | 0.7x | 13 | 182 | yes |
| VoteProof (set heavy, quantifiers) | 6962 | 318877 | 5.67 | 12.50 | 11.74 | 10.46 | 56,202 | 25,514 | 30,472 | 2.2x | 2.1x | 1.8x | 15 | 193 | yes |
| MCNanoMedium (VIEW, records, sets) | 530587 | 1120079 | 13.18 | 268.74 | 258.53 | 17.41 | 84,992 | 4,168 | 64,321 | 20.4x | 19.6x | 1.3x | 550 | 1028 | yes |
| MCBakery (functions (PlusCal)) | 655200 | 3403584 | 8.60 | 18.16 | 16.39 | 9.04 | 395,618 | 187,458 | 376,624 | 2.1x | 1.9x | 1.1x | 207 | 411 | yes |
| MCLamportMutex (functions of sequences) | 724274 | 2729079 | 13.07 | 29.84 | 24.51 | 13.72 | 208,847 | 91,470 | 198,907 | 2.3x | 1.9x | 1.0x | 524 | 851 | yes |
| MCbtree (function / set heavy) | 374727 | 2820091 | 16.36 | 37.77 | 30.48 | 30.30 | 172,364 | 74,666 | 93,075 | 2.3x | 1.9x | 1.9x | 188 | 352 | yes |
| GameOfLife (recursive operators, functions) | 65536 | 131072 | 19.96 | 36.36 | 24.57 | 10.20 | 6,566 | 3,605 | 12,845 | 1.8x | 1.2x | 0.5x | 36 | 196 | yes |

The raw per-run times are in `bench-last.log`.

### Machine and versions

- Intel Xeon @ 2.10 GHz, 4 cores (1 thread per core), 15 GB RAM, Linux 6.18 (Firecracker VM).
- rustc 1.97.0, release profile with `lto = "fat"`, `codegen-units = 1`, `panic = "abort"`, mimalloc (v2).
- Node v22.23.4 (`--experimental-strip-types`), Bun 1.4.4, OpenJDK 21.0.12 with
  `-XX:+UseParallelGC`, TLC 2026.11.06 (`tla2tools.jar` in `refs/`).
- TypeScript implementation: the frozen snapshot `refs/ts-snapshot/src`.

**Load caveat.** The machine was shared: another job was using one to two cores during the run
(load average 2.5 at the start, 1.0 at the end, on 4 cores). The benchmark itself ran strictly
sequentially, so every engine had a free core, but cache and memory-bandwidth contention is not
excluded. The three runs per cell agree within about 5 % (see `bench-last.log`), which is the
resolution of this table. Peak RSS was measured in a separate fourth run; `/usr/bin/time` is not
installed on this machine, so `bench.mjs` fell back to `getrusage(RUSAGE_CHILDREN)` through
`python3` (it uses `/usr/bin/time -v` when that exists).

### Commands

```
cd rust && cargo build --release
node rust/bench.mjs --runs 3            # prints the table; progress and raw times go to stderr
```

Per model `bench.mjs` runs, with `cwd = refs/Examples` for the first three:

```
rust/target/release/verify-rs -json -config <cfg> <spec>
node --experimental-strip-types --no-warnings refs/ts-snapshot/src/cli.ts -json -config <cfg> <spec>
bun refs/ts-snapshot/src/cli.ts -json -config <cfg> <spec>
# cwd = directory of the spec, JAVA_TOOL_OPTIONS unset:
java -XX:+UseParallelGC -DTLA-Library=refs/tlapm/library:refs/CommunityModules/modules \
     -cp refs/tla2tools.jar tlc2.TLC -workers 1 -metadir <tmp> -config <cfg> <spec>
```

The model list is fixed in `bench.mjs`. Two entries changed after a first run: CoffeeCan1000Beans
was dropped because it has a liveness property (verify-rs does not check those), and MCNanoMedium
took its place. MCNanoMedium lies outside the intended 0.1-60 s range for the TypeScript engine
(it takes 4.5 minutes there); it was kept because the reason is instructive (see below).

## Analysis

**Rust against the TypeScript engine.** On nine of the twelve models Rust is 1.8x to 3.2x faster
than the same algorithm under Node and 1.2x to 2.9x faster than under Bun; on the models that run
for more than two seconds the median is 2.3x (Node) and 1.9x (Bun). TCommit measures start-up
only (see below). The other two outliers have specific causes:

- Paxos (5.0x): symmetry reduction. The port permutes values copy-on-write and compares the permuted
  state with the best candidate variable by variable, abandoning a permutation at the first
  variable that is larger. The TypeScript checker permutes and re-normalizes the whole state for
  each of the 143 permutations. This is an algorithmic difference, not a language one; before that
  change Rust took 5.6 s here (1.9x).
- MCNanoMedium (20x): the TypeScript evaluator builds a description string for every lazy set it
  creates (`${fmt(a)} \cup ${fmt(b)}`, `{x \in ${fmt(s)} : ...}`), and formatting an enumerable lazy
  set enumerates it. A CPU profile of the small variant of this model shows 32 % of the time in
  `fmt` itself and about 40 % in formatting overall, for strings that are never printed. The port
  builds the description only when an error message needs it.

**Memory.** Rust uses 13 MB for small models against 135-195 MB for Node, and about half of Node's
peak on the large ones (207 vs 411 MB for 655 k states, 524 vs 851 MB for 724 k states). Both keep
every state as a boxed vector of values plus parent / level / action arrays for traces, so this is
the ratio of a 16-byte value enum with reference counts to V8 heap objects, not a different design.

**Start-up.** On the 34-state TCommit model the whole run takes under 10 ms in Rust, 50-60 ms under
Bun, 320 ms under Node (presumably loading and type-stripping 7.7 k lines of TypeScript, and
starting the worker thread that provides the large stack; this was not broken down), and 550 ms for TLC (JVM start plus SANY). For
anything under roughly 50 k states start-up dominates the TypeScript and Java times, which is why
the first three rows show 3x and more.

**Rust against TLC.** One worker each: Rust is ahead by 1.3x to 1.9x on five of the nine models
that run longer than two seconds, level (1.0x to 1.1x) on MCBakery and MCLamportMutex, behind on
Paxos (0.7x) and clearly behind on GameOfLife (0.5x). TLC is a tree-walking interpreter too, but
one with twenty years of tuning under a JIT; the port is a direct transliteration of the
TypeScript evaluator.

**Where the time goes in Rust.** Instruction-count profiles (callgrind) of ACP_SB, SlidingPuzzles,
VoucherIssue and GameOfLife are flat. Roughly:

- a third to a half in the tree walk itself (`eval`, `eval_app`, `enumerate` and their continuations),
  a large share of it function entry / exit and the `match` dispatch;
- 10-20 % in the allocator (context nodes, thunks, result vectors) with mimalloc; glibc malloc
  took 19 % on SlidingPuzzles;
- 3-17 % in `compare` (set normalization and binary search), depending on how set-heavy the spec is;
- 5-9 % in fingerprint hashing of states;
- 5-6 % in reference-count traffic (`Value::clone` and `drop`).

GameOfLife is the worst case for this design: `Sum(f, S)` recurses through an operator whose
argument thunks are created per call, and the function `sc` is rebuilt for each of the 16 calls per
state because each call gets a fresh thunk. The TypeScript evaluator does exactly the same work,
which is why the gap there is the smallest (1.8x Node, 1.2x Bun), and TLC, which caches
differently, wins.

**Where the time goes in TypeScript.** Only one CPU profile was taken (MCNanoSmall): `fmt` 32 %,
`compare` 14 %, garbage collection 6 %, `eval` 6 %. Apart from the formatting, the hot functions
are the same as in Rust.

**What the JIT does well.** The following is reasoning from the code and the numbers, not from
inspecting generated machine code. The gap is only about 2x, although the Rust code avoids
dynamic typing entirely, and the likely reasons are:

- Allocation of the short-lived objects that dominate this workload (context cells, thunks, small
  arrays) is a pointer bump in the young generation, and most of them die there. Rust pays for
  `malloc` / `free` and for a reference count on every shared value. This is probably the largest
  single advantage of the managed runtimes here.
- The evaluator's `switch` over node kinds, the `typeof` / `instanceof` checks in `compare` and
  `valEq`, and property loads on AST nodes are monomorphic enough for inline caches; numbers,
  booleans and strings need no boxing.
- Closures used as continuations in the action enumerator are cheap to create; Rust goes through
  `&mut dyn FnMut` calls and cannot inline them either.

Bun (JavaScriptCore) is 4-48 % faster than Node on this code (typically 10-25 %) and starts five
times faster.

**What would move Rust further.** The port keeps the TypeScript evaluator's shape so that results
stay identical. The remaining cost is structural: name-keyed linked contexts, a thunk per operator
argument, and reference counting. Resolving locals to slots, compiling the AST to closures or
bytecode, and arena-allocating per-state temporaries would attack the first two items in the list
above. None of that was attempted.

## Correctness of the comparison

- Every row has identical generated and distinct counts in all four engines.
- On the 75 models of tlaplus/Examples with a recorded runtime of at most 5 s that have no liveness
  property, the complete `-json` output of verify-rs (status, violated invariant, counts, queue,
  depth and the full error trace) is byte-identical to the TypeScript engine's.
- Against the upstream manifest (result kind and exact state counts), run from `refs/Examples`
  (one model reads a file relative to that directory):
  - recorded runtime <= 5 s (the required run): 74 pass, 45 unsupported-liveness, 0 other failures, of 119;
  - recorded runtime <= 60 s: 98 pass, 60 unsupported-liveness, 0 other failures, of 158.

## Bugs found in the TypeScript implementation while porting

Each was checked against Java TLC. The port deviates from the TypeScript behaviour in exactly
these places.

1. **Lazy set descriptions enumerate the set.** `x \in (((SUBSET (1..30)) \cup {{7}}) \cup {{8}})`
   with `x = {1, 2}` fails with "Attempted to enumerate SUBSET of a set with 30 elements" because
   building the description of the outer union calls `fmt` on the inner lazy union, which
   enumerates it. TLC: no error. It is also a large performance cost (MCNanoMedium above).
2. **UNION is always eager.** `<<1, 2>> \in UNION { [1..2 -> Int] }` fails with "Attempted to
   enumerate the non-enumerable set Int". TLC keeps a lazy union and answers TRUE. This makes
   `Disruptor/MCDisruptor_MPMC.cfg` fail in TypeScript; it passes in the port (112929 / 422781).
3. **`Op <- Replacement` also replaces Op inside its own instances.** With
   `WiderLimit(v) == LET B == INSTANCE Base IN B!Limit(v) \/ v = 3` and `CONSTANT Limit <- WiderLimit`,
   `B!Limit` resolves to the replacement again and the evaluation overflows the stack. TLC evaluates
   the original body. This makes `CheckpointCoordination/MCCheckpointCoordinationFailure.cfg` end in
   "Stack overflow" in TypeScript; the port reports the expected invariant violation. Module-scoped overrides (`NoHash = [Nano]NoHashVal`) do apply
   to instances, and the port keeps that.
4. **The parser accepts `SUBSET S \cup T`.** SANY rejects it ("Precedence conflict between ops
   SUBSET ... and \union"). The port inherits the leniency.

Repro files for 1 to 3 are in `repro/` (`LazyCup`, `LazyUnion`, `MCBase` + `Base`); run them with
`verify-rs -json repro/<Name>.tla`, the TypeScript CLI and `scripts/tlc.sh`.
