# everystate

A TLA+ model checker with no Java dependency. It reads ordinary `.tla` specs and TLC `.cfg` files,
checks every reachable state, and reports results in TLC's format.

Two engines live in this repo:

| | Status | Use it for |
|---|---|---|
| TypeScript (`src/`, npm `everystate`) | complete: safety, liveness, symmetry, TLC-compatible output | today |
| Rust (`rust/`, crate `everystate`) | safety checking done, about 2x faster; liveness, full CLI and WASM in progress | becoming the main engine |

## Example

`examples/Counter.tla`:

```tla
---- MODULE Counter ----
EXTENDS Naturals
VARIABLE n

Init == n = 0
Next == n < 5 /\ n' = n + 1
Spec == Init /\ [][Next]_n

TypeOK   == n \in 0..5
NeverFour == n /= 4
====
```

`examples/Counter.cfg`:

```
SPECIFICATION Spec
INVARIANT TypeOK
INVARIANT NeverFour
CHECK_DEADLOCK FALSE
```

```sh
npx everystate examples/Counter.tla
```

```
Error: Invariant NeverFour is violated.
Error: The behavior up to this point is:
State 1: <Initial predicate>
n = 0

State 2: <Next line 6, col 9 to line 6, col 27 of module Counter>
n = 1
...
State 5: <Next line 6, col 9 to line 6, col 27 of module Counter>
n = 4

5 states generated, 5 distinct states found, 0 states left on queue.
```

Exit status is 12, as with TLC.

### For scripts and agents

```sh
npx everystate -json examples/Counter.tla
```

```json
{"status":"invariant","name":"NeverFour","generated":5,"distinct":5,"queue":0,"depth":5,
 "trace":[{"action":null,"state":{"n":"0"}},{"action":"Next","state":{"n":"1"}}, ...]}
```

### From code

```ts
import { check } from 'everystate';

const { result } = check({
  root: 'Counter',
  modules: { Counter: tlaSource },
  config: 'SPECIFICATION Spec\nINVARIANT NeverFour\nCHECK_DEADLOCK FALSE',
});
result.status;   // 'invariant'
result.name;     // 'NeverFour'
result.trace;    // [{ state, action }, ...]
```

### In place of Java TLC

`everystate-java` accepts the `java -cp tla2tools.jar tlc2.TLC ...` command line, so tools that
shell out to TLC can point at it instead of a JVM. The pstack `statechart` script runs unmodified
this way.

## Options

```
everystate [options] SPEC[.tla]
  -config FILE     configuration file (default: SPEC.cfg)
  -deadlock        do not check for deadlock
  -json            one JSON result object
  -tool            TLC's machine-readable message framing
  -dump dot,actionlabels FILE   write the state graph
```

Exit status: 0 success, 10 assumption, 11 deadlock, 12 safety, 13 liveness, 150 parse error,
151 config error. Runs on Node 20+ and Bun.

## How it is checked

Real TLC is the reference. Results for the TypeScript engine (details in
[CONFORMANCE.md](CONFORMANCE.md)):

- [tlaplus/Examples](https://github.com/tlaplus/Examples), models up to 5 s: 122 of 122 match on
  result and exact state counts. Models up to 120 s: 161 of 164, the rest timed out.
- TLC's own `test-model` suite, run side by side with `tla2tools.jar`: 377 of 414 match.
- pstack `statechart` corpus: 33 of 33 outputs byte-identical.

The Rust engine matches the TypeScript one on all 74 non-liveness Examples models up to 5 s.
Speed comparison: [rust/BENCHMARK.md](rust/BENCHMARK.md).

## Not supported

Simulation mode, multiple workers, disk-backed state storage (everything is in memory, so a few
million distinct states is the practical limit), the PlusCal translator (already-translated specs
work), and TLAPS proof checking (proofs are parsed and skipped).

## License

MIT
