# everystate

A TLA+ model checker with no Java dependency, written in Rust. It reads ordinary `.tla` specs and
TLC `.cfg` files, checks every reachable state, and reports results in TLC's format.

```text
> use everystate's formal verification skill to find race conditions in my amazing software

⏺ Write(Store.tla)
  // ... models load() and save() from store.ts

⏺ Bash(npx everystate Store.tla)

  Error: Invariant NoLostUpdates is violated.
  State 2: <Load("a")>   a read 0
  State 3: <Load("b")>   b read 0
  State 4: <Save("a")>   memory = 1
  State 5: <Save("b")>   memory = 1

⏺ Found a race. Two overlapping requests both load before either saves,
  so one update is lost. Fix: make load-and-save atomic.
```

(Condensed. The spec is [`examples/Store.tla`](examples/Store.tla); the skill is
[`skills/formal-verification`](skills/formal-verification/SKILL.md).)

- Safety and liveness checking, fairness, symmetry, `VIEW`, `ALIAS`.
- TLC-compatible text output, exit codes, `-tool` framing and `-dump`.
- The standard and community modules are built in.
- One native binary, or WebAssembly for Node, Bun and workers.

## Install

```sh
npm install -g everystate     # prebuilt binary for Linux, macOS and Windows
cargo install everystate      # or build from source
```

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
everystate examples/Counter.tla
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
everystate -json examples/Counter.tla
```

```json
{"status":"invariant","name":"NeverFour","generated":5,"distinct":5,"queue":0,"depth":5,
 "trace":[{"action":null,"state":{"n":"0"}},{"action":"Next","state":{"n":"1"}}, ...]}
```

### From JavaScript (WebAssembly)

The npm package also exports the engine compiled to WebAssembly:

```ts
import { check } from 'everystate';

const { result } = check({
  root: 'Counter',
  modules: { Counter: tlaSource },
  config: 'SPECIFICATION Spec\nINVARIANT NeverFour\nCHECK_DEADLOCK FALSE',
});
result.status;   // 'invariant'
result.name;     // 'NeverFour'
```

`checkAsync` runs the same check in a worker with a large stack, for deeply recursive specs.
The WebAssembly build is about 2x slower than native and cannot use the file-based community
operators.

## Agent skill

[`skills/formal-verification`](skills/formal-verification/SKILL.md) teaches a coding agent to
model-check a design with everystate: choose the promise, model the steps, run the check, see it
fail, report the counterexample in the code's words. It comes with a worked example
(`example/Charge.tla`). Copy the folder into your agent's skills directory, for example
`.claude/skills/`.

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
151 config error.

## How it is checked

Real TLC is the reference (details in [CONFORMANCE.md](CONFORMANCE.md)):

- [tlaplus/Examples](https://github.com/tlaplus/Examples), models up to 5 s: 122 of 122 match on
  result and exact state counts.
- TLC's own `test-model` suite, run side by side with `tla2tools.jar`: 384 of 414 match.
- pstack `statechart` corpus: 33 of 33 outputs byte-identical.

Faster than single-worker Java TLC on all 12 benchmark models (1.1x to 4.6x, thin on three of
them), with near-instant start-up: [BENCHMARK.md](BENCHMARK.md).

## Not supported

Simulation mode, multiple workers, disk-backed state storage (everything is in memory, so a few
million distinct states is the practical limit), the PlusCal translator (already-translated specs
work), Java module overrides, labels and subexpression selectors, and TLAPS proof checking (proofs
are parsed and skipped).

## Development

```sh
npm run build      # native binary and wasm/everystate.wasm
npm test           # WASM API, pretty-printer and community-module tests
```

Releases use [changesets](.changeset/README.md): add one with `npx changeset` in your pull request,
then merge the "Version Packages" pull request that appears. That bumps `package.json` and
`Cargo.toml`, and `.github/workflows/release.yml` builds the binaries and publishes to npm and
crates.io (trusted publishing, no tokens).

An earlier pure-TypeScript engine is in the git history at commit `e8c67ce` (npm `everystate@0.1.0`).

## License

MIT
