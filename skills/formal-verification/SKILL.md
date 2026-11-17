---
name: formal-verification
description: "Model-check a design with TLA+ and everystate (no Java needed): write a small model of the code, check every reachable state, and report any counterexample in the code's own words. Use for races, retries, timeouts, locks, leases, queues, state machines, distributed protocols, or when asked to \"model-check this\", \"prove this invariant\", or \"can these steps happen in a bad order?\"."
---

# Formal verification with everystate

A test checks the cases someone thought to write. A model checker checks every order of steps in a
small model of the design. Use it when the question is "can these events happen in an order that
breaks a promise?" and the answer depends on interleavings that tests rarely reach.

It verifies the model, not the code. It does not answer "is this function correct for every input";
use property-based tests or a verifier that runs on the code for that.

## The tool

`everystate` is a TLA+ model checker with TLC's command line, output and exit codes, as one binary.

```sh
npx everystate Spec.tla                       # reads Spec.cfg next to it
npx everystate -config Other.cfg Spec.tla     # another configuration of the same spec
npx everystate -json Spec.tla                 # one JSON object on the last line of stdout
```

| Exit | Meaning |
|---|---|
| 0 | every reachable state checked, nothing found |
| 10 | an `ASSUME` is false |
| 11 | deadlock: a state with no next step |
| 12 | an invariant is violated |
| 13 | a liveness property is violated |
| 150 / 151 | the spec / the `.cfg` does not parse |

The JSON object has `status` (`ok`, `invariant`, `liveness`, `deadlock`, ...), the state counts, and
on a failure `name` and `trace`: the shortest list of `{action, state}` steps that reaches it.

Not supported: simulation mode, multiple workers, the PlusCal translator (write TLA+ directly, or
translate with the TLA+ tools first), TLAPS proofs. A model must be finite and small enough to
enumerate; a few million states is fine.

## How to do it

1. **Pick the promise.** One sentence the code is supposed to keep, where a break harms users: "a
   card is charged at most once", "two workers never hold the same lease". Read the code first and
   take the promise from it; ask the user only what you cannot see.
2. **Model the steps, not the code.** One variable per piece of state that matters, one action per
   step that can interleave with others. What the model treats as one step must be one indivisible
   step in the code: a read followed by a write is two actions unless a lock or transaction makes
   it one. Include the failures: lost messages, timeouts, crashes, retries. Use the code's names,
   and put a comment on each action saying which function it stands for.
3. **Bound it.** Constants in the `.cfg` keep the model finite (2 or 3 workers, 3 retries). Most
   design bugs show up at these sizes.
4. **State the properties.** A type invariant first, since it catches modelling mistakes. Then the
   promise as an `INVARIANT` ("never bad") or a `PROPERTY` ("eventually good", which needs fairness
   in `Spec`).
5. **Run it and read the result.** On a violation, retell the trace as a short story in the code's
   words. Then decide: is this a real bug, or did the model allow a step the code cannot take?
   Check against the code before changing either.
6. **See it fail.** A check that has never failed proves nothing. Break the model the way the code
   could be broken (remove the guard, reorder two steps) and confirm the checker reports it. Keep
   that as a second `.cfg` or note the mutation you tried.
7. **Report honestly.** Say what was checked, at which bounds, under which assumptions, and what
   the model leaves out. A pass covers the model at those bounds, not the whole system.

Do not weaken a property or the model to get a pass, and do not change product code unless asked:
a counterexample on the current code is a finding to report.

## Worked example

[`example/Charge.tla`](example/Charge.tla) models a client that retries a card charge when the
reply is lost. The promise is `ChargedAtMostOnce`. The constant `Idempotent` says whether the
server remembers the request key.

```sh
cd example
npx everystate Charge.tla                           # Idempotent = TRUE: exit 0, 29 distinct states
npx everystate -config ChargeBroken.cfg Charge.tla  # Idempotent = FALSE: exit 12
```

The broken configuration fails with this trace, which reads: the client sends, times out and sends
again; the server handles both requests and charges twice.

```
Error: Invariant ChargedAtMostOnce is violated.
State 1: <Initial predicate>   charges = 0, sent = 0
State 2: <Send ...>            sent = 1, inFlight = 1
State 3: <Send ...>            sent = 2, inFlight = 2
State 4: <Handle ...>          charges = 1
State 5: <Handle ...>          charges = 2
```

(Shortened: the real output prints every variable in every state.)

The same spec checks `EventuallyConfirmed`, a liveness property: under weak fairness on sending,
handling and receiving, the client always learns the charge went through.

## A `.cfg` in brief

```
SPECIFICATION Spec            \* or INIT Init and NEXT Next
CONSTANTS
  MaxSends = 3
  Workers = {w1, w2}          \* model values
INVARIANTS TypeOK ChargedAtMostOnce
PROPERTY EventuallyConfirmed
CHECK_DEADLOCK FALSE          \* when stopping is a legitimate end
SYMMETRY Perms                \* Perms == Permutations(Workers); safety only
```

## Leaving it for the next change

If the check should outlive this task, commit the spec and `.cfg` next to the code and record with
them: the one command that runs it, which files and functions each action stands for, the bounds,
and the commit at which the model was last confirmed against the code. Whoever changes that code
next can then rerun the check, and can see when the model needs another look.
