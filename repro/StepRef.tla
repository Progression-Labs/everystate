---- MODULE StepRef ----
\* A step reference with a selector and arguments inside a proof; SANY accepts it.
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = x
THEOREM T == \A v \in Nat : v >= 0
<1>1. \A v \in Nat : v >= 0
  OBVIOUS
<1>2. ASSUME NEW v \in Nat PROVE v >= 0
  BY <1>1!(v)
<1>3. QED
  BY <1>2
====
