---- MODULE PrecConflict ----
\* SANY: "Precedence conflict between ops SUBSET ... and \cup" (prefix 8-8 against infix 8-8).
EXTENDS Naturals
VARIABLE x
S == {1}
T == {2}
Init == x \in SUBSET S \cup T
Next == x' = x
====
