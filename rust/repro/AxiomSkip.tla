---- MODULE AxiomSkip ----
EXTENDS Naturals
VARIABLE x
\* TLC evaluates ASSUME / ASSUMPTION but skips AXIOM (SpecProcessor: assumptionIsAxiom).
AXIOM Induction == \A f : f[0] => \A n \in Nat : f[n]
AXIOM FALSE
Init == x = 0
Next == x' = x
====
