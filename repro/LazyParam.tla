---- MODULE LazyParam ----
\* TLC forces an operator parameter in "keep lazy" mode when it is applied: Op(F, 1) computes F[1] only,
\* so the division by zero at F[2] is never evaluated.
EXTENDS Integers
VARIABLE x
F == [i \in 1..3 |-> IF i = 2 THEN 1 \div (x - x) ELSE i + x]
Op(f, a) == f[a]
Init == x = 0
Next == x' = x
Inv == Op(F, 1) = 1
====
