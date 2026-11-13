---- MODULE LazyCup ----
EXTENDS Naturals
VARIABLE x
Init == x = {1, 2}
Next == x' = x
Inv == x \in (((SUBSET (1..30)) \cup {{7}}) \cup {{8}})
====
