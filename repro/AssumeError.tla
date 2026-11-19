---- MODULE AssumeError ----
EXTENDS TLC, Naturals
VARIABLE x
ASSUME (1 + "a") = 2
Init == x = 0
Next == x' = x
====
