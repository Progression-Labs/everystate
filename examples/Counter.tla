---- MODULE Counter ----
EXTENDS Naturals
VARIABLE n

Init == n = 0
Next == n < 5 /\ n' = n + 1
Spec == Init /\ [][Next]_n

TypeOK   == n \in 0..5
NeverFour == n /= 4
====
