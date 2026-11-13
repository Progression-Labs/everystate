---- MODULE Base ----
EXTENDS Naturals
VARIABLE x
Limit(v) == v < 3
Init == x = 0
Next == x' = IF Limit(x) THEN x + 1 ELSE x
====
