---- MODULE Alias ----
EXTENDS Naturals, TLC
VARIABLES x, y
Init == x = 0 /\ y = 0
Next == x < 5 /\ x' = x + 1 /\ y' = y
Inv == x < 2
AliasA == [zz |-> x' , y |-> <<y, 1 \div (2 - x)>>, aa |-> [p |-> x, q |-> {1,2}]]
Alias1 == [only |-> x + y]
Alias2 == x + 1
Alias3 == [_format |-> "<%s:%s>", b |-> x, a |-> y]
====
