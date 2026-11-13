---- MODULE LazyUnion ----
EXTENDS Integers
VARIABLE x
Init == x = <<1, 2>>
Next == x' = x
Inv == x \in UNION { [1..2 -> Int] }
====
