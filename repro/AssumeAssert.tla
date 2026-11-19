---- MODULE AssumeAssert ----
EXTENDS TLC, Naturals
VARIABLE x
ASSUME Assert(FALSE, "boom")
Init == x = 0
Next == x' = x
====
