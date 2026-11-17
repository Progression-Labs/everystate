---- MODULE ErrDefineUnclosed ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm ErrDefineUnclosed
variables x = 0;
define F(a) == a + 1
begin
  a: x := F(1);
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
