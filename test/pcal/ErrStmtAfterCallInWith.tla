---- MODULE ErrStmtAfterCallInWith ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm ErrStmtAfterCallInWith
variables x = 0;
procedure P() begin p1: return; end procedure;
begin
  a: with i \in {1} do call P(); x := i; end with;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
