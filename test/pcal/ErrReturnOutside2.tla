---- MODULE ErrReturnOutside2 ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm ErrReturnOutside2
variables x = 0;
procedure P() begin p1: x := 1; return; end procedure;
begin
  a: x := 1;
  return;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
