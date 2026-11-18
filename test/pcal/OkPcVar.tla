---- MODULE OkPcVar ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm OkPcVar
variables pc_ = 0, stack_ = 1, vars = 2;
procedure P() begin p1: return; end procedure;
begin
  a: pc_ := 1; call P();
  b: stack_ := 2;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
