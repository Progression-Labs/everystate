---- MODULE ErrCallArgs ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm ErrCallArgs
variables x = 0;
procedure P(a, b) begin p1: x := a + b; return; end procedure;
begin
  a: call P(1);
  b: skip;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
