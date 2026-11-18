---- MODULE ErrCallGotoArgs ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm ErrCallGotoArgs
variables x = 0;
procedure P(a) begin p1: return; end procedure;
begin
  a: call P() goto a;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
