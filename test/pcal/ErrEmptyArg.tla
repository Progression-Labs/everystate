---- MODULE ErrEmptyArg ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm ErrEmptyArg
variables x = 0;
procedure P(a) begin p1: return; end procedure;
begin
  a: call P(1, );
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
