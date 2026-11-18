---- MODULE ErrParamRedef ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm ErrParamRedef
variables x = 0;
procedure P(a, a) variables a; begin p1: return; end procedure;
begin
  a: call P(1, 2);
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
