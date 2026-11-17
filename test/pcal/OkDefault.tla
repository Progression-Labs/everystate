---- MODULE OkDefault ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm OkDefault
variables x, y = 0;
procedure P(a) variables b; begin p1: b := a; return; end procedure;
process p \in 1..2 variables z; begin
  a: z := x;
  b: call P(z);
end process;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
