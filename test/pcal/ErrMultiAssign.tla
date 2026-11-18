---- MODULE ErrMultiAssign ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm ErrMultiAssign
variables x = 0;
begin
  a: x := 1 || x := 2;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
