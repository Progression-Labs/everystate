---- MODULE ErrUndefMacro ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm ErrUndefMacro
variables x = 0;
begin
  a: foo(x);
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
