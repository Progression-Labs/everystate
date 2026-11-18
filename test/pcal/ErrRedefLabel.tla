---- MODULE ErrRedefLabel ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm ErrRedefLabel
variables x = 0;
begin
  a: x := 1;
  a: x := 2;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
