---- MODULE ErrEmptyWhileTest ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm ErrEmptyWhileTest
variables x = 0;
begin
  a: while do x := 1; end while;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
