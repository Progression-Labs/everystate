---- MODULE ErrMissingLabel ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm ErrMissingLabel
variables x = 0;
begin
  a: x := 1;
  x := 2;
  while x < 3 do x := x + 1; end while;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
