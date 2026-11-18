---- MODULE ErrReturnOutside ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm ErrReturnOutside
variables x = 0;
begin
  a: x := 1;
  return;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
