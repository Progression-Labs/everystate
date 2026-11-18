---- MODULE ErrUnmatchedParen ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm ErrUnmatchedParen
variables x = 0;
begin
  a: x := (1 + 2;
  b: skip;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
