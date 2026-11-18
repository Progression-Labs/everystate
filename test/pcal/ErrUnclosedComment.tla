---- MODULE ErrUnclosedComment ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm ErrUnclosedComment
variables x = 0;
begin
  a: x := 1; (* never closed
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
