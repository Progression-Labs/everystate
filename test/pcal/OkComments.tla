---- MODULE OkComments ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm OkComments
variables x = 0; (* a comment (* nested *) here *)
begin \* line comment
  a: x := 1; \* trailing (* odd
  (* multi
     line *) b: x := (* inline *) 2;
  c: x := 3 +
       (* in expr *) 4;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
