---- MODULE ErrCommentInString ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm ErrCommentInString
variables x = "(*";
begin
  a: x := "*)";
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
