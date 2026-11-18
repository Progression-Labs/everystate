---- MODULE ErrEmptyIfTest ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm ErrEmptyIfTest
variables x = 0;
begin
  a: if then x := 1; end if;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
