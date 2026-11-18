---- MODULE ErrExpected ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm ErrExpected
variables x = 0;
begin
  a: if x = 1 then x := 2; end while;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
