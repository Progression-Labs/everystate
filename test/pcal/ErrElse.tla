---- MODULE ErrElse ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm ErrElse
variables x = 0;
begin
  a: if x = 1 then x := 2; or x := 3; end if;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
