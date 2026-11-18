---- MODULE ErrMissingSemi ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm ErrMissingSemi
variables x = 0;
begin
  a: x := 1
  if x = 1 then skip; end if;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
