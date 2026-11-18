---- MODULE ErrExtraParen ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm ErrExtraParen
variables x = 0;
begin
  a: x := 1 + 2];
  b: skip;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
