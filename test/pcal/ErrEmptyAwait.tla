---- MODULE ErrEmptyAwait ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm ErrEmptyAwait
variables x = 0;
begin
  a: await ;
  x := 1;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
