---- MODULE ErrLabelInWith ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm ErrLabelInWith
variables x = 0;
begin
  a: with i \in {1,2} do
      b: x := i;
     end with;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
