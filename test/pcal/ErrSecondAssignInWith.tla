---- MODULE ErrSecondAssignInWith ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm ErrSecondAssignInWith
variables x = 0;
begin
  a: with i \in {1,2} do
      x := i; x := i + 1;
     end with;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
