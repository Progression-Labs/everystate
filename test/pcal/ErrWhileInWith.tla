---- MODULE ErrWhileInWith ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm ErrWhileInWith
variables x = 0;
begin
  a: with i \in {1,2} do
      while x < 3 do x := x + i; end while;
     end with;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
