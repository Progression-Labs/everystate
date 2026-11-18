---- MODULE OkFairAlgMP ----
EXTENDS Naturals, Sequences, TLC
(* --fair algorithm OkFairAlgMP
variables x = 0;
process p \in 1..2 begin
  a: while x < 3 do x := x + 1; end while;
end process;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
