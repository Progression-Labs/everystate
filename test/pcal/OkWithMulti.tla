---- MODULE OkWithMulti ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm OkWithMulti
variables x = 0, y = 0;
process p \in 1..2 variables l = 0; begin
  a: with i \in {1, 2} do
       with j = i * 2 do
         x := i; y := j; l := i + j;
       end with;
     end with;
  b: with k \in {l} do if k > 1 then x := k; else y := k; end if; end with;
end process;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
