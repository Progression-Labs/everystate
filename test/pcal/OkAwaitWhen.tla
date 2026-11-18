---- MODULE OkAwaitWhen ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm OkAwaitWhen
variables x = 0;
process p = 1 begin
  a: when x = 0; x := 1;
  b: await x = 1 ; x := 2 ;
end process;
process q \in {2} begin
  c: await x = 2; x := 0; goto c;
end process;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
