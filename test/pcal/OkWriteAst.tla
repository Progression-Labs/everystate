---- MODULE OkWriteAst ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm OkWriteAst
variables x = 0;
process p \in 1..2 begin a: x := 1; b: if x = 1 then c: skip; end if;
end process;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
