---- MODULE ErrRedefProcess ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm ErrRedefProcess
variables x = 0;
process p = 1 begin a: x := 1; end process;
process p = 2 begin b: x := 2; end process;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
