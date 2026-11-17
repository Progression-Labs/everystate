---- MODULE ErrCallReturnOutside ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm ErrCallReturnOutside
variables x = 0;
procedure P() begin p1: x := 1; return; end procedure;
process p = 1 begin
  a: call P() return;
end process;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
