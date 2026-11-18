---- MODULE ErrReturnInProcess ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm ErrReturnInProcess
variables x = 0;
procedure P() begin p1: x := 1; return; end procedure;
process p = 1 begin
  a: x := 1;
  return;
end process;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
