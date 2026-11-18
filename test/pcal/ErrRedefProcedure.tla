---- MODULE ErrRedefProcedure ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm ErrRedefProcedure
variables x = 0;
procedure P() begin p1: return; end procedure;
procedure P() begin p2: return; end procedure;
begin a: call P();
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
