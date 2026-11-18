---- MODULE OkRename ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm OkRename
variables x = 0, a = 1;
procedure P(x, y)
  variables a = 2;
begin
  a: x := y;
  b: return;
end procedure;
process p \in 1..2
  variables y = 0, b = 1;
begin
  a: y := x;
  b: call P(y, b);
  c: skip;
end process;
process q = 3
  variables y = 5;
begin
  a: y := y + 1;
  P: skip;
end process;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
