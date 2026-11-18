---- MODULE OkProcSetVars ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm OkProcSetVars
variables g = 0;
process p \in 1..2
  variables a = self, b \in {1, 2}, c = a + b, d \in {a, g};
begin
  l1: a := b + g || b := a;
  l2: c := [i \in 1..2 |-> a][self];
end process;
process q = 3
  variables e \in {1, 2}, f = e;
begin
  l3: e := f;
end process;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
