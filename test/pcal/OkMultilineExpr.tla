---- MODULE OkMultilineExpr ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm OkMultilineExpr
variables x = 0, f = [i \in 1..3 |-> i];
process p \in 1..3 variables v = 0; begin
  a: v := IF f[self] > 1
            THEN x +
                 v
            ELSE LET y == v
                 IN  y + 1;
  b: f[self] := CASE v = 0 -> 1
                  [] v = 1 -> 2
                  [] OTHER -> v;
  c: x := v
          + 1;
end process;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
