---- MODULE OkOmitPc ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm OkOmitPc
variables x = 0;
begin
  while TRUE do
    either x := x + 1; or x := 0; end either;
  end while;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
