---- MODULE OkCallInIf ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm OkCallInIf
variables x = 0;
procedure P(a) begin p1: x := a; return; end procedure;
begin
  a: if x = 0 then call P(1); else call P(2); end if;
  b: either call P(3); or x := 9; or goto a; end either;
  c: with i \in {1} do call P(i); end with;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
