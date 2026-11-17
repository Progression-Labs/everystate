---- MODULE OkCallReturnMP ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm OkCallReturnMP
variables x = 0;
procedure A(n) begin a1: if n > 0 then call A(n - 1) return; else a2: x := x + 1; return; end if; end procedure;
procedure B(n) variables z; begin b1: z := n; b2: call A(z) return; end procedure;
process p \in 1..2
begin
  m1: call B(self);
  m2: skip;
end process;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
