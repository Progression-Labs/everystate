---- MODULE OkCallReturn ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm OkCallReturn
variables x = 0;
procedure A(n) begin a1: if n > 0 then call A(n - 1) return; else a2: x := x + 1; return; end if; end procedure;
procedure B(n) variables z; begin b1: z := n; b2: call A(z) return; end procedure;
procedure C() begin c1: call B(2) goto c1; end procedure;
begin
  m1: call B(3);
  m2: call C();
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
