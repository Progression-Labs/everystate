---- MODULE OkMacroSubst ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm OkMacroSubst
variables f = [i \in 1..2 |-> [a |-> 0]], x = 0;
macro set(v, e) begin v := e; x := v; end macro;
macro both(v, w) begin set(v, 1) ; if w > 0 then set(w, v + (w)) end if end macro;
begin
  a: set(f[1].a, x + 1);
  b: both(f[2].a, x);
  c: set(x, 3);
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
