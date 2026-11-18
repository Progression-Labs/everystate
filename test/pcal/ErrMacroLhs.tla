---- MODULE ErrMacroLhs ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm ErrMacroLhs
variables x = 0;
macro m(a) begin a := 1; end macro;
begin
  a: m(1 + 2);
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
