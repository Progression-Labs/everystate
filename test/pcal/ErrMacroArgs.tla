---- MODULE ErrMacroArgs ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm ErrMacroArgs
variables x = 0;
macro m(a, b) begin a := b; end macro;
begin
  l: m(x);
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
