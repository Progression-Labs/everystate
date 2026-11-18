---- MODULE ErrLabelInMacro ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm ErrLabelInMacro
variables x = 0;
macro m(a) begin l: a := 1; end macro;
begin
  a: m(x);
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
