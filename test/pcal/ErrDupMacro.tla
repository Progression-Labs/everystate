---- MODULE ErrDupMacro ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm ErrDupMacro
variables x = 0;
macro m(a) begin a := 1; end macro;
macro m(a) begin a := 2; end macro;
begin
  a: m(x);
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
