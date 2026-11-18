---- MODULE OkNoLabels ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm OkNoLabels
variables x = 0, y \in {1, 2};
begin
  x := y;
  y := 3;
  if x = 1 then x := 2; else y := 4; end if;
  print <<x, y>>;
  assert x > 0;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
