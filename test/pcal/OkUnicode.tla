---- MODULE OkUnicode ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm OkUnicode
variables x = 0, y ∈ {1, 2};
begin
  a: x ≔ y ‖ y ≔ x;
  b: if ∀ i ∈ {1, 2} : i ≥ 1 then x ≔ 2; end if;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
