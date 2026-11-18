---- MODULE OkParens ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm OkParens
variables x = 1, b = x = 1, s = {1} \cup {2}, t = <<1>> \o <<2>>, u = 1 \in {1}, v = "a=b", w = [a |-> 1];
begin
  a: b := x # 1;
  c: s := s \ {1};
  d: u := x < 2 /\ b;
  e: w := [a |-> 2];
  f: t := << x = 1 >>;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
