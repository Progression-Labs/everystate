---- MODULE OkStatements ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm OkStatements
variables x = 0, f = [i \in 1..3 |-> 0], s = <<>>, r = [a |-> 1, b |-> 2];
define
  Sum(g) == g[1] + g[2] + g[3]
  Big == x > 10
end define;
macro bump(v, d) begin v := v + d; end macro;
macro twice(v) begin bump(v, 1); bump(f[2], v); end macro;
begin
  a: f[1] := 1 || f[2] := 2 || x := 5;
  b: with i \in 1..3, j = i + 1 do
       f[i] := j;
       either x := i; or skip; or await i > 1; x := j; end either;
     end with;
  c: if x > 3 then
       x := 0;
       d: f[3] := 3;
     elsif x > 2 then
       s := Append(s, x);
     else
       e: skip;
     end if;
  g: twice(x);
  h: r.a := 3 || r.b := r.a;
  i: while x < 10 /\ ~Big do
       x := x + 1;
       j: if x = 7 then goto Done; end if;
     end while;
     print "done";
  k: assert Sum(f) > 0;
     when x >= 10;
     s := <<x,
            f[1],
            f[2]>>;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
