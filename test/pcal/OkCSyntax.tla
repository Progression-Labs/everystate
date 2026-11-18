---- MODULE OkCSyntax ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm OkCSyntax
{ variables x = 0, q = <<>>;
  define { Even(i) == i % 2 = 0 } ;
  macro inc(v) { v := v + 1 }
  procedure P(a) variables t = 0; { p1: t := a; p2: x := t; return }
  fair process (w \in {1, 2}) variable n = 0; {
    a: while (n < 2) {
         either { inc(n) } or { b: skip; inc(n) } ;
         if (Even(n)) { call P(n) } else { c: q := Append(q, self) }
       } ;
    d: with (v \in {1, 2}; u = v + 1) { x := u } ;
    e: goto a
  }
  process (m = 0) {
    f: await x > 0 ;
    g: call P(7) ;
    h: print x ;
  }
}
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
