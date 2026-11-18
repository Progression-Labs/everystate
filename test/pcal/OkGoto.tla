---- MODULE OkGoto ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm OkGoto
variables x = 0;
begin
  a: x := x + 1;
     if x < 3 then goto a; elsif x = 3 then goto c; end if;
  b: goto Done;
  c: either goto a; or goto b; or skip; end either;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
