---- MODULE OkNestedIfLabels ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm OkNestedIfLabels
variables x = 0;
begin
  a: if x = 0 then
       if x = 1 then b: x := 1; c: x := 2; else x := 3; end if;
     else
       either d: x := 4; or x := 5; e: x := 6; end either;
     end if;
  f: while x < 9 do
       x := x + 1;
       g: while x < 5 do x := x + 2; end while;
       h: skip;
     end while;
     x := 0;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
