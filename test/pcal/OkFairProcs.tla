---- MODULE OkFairProcs ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm OkFairProcs
variables x = 0, sem = 1;
procedure Inc(n)
  variables t = 0;
begin
  i1: t := x;
  i2:+ x := t + n;
  i3:- return;
end procedure;
procedure Dec(n)
begin
  d1: x := x - n;
  d2: call Inc(1);
  d3: return;
end procedure;
fair process p \in 1..2
  variables loc = 0;
begin
  a: await sem = 1; sem := 0;
  b:+ call Inc(self);
  c:- sem := 1;
  d: loc := x;
end process;
fair+ process q = 3
begin
  e: call Dec(1);
  f:+ skip;
  g:- skip;
  h:- skip;
end process;
process r = <<4,
              5>>
begin
  k: x := 0;
end process;
fair process s = <<6,
                   7>>
begin
  m: x := 0;
  n: call Inc(2);
end process;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
