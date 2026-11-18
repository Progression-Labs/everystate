---- MODULE OkStringsEsc ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm OkStringsEsc
variables s = "a\"b\\c", t = "x := y; end if";
begin
  a: s := "if then (* *) \\* ";
  b: print <<s, t, "\t\n">>;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
