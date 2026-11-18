---- MODULE OkChecksumBad ----
(* --algorithm A
variables x = 0;
begin a: x := 1;
end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) = "xyz" /\ chksum(tla) = "1")
old == 1
\* END TRANSLATION
====
