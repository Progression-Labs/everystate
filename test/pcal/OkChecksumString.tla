---- MODULE OkChecksumString ----
(* --algorithm A
variables x = 0;
begin a: x := 1;
end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) \in STRING /\ chksum(tla) \in STRING)
old == 1
\* END TRANSLATION
====
