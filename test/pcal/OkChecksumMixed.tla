---- MODULE OkChecksumMixed ----
(* --algorithm A
variables x = 0;
begin a: x := 1;
end algorithm *)
\* BEGIN TRANSLATION   ( CheckSum(PlusCal) = "abc"  /\  CHKSUM(TLA+) \in  STRING )  trailing
old == 1
\* END TRANSLATION
====
