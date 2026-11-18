---- MODULE ErrNoEndTranslation ----
(* --algorithm A
variables x = 0;
begin a: x := 1;
end algorithm *)
\* BEGIN TRANSLATION
foo == 1
====
