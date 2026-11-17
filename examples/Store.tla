---- MODULE Store ----
EXTENDS Naturals
Calls == {"a", "b"}                 \* two requests running at once
VARIABLES memory, read, pc

Init == memory = 0 /\ read = [c \in Calls |-> 0] /\ pc = [c \in Calls |-> "load"]

\* store.ts load()
Load(c) == /\ pc[c] = "load"
           /\ read' = [read EXCEPT ![c] = memory]
           /\ pc' = [pc EXCEPT ![c] = "save"] /\ UNCHANGED memory

\* store.ts save(): writes back what it loaded, plus its own update
Save(c) == /\ pc[c] = "save"
           /\ memory' = read[c] + 1
           /\ pc' = [pc EXCEPT ![c] = "done"] /\ UNCHANGED read

Next == \E c \in Calls : Load(c) \/ Save(c)

NoLostUpdates == (\A c \in Calls : pc[c] = "done") => memory = 2
====
