---- MODULE Base ----
(* Fixture of test/workers.mjs: one module, many next-state relations, each exercising a feature
   that the parallel search (-workers N) has to treat exactly as the one-worker search does. *)
EXTENDS Naturals, TLC, Sequences, FiniteSets
CONSTANTS N, P
VARIABLES x, y, s, log
vars == <<x, y, s, log>>
Init == x = 0 /\ y \in 0..2 /\ s = {} /\ log = <<>>
Inc == /\ x < N /\ x' = x + 1 /\ y' \in {y, (y + 1) % 5} /\ s' = s \cup {x % 7} /\ UNCHANGED log
Flip(p) == /\ y' = (y * 3 + x) % 11 /\ x' = (x + 2) % (N + 1) /\ s' = s \ {y % 7}
           /\ log' = IF Len(log) < 2 THEN Append(log, p) ELSE log
Next == Inc \/ \E p \in P : Flip(p)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
TypeOK == x \in 0..N /\ y \in 0..10 /\ s \subseteq 0..6
Bad == ~(x = N /\ y = 7 /\ Len(log) = 2)
Cons == Cardinality(s) < 5
ACons == x' # 13
View == <<x, y, s>>
Al == [x |-> x, yy |-> y, n |-> Cardinality(s), nx |-> x']
Perms == Permutations(P)
ManyInit == x \in 0..N /\ y \in 0..10 /\ s \in SUBSET (0..3) /\ log = <<>>
BadInit == ManyInit
InitInv == ~(x = 7 /\ y = 3 /\ s = {1, 2})
PrintNext == Next /\ PrintT(<<"step", x, y>>)
SetNext == Next /\ TLCSet(1, x)
RegNext == Next /\ TLCGet(1) >= 0
LevelNext == Next /\ TLCGet("level") < 100
LevelInv == TLCGet("level") < 12
StatNext == Next /\ TLCGet("distinct") >= 0
RandNext == Next /\ RandomElement(1..3) > 0
StrNext == /\ x < N /\ x' = x + 1 /\ y' \in {y, (y + 1) % 5} /\ s' = s /\ log' = <<ToString(x * y)>>
SubNext == /\ x < 3 /\ x' = x + 1 /\ y' = y /\ s' = SUBSET (0..x) /\ log' = log
FiltNext == /\ x < 3 /\ x' = x + 1 /\ y' = y /\ s' = {v \in SUBSET (0..x) : Cardinality(v) < 2} /\ log' = log
DeadNext == x < 6 /\ Inc
ErrNext == Inc /\ (x = 9 /\ y = 4 => Assert(FALSE, "boom"))
PartNext == /\ x < N /\ x' = x + 1 /\ y' \in {y, (y + 1) % 5} /\ s' = s /\ (x < 8 => log' = log)
Rare == x = 5 /\ y = 3 /\ s = {0, 1, 2, 3, 4} /\ log = <<>>
RarePrintNext == Next /\ (Rare => PrintT(<<"rare", x, y>>))
RareStrNext == Next \/ (Rare /\ x' = x /\ y' = y /\ s' = s /\ log' = <<ToString(x + 100)>>)
ActProp == [][x' # 11 \/ y' # 4]_vars
Live == <>(x = N /\ y = 9)
ASSUME TLCSet(1, 0)
====
