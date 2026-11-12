---------------------------- MODULE UndirectedGraphsFixture ----------------------------
(* Differential fixture for the UndirectedGraphs overrides (SimplePath, AreConnectedIn,           *)
(* ConnectedComponents). Expected values were confirmed with the Java TLC + CommunityModules.     *)
EXTENDS Integers, Sequences, FiniteSets, UndirectedGraphs, TLC, TLCExt
VARIABLE x
Init == x = 0
Next == x' = x

G(n, e) == [node |-> n, edge |-> e]
Empty == G({}, {})
Line == G({1, 2, 3}, {{1, 2}, {2, 3}})
Two == G({1, 2, 3, 4}, {{1, 2}, {3, 4}})
\* edges that are no 1- or 2-element sets, or that leave the node set, are ignored; {3} is a self-loop
Junk == G({1, 2, 3}, {{1, 2}, {}, {1, 2, 3}, {3}, {3, 9}})

ASSUME AssertEq(SimplePath(Empty), {})
ASSUME AssertEq(SimplePath(G({1, 2}, {})), {<<1>>, <<2>>})
ASSUME AssertEq(SimplePath(Line), {<<1>>, <<2>>, <<3>>, <<1, 2>>, <<2, 1>>, <<2, 3>>, <<3, 2>>, <<1, 2, 3>>, <<3, 2, 1>>})
ASSUME AssertEq(SimplePath(Junk), {<<1>>, <<2>>, <<3>>, <<1, 2>>, <<2, 1>>})
ASSUME Cardinality(SimplePath(G(1..4, {{a, b} : a, b \in 1..4}))) = 64
ASSUME AssertError("The first argument of SimplePath should be a undirected graph record with a node and an edge field, but instead it is:\n42", SimplePath(42))

ASSUME AreConnectedIn(1, 3, Line)
ASSUME AreConnectedIn(3, 1, Line)
ASSUME AreConnectedIn(2, 2, Line)
ASSUME ~AreConnectedIn(1, 3, Two)
ASSUME AreConnectedIn(4, 3, Two)
ASSUME ~AreConnectedIn(1, 9, Line)
ASSUME ~AreConnectedIn(9, 9, Line)
ASSUME ~AreConnectedIn(1, 1, Empty)
ASSUME AreConnectedIn(2, 1, Junk)
ASSUME ~AreConnectedIn(2, 3, Junk)
ASSUME AssertError("The third argument of AreConnectedIn should be a undirected graph record whose edge field is a set, but instead it is:\n[node |-> {1}, edge |-> 1]", AreConnectedIn(1, 1, G({1}, 1)))

ASSUME AssertEq(ConnectedComponents(Empty), {})
ASSUME AssertEq(ConnectedComponents(G({1, 2}, {})), {{1}, {2}})
ASSUME AssertEq(ConnectedComponents(Line), {{1, 2, 3}})
ASSUME AssertEq(ConnectedComponents(Two), {{1, 2}, {3, 4}})
ASSUME AssertEq(ConnectedComponents(Junk), {{1, 2}, {3}})
ASSUME AssertEq(ConnectedComponents(G(1..6, {{1, 6}, {2, 5}, {5, 6}})), {{3}, {4}, {1, 2, 5, 6}})
ASSUME AssertEq(ConnectedComponents(G({"a", "b", "c"}, {{"c", "a"}})), {{"b"}, {"a", "c"}})
ASSUME AssertError("The first argument of ConnectedComponents should be a undirected graph record with a node and an edge field, but instead it is:\n{}", ConnectedComponents({}))
ASSUME IsStronglyConnected(Line)
ASSUME ~IsStronglyConnected(Two)
=============================================================================
