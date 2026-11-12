---------------------------- MODULE GraphsFixture ----------------------------
(* Differential fixture for the Graphs overrides (SimplePath, AreConnectedIn, IsStronglyConnected). *)
(* Expected values were confirmed with the Java TLC + CommunityModules overrides.                    *)
EXTENDS Integers, Sequences, FiniteSets, Graphs, TLC, TLCExt
VARIABLE x
Init == x = 0
Next == x' = x

G(n, e) == [node |-> n, edge |-> e]
Line == G({1, 2, 3}, {<<1, 2>>, <<2, 3>>})
Cycle == G({1, 2, 3}, {<<1, 2>>, <<2, 3>>, <<3, 1>>})
Loop == G({1}, {<<1, 1>>})
\* edges that are no 2-tuples or that leave the node set are ignored
Junk == G({1, 2, 3}, {<<1, 2>>, <<2>>, <<2, 3, 1>>, <<3, 9>>, <<9, 1>>})

ASSUME AssertEq(SimplePath(EmptyGraph), {})
ASSUME AssertEq(SimplePath(G({1, 2}, {})), {<<1>>, <<2>>})
ASSUME AssertEq(SimplePath(Loop), {<<1>>})
ASSUME AssertEq(SimplePath(Line), {<<1>>, <<2>>, <<3>>, <<1, 2>>, <<2, 3>>, <<1, 2, 3>>})
ASSUME AssertEq(SimplePath(Cycle), {<<1>>, <<2>>, <<3>>, <<1, 2>>, <<2, 3>>, <<3, 1>>, <<1, 2, 3>>, <<2, 3, 1>>, <<3, 1, 2>>})
ASSUME AssertEq(SimplePath(Junk), {<<1>>, <<2>>, <<3>>, <<1, 2>>})
ASSUME AssertEq(SimplePath(G({"a", "b"}, {<<"a", "b">>, <<"b", "a">>})), {<<"a">>, <<"b">>, <<"a", "b">>, <<"b", "a">>})
ASSUME Cardinality(SimplePath(G(1..4, (1..4) \X (1..4)))) = 64
ASSUME AssertError("The first argument of SimplePath should be a graph record with a node and an edge field, but instead it is:\n42", SimplePath(42))
ASSUME AssertError("The first argument of SimplePath should be a graph record whose node field is a set, but instead it is:\n[node |-> 1, edge |-> {}]", SimplePath(G(1, {})))
ASSUME AssertError("The first argument of SimplePath should be a graph record whose edge field is a set, but instead it is:\n[node |-> {}, edge |-> 1]", SimplePath(G({}, 1)))

ASSUME AreConnectedIn(1, 3, Line)
ASSUME ~AreConnectedIn(3, 1, Line)
ASSUME AreConnectedIn(1, 1, Line)
ASSUME AreConnectedIn(3, 1, Cycle)
ASSUME ~AreConnectedIn(1, 4, Line)
ASSUME ~AreConnectedIn(4, 4, Line)
ASSUME ~AreConnectedIn(1, 1, EmptyGraph)
ASSUME ~AreConnectedIn(1, "x", EmptyGraph)
ASSUME AreConnectedIn(1, 2, Junk)
ASSUME ~AreConnectedIn(2, 3, Junk)
ASSUME ~AreConnectedIn(3, 1, Junk)
ASSUME AssertError("The third argument of AreConnectedIn should be a graph record with a node and an edge field, but instead it is:\n<<1, 2>>", AreConnectedIn(1, 2, <<1, 2>>))

ASSUME IsStronglyConnected(EmptyGraph)
ASSUME IsStronglyConnected(G({1}, {}))
ASSUME IsStronglyConnected(Cycle)
ASSUME ~IsStronglyConnected(Line)
ASSUME ~IsStronglyConnected(G({1, 2}, {}))
ASSUME IsStronglyConnected(G({1, 2}, {<<1, 2>>, <<2, 1>>}))
ASSUME ~IsStronglyConnected(G({1, 2, 3}, {<<1, 2>>, <<2, 1>>, <<3, 1>>}))
ASSUME AssertError("The first argument of IsStronglyConnected should be a graph record with a node and an edge field, but instead it is:\n{}", IsStronglyConnected({}))

\* definitions built on top of the overridden operators
ASSUME AssertEq({p \in DOMAIN ConnectionsIn(Line) : ConnectionsIn(Line)[p]}, {<<1, 1>>, <<2, 2>>, <<3, 3>>, <<1, 2>>, <<2, 3>>, <<1, 3>>})
ASSUME HasCycle(Cycle) /\ ~HasCycle(Line)
ASSUME IsDag(Line) /\ ~IsDag(Cycle)
=============================================================================
