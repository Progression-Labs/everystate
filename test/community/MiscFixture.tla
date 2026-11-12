---------------------------- MODULE MiscFixture ----------------------------
(* Differential fixture for Combinatorics, Bitwise, DyadicRationals, VectorClocks and Statistics. *)
(* Expected values were confirmed with the Java TLC + CommunityModules overrides.                 *)
EXTENDS Integers, Sequences, FiniteSets, Combinatorics, Bitwise, DyadicRationals, VectorClocks, Statistics, TLC, TLCExt
VARIABLE x
Init == x = 0
Next == x' = x

\* ---- Combinatorics ----
ASSUME AssertEq(<<factorial[0], factorial[1], factorial[5], factorial[12]>>, <<1, 1, 120, 479001600>>)
ASSUME AssertEq(<<choose(0, 0), choose(5, 0), choose(5, 5), choose(5, 1), choose(5, 4), choose(10, 3)>>, <<1, 1, 1, 5, 5, 120>>)
ASSUME AssertEq(<<choose(5, 7), choose(3, 5), choose(0, 1), choose(1, 2)>>, <<0, 0, 0, 0>>)
ASSUME AssertEq(choose(30, 15), 155117520)
ASSUME AssertEq(choose(33, 16), 1166803110)
ASSUME \A n \in 0..40 : choose(n, 0) = 1 /\ choose(n, n) = 1 /\ choose(n, 1) = n
ASSUME \A n \in 1..20, k \in 1..20 : k <= n => choose(n, k) = choose(n - 1, k - 1) + choose(n - 1, k)
ASSUME AssertError("The first argument of choose should be a natural number, but instead it is:\n-1", choose(-1, 2))
ASSUME AssertError("The second argument of choose should be a natural number, but instead it is:\n\"a\"", choose(1, "a"))
ASSUME AssertError("Overflow when computing 40choose20", choose(40, 20))

\* ---- Bitwise ----
ASSUME AssertEq(<<5 & 3, 5 | 3, 5 ^^ 3, 0 & 7, 0 | 7, 7 ^^ 7>>, <<1, 7, 6, 0, 7, 0>>)
ASSUME AssertEq(<<1023 & 512, 1024 | 1, 65535 ^^ 255>>, <<512, 1025, 65280>>)
ASSUME AssertEq(<<Not(0), Not(1), Not(5), Not(8), Not(255), Not(256)>>, <<0, 0, 2, 7, 0, 255>>)
ASSUME AssertEq(<<shiftR(8, 1), shiftR(1, 1), shiftR(0, 3), shiftR(7, 0), shiftR(1024, 10), shiftR(1023, 3)>>, <<4, 0, 0, 7, 1, 127>>)
ASSUME \A a, b \in 0..40 : (a & b) + (a | b) = a + b /\ (a ^^ b) = (a | b) - (a & b)

\* ---- DyadicRationals (Reduce is LOCAL; reached through Add and Half) ----
R(n, d) == [num |-> n, den |-> d]
ASSUME AssertEq(Half(One), R(1, 2))
ASSUME AssertEq(Half(Half(One)), R(1, 4))
ASSUME AssertEq(Add(Half(One), Half(One)), One)
ASSUME AssertEq(Add(R(1, 4), R(1, 4)), R(1, 2))
ASSUME AssertEq(Add(R(1, 2), R(1, 4)), R(3, 4))
ASSUME AssertEq(Add(R(3, 4), R(3, 4)), R(3, 2))
ASSUME AssertEq(Add(Zero, R(2, 4)), R(2, 4))
ASSUME AssertEq(Half(R(2, 4)), R(1, 4))
ASSUME AssertEq(Half(R(6, 2)), R(3, 2))
ASSUME AssertEq(PrettyPrint(Add(R(1, 2), R(1, 4))), "3/4")
ASSUME IsDyadicRational(Half(Half(One)))

\* ---- VectorClocks!CausalOrder ----
Clock(l) == l.vc
Node(l) == l.node
Dom(vc) == DOMAIN vc
SmallLog ==
    << [node |-> 1, vc |-> <<1, 0>>],
       [node |-> 2, vc |-> <<0, 1>>],
       [node |-> 2, vc |-> <<1, 2>>],
       [node |-> 1, vc |-> <<2, 0>>] >>
ASSUME AssertEq(CausalOrder(<<>>, Clock, Node, Dom), <<>>)
ASSUME AssertEq(CausalOrder(<<[node |-> 1, vc |-> <<1>>]>>, Clock, Node, Dom), <<[node |-> 1, vc |-> <<1>>]>>)
\* A totally ordered log has exactly one causal order.
Chain == << [node |-> 1, vc |-> <<1, 0>>], [node |-> 2, vc |-> <<1, 1>>], [node |-> 1, vc |-> <<2, 1>>], [node |-> 2, vc |-> <<2, 2>>] >>
ASSUME \A p \in Permutations(1..4) :
          AssertEq(CausalOrder(<<Chain[p[1]], Chain[p[2]], Chain[p[3]], Chain[p[4]]>>, Clock, Node, Dom), Chain)
\* In general the result is some permutation of the log that is a causal order.
ASSUME \A p \in Permutations(1..4) :
          LET log == <<SmallLog[p[1]], SmallLog[p[2]], SmallLog[p[3]], SmallLog[p[4]]>>
              res == CausalOrder(log, Clock, Node, Dom)
          IN  /\ Len(res) = 4
              /\ {res[i] : i \in 1..4} = {SmallLog[i] : i \in 1..4}
              /\ IsCausalOrder(res, Clock)
\* Vector clocks as records keyed by node name.
RecLog == << [node |-> "b", vc |-> [a |-> 1, b |-> 1]], [node |-> "a", vc |-> [a |-> 1, b |-> 0]], [node |-> "a", vc |-> [a |-> 2, b |-> 1]] >>
ASSUME AssertEq(CausalOrder(RecLog, Clock, Node, Dom), <<RecLog[2], RecLog[1], RecLog[3]>>)

\* ---- Statistics!ChiSquare ----
A == [i \in 1..6 |-> i]
ASSUME ChiSquare(A, A, "0.001")
ASSUME ChiSquare(A, A, "0.5")
ASSUME ~ChiSquare([i \in 1..6 |-> 6], A, "0.45")
ASSUME ~ChiSquare([i \in 1..6 |-> 6], A, "0.5")
ASSUME ChiSquare([i \in 1..6 |-> 6], A, "0.2")
ASSUME ChiSquare([i \in 1..6 |-> 6], A, "0.3")
ASSUME ChiSquare([i \in 1..6 |-> 6], A, "0.41")
ASSUME ~ChiSquare([i \in 1..6 |-> 6], A, "0.42")
ASSUME ChiSquare(<<100, 100>>, <<90, 110>>, "0.15")
ASSUME ~ChiSquare(<<100, 100>>, <<90, 110>>, "0.16")
ASSUME ChiSquare(<<10, 10, 10>>, <<9, 11, 10>>, "0.05")
ASSUME ~ChiSquare(<<10, 10, 10>>, <<1, 28, 1>>, "0.05")
ASSUME ~ChiSquare(<<100, 100>>, <<80, 120>>, "0.05")
ASSUME ChiSquare(<<100, 100>>, <<90, 110>>, "0.05")
ASSUME ~ChiSquare(<<100, 100>>, <<90, 110>>, "0.2")
ASSUME ChiSquare([a |-> 50, b |-> 30, c |-> 20], [a |-> 48, b |-> 35, c |-> 17], "0.05")
ASSUME ~ChiSquare([a |-> 50, b |-> 30, c |-> 20], [a |-> 20, b |-> 30, c |-> 50], "0.05")
=============================================================================
