---------------------------- MODULE FoldsFixture ----------------------------
(* Differential fixture for FiniteSetsExt, Functions, Folds and BagsExt overrides. Expected values *)
(* were confirmed with the Java TLC + CommunityModules overrides.                                   *)
EXTENDS Integers, Sequences, FiniteSets, FiniteSetsExt, Functions, Folds, Bags, BagsExt, TLC, TLCExt
VARIABLE x
Init == x = 0
Next == x' = x

App(e, acc) == Append(acc, e)

\* ---- FiniteSetsExt!FoldSet: op(element, accumulator), ascending element order ----
ASSUME AssertEq(FoldSet(App, <<>>, {3, 1, 2}), <<1, 2, 3>>)
ASSUME AssertEq(FoldSet(App, <<0>>, {}), <<0>>)
ASSUME AssertEq(FoldSet(LAMBDA e, acc: e - acc, 0, {1, 2, 3}), 2)
ASSUME AssertEq(FoldSet(LAMBDA e, acc: acc - e, 0, 1..4), -10)
ASSUME AssertEq(FoldSet(App, <<>>, {{1, 2}, {3}, {}}), << {}, {3}, {1, 2} >>)
ASSUME AssertEq(FoldSet(+, 0, 1..100), 5050)
ASSUME AssertEq(SumSet({}), 0)
ASSUME AssertEq(SumSet({1, 2, 3}), 6)
ASSUME AssertEq(ProductSet({}), 1)
ASSUME AssertEq(ProductSet({2, 3, 4}), 24)
ASSUME AssertEq(ReduceSet(LAMBDA e, acc: acc - e, 1..3, 10), 4)
ASSUME AssertEq(Max({3, 1, 2}), 3)
ASSUME AssertEq(Min({3, 1, 2}), 1)
ASSUME AssertEq(Max({-3}), -3)

\* ---- Quantify ----
ASSUME AssertEq(Quantify({1, 2, 3}, LAMBDA e: e > 1), 2)
ASSUME AssertEq(Quantify({}, LAMBDA e: TRUE), 0)
ASSUME AssertEq(Quantify(1..10, LAMBDA e: e % 2 = 0), 5)
ASSUME AssertEq(Quantify(SUBSET {1, 2}, LAMBDA s: 1 \in s), 2)
ASSUME AssertError("The first argument of Quantify should be a set, but instead it is:\n42", Quantify(42, LAMBDA e: TRUE))

\* ---- kSubset ----
ASSUME AssertEq(kSubset(2, {1, 2, 3}), {{1, 2}, {1, 3}, {2, 3}})
ASSUME AssertEq(kSubset(0, {1, 2}), {{}})
ASSUME AssertEq(kSubset(0, {}), {{}})
ASSUME AssertEq(kSubset(3, {1, 2}), {})
ASSUME AssertEq(kSubset(-1, {1, 2}), {})
ASSUME AssertEq(kSubset(2, {1, 2}), {{1, 2}})
ASSUME AssertEq(Cardinality(kSubset(2, 1..5)), 10)
ASSUME {1, 2} \in kSubset(2, Nat)
ASSUME {1, 2, 3} \notin kSubset(2, Nat)
ASSUME {1, 4} \notin kSubset(2, 1..3)
ASSUME \A s \in kSubset(3, 1..5) : Cardinality(s) = 3
ASSUME AssertEq(kSubset(2, {"a", "b", "c"}) \cap kSubset(2, {"b", "c", "d"}), {{"b", "c"}})
ASSUME AssertError("The first argument of kSubset should be a natural number, but instead it is:\n\"a\"", kSubset("a", {1}))
ASSUME AssertError("The second argument of kSubset should be a set, but instead it is:\n42", kSubset(1, 42))

\* ---- Functions ----
ASSUME IsInjective(<<>>)
ASSUME IsInjective(<<1, 2, 3>>)
ASSUME ~IsInjective(<<1, 2, 1>>)
ASSUME IsInjective([a |-> 1, b |-> 2])
ASSUME ~IsInjective([a |-> 1, b |-> 1])
ASSUME IsInjective([i \in {0, 2} |-> {i}])
ASSUME ~IsInjective([i \in {0, 2} |-> 7])
ASSUME AssertError("The argument of IsInjective should be a function, but instead it is:\n{}", IsInjective({}))
ASSUME AssertEq(AntiFunction(<<"a", "b", "a">>), [a |-> 1, b |-> 2])
ASSUME AssertEq(AntiFunction([a |-> 1, b |-> 1]), <<"a">>)
ASSUME AssertEq(AntiFunction(<<>>), <<>>)
ASSUME AssertEq(AntiFunction(<<2, 1, 2>>), (1 :> 2 @@ 2 :> 1))
ASSUME AssertEq(AntiFunction([i \in {0, 5} |-> i * 2]), (0 :> 0 @@ 10 :> 5))
ASSUME AssertEq(Range(<<1, 2, 1>>), {1, 2})
ASSUME AssertEq(Range([a |-> 1, b |-> 3]), {1, 3})
\* FoldFunction: op(f[x], accumulator), ascending domain order
ASSUME AssertEq(FoldFunction(App, <<>>, <<3, 1, 2>>), <<3, 1, 2>>)
ASSUME AssertEq(FoldFunction(App, <<>>, [i \in {5, 2, 9} |-> i * 10]), <<20, 50, 90>>)
ASSUME AssertEq(FoldFunction(App, <<>>, [i \in {"a"} |-> 1]), <<1>>)
ASSUME AssertEq(FoldFunction(App, <<7>>, <<>>), <<7>>)
ASSUME AssertEq(FoldFunction(LAMBDA e, acc: e - acc, 0, <<1, 2, 3>>), 2)
ASSUME AssertEq(FoldFunctionOnSet(App, <<>>, <<10, 20, 30, 40>>, {4, 2}), <<20, 40>>)
ASSUME AssertEq(FoldFunctionOnSet(App, <<>>, <<10, 20, 30, 40>>, {}), <<>>)
ASSUME AssertEq(FoldFunctionOnSet(App, <<>>, [i \in Nat |-> i * i], {3, 1, 2}), <<1, 4, 9>>)
ASSUME AssertEq(SumFunction(<<1, 2, 3>>), 6)
ASSUME AssertError("The third argument of FoldFunction should be a function, but instead it is:\nTRUE", FoldFunction(+, 23, TRUE))
ASSUME AssertError("The fourth argument of FoldFunctionOnSet should be a set, but instead it is:\nTRUE", FoldFunctionOnSet(+, 23, <<>>, TRUE))
ASSUME AssertError("The third argument of FoldFunctionOnSet should be a function, but instead it is:\nTRUE", FoldFunctionOnSet(+, 23, TRUE, {}))

\* ---- Folds!MapThenFoldSet: the element chosen first is combined last ----
ASSUME AssertEq(MapThenFoldSet(App, <<>>, LAMBDA e: e * 10, LAMBDA s: Max(s), {1, 2, 3}), <<10, 20, 30>>)
ASSUME AssertEq(MapThenFoldSet(App, <<>>, LAMBDA e: e * 10, LAMBDA s: Min(s), {1, 2, 3}), <<30, 20, 10>>)
ASSUME AssertEq(MapThenFoldSet(App, <<>>, LAMBDA e: e, LAMBDA s: CHOOSE e \in s : TRUE, {1, 2, 3}), <<3, 2, 1>>)
ASSUME AssertEq(MapThenFoldSet(App, <<5>>, LAMBDA e: e, LAMBDA s: Max(s), {}), <<5>>)
ASSUME AssertEq(MapThenFoldSet(LAMBDA a, b: a - b, 0, LAMBDA e: e, LAMBDA s: Max(s), 1..4), 2)
ASSUME AssertEq(MapThenFoldSet(LAMBDA a, b: a - b, 0, LAMBDA e: e, LAMBDA s: Min(s), 1..4), -2)
ASSUME AssertEq(MapThenSumSet(LAMBDA e: e * e, 1..3), 14)

\* ---- BagsExt!FoldBag: op(accumulator, element), once per copy ----
B == [e \in {1, 2} |-> IF e = 1 THEN 3 ELSE 2]
ASSUME AssertEq(FoldBag(LAMBDA acc, e: Append(acc, e), <<>>, B), <<1, 1, 1, 2, 2>>)
ASSUME AssertEq(FoldBag(LAMBDA acc, e: acc - e, 100, B), 93)
ASSUME AssertEq(FoldBag(LAMBDA acc, e: Append(acc, e), <<0>>, EmptyBag), <<0>>)
ASSUME AssertEq(FoldBag(LAMBDA acc, e: Append(acc, e), <<>>, SetToBag({"a"})), <<"a">>)
ASSUME AssertEq(SumBag(B), 7)
ASSUME AssertEq(ProductBag(B), 4)
ASSUME AssertEq(SumBag(EmptyBag), 0)
ASSUME AssertError("Applying FoldBag to the following value,\nwhich is not an element of Nat:\n-1 (in: \"b\":>-1)", ProductBag(("b" :> -1)) = 42)
ASSUME AssertError("Applying FoldBag to the following value,\nwhich is not an element of Nat:\n0 (in: 5:>0)", SumBag((5 :> 0)) = 42)
ASSUME AssertError("The third argument of FoldBag should be a bag, but instead it is:\n42", ProductBag(42) = 42)
=============================================================================
