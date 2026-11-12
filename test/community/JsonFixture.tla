---------------------------- MODULE JsonFixture ----------------------------
(* Differential fixture for the Json overrides. Expected values were confirmed with the Java TLC + *)
(* CommunityModules overrides. Paths are relative to the working directory (test/community).       *)
EXTENDS Integers, Sequences, FiniteSets, Json, TLC, TLCExt
VARIABLE x
Init == x = 0
Next == x' = x
CONSTANT MV

\* ---- ToJson ----
ASSUME AssertEq(ToJson(1), "1")
ASSUME AssertEq(ToJson(-5), "-5")
ASSUME AssertEq(ToJson(TRUE), "true")
ASSUME AssertEq(ToJson("a"), "\"a\"")
ASSUME AssertEq(ToJson("a\"b\\c\nd\te"), "\"a\\\"b\\\\c\\nd\\te\"")
ASSUME AssertEq(ToJson(MV), "\"MV\"")
ASSUME AssertEq(ToJson(<<>>), "[]")
ASSUME AssertEq(ToJson({}), "[]")
ASSUME AssertEq(ToJson(<<3, 2, 1>>), "[3,2,1]")
ASSUME AssertEq(ToJson({3, 2, 1}), "[1,2,3]")
ASSUME AssertEq(ToJson(1..3), "[1,2,3]")
ASSUME AssertEq(ToJson(1..0), "[]")
ASSUME AssertEq(ToJson({<<>>}), "[[]]")
ASSUME AssertEq(ToJson(SUBSET {2, 1}), "[[],[1],[2],[1,2]]")
ASSUME AssertEq(ToJson({2, 1} \X {"b", "a"}), "[[1,\"a\"],[1,\"b\"],[2,\"a\"],[2,\"b\"]]")
ASSUME AssertEq(ToJson([a |-> 1, b |-> "x"]), "{\"a\":1,\"b\":\"x\"}")
ASSUME AssertEq(ToJson([a |-> {}, b |-> <<>>]), "{\"a\":[],\"b\":[]}")
ASSUME AssertEq(ToJson([a |-> [b |-> [c |-> <<1, {2}>>]]]), "{\"a\":{\"b\":{\"c\":[1,[2]]}}}")
ASSUME AssertEq(ToJson([i \in {3, 2, 1} |-> 2 * i + 1]), "[3,5,7]")
ASSUME AssertEq(ToJson([i \in {0, 1} |-> i]), "{\"0\":0,\"1\":1}")
ASSUME AssertEq(ToJson([i \in {2, 5} |-> TRUE]), "{\"2\":true,\"5\":true}")
ASSUME AssertEq(ToJson([s \in {{1, 2}} |-> 3]), "{\"{1, 2}\":3}")
ASSUME AssertEq(ToJson([t \in {<<1, 2>>} |-> 3]), "{\"<<1, 2>>\":3}")
ASSUME AssertEq(ToJson([b \in {TRUE} |-> "t"]), "{\"TRUE\":\"t\"}")
ASSUME AssertEq(ToJson([a: {2, 1}, b: {"a"}]), "[{\"a\":1,\"b\":\"a\"},{\"a\":2,\"b\":\"a\"}]")
ASSUME AssertEq(ToJson([{1, 0} -> {"a"}]), "[{\"0\":\"a\",\"1\":\"a\"}]")
ASSUME AssertEq(ToJson([{2, 1} -> {"a"}]), "[[\"a\",\"a\"]]")

\* ---- ToJsonArray / ToJsonObject ----
ASSUME AssertEq(ToJsonArray(<<>>), "[]")
ASSUME AssertEq(ToJsonArray({}), "[]")
ASSUME AssertEq(ToJsonArray(<<3, "a", TRUE>>), "[3,\"a\",true]")
ASSUME AssertEq(ToJsonArray({"foo"}), "[\"foo\"]")
ASSUME AssertEq(ToJsonArray([i \in 1..2 |-> {i}]), "[[1],[2]]")
ASSUME AssertEq(ToJsonArray([i \in {0, 1} |-> i]), "{\"0\":0,\"1\":1}")
ASSUME AssertEq(ToJsonObject(<<>>), "{}")
ASSUME AssertEq(ToJsonObject([a |-> 1, b |-> <<2>>]), "{\"a\":1,\"b\":[2]}")
ASSUME AssertEq(ToJsonObject([i \in {0, 1} |-> "v"]), "{\"0\":\"v\",\"1\":\"v\"}")
ASSUME AssertEq(ToJsonObject([n \in 1..2 |-> "a"]), "[\"a\",\"a\"]")

\* ---- JsonSerialize / JsonDeserialize ----
Doc == [a |-> 3, b |-> [c |-> <<4, 5, 6>>], s |-> "q\"uote", t |-> <<TRUE, FALSE>>, e |-> <<>>]
ASSUME /\ JsonSerialize("build/json/doc.json", Doc)
       /\ AssertEq(JsonDeserialize("build/json/doc.json"), Doc)
Seqs == <<[a |-> 3], 2, <<<<1, 2>>, "look">>, <<<<[b |-> [c |-> <<4, 5, 6>>]]>>>>, -7, "s">>
ASSUME /\ JsonSerialize("build/json/seq.json", Seqs)
       /\ AssertEq(JsonDeserialize("build/json/seq.json"), Seqs)
\* sets become arrays, functions with a non-sequence domain become objects with string keys
ASSUME /\ JsonSerialize("build/json/lossy.json", <<{3, 1, 2}, [i \in {0, 1} |-> i], 1..2>>)
       /\ AssertEq(JsonDeserialize("build/json/lossy.json"), << <<1, 2, 3>>, [i \in {"0", "1"} |-> IF i = "0" THEN 0 ELSE 1], <<1, 2>> >>)
ASSUME /\ JsonSerialize("build/json/empty.json", <<>>)
       /\ AssertEq(JsonDeserialize("build/json/empty.json"), <<>>)
\* overwrites, does not append
ASSUME /\ JsonSerialize("build/json/doc.json", <<1>>)
       /\ AssertEq(JsonDeserialize("build/json/doc.json"), <<1>>)

\* a checked-in document: numbers are truncated/wrapped to 32-bit integers, {} and [] are the empty function
In == JsonDeserialize("data/doc.json")
ASSUME AssertEq(DOMAIN In, {"zz", "aa", "mm", "ee", "ll", "zz2"})
ASSUME AssertEq(In.zz, 1)
ASSUME AssertEq(In.aa, <<1, 2, -3, 100, -1294967296>>)
ASSUME AssertEq(In.mm, [yy |-> TRUE, bb |-> "text \"q\" \\ \n A"])
ASSUME AssertEq(In.ee, <<>>)
ASSUME AssertEq(In.ll, <<>>)
ASSUME AssertEq(In.zz2, << <<>>, << <<1>> >>, [k |-> <<FALSE>>] >>)
\* member names are interned in document order, so they print (and serialize) in that order
ASSUME AssertEq(ToJson(In.mm), "{\"yy\":true,\"bb\":\"text \\\"q\\\" \\\\ \\n A\"}")
ASSUME AssertEq(ToJson([k \in DOMAIN In |-> 0]), "{\"zz\":0,\"aa\":0,\"mm\":0,\"ee\":0,\"ll\":0,\"zz2\":0}")

\* ---- ndJsonSerialize / ndJsonDeserialize ----
Lines == <<[a |-> 1, b |-> "a"], <<1, 2, 3>>, 4, "five", TRUE, <<>>, {2, 1}>>
ASSUME /\ ndJsonSerialize("build/json/lines.ndjson", Lines)
       /\ AssertEq(ndJsonDeserialize("build/json/lines.ndjson"), <<[a |-> 1, b |-> "a"], <<1, 2, 3>>, 4, "five", TRUE, <<>>, <<1, 2>>>>)
ASSUME /\ ndJsonSerialize("build/json/none.ndjson", <<>>)
       /\ AssertEq(ndJsonDeserialize("build/json/none.ndjson"), <<>>)
\* blank lines and surrounding white space are ignored
ASSUME AssertEq(ndJsonDeserialize("data/lines.ndjson"), <<[a |-> 1, b |-> "x"], <<1, <<2, 3>>, "s">>, "str", 42, TRUE>>)

ASSUME AssertError("The second argument of JsonSerialize should be a sequence or record, but instead it is:\n{1, 2, 3}", JsonSerialize("build/json/bad.json", {1, 2, 3}))
ASSUME AssertError("The second argument of JsonSerialize should be a sequence or record, but instead it is:\n42", JsonSerialize("build/json/bad.json", 42))
ASSUME AssertError("The second argument of ndJsonSerialize should be a sequence, but instead it is:\n[a |-> 1, b |-> TRUE]", ndJsonSerialize("build/json/bad.json", [a |-> 1, b |-> TRUE]))
ASSUME AssertError("The second argument of ndJsonSerialize should be a sequence, but instead it is:\n42", ndJsonSerialize("build/json/bad.json", 42))
=============================================================================
