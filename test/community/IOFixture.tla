---------------------------- MODULE IOFixture ----------------------------
(* Differential fixture for the CSV and IOUtils overrides. Expected values were confirmed with the *)
(* Java TLC + CommunityModules overrides. Paths are relative to the working directory              *)
(* (test/community); the environment variable SOME_TEST_ENV_VAR=TLCFTW must be set.                *)
EXTENDS Integers, Sequences, FiniteSets, CSV, IOUtils, TLC, TLCExt
VARIABLE x
Init == x = 0
Next == x' = x

\* a fresh file per run (CSV operators append)
Tmp(name) == "build/io/" \o name \o "-" \o ToString(JavaTime) \o "-" \o ToString(RandomElement(1..1000000)) \o ".csv"

\* ---- CSVWrite / CSVRead / CSVRecords ----
F1 == Tmp("write")
ASSUME AssertEq(CSVRecords(F1), 0)
ASSUME AssertEq(CSVRead(<<"a", "b", "c">>, "#", F1), <<>>)
\* a missing parent directory is not created by the CSV operators; make sure it exists
ASSUME Serialize("", "build/io/.keep", [format |-> "TXT", charset |-> "UTF-8", openOptions |-> <<"WRITE", "CREATE", "TRUNCATE_EXISTING">>]).exitValue \in {0, 1}
ASSUME CSVWrite("%1$s#%2$s#%3$s", <<42, "abc", [a |-> "a", b |-> {1, 2}]>>, F1)
ASSUME AssertEq(CSVRecords(F1), 1)
ASSUME CSVWrite("%3$s#%1$s#%s#%s", <<1, <<2>>, TRUE>>, F1)
ASSUME CSVWrite("%s;%s", <<"x#y", -1>>, F1)
ASSUME AssertEq(CSVRecords(F1), 3)
ASSUME AssertEq(CSVRead(<<"a", "b", "c">>, "#", F1)[1], [a |-> "42", b |-> "\"abc\"", c |-> "[a |-> \"a\", b |-> {1, 2}]"])
ASSUME AssertEq(CSVRead(<<"p", "q">>, "#", F1)[3], [p |-> "\"x", q |-> "y\";-1"])
ASSUME AssertError("The argument of CSVWrite should be a sequence, but instead it is:\n{1}", CSVWrite("%s", {1}, F1))

\* ---- CSVWriteRecord ----
F2 == Tmp("record")
ASSUME CSVWriteRecord([name |-> "Alice", age |-> 30], ",", CSVRecords(F2) = 0, F2)
ASSUME CSVWriteRecord([name |-> "Bob", age |-> 25], ",", CSVRecords(F2) = 0, F2)
ASSUME AssertEq(CSVRecords(F2), 3)
\* (column names are listed in the order TLC first saw them: its CSVRead mixes up columns otherwise)
ASSUME AssertEq(CSVRead(<<"a", "b">>, ",", F2), <<[a |-> "name", b |-> "age"], [a |-> "\"Alice\"", b |-> "30"], [a |-> "\"Bob\"", b |-> "25"]>>)
ASSUME AssertError("The argument of CSVWriteRecord should be a record, but instead it is:\n{1}", CSVWriteRecord({1}, ",", FALSE, F2))

\* ---- a checked-in file: values stay strings, a leading empty field is kept ----
T == CSVRead(<<"name", "age", "city">>, "#", "data/table.csv")
ASSUME AssertEq(CSVRecords("data/table.csv"), 4)
ASSUME AssertEq(Len(T), 4)
ASSUME AssertEq(T[1], [name |-> "name", age |-> "age", city |-> "city"])
ASSUME AssertEq(T[2], [name |-> "Alice", age |-> "30", city |-> "NYC"])
ASSUME AssertEq(T[4], [name |-> "", age |-> "7", city |-> "LA"])
ASSUME AssertEq(CSVRecords("data/DoesNotExist.csv"), 0)
ASSUME AssertEq(CSVRead(<<"a">>, ",", "data/DoesNotExist.csv"), <<>>)

\* ---- IOEnv / atoi ----
ASSUME AssertEq(IOEnv.SOME_TEST_ENV_VAR, "TLCFTW")
ASSUME AssertEq(IOEnv["SOME_TEST_ENV_VAR"], "TLCFTW")
ASSUME DOMAIN IOEnv \subseteq STRING
ASSUME \A var \in DOMAIN IOEnv : IOEnv[var] \in STRING
ASSUME AssertEq(<<atoi("1"), atoi("0"), atoi("-0"), atoi("-17"), atoi("+5"), atoi("007"), atoi("2147483647"), atoi("-2147483648")>>, <<1, 0, 0, -17, 5, 7, 2147483647, -2147483647 - 1>>)
ASSUME AssertError("The argument of atoi should be a string, but instead it is:\n\"\"", atoi(""))
ASSUME AssertError("The argument of atoi should be a string, but instead it is:\n\"foo\"", atoi("foo"))
ASSUME AssertError("The argument of atoi should be a string, but instead it is:\n\"1.5\"", atoi("1.5"))
ASSUME AssertError("The argument of atoi should be a string, but instead it is:\n\"2147483648\"", atoi("2147483648"))
ASSUME AssertError("The argument of atoi should be a string, but instead it is:\n42", atoi(42))
ASSUME AssertEq(zeroPadN(42, 5), "00042")

\* ---- IOSerialize / IODeserialize (TLC's binary value format) ----
Payload == <<"foo", {"bar"}, 42, -7, 1..3, [u |-> 1, y |-> <<TRUE, FALSE>>], [i \in {0, 5} |-> {i}], <<>>, {}, {{1, 2}, {3}}, 70000>>
ASSUME /\ IOSerialize(Payload, "build/io/payload.vos", FALSE)
       /\ AssertEq(IODeserialize("build/io/payload.vos", FALSE), Payload)
ASSUME /\ IOSerialize(TRUE, "build/io/payload.vos", FALSE)
       /\ AssertEq(IODeserialize("build/io/payload.vos", FALSE), TRUE)
ASSUME /\ IOSerialize([i \in 1..40000 |-> i % 7], "build/io/long.vos", FALSE)
       /\ AssertEq(IODeserialize("build/io/long.vos", FALSE), [i \in 1..40000 |-> i % 7])
\* a file written by the Java TLC
ASSUME AssertEq(IODeserialize("data/tlc-written.vos", FALSE), Payload)

\* ---- Serialize / Deserialize with the plain-text format ----
Txt == "build/io/text.txt"
Opts == [format |-> "TXT", charset |-> "UTF-8", openOptions |-> <<"WRITE", "CREATE", "TRUNCATE_EXISTING">>]
ASSUME AssertEq(Serialize("Some text with \" escapes \" \\ and\nlines", Txt, Opts), [exitValue |-> 0, stdout |-> "Finish writing to the file with success!", stderr |-> ""])
ASSUME AssertEq(Deserialize(Txt, [format |-> "TXT", charset |-> "UTF-8"]), [exitValue |-> 0, stdout |-> "Some text with \" escapes \" \\ and\nlines", stderr |-> ""])
ASSUME AssertEq(Serialize(" more", Txt, [Opts EXCEPT !.openOptions = <<"WRITE", "APPEND">>]).exitValue, 0)
ASSUME AssertEq(Deserialize(Txt, [format |-> "TXT", charset |-> "UTF-8"]).stdout, "Some text with \" escapes \" \\ and\nlines more")
ASSUME AssertEq(Serialize("short", Txt, Opts).exitValue, 0)
ASSUME AssertEq(Deserialize(Txt, [format |-> "TXT", charset |-> "UTF-8"]).stdout, "short")
ASSUME LET r == Deserialize("build/io/missing.txt", [format |-> "TXT", charset |-> "UTF-8"])
       IN  r.exitValue = 1 /\ r.stdout = "" /\ r.stderr # ""
ASSUME LET r == Serialize("x", Txt, [Opts EXCEPT !.openOptions = <<"WRITE", "CREATE_NEW">>])
       IN  r.exitValue = 1 /\ r.stdout = "" /\ r.stderr # ""
=============================================================================
