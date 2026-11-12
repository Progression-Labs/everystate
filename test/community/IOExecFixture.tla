---------------------------- MODULE IOExecFixture ----------------------------
(* Differential fixture for IOUtils!IOExec and friends (needs a Unix-like host that can spawn    *)
(* processes). Expected values were confirmed with the Java TLC + CommunityModules overrides.    *)
(* The environment variable SOME_TEST_ENV_VAR=TLCFTW must be set.                                *)
EXTENDS Integers, Sequences, IOUtils, TLC, TLCExt
VARIABLE x
Init == x = 0
Next == x' = x

R(e, o, s) == [exitValue |-> e, stdout |-> o, stderr |-> s]

\* arguments are passed verbatim: no shell, no quoting
ASSUME AssertEq(IOExec(<<"echo", "'foo' ", " \"bar\"">>), R(0, "'foo'   \"bar\"\n", ""))
ASSUME AssertEq(IOExec(<<"/bin/sh", "-c", "echo out; echo err 1>&2; exit 3">>), R(3, "out\n", "err\n"))
ASSUME AssertEq(IOExec(<<"/bin/sh", "-c", "echo $SOME_TEST_ENV_VAR">>), R(0, "TLCFTW\n", ""))
ASSUME AssertEq(IOEnvExec([SOME_VAR_42 |-> "42"], <<"/bin/sh", "-c", "echo $SOME_VAR_42 $SOME_TEST_ENV_VAR">>), R(0, "42 TLCFTW\n", ""))
ASSUME AssertEq(IOEnvExec([A |-> 1, B |-> {2}], <<"/bin/sh", "-c", "echo $A $B">>), R(0, "1 {2}\n", ""))
ASSUME AssertEq(IOExecTemplate(<<"/bin/sh", "-c", "echo %1$s %2$s %1$s">>, <<"foo", "bar">>), R(0, "foo bar foo\n", ""))
ASSUME AssertEq(IOExecTemplate(<<"echo", "'%s'", "\"%s\"", "100%%">>, <<" foo", "bar ">>), R(0, "' foo' \" foo\" 100%\n", ""))
ASSUME AssertEq(IOExecTemplate(<<"echo", "-n">>, <<>>), R(0, "", ""))
ASSUME AssertEq(IOEnvExecTemplate([V |-> "v"], <<"/bin/sh", "-c", "echo $V %s">>, <<"w">>), R(0, "v w\n", ""))
ASSUME AssertError("The argument of IOExec should be a sequence, but instead it is:\n{1}", IOExec({1}))
ASSUME AssertError("The argument of IOExec should be a sequence, but instead it is:\n1", IOExec(<<"echo", 1>>))
ASSUME AssertError("The argument of IOEnvExec should be a record, but instead it is:\n{1}", IOEnvExec({1}, <<"echo">>))
ASSUME AssertError("The argument of IOExecTemplate should be a sequence, but instead it is:\n{1}", IOExecTemplate(<<"echo">>, {1}))
=============================================================================
