---- MODULE OkManyProcs ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm OkManyProcs
variables x = 0;
procedure Proc_with_long_name_0() begin pl0: x := 0; return; end procedure;
procedure Proc_with_long_name_1() begin pl1: x := 1; return; end procedure;
procedure Proc_with_long_name_2() begin pl2: x := 2; return; end procedure;
procedure Proc_with_long_name_3() begin pl3: x := 3; return; end procedure;
procedure Proc_with_long_name_4() begin pl4: x := 4; return; end procedure;
procedure Proc_with_long_name_5() begin pl5: x := 5; return; end procedure;
procedure Proc_with_long_name_6() begin pl6: x := 6; return; end procedure;
procedure Proc_with_long_name_7() begin pl7: x := 7; return; end procedure;
process proc_with_long_name_0 \in {0} begin ql0: call Proc_with_long_name_0(); rl0: skip; sl0: skip; tl0: skip; ul0: skip; vl0: skip; wl0: skip; end process;
process proc_with_long_name_1 \in {1} begin ql1: call Proc_with_long_name_1(); rl1: skip; sl1: skip; tl1: skip; ul1: skip; vl1: skip; wl1: skip; end process;
process proc_with_long_name_2 \in {2} begin ql2: call Proc_with_long_name_2(); rl2: skip; sl2: skip; tl2: skip; ul2: skip; vl2: skip; wl2: skip; end process;
process proc_with_long_name_3 \in {3} begin ql3: call Proc_with_long_name_3(); rl3: skip; sl3: skip; tl3: skip; ul3: skip; vl3: skip; wl3: skip; end process;
process proc_with_long_name_4 \in {4} begin ql4: call Proc_with_long_name_4(); rl4: skip; sl4: skip; tl4: skip; ul4: skip; vl4: skip; wl4: skip; end process;
process proc_with_long_name_5 \in {5} begin ql5: call Proc_with_long_name_5(); rl5: skip; sl5: skip; tl5: skip; ul5: skip; vl5: skip; wl5: skip; end process;
process proc_with_long_name_6 \in {6} begin ql6: call Proc_with_long_name_6(); rl6: skip; sl6: skip; tl6: skip; ul6: skip; vl6: skip; wl6: skip; end process;
process proc_with_long_name_7 \in {7} begin ql7: call Proc_with_long_name_7(); rl7: skip; sl7: skip; tl7: skip; ul7: skip; vl7: skip; wl7: skip; end process;
fair process single_0 = 100 begin zl0: x := 0; end process;
fair process single_1 = 101 begin zl1: x := 1; end process;
fair process single_2 = 102 begin zl2: x := 2; end process;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
