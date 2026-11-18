---- MODULE OkLongLabelNames ----
EXTENDS Naturals, Sequences, TLC
(* --algorithm OkLongLabelNames
variables x = 0;
process the_process_with_a_long_name = 1 begin
  a_label_with_a_rather_long_name_0: x := 0;
  a_label_with_a_rather_long_name_1: x := 1;
  a_label_with_a_rather_long_name_2: x := 2;
  a_label_with_a_rather_long_name_3: x := 3;
  a_label_with_a_rather_long_name_4: x := 4;
  a_label_with_a_rather_long_name_5: x := 5;
  a_label_with_a_rather_long_name_6: x := 6;
  a_label_with_a_rather_long_name_7: x := 7;
  a_label_with_a_rather_long_name_8: x := 8;
  a_label_with_a_rather_long_name_9: x := 9;
  a_label_with_a_rather_long_name_10: x := 10;
  a_label_with_a_rather_long_name_11: x := 11;
end process;
process other \in {2, 3} begin
  another_label_with_a_rather_long_name_0: x := 0;
  another_label_with_a_rather_long_name_1: x := 1;
  another_label_with_a_rather_long_name_2: x := 2;
  another_label_with_a_rather_long_name_3: x := 3;
  another_label_with_a_rather_long_name_4: x := 4;
  another_label_with_a_rather_long_name_5: x := 5;
  another_label_with_a_rather_long_name_6: x := 6;
  another_label_with_a_rather_long_name_7: x := 7;
  another_label_with_a_rather_long_name_8: x := 8;
  another_label_with_a_rather_long_name_9: x := 9;
  another_label_with_a_rather_long_name_10: x := 10;
  another_label_with_a_rather_long_name_11: x := 11;
end process;
end algorithm
*)
\* BEGIN TRANSLATION
\* END TRANSLATION
====
