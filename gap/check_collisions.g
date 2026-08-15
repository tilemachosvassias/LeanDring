Read("gap/dring_sieve_standalone.g");
Read("gap/df_trace_corrected_snf.g");

CheckGroup := function(id)
  local ed;
  ed := DFTraceReport(32, id);
  return ed;
end;

Print("Group 3:\n"); CheckGroup(3);
Print("Group 12:\n"); CheckGroup(12);
Print("Group 13:\n"); CheckGroup(13);
Print("Group 14:\n"); CheckGroup(14);
Print("Group 6:\n"); CheckGroup(6);
Print("Group 9:\n"); CheckGroup(9);
Print("Group 33:\n"); CheckGroup(33);
Print("Group 38:\n"); CheckGroup(38);
Print("Group 24:\n"); CheckGroup(24);
Print("Group 26:\n"); CheckGroup(26);
Print("Group 2:\n"); CheckGroup(2);
Print("Group 39:\n"); CheckGroup(39);
Print("Group 29:\n"); CheckGroup(29);
Print("Group 35:\n"); CheckGroup(35);

QUIT;
