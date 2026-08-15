# Exact regression of the GAP trace-corrected presentation on the four
# first S-not-subset-R witnesses.
Read("gap/dring_sieve_standalone.g");;
Read("gap/df_trace_corrected_snf.g");;

expected := [
  [7,  [[1,1],[2,12],[4,31],[8,18],[16,7],[32,6]]],
  [8,  [[1,1],[2,10],[4,25],[8,14],[16,7],[32,6]]],
  [9,  [[1,1],[2,15],[4,31],[8,17],[16,14],[32,7]]],
  [10, [[1,1],[2,13],[4,25],[8,13],[16,14],[32,7]]]
];;

for item in expected do
  ed := DFTraceReport(32, item[1]);;
  if Collected(ed) <> item[2] then
    Error("order-32 trace regression failed at id ", item[1]);
  fi;
od;
Print("TRACE_ORDER32_ALL_PASS\n");
QUIT;
