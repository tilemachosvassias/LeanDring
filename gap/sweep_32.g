Read("gap/dring_sieve_standalone.g");
Read("gap/df_trace_corrected_snf.g");

Print("Starting sweep of order 32...\n");
for id in [1..51] do
  G := SmallGroup(32, id);
  mat := DFTraceCorrectedMatrix(G);
  F := Length(mat);
  Print("Group 32,", id, " |F| = ", F, "\n");
od;
Print("Sweep complete.\n");
QUIT;
