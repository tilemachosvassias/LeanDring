Print("=== Probe missing maxes SLPs ===\n");
LoadPackage("atlasrep");
Print("--- O7(3) AtlasProgramInfo maxes ---\n");
for i in [1..15] do
  info := AtlasProgramInfo("O7(3)", "maxes", i);
  Print(i, ": ", info, "\n");
od;
Print("--- S6(3) AtlasProgramInfo maxes ---\n");
for i in [1..11] do
  info := AtlasProgramInfo("S6(3)", "maxes", i);
  Print(i, ": ", info, "\n");
od;
Print("=== done ===\n");
