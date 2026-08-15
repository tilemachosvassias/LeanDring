Print("=== Route 2e: perfect groups library limits ===\n");
Print("IsBoundGlobal NumberPerfectGroups: ", IsBoundGlobal("NumberPerfectGroups"), "\n");
Print("NumberPerfectLibraryGroups(60): ");
Print(NumberPerfectGroups(60), "\n");
for ord in [60, 120, 360, 1000, 1000000, 2000000, 5000000, 10000000, 13000000] do
  Print("order ", ord, ": NumberPerfectGroups = ");
  n := NumberPerfectGroups(ord);
  Print(n, "\n");
od;
Print("=== done route2e ===\n");
