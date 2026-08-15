Print("=== Route 2c: AtlasSubgroup maximal subgroups + help text ===\n");
LoadPackage("atlasrep");

Print("--- Help for RepresentativesPerfectSubgroups ---\n");
h := HELP_GET_MATCHES(HELP_KNOWN_BOOKS[1], "RepresentativesPerfectSubgroups", true);
Print(h, "\n");

Print("--- O7(3) maximal subgroups via AtlasSubgroup ---\n");
G1 := AtlasGroup("O7(3)");
for i in [1..15] do
  M := AtlasSubgroup("O7(3)", i);
  if M = fail then
    Print(i, ": FAIL (no SLP)\n");
  else
    Print(i, ": order = ", Size(M), "\n");
  fi;
od;

Print("--- S6(3) maximal subgroups via AtlasSubgroup ---\n");
for i in [1..11] do
  M := AtlasSubgroup("S6(3)", i);
  if M = fail then
    Print(i, ": FAIL (no SLP)\n");
  else
    Print(i, ": order = ", Size(M), "\n");
  fi;
od;

Print("=== done route2c ===\n");
