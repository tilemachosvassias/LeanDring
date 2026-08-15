Print("=== Route 2b: get groups and maximal subgroups via SLPs ===\n");
LoadPackage("atlasrep");

Print("--- Checking RepresentativesPerfectSubgroups existence ---\n");
Print("IsBoundGlobal RepresentativesPerfectSubgroups: ", IsBoundGlobal("RepresentativesPerfectSubgroups"), "\n");
Print("IsBoundGlobal PerfectResiduum: ", IsBoundGlobal("PerfectResiduum"), "\n");
Print("IsBoundGlobal PerfectIdentification: ", IsBoundGlobal("PerfectIdentification"), "\n");
Print("IsBoundGlobal PerfectGroup: ", IsBoundGlobal("PerfectGroup"), "\n");

Print("--- O7(3): building perm group, degree 351 ---\n");
G1 := AtlasGroup("O7(3)");
Print("G1: ", G1, "\n");
if G1 <> fail then
  Print("Size G1: ", Size(G1), "\n");
fi;

Print("--- S6(3): building perm group, degree 364 ---\n");
G2 := AtlasGroup("S6(3)");
Print("G2: ", G2, "\n");
if G2 <> fail then
  Print("Size G2: ", Size(G2), "\n");
fi;

Print("=== done route2b ===\n");
