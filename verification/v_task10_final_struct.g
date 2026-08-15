Print("=== Final structure descriptions ===\n");
LoadPackage("atlasrep");

Print("--- S6(3) order-466560 hit (from maximal #1) ---\n");
G2 := AtlasGroup("S6(3)");
M1 := AtlasSubgroup("S6(3)", 1);
R1 := PerfectResiduum(M1);
reps1 := RepresentativesPerfectSubgroups(R1);
h466560 := Filtered(reps1, u -> Size(u) = 466560);
Print("count: ", Length(h466560), "\n");
for u in h466560 do
  N := Normalizer(G2, u);
  Print("order=", Size(u), " |N|=", Size(N), " selfnorm=", Size(N)=Size(u),
        " struct=", StructureDescription(u), "\n");
od;

Print("--- O7(3) final hit structure descriptions recap ---\n");
G1 := AtlasGroup("O7(3)");

M13 := AtlasSubgroup("O7(3)", 13); R13 := PerfectResiduum(M13);
reps13 := RepresentativesPerfectSubgroups(R13);
for u in Filtered(reps13, x -> Size(x) in [1344,10752]) do
  Print("order=", Size(u), " struct=", StructureDescription(u), "\n");
od;

M4 := AtlasSubgroup("O7(3)", 4); R4 := PerfectResiduum(M4);
reps4 := RepresentativesPerfectSubgroups(R4);
for u in Filtered(reps4, x -> Size(x)=1092) do
  Print("order=", Size(u), " struct=", StructureDescription(u), "\n");
od;

Print("=== done final struct ===\n");
