Print("=== Dedup pass 3: consolidate O7(3) order-1344, order-151632, order-40320, order-1092 ===\n");
LoadPackage("atlasrep");
G := AtlasGroup("O7(3)");

M13 := AtlasSubgroup("O7(3)", 13); R13 := PerfectResiduum(M13);
reps13 := RepresentativesPerfectSubgroups(R13);
h1344_13 := Filtered(reps13, u -> Size(u) = 1344);
Print("recheck #13 order-1344 count: ", Length(h1344_13), "\n");

M4 := AtlasSubgroup("O7(3)", 4); R4 := PerfectResiduum(M4);
reps4 := RepresentativesPerfectSubgroups(R4);
h1344_4 := Filtered(reps4, u -> Size(u) = 1344);
h1092_4 := Filtered(reps4, u -> Size(u) = 1092);
Print("recheck #4 order-1344 count: ", Length(h1344_4), "  order-1092 count: ", Length(h1092_4), "\n");

Print("--- order 1344: #13 vs #4 cross conjugacy ---\n");
for i in [1..Length(h1344_13)] do
  for j in [1..Length(h1344_4)] do
    Print("13#", i, " vs 4#", j, ": ", IsConjugate(G, h1344_13[i], h1344_4[j]), "\n");
  od;
od;

Print("--- order 1092: N_G check reconfirm ---\n");
for u in h1092_4 do
  N := Normalizer(G, u);
  Print("order 1092 hit: |N_G(U)|=", Size(N), " selfnorm=", Size(N)=Size(u), " struct=", StructureDescription(u), "\n");
od;

M6 := AtlasSubgroup("O7(3)", 6); R6 := PerfectResiduum(M6);
reps6 := RepresentativesPerfectSubgroups(R6);
h151632_6 := Filtered(reps6, u -> Size(u) = 151632);
Print("recheck #6 order-151632 count: ", Length(h151632_6), "\n");

M3 := AtlasSubgroup("O7(3)", 3); R3 := PerfectResiduum(M3);
reps3 := RepresentativesPerfectSubgroups(R3);
h151632_3 := Filtered(reps3, u -> Size(u) = 151632);
Print("recheck #3 order-151632 count: ", Length(h151632_3), "\n");

Print("--- order 151632: #6 vs #3 cross conjugacy ---\n");
for i in [1..Length(h151632_6)] do
  for j in [1..Length(h151632_3)] do
    Print("6#", i, " vs 3#", j, ": ", IsConjugate(G, h151632_6[i], h151632_3[j]), "\n");
  od;
od;
Print("--- order 151632: #3 internal pairwise ---\n");
for i in [1..Length(h151632_3)] do
  for j in [i+1..Length(h151632_3)] do
    Print("3#", i, " vs 3#", j, ": ", IsConjugate(G, h151632_3[i], h151632_3[j]), "\n");
  od;
od;

M1 := AtlasSubgroup("O7(3)", 1); R1 := PerfectResiduum(M1);
reps1 := RepresentativesPerfectSubgroups(R1);
h40320_1 := Filtered(reps1, u -> Size(u) = 40320);
Print("recheck #1 order-40320 count: ", Length(h40320_1), "\n");
Print("--- order 40320: internal pairwise ---\n");
for i in [1..Length(h40320_1)] do
  for j in [i+1..Length(h40320_1)] do
    Print("1#", i, " vs 1#", j, ": ", IsConjugate(G, h40320_1[i], h40320_1[j]), "\n");
  od;
od;
for u in h40320_1 do
  Print("order40320 struct: ", StructureDescription(u), "\n");
od;

Print("=== dedup3 done ===\n");
