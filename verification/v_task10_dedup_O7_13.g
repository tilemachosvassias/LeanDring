Print("=== Dedup O7(3) maximal #13 hits (order 1344 x4, order 10752 x2) ===\n");
LoadPackage("atlasrep");
G := AtlasGroup("O7(3)");
M := AtlasSubgroup("O7(3)", 13);
R := PerfectResiduum(M);
Print("|R|=", Size(R), "\n");
reps := RepresentativesPerfectSubgroups(R);
hits1344 := Filtered(reps, u -> Size(u) = 1344);
hits10752 := Filtered(reps, u -> Size(u) = 10752);
Print("num order-1344 reps: ", Length(hits1344), "\n");
Print("num order-10752 reps: ", Length(hits10752), "\n");

Print("--- pairwise G-conjugacy check, order 1344 ---\n");
for i in [1..Length(hits1344)] do
  for j in [i+1..Length(hits1344)] do
    c := IsConjugate(G, hits1344[i], hits1344[j]);
    Print(i, " vs ", j, ": conjugate in G = ", c, "\n");
  od;
od;

Print("--- pairwise G-conjugacy check, order 10752 ---\n");
for i in [1..Length(hits10752)] do
  for j in [i+1..Length(hits10752)] do
    c := IsConjugate(G, hits10752[i], hits10752[j]);
    Print(i, " vs ", j, ": conjugate in G = ", c, "\n");
  od;
od;

Print("--- StructureDescription attempts ---\n");
for u in hits1344 do
  Print("order 1344 struct: ", StructureDescription(u), "\n");
od;
for u in hits10752 do
  Print("order 10752 struct: ", StructureDescription(u), "\n");
od;

Print("=== dedup done ===\n");
