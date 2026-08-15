Print("=== Dedup pass 2: O7(3) #13 hits vs #7 hits, and #6 order-151632 struct ===\n");
LoadPackage("atlasrep");
G := AtlasGroup("O7(3)");

M13 := AtlasSubgroup("O7(3)", 13);
R13 := PerfectResiduum(M13);
reps13 := RepresentativesPerfectSubgroups(R13);
h1344_13 := Filtered(reps13, u -> Size(u) = 1344);
h10752_13 := Filtered(reps13, u -> Size(u) = 10752);

M7 := AtlasSubgroup("O7(3)", 7);
R7 := PerfectResiduum(M7);
reps7 := RepresentativesPerfectSubgroups(R7);
h1344_7 := Filtered(reps7, u -> Size(u) = 1344);
h10752_7 := Filtered(reps7, u -> Size(u) = 10752);

Print("#13 order-1344 count: ", Length(h1344_13), "  #7 order-1344 count: ", Length(h1344_7), "\n");
Print("#13 order-10752 count: ", Length(h10752_13), "  #7 order-10752 count: ", Length(h10752_7), "\n");

Print("--- cross conjugacy check order 1344 (13 vs 7) ---\n");
for i in [1..Length(h1344_13)] do
  for j in [1..Length(h1344_7)] do
    c := IsConjugate(G, h1344_13[i], h1344_7[j]);
    Print("13#", i, " vs 7#", j, ": ", c, "\n");
  od;
od;

Print("--- within #7 order-1344 pairwise ---\n");
for i in [1..Length(h1344_7)] do
  for j in [i+1..Length(h1344_7)] do
    Print("7#", i, " vs 7#", j, ": ", IsConjugate(G, h1344_7[i], h1344_7[j]), "\n");
  od;
od;

Print("--- cross conjugacy check order 10752 (13 vs 7) ---\n");
for i in [1..Length(h10752_13)] do
  for j in [1..Length(h10752_7)] do
    c := IsConjugate(G, h10752_13[i], h10752_7[j]);
    Print("13#", i, " vs 7#", j, ": ", c, "\n");
  od;
od;

Print("--- StructureDescription for #7 hits ---\n");
for u in h1344_7 do Print("order1344: ", StructureDescription(u), "\n"); od;
for u in h10752_7 do Print("order10752: ", StructureDescription(u), "\n"); od;

Print("--- O7(3) #6 order-151632 structure ---\n");
M6 := AtlasSubgroup("O7(3)", 6);
R6 := PerfectResiduum(M6);
reps6 := RepresentativesPerfectSubgroups(R6);
h151632 := Filtered(reps6, u -> Size(u) = 151632);
for u in h151632 do
  Print("order151632 struct: ", StructureDescription(u), "\n");
od;

Print("=== dedup2 done ===\n");
