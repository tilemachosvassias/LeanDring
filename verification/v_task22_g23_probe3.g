# v_task22_g23_probe3.g -- build a low-degree permutation representation of
# G2(3) via coset action on the smallest-index maximal subgroup (U3(3).2,
# index 351), and list orders of all 10 maximal subgroup classes (SLPs known
# to exist per probe2).

LoadPackage("atlasrep");

G := AtlasGroup("G2(3)");
Print("G2(3) matrix rep: order=", Size(G), "\n");

for i in [1..10] do
  t0 := Runtime();
  M := AtlasSubgroup("G2(3)", i);
  if M = fail then
    Print("maximal #", i, ": NO SLP\n");
  else
    Print("maximal #", i, ": order=", Size(M), " index=", Size(G)/Size(M), " time=", Runtime()-t0, "\n");
  fi;
od;

Print("--- building coset action on maximal #1 (smallest index) ---\n");
t0 := Runtime();
M1 := AtlasSubgroup("G2(3)", 1);
Print("M1 order=", Size(M1), " index=", Size(G)/Size(M1), "\n");
hom := FactorCosetAction(G, M1);
pg := Image(hom);
Print("coset action degree=", NrMovedPoints(pg), " order=", Size(pg), " time=", Runtime()-t0, "\n");
Print("faithful: ", Size(pg) = Size(G), "\n");

Print("=== DONE probe3 ===\n");
