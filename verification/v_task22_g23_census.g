# v_task22_g23_census.g -- direct full p.s.n. census for G2(3) on the
# degree-351 permutation representation (coset action on maximal U3(3).2,
# built and validated faithful in v_task22_g23_probe3.g).

LoadPackage("atlasrep");

G := AtlasGroup("G2(3)");
M1 := AtlasSubgroup("G2(3)", 1);
hom := FactorCosetAction(G, M1);
pg := Image(hom);
Print("G2(3) perm rep: degree=", NrMovedPoints(pg), " order=", Size(pg), "\n");

t0 := Runtime();
reps := RepresentativesPerfectSubgroups(pg);
Print("RepresentativesPerfectSubgroups: ", Length(reps), " classes, time=", Runtime()-t0, "\n");

cnt := 0;
for u in reps do
  s := Size(u);
  t0 := Runtime();
  nrm := Normalizer(pg, u);
  if Size(nrm) = s and s > 1 then
    cnt := cnt + 1;
    Print("  HIT order=", s, " selfnorm=true  StructureDescription=", StructureDescription(u),
          "  (Normalizer time=", Runtime()-t0, ")\n");
  else
    Print("  order=", s, " selfnorm=", (Size(nrm)=s), " (Normalizer time=", Runtime()-t0, ")\n");
  fi;
od;
Print("G2(3): TOTAL psn count (nontrivial) = ", cnt, "\n");
Print("=== DONE g23_census ===\n");
