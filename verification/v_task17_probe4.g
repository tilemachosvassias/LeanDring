# v_task17_probe4.g -- M24 twin factor L2(23).2 = PGL(2,23), and full twins.

Print("=== PGL(2,23) (= L2(23).2) ===\n");
t0 := Runtime();
g1 := PGL(2,23);;
Print("order=", Size(g1), " time=", Runtime()-t0, "\n");
t0 := Runtime();
reps1 := RepresentativesPerfectSubgroups(g1);;
Print("RepresentativesPerfectSubgroups: ", Length(reps1), " classes, time=", Runtime()-t0, "\n");
cnt := 0;;
for u in reps1 do
  nrm := Normalizer(g1, u);
  isSelfNorm := (Size(nrm) = Size(u));
  if isSelfNorm and Size(u) > 1 then cnt := cnt+1; fi;
  Print("  order=", Size(u), " struct=", StructureDescription(u), " selfnorm(own)=", isSelfNorm, "\n");
od;
Print("PGL(2,23) own p.s.n. count: ", cnt, "\n");

Print("\n=== L2(23) itself (perfect residuum check) ===\n");
g1b := PSL(2,23);;
Print("order=", Size(g1b), "\n");
t0 := Runtime();
reps1b := RepresentativesPerfectSubgroups(g1b);;
Print("RepresentativesPerfectSubgroups(L2(23)): ", Length(reps1b), " classes, time=", Runtime()-t0, "\n");
for u in reps1b do
  Print("  order=", Size(u), " struct=", StructureDescription(u), "\n");
od;
