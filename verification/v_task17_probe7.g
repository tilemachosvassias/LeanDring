# v_task17_probe7.g -- try RepresentativesPerfectSubgroups directly on
# PSU(3,8) (order 5,515,776), natural permutation rep on 513 points.

Print("=== PSU(3,8) ===\n");
t0 := Runtime();
g := PSU(3,8);;
Print("built (matrix group), order=", Size(g), " time=", Runtime()-t0, "\n");
t0 := Runtime();
pg := Image(IsomorphismPermGroup(g));;
Print("converted to perm group, degree=", NrMovedPoints(pg), " time=", Runtime()-t0, "\n");
t0 := Runtime();
reps := RepresentativesPerfectSubgroups(pg);;
Print("RepresentativesPerfectSubgroups: ", Length(reps), " classes, time=", Runtime()-t0, "\n");
cnt := 0;;
for u in reps do
  nrm := Normalizer(pg, u);
  isSelfNorm := (Size(nrm) = Size(u));
  if isSelfNorm and Size(u) > 1 then cnt := cnt+1; fi;
  Print("  order=", Size(u), " selfnorm(own)=", isSelfNorm, "\n");
od;
Print("U3(8) own p.s.n. count: ", cnt, "\n");
Print("=== DONE probe7 ===\n");
