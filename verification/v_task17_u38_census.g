# v_task17_u38_census.g -- own p.s.n. census for U3(8) using its natural
# degree-513 permutation representation (via SmallerDegreePermutationRepresentation
# applied to GAP's built-in PSU(3,8), which is otherwise given in degree 4161).

g0 := PSU(3,8);;
Print("PSU(3,8) built-in degree=", NrMovedPoints(g0), " order=", Size(g0), "\n");
t0 := Runtime();
hom := SmallerDegreePermutationRepresentation(g0);;
pg := Image(hom);;
Print("reduced degree=", NrMovedPoints(pg), " order=", Size(pg), " time=", Runtime()-t0, "\n");

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
Print("U3(8) own p.s.n. count (nontrivial): ", cnt, "\n");
Print("=== DONE u38_census ===\n");
