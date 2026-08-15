# v_task20_full_a9.g -- FULL exact conductor-1 (mult1) census of A9 itself
# via RepresentativesPerfectSubgroups(AlternatingGroup(9)), order 181440.
# Tightens the Maxes-based lower bound (2) to an exact value.

Print("=== A9 full p.s.n. census, |A9|=181440 ===\n");
G := AlternatingGroup(9);;
t0 := Runtime();;
reps := RepresentativesPerfectSubgroups(G);;
Print("RepresentativesPerfectSubgroups: ", Length(reps), " classes, time(ms)=", Runtime()-t0, "\n");
cnt := 0;;
for u in reps do
  nrm := Normalizer(G, u);
  isSelfNorm := (Size(nrm) = Size(u));
  if isSelfNorm and Size(u) > 1 then cnt := cnt + 1; fi;
  Print("  order=", Size(u), " struct=", StructureDescription(u), " selfnorm=", isSelfNorm, "\n");
od;
Print("A9 mult1 (EXACT) = ", cnt, "\n");
Print("=== DONE full_a9 ===\n");
