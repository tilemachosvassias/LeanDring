# v_task20_full_a11.g -- FULL exact conductor-1 (mult1) census of A11
# itself via RepresentativesPerfectSubgroups(AlternatingGroup(11)),
# order 19958400. Needed because the Maxes lower bound (4) does NOT
# exceed the A11 twin's exact mult1 value (20, v_task20_a11_out.txt).

Print("=== A11 full p.s.n. census, |A11|=19958400 ===\n");
G := AlternatingGroup(11);;
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
Print("A11 mult1 (EXACT) = ", cnt, "\n");
Print("=== DONE full_a11 ===\n");
