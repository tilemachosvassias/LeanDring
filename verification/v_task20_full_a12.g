# v_task20_full_a12.g -- FULL exact conductor-1 (mult1) census of A12
# itself via RepresentativesPerfectSubgroups(AlternatingGroup(12)),
# order 239500800. A_n itself has proven MUCH cheaper than the twin
# direct-product groups of comparable order for n=9,10,11 (sub-second
# vs tens of seconds) -- attempting the same here.

Print("=== A12 full p.s.n. census, |A12|=239500800 ===\n");
G := AlternatingGroup(12);;
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
Print("A12 mult1 (EXACT) = ", cnt, "\n");
Print("=== DONE full_a12 ===\n");
