# v_task20_full_a10.g -- FULL exact conductor-1 (mult1) census of A10
# itself via RepresentativesPerfectSubgroups(AlternatingGroup(10)),
# order 1814400. Needed because the Maxes lower bound (2) does NOT
# exceed some of the A10 twins' exact mult1 values (up to 11,
# v_task20_a10_out.txt) -- an exact/tighter census is required for
# separation.

Print("=== A10 full p.s.n. census, |A10|=1814400 ===\n");
G := AlternatingGroup(10);;
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
Print("A10 mult1 (EXACT) = ", cnt, "\n");
Print("=== DONE full_a10 ===\n");
