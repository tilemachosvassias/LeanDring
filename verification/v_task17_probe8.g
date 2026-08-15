# v_task17_probe8.g -- U3(8) via its natural degree-513 permutation
# representation (action on isotropic points of the Hermitian unital),
# which should be far more tractable for RepresentativesPerfectSubgroups
# than the large-degree IsomorphismPermGroup default (degree 4161, aborted).

g := PSU(3,8);;
Print("PSU(3,8) matrix group order=", Size(g), "\n");
f := GF(64);;
v := [One(f), Zero(f), Zero(f)];;
Print("test vector v=", v, "\n");
orb := Orbit(g, v, OnLines);;
Print("orbit size (should be 513 if isotropic & transitive): ", Length(orb), "\n");

if Length(orb) = 513 then
  hom := ActionHomomorphism(g, orb, OnLines);;
  pg := Image(hom);;
  Print("perm group degree=", NrMovedPoints(pg), " order=", Size(pg), "\n");
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
else
  Print("orbit not 513 -- try a different isotropic vector\n");
fi;
Print("=== DONE probe8 ===\n");
