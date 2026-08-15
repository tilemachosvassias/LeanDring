# v_task17_probe3.g -- try RepresentativesPerfectSubgroups directly on the
# FULL twin direct product, for the two smallest twins (M22, J2), as a
# cross-check against the Goursat hand-analysis done separately.

Print("=== M22 twin: DirectProduct(PGL(2,7),PGL(2,11)), order 443520 ===\n");
t0 := Runtime();
dp1 := DirectProduct(PGL(2,7), PGL(2,11));;
Print("built, order=", Size(dp1), " time(ms)=", Runtime()-t0, "\n");
t0 := Runtime();
reps1 := RepresentativesPerfectSubgroups(dp1);;
Print("RepresentativesPerfectSubgroups: ", Length(reps1), " classes, time(ms)=", Runtime()-t0, "\n");
cnt1 := 0;;
for u in reps1 do
  nrm := Normalizer(dp1, u);
  isSelfNorm := (Size(nrm) = Size(u));
  if isSelfNorm and Size(u) > 1 then
    cnt1 := cnt1 + 1;
  fi;
  Print("  order=", Size(u), " selfnorm=", isSelfNorm, "\n");
od;
Print("M22 twin mult1 (nontrivial p.s.n. classes): ", cnt1, "\n");

Print("\n=== J2 twin: DirectProduct(S5,S7), order 604800 ===\n");
t0 := Runtime();
dp2 := DirectProduct(SymmetricGroup(5), SymmetricGroup(7));;
Print("built, order=", Size(dp2), " time(ms)=", Runtime()-t0, "\n");
t0 := Runtime();
reps2 := RepresentativesPerfectSubgroups(dp2);;
Print("RepresentativesPerfectSubgroups: ", Length(reps2), " classes, time(ms)=", Runtime()-t0, "\n");
cnt2 := 0;;
for u in reps2 do
  nrm := Normalizer(dp2, u);
  isSelfNorm := (Size(nrm) = Size(u));
  if isSelfNorm and Size(u) > 1 then
    cnt2 := cnt2 + 1;
  fi;
  Print("  order=", Size(u), " struct=", StructureDescription(u), " selfnorm=", isSelfNorm, "\n");
od;
Print("J2 twin mult1 (nontrivial p.s.n. classes): ", cnt2, "\n");

Print("\n=== DONE probe3 ===\n");
