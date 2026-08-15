# v_task17_m24a_direct.g -- direct-census cross-check of M24 twin (a):
# L2(23).2 x A8 = PGL(2,23) x A8, order 244823040. Hand proof gives
# mult1 = 0 exactly (own(PGL(2,23))=0, diagonal blocked by 23 not
# dividing |A8|). Brute-force confirmation.

Print("=== M24 twin (a): DirectProduct(PGL(2,23), A8), order 244823040 ===\n");
t0 := Runtime();
dp := DirectProduct(PGL(2,23), AlternatingGroup(8));;
Print("built, order=", Size(dp), " time(ms)=", Runtime()-t0, "\n");
t0 := Runtime();
reps := RepresentativesPerfectSubgroups(dp);;
Print("RepresentativesPerfectSubgroups: ", Length(reps), " classes, time(ms)=", Runtime()-t0, "\n");
cnt := 0;;
for u in reps do
  nrm := Normalizer(dp, u);
  isSelfNorm := (Size(nrm) = Size(u));
  if isSelfNorm and Size(u) > 1 then cnt := cnt + 1; fi;
  Print("  order=", Size(u), " struct=", StructureDescription(u), " selfnorm=", isSelfNorm, "\n");
od;
Print("M24(a) twin mult1 (nontrivial p.s.n. classes): ", cnt, "\n");
Print("=== DONE m24a_direct ===\n");
