# v_task17_m24b_direct.g -- direct-census cross-check of M24 twin (b):
# L2(23) x S8, order 244823040. Hand (Goursat) proof already gives
# mult1 = 2 exactly; this attempts brute-force confirmation via
# RepresentativesPerfectSubgroups on the full product, as an audit.

Print("=== M24 twin (b): DirectProduct(PSL(2,23), S8), order 244823040 ===\n");
t0 := Runtime();
dp := DirectProduct(PSL(2,23), SymmetricGroup(8));;
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
Print("M24(b) twin mult1 (nontrivial p.s.n. classes): ", cnt, "\n");
Print("=== DONE m24b_direct ===\n");
