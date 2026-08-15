# v_task20_a11.g -- PROVEN-tier TwinSeparation for A11 vs its v_task19
# witness `A7 * M11 * 1` (order 19958400 = |A11|).
#
# c=1: Out(socle) = Out(A7) x Out(M11) = C2 x 1 = C2, and the required
# extension order is c=1 (trivial subgroup) -- so T = socle itself, the
# UNIQUE Fitting-free group realizing this witness: T = A7 x M11 (a
# genuine unconditional c=1 witness, same strength as the n=17/n=22 cases
# in v_task19).  Full exact mult1 census via RepresentativesPerfectSubgroups
# directly on A7 x M11.

Print("=== n=11 twin: A7 x M11, order 19958400, c=1 (unconditional) ===\n");
s1 := AlternatingGroup(7);;
s2 := MathieuGroup(11);;
Print("|A7|=", Size(s1), " |M11|=", Size(s2), "\n");

t0 := Runtime();;
T := DirectProduct(s1, s2);;
Print("T built, |T|=", Size(T), " (expect 19958400) time(ms)=", Runtime()-t0, "\n");
Print("Sanity: Size(FittingSubgroup(T))=", Size(FittingSubgroup(T)), " (expect 1) IsSimpleGroup(T)=", IsSimpleGroup(T), " (expect false)\n");

t0 := Runtime();;
reps := RepresentativesPerfectSubgroups(T);;
Print("RepresentativesPerfectSubgroups: ", Length(reps), " classes, time(ms)=", Runtime()-t0, "\n");

cnt := 0;;
for u in reps do
  nrm := Normalizer(T, u);
  isSelfNorm := (Size(nrm) = Size(u));
  if isSelfNorm and Size(u) > 1 then cnt := cnt + 1; fi;
  Print("  order=", Size(u), " struct=", StructureDescription(u), " selfnorm=", isSelfNorm, "\n");
od;
Print("n=11 twin mult1 (nontrivial p.s.n. classes) = ", cnt, "\n");
Print("=== DONE a11 ===\n");
