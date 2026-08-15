# v_task20_a9.g -- PROVEN-tier TwinSeparation for A9 vs its v_task19 witness
# `A5 * L2(8) * 6` (order 181440 = |A9|).
#
# Method (v_task17): T embeds in Aut(socle) = Aut(A5) x Aut(L2(8)); T/socle
# is a subgroup K <= Out(socle) = Out(A5) x Out(L2(8)) = C2 x C3 = C6 of
# order c=6.  Since C6 is cyclic, it has a UNIQUE subgroup of order 6 --
# itself -- so there is exactly ONE Fitting-free group realizing this
# witness: T = S5 x AutPGammaL(L2(8)) (matches the direct GAP construction
# already verified in v_task19_out.txt).  Full exact conductor-1 (mult1)
# census via RepresentativesPerfectSubgroups(T) directly, T is tiny
# (order 181440) so no Goursat argument is even needed.

Print("=== n=9 twin: Aut(A5) x Aut(L2(8)) = S5 x PGammaL(2,8), order 181440 ===\n");
a1 := SymmetricGroup(5);;
a2 := Image(IsomorphismPermGroup(AutomorphismGroup(PSL(2,8))));;
soc1 := Socle(a1);;
soc2 := Socle(a2);;
Print("|Aut(A5)|=", Size(a1), " |Socle|=", Size(soc1), " |Out(A5)|=", Size(a1)/Size(soc1), "\n");
Print("|Aut(L2(8))|=", Size(a2), " |Socle|=", Size(soc2), " |Out(L2(8))|=", Size(a2)/Size(soc2), "\n");

t0 := Runtime();;
T := DirectProduct(a1, a2);;
Print("T built, |T|=", Size(T), " (expect 181440) time(ms)=", Runtime()-t0, "\n");

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
Print("n=9 twin mult1 (nontrivial p.s.n. classes) = ", cnt, "\n");
Print("=== DONE a9 ===\n");
