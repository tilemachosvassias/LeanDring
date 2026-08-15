# v_task20_a10.g -- PROVEN-tier TwinSeparation for A10 vs ALL its v_task19
# witness `A6 * A7 * 2` (order 1814400 = |A10|) Fitting-free realizations.
#
# Socle = A6 x A7.  Out(A6) = C2 x C2 (order 4: the classical S6/M10/
# PGL(2,9) triple), Out(A7) = C2 (order 2, standard n<>6).  Out(socle) =
# C2 x C2 x C2 (order 8, elementary abelian).  c=2: there are SEVEN
# distinct subgroups of order 2 in an elementary abelian group of order 8
# -- one for each nonzero element -- giving SEVEN a priori non-isomorphic
# Fitting-free extensions T = socle.<elt>, not just the two "extend one
# factor" witnesses v_task16's method would settle for.  Method: T embeds
# in Aut(socle) = Aut(A6) x Aut(A7); build D = Aut(A6) x Aut(A7), socD =
# Socle(Aut(A6)) x Socle(Aut(A7)), enumerate every order-2 subgroup K of
# Out(socle) = D/socD, T_K := preimage of K.  Full exact mult1 census via
# RepresentativesPerfectSubgroups(T_K) on EACH of the 7.

EnumerateTwins := function(A1, A2, cTarget, label)
  local soc1, soc2, nat1, nat2, Out1, Out2, D, e1, e2, socD, Q, allsubs, subs,
        K, gens, elt, g, o1, o2, liftA, liftB, T, results, i, ext1, ext2, typ;
  soc1 := Socle(A1);
  soc2 := Socle(A2);
  nat1 := NaturalHomomorphismByNormalSubgroup(A1, soc1);
  nat2 := NaturalHomomorphismByNormalSubgroup(A2, soc2);
  Out1 := Image(nat1);
  Out2 := Image(nat2);
  D := DirectProduct(A1, A2);
  e1 := Embedding(D,1);
  e2 := Embedding(D,2);
  socD := ClosureGroup(Image(e1,soc1), Image(e2,soc2));
  Q := DirectProduct(Out1, Out2);
  allsubs := AllSubgroups(Q);
  subs := Filtered(allsubs, s -> Size(s) = cTarget);
  Print(label, ": |socD|=", Size(socD), " |Out(socle)|=", Size(Q),
        " # order-", cTarget, " subgroups = ", Length(subs), "\n");
  results := [];
  for i in [1..Length(subs)] do
    K := subs[i];
    gens := GeneratorsOfGroup(K);
    elt := [];
    for g in gens do
      o1 := Image(Projection(Q,1), g);
      o2 := Image(Projection(Q,2), g);
      liftA := PreImagesRepresentative(nat1, o1);
      liftB := PreImagesRepresentative(nat2, o2);
      Add(elt, Image(e1,liftA)*Image(e2,liftB));
    od;
    ext1 := ClosureGroup(soc1, List(gens, g -> PreImagesRepresentative(nat1, Image(Projection(Q,1),g))));
    ext2 := ClosureGroup(soc2, List(gens, g -> PreImagesRepresentative(nat2, Image(Projection(Q,2),g))));
    if Size(ext1) = Size(soc1) then
      typ := "pure-factor2 (soc1 x ext2)";
    elif Size(ext2) = Size(soc2) then
      typ := "pure-factor1 (ext1 x soc2)";
    else
      typ := "diagonal (fiber product)";
    fi;
    T := ClosureGroup(socD, elt);
    Add(results, rec(T:=T, ext1:=ext1, ext2:=ext2, typ:=typ, idx:=i));
  od;
  return results;
end;;

Print("=== n=10 twin family: Aut(A6) x Aut(A7), socle A6 x A7, c=2 ===\n");
b1 := Image(IsomorphismPermGroup(AutomorphismGroup(AlternatingGroup(6))));;
b2 := SymmetricGroup(7);;
twins := EnumerateTwins(b1, b2, 2, "n10");;

overallMult1 := [];;
for tw in twins do
  Print("\n--- twin #", tw.idx, " type=", tw.typ,
        " ext1(A6-side)=", StructureDescription(tw.ext1),
        " ext2(A7-side)=", StructureDescription(tw.ext2), " ---\n");
  Print("|T|=", Size(tw.T), " (expect 1814400)\n");
  t0 := Runtime();;
  reps := RepresentativesPerfectSubgroups(tw.T);;
  Print("RepresentativesPerfectSubgroups: ", Length(reps), " classes, time(ms)=", Runtime()-t0, "\n");
  cnt := 0;;
  for u in reps do
    nrm := Normalizer(tw.T, u);
    isSelfNorm := (Size(nrm) = Size(u));
    if isSelfNorm and Size(u) > 1 then cnt := cnt + 1; fi;
    Print("  order=", Size(u), " struct=", StructureDescription(u), " selfnorm=", isSelfNorm, "\n");
  od;
  Print("twin #", tw.idx, " mult1 = ", cnt, "\n");
  Add(overallMult1, cnt);
od;

Print("\n=== SUMMARY n=10: mult1 per twin = ", overallMult1, " ===\n");
Print("=== DONE a10 ===\n");
