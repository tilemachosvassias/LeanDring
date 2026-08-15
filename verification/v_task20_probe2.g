# v_task20_probe2.g -- test the general twin-enumeration machinery (build
# D = Aut(S1) x Aut(S2), socD = Socle(S1)xSocle(S2), Q = Out1 x Out2,
# enumerate ALL subgroups K <= Q of the target order c, build preimage
# T = socD.K for each) on all 4 witnesses (A9,A10,A11,A12), CHEAP part only
# (no RepresentativesPerfectSubgroups yet -- just verify subgroup counts
# and |T| match expectations before committing to the expensive census).

EnumerateTwins := function(A1, A2, cTarget, label)
  local soc1, soc2, nat1, nat2, Out1, Out2, D, e1, e2, socD, Q, allsubs, subs,
        K, gens, elt, g, o1, o2, liftA, liftB, T, results, i;
  soc1 := Socle(A1);
  soc2 := Socle(A2);
  nat1 := NaturalHomomorphismByNormalSubgroup(A1, soc1);
  nat2 := NaturalHomomorphismByNormalSubgroup(A2, soc2);
  Out1 := Image(nat1);
  Out2 := Image(nat2);
  Print(label, ": |A1|=", Size(A1), " |soc1|=", Size(soc1), " |Out1|=", Size(Out1), "\n");
  Print(label, ": |A2|=", Size(A2), " |soc2|=", Size(soc2), " |Out2|=", Size(Out2), "\n");
  D := DirectProduct(A1, A2);
  e1 := Embedding(D,1);
  e2 := Embedding(D,2);
  socD := ClosureGroup(Image(e1,soc1), Image(e2,soc2));
  Print(label, ": |D|=", Size(D), " |socD|=", Size(socD), " (expect ", Size(soc1)*Size(soc2), ")\n");
  Q := DirectProduct(Out1, Out2);
  Print(label, ": |Q|=", Size(Q), " (expect ", Size(Out1)*Size(Out2), ")\n");
  allsubs := AllSubgroups(Q);
  subs := Filtered(allsubs, s -> Size(s) = cTarget);
  Print(label, ": # subgroups of Q of order ", cTarget, " = ", Length(subs), "\n");
  results := [];
  for i in [1..Length(subs)] do
    K := subs[i];
    gens := GeneratorsOfGroup(K);
    if Length(gens) = 0 then
      elt := [];
    else
      elt := [];
      for g in gens do
        o1 := Image(Projection(Q,1), g);
        o2 := Image(Projection(Q,2), g);
        liftA := PreImagesRepresentative(nat1, o1);
        liftB := PreImagesRepresentative(nat2, o2);
        Add(elt, Image(e1,liftA)*Image(e2,liftB));
      od;
    fi;
    T := ClosureGroup(socD, elt);
    Print(label, ": twin#", i, " |T|=", Size(T), " (expect ", Size(socD)*cTarget, ")\n");
    Add(results, T);
  od;
  return results;
end;;

Print("=== n=9: A5 x L2(8), c=6 ===\n");
a1 := SymmetricGroup(5);;
a2 := Image(IsomorphismPermGroup(AutomorphismGroup(PSL(2,8))));;
r9 := EnumerateTwins(a1, a2, 6, "n9");;

Print("\n=== n=10: A6 x A7, c=2 ===\n");
b1 := Image(IsomorphismPermGroup(AutomorphismGroup(AlternatingGroup(6))));;
b2 := SymmetricGroup(7);;
r10 := EnumerateTwins(b1, b2, 2, "n10");;

Print("\n=== n=11: A7 x M11, c=1 ===\n");
c1 := SymmetricGroup(7);;
c2 := MathieuGroup(11);;
r11 := EnumerateTwins(c1, c2, 1, "n11");;

Print("\n=== n=12: L2(11) x A9, c=2 ===\n");
d1 := Image(IsomorphismPermGroup(AutomorphismGroup(PSL(2,11))));;
d2 := SymmetricGroup(9);;
r12 := EnumerateTwins(d1, d2, 2, "n12");;

Print("\n=== DONE probe2 ===\n");
