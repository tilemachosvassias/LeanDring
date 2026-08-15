# The TRUE distinguishing invariant of (128,1597)/(128,1598), and whether
# their Burnside rings (tables of marks) agree. Replaces the garbled §5
# "irreducible Singer" description.
LogTo("/Users/tilemachosvassias/DissAnalysis/dring-project/results/order128_pairs/pair128_invariant.out");

Taction := function(id)
  local G, A, Phi, t, hom, U, gens, mats, a, img, T, cp;
  G := SmallGroup(128, id);
  Phi := FrattiniSubgroup(G);
  A := First(MaximalSubgroupClassReps(G),
             m -> IsAbelian(m) and IsNormal(G,m)
                  and StructureDescription(m) = "C4 x C4 x C4");
  # an involution outside A
  t := First(Elements(G), g -> Order(g)=2 and not g in A);
  # U = A / Phi  (= A / A^2 ~ F_2^3); t-conjugation as a matrix over GF(2)
  hom := NaturalHomomorphismByNormalSubgroup(A, Phi);
  U := Image(hom);                       # elementary abelian C2^3
  gens := IndependentGeneratorsOfAbelianGroup(U);
  mats := List(gens, u -> ExponentsOfPcElement(Pcgs(U),
              Image(hom, t * PreImagesRepresentative(hom,u) * t^-1)) * Z(2)^0);
  T := ImmutableMatrix(GF(2), mats);
  cp := CharacteristicPolynomial(T);
  Print("id=", id, ": T on A/Phi order=", Order(T),
        "  charpoly=", CoefficientsOfUnivariatePolynomial(cp),
        "  trace(F2)=", TraceMat(T), "  T^2=I: ", T*T = One(T), "\n");
  return G;
end;

Print("\n== t-action on A/Phi ==\n");
G1 := Taction(1597);
G2 := Taction(1598);

# Do they differ on the square map q(u,1)=(I+T)u restricted issue? print I+T rank.
Print("\n== square-map operator (I+T) on the t-coset ==\n");
DoIT := function(id)
  local G, A, Phi, t, hom, U, gens, mats, T, IT;
  G := SmallGroup(128, id); Phi := FrattiniSubgroup(G);
  A := First(MaximalSubgroupClassReps(G),
             m -> IsAbelian(m) and IsNormal(G,m) and StructureDescription(m)="C4 x C4 x C4");
  t := First(Elements(G), g -> Order(g)=2 and not g in A);
  hom := NaturalHomomorphismByNormalSubgroup(A, Phi); U := Image(hom);
  gens := IndependentGeneratorsOfAbelianGroup(U);
  mats := List(gens, u -> ExponentsOfPcElement(Pcgs(U),
              Image(hom, t*PreImagesRepresentative(hom,u)*t^-1))*Z(2)^0);
  T := ImmutableMatrix(GF(2), mats); IT := T + One(T);
  Print("id=", id, ": rank(I+T)=", RankMat(IT), "  det(I+T)=", DeterminantMat(IT), "\n");
end;
DoIT(1597); DoIT(1598);

# Burnside rings: tables of marks. Are they equal up to relabelling?
Print("\n== tables of marks ==\n");
tm1 := TableOfMarks(SmallGroup(128,1597));
tm2 := TableOfMarks(SmallGroup(128,1598));
Print("#subgroup classes: ", Length(OrdersTom(tm1)), " vs ", Length(OrdersTom(tm2)), "\n");
Print("subgroup-order multiset equal: ",
      Collected(OrdersTom(tm1)) = Collected(OrdersTom(tm2)), "\n");
Print("multiset of ALL marks equal: ",
      Collected(Concatenation(MarksTom(tm1))) = Collected(Concatenation(MarksTom(tm2))), "\n");
# sorted row-multisets (permutation invariant of the mark matrix)
r1 := SortedList(List(MarksTom(tm1), SortedList));
r2 := SortedList(List(MarksTom(tm2), SortedList));
Print("sorted sorted-row multisets equal: ", r1 = r2, "\n");
LogTo();
QUIT;
