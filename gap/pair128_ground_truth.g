# Ground truth on (128,1597)/(128,1598): the real structure and the true
# distinguishing invariant below Phi. Tests the §5 "reciprocal Singer" claim.
LogTo("/Users/tilemachosvassias/DissAnalysis/dring-project/results/order128_pairs/pair128_ground_truth.out");

Structure := function(id)
  local G, F, Q, A, maxs, absub, t, act, U, gens, i, order_t, cc, elord;
  G := SmallGroup(128, id);
  Print("\n==== SmallGroup(128,", id, ") ====\n");
  F := FrattiniSubgroup(G);
  Q := G / F;
  Print("|G|=", Size(G), "  |Phi|=", Size(F),
        "  G/Phi=", StructureDescription(Q), " (rank ", Length(Pcgs(Q)), ")\n");
  Print("Z(G)=", StructureDescription(Centre(G)),
        "  G'=", StructureDescription(DerivedSubgroup(G)),
        "  Phi=", StructureDescription(F), "\n");
  # element order distribution
  elord := Collected(List(ConjugacyClasses(G), c -> [Order(Representative(c)), Size(c)]));
  Print("nclasses=", Length(ConjugacyClasses(G)),
        "  exponent=", Exponent(G), "\n");
  Print("order->#elements: ",
        Collected(List(Elements(G), Order)), "\n");
  # abelian maximal subgroups and their iso type
  maxs := MaximalSubgroupClassReps(G);
  absub := Filtered(maxs, m -> IsAbelian(m));
  Print("#maximal classes=", Length(maxs),
        "  abelian ones: ", List(absub, StructureDescription), "\n");
  # (The t-action on A/Phi is trivial since A/Phi <= G/Phi is abelian; the
  #  genuine Singer operator sigma^-1[t,-] is computed in pair128_singer_check.g.)
  return G;
end;

G1 := Structure(1597);
G2 := Structure(1598);

# Burnside test: are the tables of marks equivalent (=> B(G1)=B(G2))?
Print("\n---- tables of marks ----\n");
t1 := TableOfMarks(G1);
t2 := TableOfMarks(G2);
Print("length(ToM1)=", Length(OrdersTom(t1)),
      "  length(ToM2)=", Length(OrdersTom(t2)), "\n");
Print("sorted subgroup-order multiset equal: ",
      SortedList(OrdersTom(t1)) = SortedList(OrdersTom(t2)), "\n");
# a cheap ring-iso necessary invariant: multiset of (|H|,|N_G(H)/H|) via marks diagonal
LogTo();
QUIT;
