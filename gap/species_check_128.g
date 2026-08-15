# 2^7 check (Boltje-Garcia species-iso NECESSARY conditions) for (128,1597)/(128,1598).
# A species iso needs a subgroup-class bijection theta_[S] with group isos
# theta_K: Hom(K,C^x)=K^ab -> (theta K)^ab.  So the multiset over subgroup
# classes of (|K|, |N_G(K)|, K^ab-type) must match.  Bounded: subgroup lattice only.
Prof := function(id)
  local G, ccs, c, K, out;
  G := SmallGroup(128,id);
  ccs := ConjugacyClassesSubgroups(G);
  out := [];
  for c in ccs do
    K := Representative(c);
    Add(out, [ Size(K), Size(Normalizer(G,K)),
               AbelianInvariants(K/DerivedSubgroup(K)) ]);
  od;
  return Collected(out);
end;
p1 := Prof(1597);; p2 := Prof(1598);;
Print("(1597) #subgroup classes = ", Sum(p1,x->x[2]), "\n");
Print("(1598) #subgroup classes = ", Sum(p2,x->x[2]), "\n");
Print("subgroup-class (|K|,|N_G K|,K^ab) multiset EQUAL: ", p1 = p2, "\n");
if p1 <> p2 then
  Print("  DIFFERENCES (in 1597 not 1598): ", Filtered(p1, x-> not x in p2){[1..Minimum(6,Length(Filtered(p1,x->not x in p2)))]}, "\n");
fi;
QUIT;
G1 := SmallGroup(128,1597);; G2 := SmallGroup(128,1598);;
t1 := CharacterTable(G1);; t2 := CharacterTable(G2);;
tr := TransformingPermutationsCharacterTables(t1, t2);;
Print("char-table-with-power-maps EQUIVALENT (1597 ~ 1598): ", tr <> fail, "\n");
Print("element-order multisets equal: ",
  SortedList(OrdersClassRepresentatives(t1)) = SortedList(OrdersClassRepresentatives(t2)), "\n");
Print("degree multisets equal: ",
  SortedList(List(Irr(t1),Degree)) = SortedList(List(Irr(t2),Degree)), "\n");
QUIT;
