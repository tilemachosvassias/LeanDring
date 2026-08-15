# verify_cyclic_ambient_ranks.g -- data for the cyclic-ambient RAT-BR theorem.
# For each 2-group order 2^r (r=2..6): subgroup-class count m(W) per group,
# flagged against the fixed-species bound 2r+1 of the cyclic ambient D(C_{2^r});
# and det B(W) = prod of ToM diagonal for the groups with m(W) <= 2r+1.
# Run: ~/gap-4.15.1/gap -q -b gap/verify_cyclic_ambient_ranks.g < /dev/null

for r in [2..6] do
  n := 2^r;;
  Print("== order ", n, "  (rank bound 2r+1 = ", 2*r+1, ")\n");
  for id in [1..NumberSmallGroups(n)] do
    W := SmallGroup(n, id);;
    m := Length(ConjugacyClassesSubgroups(W));;
    if m <= 2*r+1 then
      T := MatTom(TableOfMarks(W));;
      d := Product(List([1..m], i -> T[i][i]));;
      Print("  [", n, ",", id, "] ", StructureDescription(W),
            "  m=", m, "  detB=2^", LogInt(d, 2), "\n");
    else
      Print("  [", n, ",", id, "] ", StructureDescription(W),
            "  m=", m, "  RANK-EXCLUDED\n");
    fi;
  od;
od;
QUIT;
