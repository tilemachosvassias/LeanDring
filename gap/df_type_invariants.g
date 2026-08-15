# df_type_invariants.g -- rank |F| and det exponent of D_F(G) for every
# abelian 2-group of order <= 64, from the closed formulas in
# results/df_decorated_dress_congruences.md:
#   |F|    = sum_K 2^(rank K)
#   log2 det = sum_K [ (r - log2|K|)*2^(rank K) + rank(K)*2^(rank K - 1) ]
# Collision of the pair (|F|, det) between two types of one order would mark
# the exact spot where higher-arity congruence data is needed.
# Run: ~/gap-4.15.1/gap -q -b gap/df_type_invariants.g < /dev/null

for r in [2..6] do
  n := 2^r;;
  Print("== order ", n, "\n");
  seen := [];;
  for part in Partitions(r) do
    G := AbelianGroup(List(part, i -> 2^i));;
    rk := 0;; e := 0;;
    for cl in ConjugacyClassesSubgroups(G) do
      K := Representative(cl);;
      d := Length(AbelianInvariants(K));;
      kk := LogInt(Maximum(Size(K),1), 2);;
      rk := rk + 2^d;;
      e := e + (r - kk)*2^d;;
      if d > 0 then e := e + d*2^(d-1); fi;
    od;
    Print("  ", part, "  |F|=", rk, "  log2det=", e, "\n");
    Add(seen, [rk, e]);
  od;
  if Length(Set(seen)) < Length(seen) then
    Print("  *** COLLISION at order ", n, " ***\n");
  else
    Print("  all types separated by (|F|, det)\n");
  fi;
od;
QUIT;
