# The H notsubset S case: iota(T) can also be attained at an abelian H meeting T
# outside the socle.  Measure nu(S) = min over OUTER automorphisms a of [S : C_S(a)],
# for the alternating factors -- the case that matters (A_m factors are ubiquitous).
for m in [5..12] do
  A := AlternatingGroup(m); Sm := SymmetricGroup(m);
  best := infinity; wit := fail;
  for c in ConjugacyClasses(Sm) do
    x := Representative(c);
    if not x in A and Order(x) > 1 then
      idx := Size(A) / Size(Centralizer(A, x));
      if idx < best then best := idx; wit := CycleStructurePerm(x); fi;
    fi;
  od;
  Print("A", m, ": iota = ", 0, "   nu(A_m) = min outer [S:C_S(a)] = ", best,
        "  witness cycle type ", wit,
        "   C(m,2)=", Binomial(m,2), "  C(m,3)=", Binomial(m,3), "\n");
od;
QUIT;
