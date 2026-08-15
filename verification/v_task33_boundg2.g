# v_task33: Bound G2 for q = p >= 5.
#
# Claim to spot-check at q = 5 (where 3 | q+1, so the twisted subsystem
# subgroup SU_3(5) has centre C_3):
#
#   A := Z(SU_3(5)) ~ C_3  =>  C_S(A) = SU_3(5),  N_S(A) = SU_3(5).2,
#   [S : N_S(A)] = q^3(q^3-1)/2 = 7750.
#
# Also re-runs the ratio-trick elimination for G2(q) with the new constant
# c(q) = (q+1)/2 for q = p >= 5 (and the old c(q) = q+1 elsewhere).

LoadPackage("atlasrep");;

Print("=== part 1: q = 5 structural check ===\n");
G := AtlasGroup("G2(5)", NrMovedPoints, 3906);;
Print("G2(5): degree ", NrMovedPoints(G), ", |G| = ", Size(G), "\n");

# locate the maximal subgroup of index 7750
M := fail;;
for i in [1..10] do
  m := AtlasSubgroup(G, i);
  if m <> fail and Index(G, m) = 7750 then M := m; break; fi;
od;
Print("maximal M of index ", Index(G, M), ", |M| = ", Size(M), "\n");

D := DerivedSubgroup(M);;
Print("  |M'| = ", Size(D), "  (expect 3*|U3(5)| = ", 3*126000, ")\n");
A := Centre(D);;
Print("  |Z(M')| = ", Size(A), "  abelian invariants ", AbelianInvariants(A), "\n");

C := Centralizer(G, A);;
Print("  |C_G(A)| = ", Size(C), "  index ", Index(G, C), "\n");
N := Normalizer(G, A);;
Print("  |N_G(A)| = ", Size(N), "  index ", Index(G, N), "\n");
Print("  N_G(A) = M ? ", N = M, "\n");
Print("  [N:C] = ", Index(N, C), " (expect 2)\n");
Print("  predicted index q^3(q^3-1)/2 = ", 5^3*(5^3-1)/2, "\n");

Print("\n=== part 2: ratio-trick elimination with c(q) ===\n");
# c(q): q = p >= 5 -> (q+1)/2 ; q = 3 -> q+1 ; q = p^f, f >= 2 -> q+1 (safe)
cq := function(q)
  local f;
  f := Factors(q);
  if Length(f) = 1 and f[1] >= 5 then return (q+1)/2; fi;
  return q+1;
end;;

for q in Filtered([3..40], IsPrimePowerInt) do
  i1 := (q^6-1)/(q-1);
  c := cq(q);
  nmax := Int(3 + 8*c);
  if Binomial(nmax,3) < i1 then
    Print("  q=", q, " c=", c, " nmax=", nmax,
          " C(nmax,3)=", Binomial(nmax,3), " < iota1=", i1,
          "  -> IMPOSSIBLE (size)\n");
  else
    good := Filtered([4..nmax], n -> Binomial(n,3) mod i1 = 0);
    Print("  q=", q, " c=", c, " nmax=", nmax, " iota1=", i1,
          "  n with iota1 | C(n,3): ", good, "\n");
    if q = 3 then
      Print("    q=3 ratio-forced n = 3+16*rho: ",
            List([1/2,1,2], r -> 3+16*r), "\n");
    fi;
  fi;
od;

Print("\ndone\n");
QUIT;
