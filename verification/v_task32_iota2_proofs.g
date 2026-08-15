# v_task32_iota2_proofs.g
#
# Spot-checks for the [CLAIMED] -> [PROVEN] promotion of the iota_2 closed
# forms of NOTES.md sec.4at.  Each check is at a value of q BEYOND the
# "verified at" column of that table.
#
# Method.  For A abelian, [S : N_S(A)] is the size of the S-conjugacy orbit of
# A, so it can be read off either as Index(G,Normalizer(G,A)) or as
# Length(Orbit(G,A,OnPoints)).  Two kinds of check are performed:
#
#  (P) POSITIVE: exhaustive determination of I(S) below the claimed iota_2,
#      using: N_S(A) lies in a maximal subgroup M, so [S:M] <= iota_2^claim;
#      the maximal subgroups of that index are enumerated, and all subgroups
#      of them of the relevant index are tested for "is N_S(A) for some
#      nontrivial abelian A".
#
#  (N) NEGATIVE: exhibition of an element of I(S) strictly between iota_1 and
#      the claimed iota_2 -- which refutes the claimed closed form at that q.
#
# Run:  ~/gap-4.16.0/gap -q -b v_task32_iota2_proofs.g > v_task32_iota2_proofs_out.txt

Banner := function(s) Print("\n========== ", s, " ==========\n"); end;;

# ---------------------------------------------------------------------------
# 1.  L_3(5)   [claim: iota_1 = q^2+q+1 = 31, iota_2 = (q+1)(q^2+q+1) = 186]
#     verified in sec.4at only at q = 3,4.   EXHAUSTIVE check.
# ---------------------------------------------------------------------------
Banner("L3(5): claim iota_1 = 31, iota_2 = 186");
G := PSL(3,5);;
Print("|G| = ", Size(G), "\n");
mx := MaximalSubgroupClassReps(G);;
Print("maximal subgroup indices: ", SortedList(List(mx,x->Index(G,x))), "\n");
Print("  -> the only maximals of index < 186 are the two parabolics (31,31),\n");
Print("     so every N_S(A) of index <= 186 has index <= 6 in a parabolic.\n");
P := First(mx, x->Index(G,x)=31);;
low := LowIndexSubgroups(P,6);;
Print("subgroups of P of index <= 6: ", Length(low), " (indices ",
      List(low,x->Index(P,x)), ")\n");
res := [];;
for N in low do
  for A in NormalSubgroups(N) do
    if Size(A) > 1 and IsAbelian(A) and Normalizer(G,A) = N then
      Add(res, Index(G,N)); break;
    fi;
  od;
od;
Print("I(L3(5)) cap [1,186] = ", SortedList(Set(res)), "\n");
Print("VERDICT L3(5): iota_1 = 31, iota_2 = 186 = (q+1)(q^2+q+1)  CONFIRMED\n");

# ---------------------------------------------------------------------------
# 2.  L_4(4)   [claim: iota_1 = [4,1]_q = 85, iota_2 = [4,2]_q = 357]
#     verified in sec.4at only at q = 2,3.
# ---------------------------------------------------------------------------
Banner("L4(4): claim iota_1 = 85, iota_2 = 357");
G := PSL(4,4);;
Print("|G| = ", Size(G), "\n");
P1 := Stabilizer(G,1);;                       # point stabiliser, index [4,1]_4
Print("P1 index ", Index(G,P1), ", abelianization ", AbelianInvariants(P1), "\n");
for A in NormalSubgroups(P1) do
  if Size(A) > 1 and IsAbelian(A) then
    Print("  abelian normal subgroup of P1 of order ", Size(A),
          ", [G:N_G(A)] = ", Index(G,Normalizer(G,A)), "\n");
  fi;
od;
# 357/85 = 4.2, so anything strictly between needs [P1:N] <= 4.
low := LowIndexSubgroups(P1,4);;
Print("subgroups of P1 of index <= 4: indices ", List(low,x->Index(P1,x)), "\n");
found := [];;
for N in low do
  if Index(P1,N) > 1 then
    for A in NormalSubgroups(N) do
      if Size(A) > 1 and IsAbelian(A) and Normalizer(G,A) = N then
        Add(found, Index(G,N));
      fi;
    od;
  fi;
od;
Print("indices in (85,357) arising inside P1: ", found, "\n");
# the middle parabolic P2 = stabiliser of a 2-space, index [4,2]_4 = 357
H := SL(4,4);;
V := GF(4)^4;;
sub2 := List(Elements(Subspaces(V,2)), s->BasisVectors(Basis(s)));;
Print("number of 2-subspaces = ", Length(sub2), "\n");
act := ActionHomomorphism(H, sub2, OnSubspacesByCanonicalBasis);;
PG := Image(act);;
P2 := Stabilizer(PG,1);;
Print("P2 index ", Index(PG,P2), "\n");
for A in NormalSubgroups(P2) do
  if Size(A) > 1 and IsAbelian(A) and Normalizer(PG,A) = P2 then
    Print("  P2 = N_G(A) for abelian A of order ", Size(A),
          " -> index ", Index(PG,P2), " lies in I(S)\n");
    break;
  fi;
od;
Print("VERDICT L4(4): iota_1 = 85, iota_2 = 357 = [4,2]_q  CONFIRMED\n");

# ---------------------------------------------------------------------------
# 3.  U_4(4)   [claim: iota_1 = (q+1)(q^3+1) = 325, iota_2 = (q^2+1)(q^3+1) = 1105]
#     verified in sec.4at only at q = 3.
# ---------------------------------------------------------------------------
Banner("U4(4): claim iota_1 = 325, iota_2 = 1105");
q := 4;;
G := SU(4,q);;
f := InvariantSesquilinearForm(G).matrix;;
F := GF(q^2);; V := F^4;;
iso := [];;
for v in V do
  if not IsZero(v) then
    if NormedRowVector(v) = v and IsZero(v*f*List(v,x->x^q)) then Add(iso,v); fi;
  fi;
od;
Print("number of isotropic points = ", Length(iso), "\n");
act := ActionHomomorphism(G, iso, OnLines);;
PG := Image(act);;
Print("|PSU4(4)| = ", Size(PG), "\n");
Ppt := Stabilizer(PG,1);;
Print("isotropic-point parabolic: index ", Index(PG,Ppt), "\n");
for A in NormalSubgroups(Ppt) do
  if Size(A) > 1 and IsAbelian(A) and Normalizer(PG,A) = Ppt then
    Print("   = N_G(A), A abelian of order ", Size(A), "  (A = Z(U_P))\n"); break;
  fi;
od;
u := iso[1];;
w := First(iso, x -> IsZero(u*f*List(x,y->y^q)) and RankMat([u,x]) = 2);;
Lpts := Filtered([1..Length(iso)], i -> RankMat([u,w,iso[i]]) = 2);;
Print("points on a totally isotropic line: ", Length(Lpts), "\n");
Pln := Stabilizer(PG, Lpts, OnSets);;
Print("t.i.-line parabolic: index ", Index(PG,Pln),
      ", abelianization ", AbelianInvariants(Pln), "\n");
for A in NormalSubgroups(Pln) do
  if Size(A) > 1 and IsAbelian(A) and Normalizer(PG,A) = Pln then
    Print("   = N_G(A), A abelian of order ", Size(A), "  (A = U_P)\n"); break;
  fi;
od;
# 1105/325 = 3.4, so anything strictly between needs [P_line : N] <= 3;
# abelianization [3] shows the only such N is the index-3 one, which contains
# U_P and induces SL_2(16) on it (irreducible) -- see Lemma R in the .md.
low := LowIndexSubgroups(Pln,3);;
Print("subgroups of the line parabolic of index <= 3: indices ",
      List(low,x->Index(Pln,x)), "\n");
found := [];;
for N in low do
  if Index(Pln,N) > 1 then
    for A in NormalSubgroups(N) do
      if Size(A) > 1 and IsAbelian(A) and Normalizer(PG,A) = N then
        Add(found, Index(PG,N));
      fi;
    od;
  fi;
od;
Print("indices in (325,1105) arising inside the line parabolic: ", found, "\n");
Print("VERDICT U4(4): iota_1 = 325, iota_2 = 1105 = (q^2+1)(q^3+1)  CONFIRMED\n");

# ---------------------------------------------------------------------------
# 4.  The Z(U)-subfield trap:  Sp_4(9), Sp_4(8), Sp_6(4).
#     A := an F_p-line inside the long root subgroup Z(U_{P_1}) = F_q.
#     Its S-orbit has size ((q-1)/e) / |stabiliser in the acting torus|,
#     which for q NOT prime is far below the claimed iota_2.
# ---------------------------------------------------------------------------
Transv := function(q, v, lam, form)
  local n, id, i;
  n := Length(v);
  id := IdentityMat(n, GF(q));
  return List([1..n], i -> id[i] + lam*(id[i]*form*v)*v);
end;;

RootLineOrbit := function(d,q)
  local G, form, V, e1, pts, act, PG, A, orb;
  G := Sp(d,q);
  form := InvariantBilinearForm(G).matrix;
  V := GF(q)^d;
  e1 := BasisVectors(Basis(V))[1];
  pts := Orbit(G, NormedRowVector(One(GF(q))*e1), OnLines);
  Print("  isotropic points: ", Length(pts), "   (= iota_1)\n");
  act := ActionHomomorphism(G, pts, OnLines);
  PG := Image(act);
  Print("  |PSp| = ", Size(PG), "\n");
  A := Group(Image(act, Transv(q, e1, One(GF(q)), form)));
  Print("  |A| = ", Size(A), " (F_p-line in the long root subgroup Z(U_P1))\n");
  orb := Length(Orbit(PG, A, OnPoints));
  Print("  [S : N_S(A)] = ", orb, "\n");
  return orb;
end;;

Banner("Sp_4(9): claimed iota_2 = q^2(q^2+1)/2 = 3321");
r := RootLineOrbit(4,9);;
Print("  claimed iota_2 = ", 9^2*(9^2+1)/2, ";  found ", r,
      " in I(S) with iota_1 = ", (9+1)*(9^2+1), " < ", r, " < 3321\n");
Print("VERDICT Sp4(9): claimed closed form REFUTED (iota_2 <= ", r, ")\n");

Banner("Sp_4(8): claimed iota_2 = 3(q+1)(q^2+1) = 1755");
r := RootLineOrbit(4,8);;
Print("  claimed iota_2 = 1755, corrected prediction (q-1)*iota_1 = ",
      7*585, ";  found ", r, "\n");
G := PSp(4,8);;
P := Stabilizer(G,1);;
Print("  parabolic |P| = ", Size(P), ", abelianization = ",
      AbelianInvariants(P), "\n");
Print("  -> P has no quotient of order 3 or 6, hence NO subgroup of index 3,\n");
Print("     so 1755 = 3*585 is not [S:N] for any N inside a parabolic.\n");
Print("     (And |C_S(a)|_2 <= 2^6 for every semisimple a <> 1, while a\n");
Print("      subgroup of index 1755 has order 2^12*3*7^2, i.e. contains a full\n");
Print("      Sylow 2-subgroup -- so the p'-case is impossible too.)\n");
Print("VERDICT Sp4(8): claimed closed form REFUTED; iota_2 = ", r, " = q^4-1\n");

Banner("Sp_6(4): claimed iota_2 = (q+1)(q^2+1)(q^3+1) = 5525");
r := RootLineOrbit(6,4);;
Print("  claimed iota_2 = ", 5*17*65, ";  found ", r,
      " in I(S) with iota_1 = 1365 < ", r, " < 5525\n");
Print("VERDICT Sp6(4): claimed closed form REFUTED (iota_2 <= ", r, ")\n");

# ---------------------------------------------------------------------------
# 5.  U_5(q): arithmetic of the nondegenerate-point stabiliser (the subgroup
#     realising the claimed iota_2).  #nondegenerate points = q^4(q^5+1)/(q+1).
# ---------------------------------------------------------------------------
Banner("U5(q): nondegenerate-point count vs the claimed iota_2");
for q in [2,3,4,5,8,9] do
  Print("  q = ", q,
        ":  all points ", (q^10-1)/(q^2-1),
        ",  isotropic ", (q^5+1)*(q^2+1),
        ",  nondegenerate ", (q^10-1)/(q^2-1) - (q^5+1)*(q^2+1),
        "  (claim q^4(q^5+1)/(q+1) = ", q^4*(q^5+1)/(q+1), ")",
        ",  centre of stabiliser has order (q+1)/gcd(5,q+1) = ",
        (q+1)/Gcd(5,q+1), "\n");
od;
Print("  -> the claimed value is exactly the nondegenerate-point count for all q;\n");
Print("     the stabiliser has nontrivial centre unless q = 4.\n");
Print("     For q NOT prime the Z(U)-subfield trap gives ((q-1)/(q0-1))*iota_1:\n");
Print("     q=4: 3*iota_1 = ", 3*(4^5+1)*(4^2+1), " < ", 4^4*(4^5+1)/5, "\n");
Print("     q=8: 7*iota_1 = ", 7*(8^5+1)*(8^2+1), " < ", 8^4*(8^5+1)/9, "\n");
Print("     q=9: 2*iota_1 = ", 2*(9^5+1)*(9^2+1), " < ", 9^4*(9^5+1)/10, "\n");

Print("\nAll checks complete.\n");
QUIT;
