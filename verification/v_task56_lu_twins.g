# v_task56_lu_twins.g -- GAP spot-checks for the linear/unitary tower
#
#  PART A : orders and |Out| for L_d(q), U_d(q), d = 4,5,6
#  PART B : the iota WITNESS  A = O_p(P_min)  at L_4(3), U_4(3), L_5(2),
#           U_5(2)  --  ind*(A) = [S:P_min] = iota(S),
#           and the RANK->=2 TRAP  ind*(Z(Syl_p)) > iota(S)
#  PART C : minimal degrees from the stored Maxes, where available
#  PART D : the U_4 parabolic comparison  [S:P_2] < [S:P_1]
#
# run:  gap -q -o 8g v_task56_lu_twins.g > v_task56_lu_twins_g_out.txt

Print("========================================================\n");
Print("PART A -- orders and |Out|\n");
Print("========================================================\n");

ordL := function(d,q) local o,i;
  o := q^(d*(d-1)/2);
  for i in [2..d] do o := o*(q^i-1); od;
  return o/Gcd(d,q-1);
end;
ordU := function(d,q) local o,i;
  o := q^(d*(d-1)/2);
  for i in [2..d] do o := o*(q^i-(-1)^i); od;
  return o/Gcd(d,q+1);
end;
iotaL := function(d,q) return (q^d-1)/(q-1); end;
iotaU := function(d,q)
  if d = 4 then return (q+1)*(q^3+1); fi;
  return (q^d-(-1)^d)*(q^(d-1)+(-1)^d)/(q^2-1);
end;

for d in [4,5,6] do
  for q in [2,3,4,5] do
    Print("  L_",d,"(",q,")  formula ", ordL(d,q),
          "   GAP ", Size(PSL(d,q)),
          "   equal: ", ordL(d,q) = Size(PSL(d,q)), "\n");
    Print("  U_",d,"(",q,")  formula ", ordU(d,q),
          "   GAP ", Size(PSU(d,q)),
          "   equal: ", ordU(d,q) = Size(PSU(d,q)), "\n");
  od;
od;

Print("\n========================================================\n");
Print("PART B -- the iota witness  A = O_p(P_min),  N_S(A) = P_min\n");
Print("          and the rank->=2 trap  Z(Syl_p)\n");
Print("========================================================\n");

indstar := function(G, A)
  return Index(G, Normalizer(G, A)) * Size(DerivedSubgroup(A));
end;

# The witness is  A = Z(U_P) = Z(O_p(P))  (Borel-Tits: N_G(Z(U_P)) = P).
# For the LINEAR tower O_p(P_1) is already elementary abelian, so A = O_p(P);
# for the UNITARY tower O_p(P) is NOT abelian (see the |A'| column), and
# taking its centre is essential -- a second rank->=2 trap.
check := function(name, G, p, claim)
  local P, U, A, N, ind, Z, indZ, best, M, m, ii;
  Print("  ", name, "   |G| = ", Size(G), "   natural degree ",
        LargestMovedPoint(G), "\n");
  # smallest-index maximal subgroup with a nontrivial p-core = the smallest
  # parabolic, found over ALL maximal subgroups (not just the point stabiliser)
  best := fail;
  for M in MaximalSubgroupClassReps(G) do
    if Size(PCore(M, p)) > 1 then
      if best = fail or Index(G, M) < Index(G, best) then best := M; fi;
    fi;
  od;
  P := best;
  Print("     smallest parabolic index [G:P_min] = ", Index(G,P),
        "   claimed iota = ", claim, "   ", Index(G,P) = claim, "\n");
  U := PCore(P, p);
  A := Centre(U);
  Print("     U := O_p(P) : |U| = ", Size(U), "  abelian: ", IsAbelian(U),
        "   |Z(U)| = ", Size(A), "\n");
  N := Normalizer(G, A);
  ind := Index(G, N) * Size(DerivedSubgroup(A));
  Print("     N_G(Z(U)) = P : ", N = P,
        "     ind*(Z(U)) = ", ind, "   = iota ? ", ind = claim, "\n");
  Z := Centre(SylowSubgroup(G, p));
  indZ := Index(G, Normalizer(G,Z)) * Size(DerivedSubgroup(Z));
  Print("     TRAP: ind*(Z(Syl_p)) = ", indZ,
        "   ratio to iota = ", indZ/claim, "\n");
  ii := List(MaximalSubgroupClassReps(G), M -> Index(G,M));
  Print("     all maximal-subgroup indices: ", SortedList(ii),
        "   minimal degree = ", Minimum(ii), "\n");
end;

check("L_4(3)", PSL(4,3), 3, 40);
check("L_5(2)", PSL(5,2), 2, 31);
check("U_4(3)", PSU(4,3), 3, 112);
check("U_5(2)", PSU(5,2), 2, 165);
check("L_4(2)=A_8", PSL(4,2), 2, 15);
check("U_4(2)=S_4(3)", PSU(4,2), 2, 27);

Print("\n========================================================\n");
Print("PART C -- minimal degrees from the stored Maxes\n");
Print("========================================================\n");

if IsBoundGlobal("CharacterTable") then
  for nm in ["L4(2)","L4(3)","L5(2)","U4(2)","U4(3)","U5(2)","L6(2)","U6(2)"] do
    t := CharacterTable(nm);
    if t <> fail and HasMaxes(t) then
      m := List(Maxes(t), s -> Size(t)/Size(CharacterTable(s)));
      Print("  ", nm, "  |G| = ", Size(t),
            "   maximal-subgroup indices: ", SortedList(m), "\n");
      Print("        minimal degree m(G) = ", Minimum(m), "\n");
    else
      Print("  ", nm, "  : no stored Maxes\n");
    fi;
  od;
fi;

Print("\n========================================================\n");
Print("PART D -- U_4(q): the SMALLER parabolic is P_2, not P_1\n");
Print("========================================================\n");
for q in [2,3,4,5,7,8] do
  Print("  q = ", q, "   [S:P_1] = (q^2+1)(q^3+1) = ", (q^2+1)*(q^3+1),
        "   [S:P_2] = (q+1)(q^3+1) = ", (q+1)*(q^3+1),
        "   ratio = ", (q^2+1)/(q+1), "\n");
od;
Print("  (v_task50's IOTA_UB rows for U4(4), U4(5), U4(8) are the P_1\n");
Print("   index, i.e. upper bounds; the exact CTblLib rows U4(2) = 27 and\n");
Print("   U4(3) = 112 agree with the P_2 formula.)\n");

QUIT;
