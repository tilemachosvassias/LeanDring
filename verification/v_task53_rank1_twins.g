# v_task53_rank1_twins.g -- GAP spot-checks for the rank-1 Lie twin
# elimination (U_3(q), Sz(q) = 2B_2(q), R(q) = 2G_2(q)).
#
# PART A : the ORDER formulas used uniformly in the python script, checked
#          against GAP's own construction of the groups.
#             |U_3(q)| = q^3(q^2-1)(q^3+1)/gcd(3,q+1)
#             |Sz(q)|  = q^2(q-1)(q^2+1)
#             |R(q)|   = q^3(q-1)(q^3+1)
#
# PART B : the iota UPPER bound witness, verified directly:  P = Syl_p(S),
#          A = Z(P) is a NON-TRIVIAL ABELIAN subgroup and
#             ind*(A) = [S : N_S(A)] * |A'| = [S : N_S(A)]
#          equals q^3+1 (U_3, R) resp. q^2+1 (Sz).  This is the Borel-Tits
#          witness made explicit.
#
# PART C : the iota LOWER bound, i.e. that ind*(H) >= q^3+1 (resp. q^2+1)
#          for EVERY 1 <> H <= S -- exhaustively over all conjugacy classes
#          of subgroups, where the lattice is in reach (U_3(3), Sz(8)).
#          This is what makes the target (AB)-FREE.
#
# PART D : Lemma K analogues: the largest prime power dividing |S|, against
#          the claimed uniform bounds.
#
# Run: ~/gap-4.16.0/gap -q -o 4g v_task53_rank1_twins.g \
#        > v_task53_rank1_twins_g_out.txt

IndStar := function(G, H)
  return Index(G, Normalizer(G, H)) * Size(DerivedSubgroup(H));
end;

Print("### PART A -- order formulas\n");
Print("# group | GAP |S| | formula | equal?\n");
for q in [3,4,5,7,8,9,11,13,16,17,19,23,25,27,32] do
  G := PSU(3, q);
  f := q^3*(q^2-1)*(q^3+1)/GcdInt(3,q+1);
  Print("U3(", q, ") | ", Size(G), " | ", f, " | ", Size(G) = f, "\n");
od;
for q in [8,32,128,512,2048] do
  G := SuzukiGroup(q);
  f := q^2*(q-1)*(q^2+1);
  Print("Sz(", q, ") | ", Size(G), " | ", f, " | ", Size(G) = f, "\n");
od;
for q in [27,243,2187] do
  G := ReeGroup(q);
  f := q^3*(q-1)*(q^3+1);
  Print("R(", q, ") | ", Size(G), " | ", f, " | ", Size(G) = f, "\n");
od;

Print("\n### PART B -- iota upper-bound witness A = Z(Syl_p(S))\n");
Print("# group | |A| | A abelian? | [S:N_S(A)] | ind*(A) | claimed iota\n");
for q in [3,4,5,7,8,9,11,13,16,17,19,23,25,27] do
  G := PSU(3, q);
  p := SmallestRootInt(q);
  P := SylowSubgroup(G, p);
  A := Centre(P);
  Print("U3(", q, ") | ", Size(A), " | ", IsAbelian(A), " | ",
        Index(G, Normalizer(G, A)), " | ", IndStar(G, A), " | ", q^3+1,
        " | ok? ", IndStar(G, A) = q^3+1, "\n");
od;
for q in [8,32,128] do
  G := SuzukiGroup(q);
  P := SylowSubgroup(G, 2);
  A := Centre(P);
  Print("Sz(", q, ") | ", Size(A), " | ", IsAbelian(A), " | ",
        Index(G, Normalizer(G, A)), " | ", IndStar(G, A), " | ", q^2+1,
        " | ok? ", IndStar(G, A) = q^2+1, "\n");
od;
# For R(q) neither route is in reach in GAP: ReeGroup(q) is returned as a
# 7-dimensional MATRIX group (so there is no point set to stabilise), and the
# Normalizer of Z(Syl_3) in a group of order 10^10 does not terminate.  The
# iota witness for the Ree family is therefore checked ONLY through PART C2
# below, which reads the maximal-subgroup indices of R(27) off CTblLib and
# exhibits m(R(27)) = 19684 = 27^3 + 1 -- together with Borel-Tits this is the
# same statement.  (Recorded explicitly so the gap is visible.)
Print("R(q) : PART B skipped -- see PART C2 (matrix group / infeasible ",
      "Normalizer)\n");

Print("\n### PART C -- EXACT iota over ALL subgroups (no (AB) restriction)\n");
Print("# where the subgroup lattice is in reach\n");
tests := [ ["U3(3)", PSU(3,3), 3^3+1], ["Sz(8)", SuzukiGroup(8), 8^2+1] ];
for t in tests do
  G := t[2];
  cl := ConjugacyClassesSubgroups(G);
  vals := [];
  for c in cl do
    H := Representative(c);
    if Size(H) > 1 then AddSet(vals, IndStar(G, H)); fi;
  od;
  Print(t[1], " : iota = ", vals[1], "   claimed ", t[3],
        "   ok? ", vals[1] = t[3],
        "   iota_2 = ", vals[2],
        "   first 6 of I(S) = ", vals{[1..Minimum(6,Length(vals))]}, "\n");
od;

Print("\n### PART C2 -- minimal degree m(S) (smallest index of a proper\n");
Print("### subgroup) from the maximal subgroups, incl. the U_3(5) exception\n");
for nm in ["U3(3)","U3(4)","U3(5)","U3(7)","U3(8)","U3(9)","U3(11)",
           "Sz(8)","Sz(32)","R(27)"] do
  t := CharacterTable(nm);
  if t = fail or not HasMaxes(t) then
    Print(nm, " : no stored Maxes\n"); continue;
  fi;
  idx := List(Maxes(t), s -> Size(t)/Size(CharacterTable(s)));
  Print(nm, " : maximal-subgroup indices ", SortedList(idx),
        "   m(S) = ", Minimum(idx), "\n");
od;

Print("\n### PART D -- Lemma K analogues (largest prime power dividing |S|)\n");
badU := []; badS := []; badR := [];
for q in Filtered([3..3000], IsPrimePowerInt) do
  N := q^3*(q^2-1)*(q^3+1)/GcdInt(3,q+1);
  m := Maximum(List(Collected(FactorsInt(N)), x -> x[1]^x[2]));
  if m > Maximum(q^3, 2*(q+1)^2) then Add(badU, [q,m]); fi;
od;
Print("U3: violations of ppmax <= max(q^3, 2(q+1)^2), 3 <= q <= 3000: ",
      badU, "\n");
for f in [3,5,7,9,11,13,15,17,19,21,23,25,27,29,31] do
  q := 2^f;
  N := q^2*(q-1)*(q^2+1);
  m := Maximum(List(Collected(FactorsInt(N)), x -> x[1]^x[2]));
  if m > q^2+1 then Add(badS, [q,m]); fi;
od;
Print("Sz: violations of ppmax <= q^2+1, q = 2^f, f odd <= 31: ", badS, "\n");
for f in [3,5,7,9,11,13,15,17,19,21] do
  q := 3^f;
  N := q^3*(q-1)*(q^3+1);
  m := Maximum(List(Collected(FactorsInt(N)), x -> x[1]^x[2]));
  if m > q^3 then Add(badR, [q,m]); fi;
od;
Print("R : violations of ppmax <= q^3, q = 3^f, f odd <= 21: ", badR, "\n");

Print("\n### PART E -- the order coincidence |U_3(q)| = (q+1)*|R(q)|/e\n");
Print("### (found by the python negative control; it is the ONLY order\n");
Print("###  near-coincidence between the three target families)\n");
for f in [3,5,7] do
  q := 3^f;
  Print("q = ", q, " : |U3(q)|/|R(q)| = ",
        (q^3*(q^2-1)*(q^3+1)/GcdInt(3,q+1)) / (q^3*(q-1)*(q^3+1)),
        "   (q+1)/gcd(3,q+1) = ", (q+1)/GcdInt(3,q+1), "\n");
od;
Print("### it is killed because c = (q+1)/e does NOT divide |Out(R(q))| = f.\n");
QUIT;
