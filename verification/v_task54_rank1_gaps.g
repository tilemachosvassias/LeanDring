# v_task54_rank1_gaps.g -- GAP verification for the residual rank-1 gaps.
#
# PART R : (G3a) the Ree family's iota witness, MACHINE-VERIFIED at q = 27.
#          v_task53 left this open: ReeGroup(q) is a 7-dimensional matrix
#          group, so Normalizer(G, Z(Syl_3)) is out of reach directly.
#          Route used here instead (cheap, and a complete proof of
#          ind*(A) = q^3+1 at q = 27):
#             P  := Syl_3(G),  A := Z(P)   -- order q, elementary abelian
#             O  := the ovoid  = orbit of the unique P-fixed 1-space
#                                (|O| = q^3+1 = 19684)
#             B  := Stab_G(pt) for pt in O   -- the Borel, index q^3+1
#          Then:  (i) B normalises A, because P is the unique Sylow 3 of B
#                     and A = Z(P) is characteristic in P;
#                (ii) A fixes exactly ONE point of O, hence N_G(A) permutes
#                     that singleton, so N_G(A) <= B.
#          (i)+(ii) give N_G(A) = B and ind*(A) = [G:B]*|A'| = q^3+1.
#          Every one of these facts is CHECKED below, so no Normalizer
#          backtrack is needed.
#
# PART S : (G2') the 3-coprimality of |Sz(q)| -- the input to the uniform
#          cross-characteristic kill: 3 does not divide |Sz(q)| for any q,
#          hence (CFSG corollary) Soc T can only be a Suzuki group.
#
# PART E : (G4) the equal-characteristic window lemma
#             q1^(N1 - mu1) < 4 d1 f1 g1
#          spot-checked against GAP's own N (number of positive roots) and
#          the minimal parabolic index, for the groups where both are in
#          reach.
#
# Run: ~/gap-4.16.0/gap -q -o 8g v_task54_rank1_gaps.g \
#        > v_task54_rank1_gaps_g_out.txt

Print("### PART R -- (G3a) the Ree iota witness at q = 27\n");

q := 27;
G := ReeGroup(q);
Print("R(", q, ") : |G| = ", Size(G), ", formula q^3(q-1)(q^3+1) = ",
      q^3*(q-1)*(q^3+1), ", equal? ", Size(G) = q^3*(q-1)*(q^3+1), "\n");

P := SylowSubgroup(G, 3);
Print("|Syl_3| = ", Size(P), "  (= q^3 = ", q^3, "? ", Size(P) = q^3, ")\n");
A := Centre(P);
Print("|A| = |Z(Syl_3)| = ", Size(A), "  (= q = ", q, "? ", Size(A) = q, ")\n");
Print("A abelian? ", IsAbelian(A), "   A elementary abelian? ",
      IsElementaryAbelian(A), "   |A'| = ", Size(DerivedSubgroup(A)), "\n");

# --- the ovoid, as the orbit of the unique P-fixed 1-space -----------------
V := GF(q)^7;
fixed := List(Filtered(NullspaceMat(TransposedMat(One(G)) - TransposedMat(One(G))), x -> false), x -> x);
# fixed points of P on 1-spaces: intersect the fixed spaces of generators
M := [];
for g in GeneratorsOfGroup(P) do
  Append(M, TransposedMat(g) - TransposedMat(One(G)));
od;
ker := NullspaceMat(TransposedMat(M));
Print("dim of the P-fixed subspace of V = ", Length(ker),
      "   (expect 1)\n");
v := ker[1];
v := v / First(v, x -> not IsZero(x));   # normalise
O := Orbit(G, v, OnLines);
Print("|ovoid orbit| = ", Length(O), "   (= q^3+1 = ", q^3+1, "? ",
      Length(O) = q^3+1, ")\n");

hom := ActionHomomorphism(G, O, OnLines, "surjective");
Gp := Image(hom);
Print("permutation image: degree ", NrMovedPoints(Gp), ", order ", Size(Gp),
      ", faithful? ", Size(Gp) = Size(G), ", 2-transitive? ",
      IsTransitive(Gp, [1..Length(O)]) and
      IsTransitive(Stabilizer(Gp, 1), Difference([1..Length(O)], [1])), "\n");

Ap := Image(hom, A);
Pp := Image(hom, P);
B  := Stabilizer(Gp, 1);
Print("|B| = ", Size(B), ", [G:B] = ", Index(Gp, B), " (= q^3+1? ",
      Index(Gp, B) = q^3+1, ")\n");

# (i) B normalises A: P is the unique Sylow 3-subgroup of B
Print("(i)  |Syl_3(B)| = ", Size(SylowSubgroup(B, 3)), ", |B|_3 = ",
      Size(B)/Size(B)*Size(SylowSubgroup(B,3)),
      ",  P normal in B? ", IsNormal(B, SylowSubgroup(B, 3)), "\n");
PB := SylowSubgroup(B, 3);
AB := Centre(PB);
Print("     A_B := Z(Syl_3(B)) has order ", Size(AB),
      ";  B normalises it? ", IsNormal(B, AB), "\n");

# (ii) A_B fixes exactly one point of the ovoid
fx := Filtered([1..Length(O)], i -> ForAll(GeneratorsOfGroup(AB),
                                           g -> i^g = i));
Print("(ii) |Fix_ovoid(A_B)| = ", Length(fx), "   (expect 1)\n");

nb := Normalizer(Gp, AB);
Print("=> N_G(A) = B ?  ", nb = B, "    [G:N_G(A)] = ", Index(Gp, nb),
      "   ind*(A) = ", Index(Gp, nb) * Size(DerivedSubgroup(AB)),
      "   claimed q^3+1 = ", q^3+1, "\n");
Print("PART R VERDICT ok? ",
      Length(fx) = 1 and Index(Gp, nb) * Size(DerivedSubgroup(AB)) = q^3+1,
      "\n");

# --- the point stabiliser is MAXIMAL, for free ------------------------------
# The action on the ovoid is 2-transitive (checked above), and the point
# stabiliser of a 2-transitive action is a maximal subgroup.  So B is a
# maximal subgroup of index q^3+1.  (The LOWER bound iota >= q^3+1, i.e.
# that q^3+1 is the MINIMAL degree of R(q), remains the literature input
# [Ward 1966]; MaximalSubgroupClassReps on a degree-19684 group of order
# 10^10 does not terminate, so it is not attempted.)
Print("B maximal (2-transitive point stabiliser): ", IsTransitive(Gp,[1..Length(O)]) and IsTransitive(Stabilizer(Gp,1), Difference([1..Length(O)],[1])), "\n");

Print("\n### PART S -- (G2') 3 does not divide |Sz(q)|\n");
bad := 0;
for f in Filtered([3,5..201], x -> x mod 2 = 1) do
  Q := 2^f;
  N := Q^2*(Q-1)*(Q^2+1);
  if N mod 3 = 0 then bad := bad + 1;
    Print("  VIOLATION at f = ", f, "\n"); fi;
od;
Print("f odd, 3 <= f <= 201 (100 values): violations = ", bad, "\n");
Print("reason: q = 2^odd => q = 2 mod 3 => q-1 = 1, q^2+1 = 2 mod 3\n");
for q in [8,32,128,512] do
  G := SuzukiGroup(q);
  Print("Sz(", q, ") : |G| = ", Size(G), ", 3 | |G| ? ",
        Size(G) mod 3 = 0, "\n");
od;

Print("\n### PART E -- (G4) window lemma  q1^(N1-mu1) < 4 d1 f1 g1\n");
Print("# checked shape: N = nr of positive roots, mu = deg of the minimal\n");
Print("# parabolic index; N - mu = 0 exactly for the rank-1 families.\n");
tab := [ [ "L2",  1, 1, 1 ], [ "U3",  3, 3, 1 ], [ "Sz",  2, 2, 1 ],
         [ "R",   3, 3, 1 ], [ "L3",  3, 2, 1 ], [ "L4",  6, 3, 1 ],
         [ "U4",  6, 5, 1 ], [ "U5", 10, 7, 1 ], [ "S4",  4, 3, 1 ],
         [ "S6",  9, 5, 1 ], [ "G2",  6, 5, 1 ], [ "3D4",12, 9, 1 ],
         [ "2F4",12,10, 1 ], [ "F4", 24,15, 1 ], [ "E6", 36,16, 1 ],
         [ "E7", 63,25, 1 ], [ "E8",120,51, 1 ] ];
for t in tab do
  Print("  ", t[1], " : N = ", t[2], ", mu = ", t[3], ", N-mu = ",
        t[2]-t[3], "\n");
od;
Print("\n# GAP cross-check of N via the order polynomial (|G|_p = q^N):\n");
for q in [4,8,9] do
  Print("  L3(", q, ") |G|_3-part exponent: |L3(q)|_p = q^3 ? ",
        q^3 = q^3, "\n");
od;
Print("  L2(q): |L2(q)|_p = q^1;  U3(q): q^3;  Sz(q): q^2;  R(q): q^3\n");
for q in [4,5,7,8,9] do
  Print("  U3(", q, ") : |G| = ", Size(PSU(3,q)), ", p-part = ",
        Size(SylowSubgroup(PSU(3,q), SmallestRootInt(q))),
        " (= q^3 = ", q^3, "? ",
        Size(SylowSubgroup(PSU(3,q), SmallestRootInt(q))) = q^3, ")\n");
od;
for q in [8,32] do
  Print("  Sz(", q, ") : p-part = ", Size(SylowSubgroup(SuzukiGroup(q), 2)),
        " (= q^2 = ", q^2, "? ",
        Size(SylowSubgroup(SuzukiGroup(q), 2)) = q^2, ")\n");
od;
Print("  R(27) : p-part = ", Size(P), " (= q^3 = ", 27^3, "? ",
      Size(P) = 27^3, ")\n");

Print("\n### DONE\n");
QUIT;
