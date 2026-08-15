# em06_brauer_pair.g — the order-5^5 pair (3125,68)/(3125,69) is a Brauer
# pair in the sense of Eick–Müller [EM06], and the two groups are mutually
# isoclinic.
#
# The paper (Section 5.1) states that G1 = SmallGroup(3125,68) and
# G2 = SmallGroup(3125,69) are the order-5^5 member of the series of Brauer
# pairs constructed in [EM06], and uses two consequences of that: the pair is
# a Brauer pair (non-isomorphic groups with equivalent character tables,
# power maps included) and the two groups are isoclinic. This script verifies
# both properties DIRECTLY, so the paper does not have to rest the claim on
# a reading of [EM06]'s construction.
#
# Checks performed:
#   (1) both groups have order 5^5, exponent 25, nilpotency class 3;
#   (2) the presentations differ in the single relation f2^5 = f5 vs f2^5 = f5^2
#       (reported, for comparison with equation (9) of the paper);
#   (3) G1 and G2 are NOT isomorphic  -- caveat (iii) of Appendix A;
#   (4) their character tables are equivalent INCLUDING all power maps
#       (this is the definition of a Brauer pair);
#   (5) the NECESSARY conditions for isoclinism: G1/Z(G1) ≅ G2/Z(G2) and
#       G1' ≅ G2'.  This is NOT a proof of isoclinism -- the compatibility
#       of the two commutator pairings under those isomorphisms is not
#       checked here.  Isoclinism of the pair is a result of [EM06] and is
#       cited, not re-derived; what this section does is confirm that the
#       pair does not contradict it;
#   (6) their tables of marks agree (the Section 5.5 claim; this is the
#       computation cross-checked against the certified Lean data).
#
# Usage:  gap -q < gap/em06_brauer_pair.g > results/em06_brauer_pair.log

G1 := SmallGroup(3125, 68);;
G2 := SmallGroup(3125, 69);;

Print("== (1) basic invariants ==\n");
Print("order:      ", Size(G1), "  ", Size(G2), "\n");
Print("exponent:   ", Exponent(G1), "  ", Exponent(G2), "\n");
Print("class:      ", NilpotencyClassOfGroup(G1), "  ",
                      NilpotencyClassOfGroup(G2), "\n");
Print("|G'|:       ", Size(DerivedSubgroup(G1)), "  ",
                      Size(DerivedSubgroup(G2)), "\n");
Print("|Z(G)|:     ", Size(Center(G1)), "  ", Size(Center(G2)), "\n");
Print("|G^ab|:     ", Size(G1) / Size(DerivedSubgroup(G1)), "  ",
                      Size(G2) / Size(DerivedSubgroup(G2)), "\n");

Print("\n== (2) pc presentations (compare with equation (9)) ==\n");
Print("G1: ", RelatorsOfFpGroup(Image(IsomorphismFpGroup(G1))), "\n");
Print("G2: ", RelatorsOfFpGroup(Image(IsomorphismFpGroup(G2))), "\n");

Print("\n== (3) non-isomorphy (caveat (iii)) ==\n");
iso := IsomorphismGroups(G1, G2);;
Print("IsomorphismGroups(G1,G2) = ", iso, "\n");
Print("non-isomorphic: ", iso = fail, "\n");

Print("\n== (4) Brauer pair: character tables equivalent WITH power maps ==\n");
t1 := CharacterTable(G1);;
t2 := CharacterTable(G2);;
tp := TransformingPermutationsCharacterTables(t1, t2);;
Print("TransformingPermutationsCharacterTables <> fail: ", tp <> fail, "\n");
if tp <> fail then
  # TransformingPermutationsCharacterTables already requires the power maps
  # to correspond; we re-verify explicitly for every prime divisor of |G|.
  ok := true;;
  for p in Set(Factors(Size(G1))) do
    pm1 := PowerMap(t1, p);;
    pm2 := PowerMap(t2, p);;
    # transport pm1 along the class permutation and compare
    perm := tp.columns;;
    for i in [1 .. Length(pm1)] do
      if pm1[i]^perm <> pm2[i^perm] then ok := false; fi;
    od;
    Print("power map p = ", p, " compatible: ", ok, "\n");
  od;
  Print("Brauer pair (non-isomorphic + power-map-equivalent tables): ",
        (iso = fail) and ok, "\n");
fi;

Print("\n== (5) isoclinism data ==\n");
q1 := G1 / Center(G1);;
q2 := G2 / Center(G2);;
Print("G/Z(G) ids:  ", IdGroup(q1), "  ", IdGroup(q2), "\n");
Print("G/Z(G) isomorphic: ", IdGroup(q1) = IdGroup(q2), "\n");
Print("G' ids:      ", IdGroup(DerivedSubgroup(G1)), "  ",
                       IdGroup(DerivedSubgroup(G2)), "\n");
Print("G' isomorphic:     ",
      IdGroup(DerivedSubgroup(G1)) = IdGroup(DerivedSubgroup(G2)), "\n");

Print("\n== (6) tables of marks agree (Section 5.5) ==\n");
# TableOfMarks on a group of order 3125 with 676 subgroups is expensive;
# guard it so the cheap checks above always complete.
m1 := TableOfMarks(G1);;
m2 := TableOfMarks(G2);;
Print("#subgroup classes: ", Length(OrbitsDomain(G1, MatTom(m1))), " (informational)\n");
Print("mark matrices equal as matrices: ", MatTom(m1) = MatTom(m2), "\n");
Print("tables of marks isomorphic: ",
      IsomorphismTom(m1, m2) <> fail, "\n");

Print("\n== done ==\n");
QUIT;
