# v_task81_ree.g
# ADVERSARIAL INDEPENDENT RE-VERIFICATION of the R(27) = ^2G_2(27) rank-1 claim
# from v_task54_rank1_gaps.md section 5.
#
# Claim under test:
#   G := R(27), |G| = 27^3*(27^3+1)*(27-1) = 10073444472
#   P := Syl_3(G), |P| = 27^3 = 19683
#   A := Z(P) elementary abelian of order 27, A' = 1
#   N_G(A) = B (the Borel / point stabiliser of the ovoid), |B| = 19683*26 = 511758
#   [G : N_G(A)] = 19684 = q^3+1
#   ind*(A) = [G:N_G(A)] * |A'| = 19684
#
# This script was written WITHOUT reading v_task54_rank1_gaps.g.
#
# Run: ~/gap-4.16.0/gap -q -o 8g v_task81_ree.g > v_task81_ree_out.txt

SetInfoLevel(InfoWarning, 0);

Sep := function(s)
  Print("\n============================================================\n");
  Print(s, "\n");
  Print("============================================================\n");
end;

Chk := function(name, got, want)
  Print("  ", name, " = ", got);
  if got = want then Print("   [OK, expected ", want, "]\n");
  else Print("   [*** MISMATCH, expected ", want, " ***]\n"); fi;
end;

Sep("STEP 0: arithmetic targets (re-derived, not assumed)");
q     := 27;
ordG  := q^3 * (q^3+1) * (q-1);
ordB  := q^3 * (q-1);
Print("  q                       = ", q, "\n");
Print("  q^3                     = ", q^3, "\n");
Print("  q^3+1                   = ", q^3+1, "\n");
Print("  q^3*(q^3+1)*(q-1)       = ", ordG, "\n");
Print("  q^3*(q-1)               = ", ordB, "\n");
Print("  Factors of |G|          = ", Collected(FactorsInt(ordG)), "\n");
Print("  Factors of q^3+1        = ", Collected(FactorsInt(q^3+1)), "\n");
Print("  3-part of |G|           = 3^", PValuation(ordG, 3), "\n");

Sep("STEP 1: construct G and check its order");
G := ReeGroup(27);
Print("  G                       = ", G, "\n");
Print("  IsMatrixGroup           = ", IsMatrixGroup(G), "\n");
Print("  dim / field             = ", DimensionOfMatrixGroup(G), " / ",
                                      FieldOfMatrixGroup(G), "\n");
Print("  #generators             = ", Length(GeneratorsOfGroup(G)), "\n");
Chk("Size(G) [library value]", Size(G), ordG);

Sep("STEP 2: build the degree-(q^3+1) ovoid action from scratch");
# Capped breadth-first orbit on 1-spaces, so a bad seed cannot blow up memory.
CapOrbit := function(grp, v0, cap)
  local gens, d, orb, i, g, w;
  gens := GeneratorsOfGroup(grp);
  v0 := OnLines(v0, One(grp));
  d := NewDictionary(v0, false);
  orb := [v0]; AddDictionary(d, v0);
  i := 1;
  while i <= Length(orb) do
    for g in gens do
      w := OnLines(orb[i], g);
      if not KnowsDictionary(d, w) then
        Add(orb, w); AddDictionary(d, w);
        if Length(orb) > cap then return fail; fi;
      fi;
    od;
    i := i + 1;
  od;
  return orb;
end;

Print("  capped (60000) line-orbit lengths of the 7 basis vectors:\n");
basorb := [];
for r in [1..7] do
  o := CapOrbit(G, One(G)[r], 60000);
  if o = fail then
    Print("    e", r, " -> > 60000 (aborted)\n"); Add(basorb, fail);
  else
    Print("    e", r, " -> ", Length(o), "\n"); Add(basorb, Length(o));
  fi;
od;

ovoid := CapOrbit(G, One(G)[1], 60000);
ovoid := Set(ovoid);
Chk("|G-orbit of <e1>| (the ovoid)", Length(ovoid), q^3+1);
Print("  <e7> lies in that same orbit? ",
      OnLines(One(G)[7], One(G)) in ovoid, "\n");

Sep("STEP 3: the action is faithful; check 2-transitivity");
hom := ActionHomomorphism(G, ovoid, OnLines, "surjective");
PG  := Image(hom);
Print("  PG is a perm group of degree ", LargestMovedPoint(PG), "\n");
SetSize(PG, Size(PG));  # forces a stabiliser chain
Chk("Size(PG) [stabiliser chain, independent]", Size(PG), ordG);
Print("  kernel of the action is trivial? ", IsTrivial(Kernel(hom)), "\n");
Print("  => action faithful: |G| = |PG| = ", Size(PG), "\n");
Print("  IsTransitive(PG)        = ", IsTransitive(PG, [1..q^3+1]), "\n");

Sep("STEP 4: Sylow 3-subgroup P and A := Z(P)");
P := SylowSubgroup(PG, 3);
Chk("Size(P)", Size(P), q^3);
Print("  Size(P) = 3^", PValuation(Size(P),3),
      "; is that the full 3-part of |G|? ",
      PValuation(Size(P),3) = PValuation(ordG,3), "\n");
Print("  IsSylow (|G|/|P| coprime to 3)? ", (ordG/Size(P)) mod 3 <> 0, "\n");

A := Centre(P);
Chk("Size(A) = |Z(P)|", Size(A), 27);
Print("  IsAbelian(A)            = ", IsAbelian(A), "\n");
Print("  IsElementaryAbelian(A)  = ", IsElementaryAbelian(A), "\n");
Print("  Exponent(A)             = ", Exponent(A), "\n");
Print("  AbelianInvariants(A)    = ", AbelianInvariants(A), "\n");
Print("  IsTrivial(A')           = ", IsTrivial(DerivedSubgroup(A)), "\n");
Print("  |A'|                    = ", Size(DerivedSubgroup(A)), "\n");
Print("  Exponent(P), |P'|, |P/P'| = ", Exponent(P), ", ",
      Size(DerivedSubgroup(P)), ", ", Size(P)/Size(DerivedSubgroup(P)), "\n");

Sep("STEP 5: fixed points of A on the ovoid");
fixA := Filtered([1..q^3+1], i -> ForAll(GeneratorsOfGroup(A), g -> i^g = i));
Print("  Fix(A) = ", fixA, "\n");
Chk("|Fix(A)|", Length(fixA), 1);
fixP := Filtered([1..q^3+1], i -> ForAll(GeneratorsOfGroup(P), g -> i^g = i));
Print("  Fix(P) = ", fixP, "  (|Fix(P)| = ", Length(fixP), ")\n");
Print("  Fix(A) = Fix(P)?        = ", fixA = fixP, "\n");

Sep("STEP 6: the point stabiliser B and its relation to A");
pt := fixA[1];
B  := Stabilizer(PG, pt);
Chk("Size(B) = |G_pt|", Size(B), ordB);
Chk("[G:B]", Index(PG, B), q^3+1);
Print("  orbits of B on the ovoid have lengths ",
      SortedList(List(Orbits(B, [1..q^3+1]), Length)), "\n");
Print("  => PG is 2-transitive?  = ", Length(Orbits(B,[1..q^3+1])) = 2, "\n");
Print("  P <= B ?                = ", IsSubgroup(B, P), "\n");
Print("  P normal in B ?         = ", IsNormal(B, P), "\n");
Print("  A <= B ?                = ", IsSubgroup(B, A), "\n");
Print("  A NORMAL in B ?         = ", IsNormal(B, A), "   (gives B <= N_G(A))\n");
Print("  A = Z(P) recomputed inside B: ", A = Centre(SylowSubgroup(B,3)), "\n");
Print("  B/P cyclic of order ", Size(B)/Size(P), " ? IsCyclic = ",
      IsCyclic(B/P), "\n");

Sep("STEP 7: N_G(A) computed directly (the load-bearing step)");
N := Normalizer(PG, A);
Print("  Size(N_G(A))            = ", Size(N), "\n");
Chk("Size(N_G(A))", Size(N), ordB);
Chk("[G : N_G(A)]", Index(PG, N), q^3+1);
Print("  N = B ?                 = ", N = B, "\n");
Print("  N <= B ?                = ", IsSubgroup(B, N), "\n");
Print("  B <= N ?                = ", IsSubgroup(N, B), "\n");

Sep("STEP 8: the ind* number");
indstar := Index(PG, N) * Size(DerivedSubgroup(A));
Print("  [G:N_G(A)]              = ", Index(PG, N), "\n");
Print("  |A'|                    = ", Size(DerivedSubgroup(A)), "\n");
Chk("ind*(A) = [G:N_G(A)]*|A'|", indstar, q^3+1);
Print("  q^3+1                   = ", q^3+1, "\n");
Print("  ind*(A) = q^3+1 ?       = ", indstar = q^3+1, "\n");

Sep("STEP 9: adversarial extras");
# Is A the UNIQUE minimal normal-ish candidate?  Check A is characteristic in P
# (so N_G(P) <= N_G(A)) and check N_G(P).
NP := Normalizer(PG, P);
Print("  Size(N_G(P))            = ", Size(NP), "\n");
Print("  N_G(P) = B ?            = ", NP = B, "\n");
Print("  |G| / |B|               = ", ordG/ordB, "\n");
# NOT VERIFIED HERE: the LOWER bound (that no proper subgroup of G has index
# < q^3+1, equivalently that the minimal faithful permutation degree of R(27)
# is q^3+1).  That is literature input [Ward 1966]; MaximalSubgroupClassReps
# on a degree-19684 group of order ~10^10 is out of reach.  This script
# therefore establishes only the UPPER bound ind*(A) = q^3+1, i.e. a witness
# for iota(R(27)) <= 19684 -- which is exactly what the claim asserts.
Print("  [NOT CHECKED HERE] minimality of the index q^3+1 (lower bound)\n");
Print("  => this script certifies the UPPER bound only: iota <= ",
      q^3+1, "\n");
# A is elementary abelian so ind*(A) cannot be reduced by the |A'| factor.
Print("  A is elem. abelian => |A'| = 1 => ind*(A) = [G:N_G(A)] exactly\n");

Sep("STEP 10: chain of custody -- the literal claimed object Z(Syl_3(G))");
# Steps 4-8 built A inside the PERMUTATION group.  The claim is literally
# about A = Z(Syl_3(G)) computed in the matrix group G.  Redo it that way
# and push it through hom, so nothing rests on 'conjugate, hence same index'.
Pm := SylowSubgroup(G, 3);
Chk("Size(Syl_3(G)) in the matrix group", Size(Pm), q^3);
Am := Centre(Pm);
Chk("Size(Z(Syl_3(G))) in the matrix group", Size(Am), 27);
Print("  IsElementaryAbelian            = ", IsElementaryAbelian(Am), "\n");
A0 := Image(hom, Am);
Chk("Size of its permutation image", Size(A0), 27);
fix0 := Filtered([1..q^3+1], i -> ForAll(GeneratorsOfGroup(A0), g -> i^g = i));
Chk("|Fix_ovoid(Z(Syl_3(G)))|", Length(fix0), 1);
N0 := Normalizer(PG, A0);
Chk("Size(N_G(Z(Syl_3(G))))", Size(N0), ordB);
Chk("[G : N_G(Z(Syl_3(G)))]", Index(PG, N0), q^3+1);
Print("  N_G(A0) = Stab(Fix(A0)) ?      = ",
      N0 = Stabilizer(PG, fix0[1]), "\n");
Chk("ind*(A0) = [G:N_G(A0)]*|A0'|",
    Index(PG, N0) * Size(DerivedSubgroup(A0)), q^3+1);

Sep("DONE");
QUIT;
