# dg_correct.g -- generally-correct replacement for Work_New::DG_G.
#
# WHY. Work_New::DG_G parametrizes the D(G) species rows (H, hH') by the
# N_G(H)-orbits on the ELEMENTS of RightTransversal(H, H'). Element-conjugacy
# only REFINES the correct equivalence -- N_G(H)-orbits on the COSETS H/H' --
# so DG_G can OVERCOUNT rows whenever some subgroup H is nonabelian (H' <> 1).
# It is correct exactly on groups where an a-posteriori squareness/count check
# (#DG-rows = #MG-cols per class) happens to pass; see
# docs/audit_gap_table_algorithm.md sec.2 and the "Correction" note there.
#
# THIS VERSION computes the coset-orbits directly: it acts with N_G(H) on the
# abelianization A = H/H' (a conjugation-induced automorphism action, well
# defined because N_G(H) normalizes the characteristic subgroup H'), and takes
# one preimage element per orbit as the stored fibre. Correct for EVERY finite
# group, with no count check required. For abelian H it reduces to DG_G.
#
# Row format [subgroup, element] and per-class ordering match DG_G exactly
# (same cached ConjugacyClassesSubgroups objects; trivial coset first in each
# H-block), so it is a drop-in replacement in regen_3125.g. The stored element
# is any representative of its coset: the species entry lambda(h^t) depends only
# on hH' (fibre rep-independence lemma, audit sec.2), so the choice is immaterial.

DG_G_coset := function(G)
  local DG, cl, H, N, Hd, pi, A, act, orbs, o, a, h;
  DG := [];
  for cl in ConjugacyClassesSubgroups(G) do
    H  := Representative(cl);
    N  := Normalizer(G, H);
    Hd := DerivedSubgroup(H);
    pi := NaturalHomomorphismByNormalSubgroup(H, Hd);
    A  := Image(pi);
    act := function(pnt, n)
      return Image(pi, PreImagesRepresentative(pi, pnt) ^ n);
    end;
    orbs := Orbits(N, AsList(A), GeneratorsOfGroup(N),
                   GeneratorsOfGroup(N), act);
    # trivial coset (image of 1) first, to preserve the [H,1]-block ordering
    Add(DG, [H, One(G)]);
    for o in orbs do
      if not (One(A) in o) then
        a := o[1];
        h := PreImagesRepresentative(pi, a);
        Add(DG, [H, h]);
      fi;
    od;
  od;
  return DG;
end;
