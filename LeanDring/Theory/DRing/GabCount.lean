/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Theory.DRing.Unipotent
import LeanDring.Theory.DRing.Bridge
import LeanDring.Theory.DRing.BridgeTransport
import LeanDring.Theory.DRing.BridgeCounts
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic

-- The `[Fintype _]` binders below are unused in several *statements* but are
-- load-bearing in their *proofs* (instance synthesis for cardinality and basis
-- constructions), so they cannot be `omit`ted.  The linter's suggested rewrite
-- to `[Finite _]` + `Fintype.ofFinite` is a genuine refactor, not a cleanup.
set_option linter.unusedFintypeInType false

/-!
# Counting the torsion units: `|UT(D(G))| = 2·|G^ab|`

The `G^ab` payoff of Satz 2.6.3. Two ingredients:

* `card_charHom_eq_card_abelianization` — finite-abelian duality:
  `|Ĝ| = |Hom(G, ℂˣ)| = |G^ab|` (via Mathlib's Pontryagin count for
  groups with enough roots of unity, ℂ being algebraically closed);
* `card_torsionUnits_eq` — under the normalizer-growth hypothesis, the
  torsion units of `D(G)` are exactly `±Ĝ`, an explicit `Bool × Ĝ`, so
  `|UT(D(G))| = 2·|G^ab|`.

This is the table-transportable invariant that separates abelian from
non-abelian groups of the same order (`p⁴` vs `≤ p³`).
-/

namespace LeanDring

open Finset MulAction MonGSet

universe u

namespace DRing

variable {G : Type u} [Group G] [Fintype G]

/-! ## Finite-abelian duality: `|Hom(G, ℂˣ)| = |G^ab|` -/

-- The `Fintype G` binder is kept rather than `omit`ted: this signature is the
-- paper-facing statement audited in `LeanDring/AxiomAudit.lean`.
/-- **Finite-abelian duality**: `|Hom(G, ℂˣ)| = |G^ab|`. Characters of `G`
factor through the abelianization, and `ℂ` (algebraically closed) has
enough roots of unity for Pontryagin counting. -/
theorem card_charHom_eq_card_abelianization :
    Nat.card (G →* ℂˣ) = Nat.card (Abelianization G) := by
  haveI : Finite G := Finite.of_fintype G
  haveI : Finite (Abelianization G) := Quotient.finite _
  haveI : NeZero ((Monoid.exponent (Abelianization G) : ℂ)) :=
    ⟨by exact_mod_cast Monoid.exponent_ne_zero_of_finite⟩
  haveI : HasEnoughRootsOfUnity ℂ (Monoid.exponent (Abelianization G)) :=
    IsSepClosed.hasEnoughRootsOfUnity ℂ _
  rw [Nat.card_congr Abelianization.lift]
  exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (Abelianization G) ℂ

/-! ## The torsion units are `±Ĝ` -/

/-- A unit of `D(G)` is torsion if some positive power is `1`. -/
def IsTorsionUnit (u : (DRing G)ˣ) : Prop := ∃ n : ℕ, 0 < n ∧ u ^ n = 1

/-- The `±Ĝ` parametrization of the torsion units: `(s, λ) ↦ ±[G, λ]`. -/
noncomputable def pmUnit (s : Bool) (l : G →* ℂˣ) : (DRing G)ˣ :=
  cond s (unitsHom l) (-unitsHom l)

omit [Fintype G] in
theorem pmUnit_val (s : Bool) (l : G →* ℂˣ) :
    (pmUnit s l : DRing G) = cond s (charElt l) (-charElt l) := by
  cases s <;> rfl

/-- The character units are annihilated by `|G|`. -/
theorem unitsHom_pow_card (l : G →* ℂˣ) :
    (unitsHom l) ^ Nat.card G = 1 := by
  have hl1 : l ^ Nat.card G = 1 := by
    refine MonoidHom.ext fun g => ?_
    rw [MonoidHom.pow_apply, ← map_pow, Nat.card_eq_fintype_card,
      pow_card_eq_one, map_one, MonoidHom.one_apply]
  rw [← map_pow, hl1, map_one]

theorem isTorsionUnit_pmUnit (s : Bool) (l : G →* ℂˣ) :
    IsTorsionUnit (pmUnit s l) := by
  cases s with
  | true => exact ⟨Nat.card G, Nat.card_pos, unitsHom_pow_card l⟩
  | false =>
    refine ⟨2 * Nat.card G, by have := Nat.card_pos (α := G); omega, ?_⟩
    change (-unitsHom l) ^ (2 * Nat.card G) = 1
    rw [Even.neg_pow (even_two_mul _), two_mul, pow_add, unitsHom_pow_card,
      one_mul]

/-- The parametrization lands in the torsion units. -/
noncomputable def pmMap (p : Bool × (G →* ℂˣ)) :
    {u : (DRing G)ˣ // IsTorsionUnit u} :=
  ⟨pmUnit p.1 p.2, isTorsionUnit_pmUnit p.1 p.2⟩

omit [Fintype G] in
/-- Positive and negative character units never coincide (the augmentation
species separates `+1` from `-1`). -/
theorem charElt_ne_neg_charElt (l m : G →* ℂˣ) : charElt l ≠ -charElt m := by
  intro h
  have hs := congrArg (species ⊤ ⟨1, trivial⟩) h
  rw [species_charElt, map_neg, species_charElt] at hs
  simp only [map_one, Units.val_one] at hs
  norm_num at hs

theorem pmMap_injective : Function.Injective (pmMap (G := G)) := by
  rintro ⟨s, l⟩ ⟨t, m⟩ h
  have hval : (pmUnit s l : DRing G) = (pmUnit t m : DRing G) :=
    congrArg (fun u => (u.1 : DRing G)) h
  rw [pmUnit_val, pmUnit_val] at hval
  have hlm : l = m ∧ s = t := by
    cases s <;> cases t <;> simp only [cond_true, cond_false] at hval
    · -- (false, false): `-charElt l = -charElt m`
      refine ⟨unitsHom_injective (Units.ext ?_), rfl⟩
      exact neg_injective hval
    · -- (false, true): `-charElt l = charElt m`
      exact absurd (charElt_ne_neg_charElt m l) (by rw [← hval]; simp)
    · -- (true, false): `charElt l = -charElt m`
      exact absurd hval (charElt_ne_neg_charElt l m)
    · -- (true, true): `charElt l = charElt m`
      exact ⟨unitsHom_injective (Units.ext hval), rfl⟩
  obtain ⟨hl, hst⟩ := hlm
  exact Prod.ext hst hl

theorem pmMap_surjective
    (hmass : ∀ K : Subgroup G, Nat.card K < Nat.card G →
      3 ≤ Nat.card (fixedPoints K (G ⧸ K))) :
    Function.Surjective (pmMap (G := G)) := by
  rintro ⟨u, n, hn, hu⟩
  have huval : (u : DRing G) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
  obtain ⟨l, hl⟩ := torsion_unit_eq_pm_charElt hmass hn huval
  rcases hl with h | h
  · refine ⟨(true, l), ?_⟩
    refine Subtype.ext (Units.ext ?_)
    rw [pmMap]; exact h.symm ▸ rfl
  · refine ⟨(false, l), ?_⟩
    refine Subtype.ext (Units.ext ?_)
    change (pmUnit false l : DRing G) = (u : DRing G)
    rw [pmUnit_val]; exact h.symm

-- The `Fintype G` binder is kept rather than `omit`ted: this signature is the
-- paper-facing statement audited in `LeanDring/AxiomAudit.lean`.
/-- **The torsion-unit count**: under the normalizer-growth hypothesis, the
torsion units of `D(G)` are exactly `±Ĝ`, hence `|UT(D(G))| = 2·|G^ab|`. -/
theorem card_torsionUnits_eq
    (hmass : ∀ K : Subgroup G, Nat.card K < Nat.card G →
      3 ≤ Nat.card (fixedPoints K (G ⧸ K))) :
    Nat.card {u : (DRing G)ˣ // IsTorsionUnit u} =
      2 * Nat.card (Abelianization G) := by
  rw [← Nat.card_eq_of_bijective pmMap
    ⟨pmMap_injective, pmMap_surjective hmass⟩, Nat.card_prod,
    card_charHom_eq_card_abelianization,
    show Nat.card Bool = 2 from by rw [Nat.card_eq_fintype_card, Fintype.card_bool]]

/-- **The torsion-unit count for `p`-groups, `p ≥ 3`**:
`|UT(D(G))| = 2·|G^ab|`. -/
theorem card_torsionUnits_eq_of_pgroup {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p)
    {t : ℕ} (hcard : Nat.card G = p ^ t) :
    Nat.card {u : (DRing G)ˣ // IsTorsionUnit u} =
      2 * Nat.card (Abelianization G) :=
  card_torsionUnits_eq (mass_ge_three_of_pgroup hp3 hcard)

/-! ## Transport of `|G^ab|` along a species-table isomorphism -/

variable {G' : Type u} [Group G'] [Fintype G']

/-- A ring isomorphism of D-rings restricts to an equivalence of their
torsion units (torsion is a purely multiplicative property). -/
noncomputable def torsionUnitEquivOfRingEquiv (φ : DRing G ≃+* DRing G') :
    {u : (DRing G)ˣ // IsTorsionUnit u} ≃
      {u' : (DRing G')ˣ // IsTorsionUnit u'} :=
  (Units.mapEquiv φ.toMulEquiv).toEquiv.subtypeEquiv fun u => by
    change IsTorsionUnit u ↔ IsTorsionUnit (Units.mapEquiv φ.toMulEquiv u)
    constructor
    · rintro ⟨n, hn, hu⟩
      exact ⟨n, hn, by rw [← map_pow, hu, map_one]⟩
    · rintro ⟨n, hn, hu⟩
      refine ⟨n, hn, (Units.mapEquiv φ.toMulEquiv).injective ?_⟩
      rw [map_pow, map_one]; exact hu

/-- A species-table isomorphism induces a ring isomorphism `D(G) ≃+* D(G′)`
(the certificate bridge applied to its row bijection). -/
noncomputable def SpeciesTableIso.toDRingEquiv (T : SpeciesTableIso G G') :
    DRing G ≃+* DRing G' :=
  equivOfSpeciesMatch T.rows fun H' h' =>
    ⟨T.sub' H', T.el' h', fun c => by
      have hkey := T.entry' H' h' (T.rows c)
      rw [Equiv.symm_apply_apply] at hkey
      exact hkey.symm⟩

open MulAction in
/-- **`|G^ab|` is a species-table invariant**: table-isomorphic groups (both
satisfying the normalizer-growth hypothesis) have equal abelianization
orders. Their D-rings are isomorphic, hence carry equally many torsion
units, and each count is `2·|G^ab|`. -/
theorem card_abelianization_eq_of_speciesTableIso (T : SpeciesTableIso G G')
    (hmass : ∀ K : Subgroup G, Nat.card K < Nat.card G →
      3 ≤ Nat.card (fixedPoints K (G ⧸ K)))
    (hmass' : ∀ K' : Subgroup G', Nat.card K' < Nat.card G' →
      3 ≤ Nat.card (fixedPoints K' (G' ⧸ K'))) :
    Nat.card (Abelianization G) = Nat.card (Abelianization G') := by
  have hcard : Nat.card {u : (DRing G)ˣ // IsTorsionUnit u} =
      Nat.card {u' : (DRing G')ˣ // IsTorsionUnit u'} :=
    Nat.card_congr (torsionUnitEquivOfRingEquiv T.toDRingEquiv)
  rw [card_torsionUnits_eq hmass, card_torsionUnits_eq hmass'] at hcard
  omega

/-- **`|G^ab|` separates `p`-group species tables** (`p ≥ 3`): table-isomorphic
`p`-groups have equal abelianization orders — so abelian and non-abelian
`p⁴`-groups (`|G^ab| = p⁴` vs `≤ p³`) can never share a species table. -/
theorem card_abelianization_eq_of_speciesTableIso_of_pgroup {p : ℕ}
    [Fact p.Prime] (hp3 : 3 ≤ p) {s t : ℕ} (hcard : Nat.card G = p ^ s)
    (hcard' : Nat.card G' = p ^ t) (T : SpeciesTableIso G G') :
    Nat.card (Abelianization G) = Nat.card (Abelianization G') :=
  card_abelianization_eq_of_speciesTableIso T
    (mass_ge_three_of_pgroup hp3 hcard) (mass_ge_three_of_pgroup hp3 hcard')

/-! ## The consolidated species-table criteria

Everything a species-table isomorphism between two `p`-groups provably
forces, bundled. A `D ⇒ B` counterexample — two non-isomorphic groups
sharing a species table — must satisfy **all** of these simultaneously;
this is the checklist the `p⁴`/`5⁵` analysis works against. -/

/-- The numeric invariants shared by two groups with isomorphic species
tables: equal order, equal subgroup counts in every order, and equal
abelianization order. -/
structure SharedSpeciesInvariants (G G' : Type u) [Group G] [Fintype G]
    [Group G'] [Fintype G'] : Prop where
  /-- The groups have the same order. -/
  card_eq : Nat.card G = Nat.card G'
  /-- The groups have the same number of subgroups of every order. -/
  subgroup_count_eq : ∀ n : ℕ,
    Nat.card {L : Subgroup G // Nat.card L = n} =
      Nat.card {L' : Subgroup G' // Nat.card L' = n}
  /-- The groups have the same abelianization order. -/
  abelianization_card_eq :
    Nat.card (Abelianization G) = Nat.card (Abelianization G')

/-- **All proven species-table criteria at once** (`p`-groups, `p ≥ 3`): a
species-table isomorphism forces equal order, equal subgroup counts per
order, and equal abelianization order. Contrapositive: any two `p`-groups
differing in *any* of these three invariants have non-isomorphic species
tables. -/
theorem sharedSpeciesInvariants_of_pgroup {p : ℕ} [Fact p.Prime]
    (hp3 : 3 ≤ p) {s t : ℕ} (hcard : Nat.card G = p ^ s)
    (hcard' : Nat.card G' = p ^ t) (T : SpeciesTableIso G G') :
    SharedSpeciesInvariants G G' where
  card_eq := T.card_eq
  subgroup_count_eq := T.card_subgroups_eq
  abelianization_card_eq :=
    card_abelianization_eq_of_speciesTableIso_of_pgroup hp3 hcard hcard' T

open MulAction in
/-- The consolidated criteria under the bare normalizer-growth hypotheses
(the general form behind `sharedSpeciesInvariants_of_pgroup`). -/
theorem sharedSpeciesInvariants (T : SpeciesTableIso G G')
    (hmass : ∀ K : Subgroup G, Nat.card K < Nat.card G →
      3 ≤ Nat.card (fixedPoints K (G ⧸ K)))
    (hmass' : ∀ K' : Subgroup G', Nat.card K' < Nat.card G' →
      3 ≤ Nat.card (fixedPoints K' (G' ⧸ K'))) :
    SharedSpeciesInvariants G G' where
  card_eq := T.card_eq
  subgroup_count_eq := T.card_subgroups_eq
  abelianization_card_eq :=
    card_abelianization_eq_of_speciesTableIso T hmass hmass'

/-! ## The species-rigidity certificate (the `5⁵`-counterexample form)

A *species-rigidity counterexample* is a pair of non-isomorphic groups whose
species tables are isomorphic — witnessing that the species table (hence the
`D`-ring) does not determine the group. The `5⁵` pair
`(3125, 68)/(3125, 69)` is the intended instance.

The **checking algorithm** is: (i) find a species-table isomorphism `T`
(a row bijection matching every species column) and (ii) verify the groups
are non-isomorphic. The theorems below are its **soundness**: from those two
externally-supplied facts, the `D`-ring isomorphism and all shared invariants
follow as proofs. (Producing `T` and the non-isomorphism at order `3125` is a
finite external computation — GAP — not an in-kernel search; the structural
proof that the entries match is the Gauss-sum argument.) -/

/-- A **certificate** for the failure of species-table rigidity: a
species-table isomorphism together with a witness that the groups are not
isomorphic. -/
structure SpeciesRigidityWitness (G G' : Type u) [Group G] [Fintype G]
    [Group G'] [Fintype G'] where
  /-- The species tables match. -/
  tableIso : SpeciesTableIso G G'
  /-- The groups are not isomorphic. -/
  notIso : G ≃* G' → False

/-- **Soundness, part 1**: a species-rigidity witness produces a genuine
ring isomorphism `D(G) ≃+* D(G′)` — the tables matching really does force the
`D`-rings isomorphic, even though the groups differ. -/
theorem SpeciesRigidityWitness.dringEquiv (w : SpeciesRigidityWitness G G') :
    Nonempty (DRing G ≃+* DRing G') :=
  ⟨w.tableIso.toDRingEquiv⟩

/-- **Soundness, part 2** (`p`-groups, `p ≥ 3`): a witness certifies that two
*non-isomorphic* groups share every proven species invariant — the precise
sense in which the species table fails to determine the group. -/
theorem SpeciesRigidityWitness.sound_of_pgroup {p : ℕ} [Fact p.Prime]
    (hp3 : 3 ≤ p) {s t : ℕ} (hcard : Nat.card G = p ^ s)
    (hcard' : Nat.card G' = p ^ t) (w : SpeciesRigidityWitness G G') :
    Nonempty (DRing G ≃+* DRing G') ∧ SharedSpeciesInvariants G G' ∧
      (G ≃* G' → False) :=
  ⟨w.dringEquiv,
    sharedSpeciesInvariants_of_pgroup hp3 hcard hcard' w.tableIso, w.notIso⟩

/-! ## The `p = 2` frontier (toward order `2⁹`)

At `p = 2` the abelianization criterion is **unavailable**: it rests on
`UT(D(G)) = ±Ĝ`, whose normalizer-growth hypothesis `|N(K):K| ≥ 3` can fail
(a `2`-group can have `|N(K):K| = 2`) — this is the known `p = 2` obstruction.
What *does* survive at every prime, with no mass hypothesis, is the pair of
purely table-theoretic invariants below. Together with the prime-agnostic
`SpeciesRigidityWitness.dringEquiv`, this is the complete toolkit a `2⁹`
counterexample (if one exists — the smallest order not yet ruled out) would be
checked against; the search itself is external (Weisfeiler–Leman on the
`2`-groups of order `512`), not an in-kernel computation. -/

/-- **The subgroup-class count is a species-table invariant**: two groups with
isomorphic species tables have the same number of *conjugacy classes* of
subgroups. The mark classes `⟦K,1⟧` are exactly the subgroup conjugacy classes
(`⟦K,1⟧ = ⟦K',1⟧ ⟺ K, K′ conjugate), and the row bijection preserves them
(`isMarkClass_rows`). No normalizer-growth hypothesis — prime-agnostic. This is
the invariant that separates the `p⁴` quartet {ids 3,8,9,10}: they share
subgroup *counts* but not subgroup-*class* counts (`6p+5 / 4p+7 / 2p+8`). -/
theorem card_markClasses_eq (T : SpeciesTableIso G G') :
    Nat.card {c : CharPairClass G ℂˣ // IsMarkClass c} =
      Nat.card {c' : CharPairClass G' ℂˣ // IsMarkClass c'} :=
  Nat.card_congr (T.rows.subtypeEquiv fun c =>
    ⟨fun h => T.isMarkClass_rows h, fun h => by
      have h2 : IsMarkClass (T.rows.symm (T.rows c)) := T.symm.isMarkClass_rows h
      rwa [Equiv.symm_apply_apply] at h2⟩)

/-- **Prime-agnostic species-table invariants**: a species-table isomorphism
always forces equal order and equal subgroup counts in every order — no
normalizer-growth hypothesis, so these hold for `2`-groups too. -/
theorem card_eq_and_subgroup_count_eq (T : SpeciesTableIso G G') :
    Nat.card G = Nat.card G' ∧
    (∀ n : ℕ, Nat.card {L : Subgroup G // Nat.card L = n} =
      Nat.card {L' : Subgroup G' // Nat.card L' = n}) :=
  ⟨T.card_eq, T.card_subgroups_eq⟩

end DRing

end LeanDring
