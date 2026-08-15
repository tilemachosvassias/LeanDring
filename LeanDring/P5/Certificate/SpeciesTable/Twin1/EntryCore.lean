/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.ConjugacyClasses.Twin1.PairClass
import LeanDring.P5.Certificate.Support.CyclotomicCode

/-!
# The species-entry-code machinery

This module builds the once-per-family unfolding infrastructure for
species-table entries `φ_{H,h}[K,λ]`.

Three layers, GENERIC → CONCRETE:

## Generic (any finite group)

* `section_independence` — Müller's summand `λ(s(q)⁻¹·h·s(q))` is independent of
  the coset section (the crux, `[propext]` only): any representative `t` of the
  same coset gives the same value, since `A` is abelian and the two reps differ
  by conjugation by an element of `K`. This is what legitimizes replacing the
  abstract sum over the noncomputable `fixedPoints H (G/K)` by a sum over a
  supplied **concrete transversal**.
* `DRing.species_basisElt_transversal` — Müller's formula re-expressed over a
  concrete transversal `t : T → G`, given a bijection `T ≃ (G/K)^H` respecting
  representatives:
  `φ_{H,h}[K,λ] = ∑_{i} λ(t(i)⁻¹·h·t(i))`.
* `DRing.transversalEquiv` / `species_basisElt_of_transversal` — the bijection
  **builder** from `siftB`-decidable data: injective-mod-`K` + all-`H`-fixed +
  a single **cardinality** input `|T| = |(G/K)^H|` (see the module tail).

## Concrete (`Coordinate 1` / `reps`)

* `charOfVec_val_summand` — a certified character's value coerced to `ℂ` is a
  literal power of `ζ₂₅`: `(charOfVec r e he x : ℂ) = ζ₂₅ ^ (charForm (basisAt r) e x).val`.
* `DRing.species_entry_eq_sum` — the entry as a finite sum of `ζ₂₅`-powers with a
  **kernel-computable exponent list**
  `e_T(i) = (charForm (basisAt rK) e (t(i)⁻¹·h·t(i))).val`.
* `entryCode` / `entryCode_eq_species` — the `Code`-format entry (a length-20
  integer array) with the headline **once-lemma**:
  `sumPowers (entryExp …) = sumPowers (entryExp …) ↔ φ = φ`, feeding
  `P5CyclotomicCode.sumPowers_eq_iff_value_eq`.

## Inputs to the transversal builder

The builder consumes one non-decidable hypothesis — the completeness count
`hcard : |T| = |(G/K)^H|` — and the all-`H`-fixedness `hfix` (a
generator-closure upgrade of the per-generator `siftB` kernel checks). Both are
discharged for the concrete transversals in
`LeanDring/P5/Certificate/SpeciesTable/EntryTransA.lean`; everything
downstream of a supplied transversal is proven here.
-/

namespace LeanDring

open MulAction Finset

universe u v

/-! ## The crux: section-independence of the species summand (generic) -/

/-- The Müller summand `l(s(q)⁻¹·h·s(q))` does not depend on the choice of coset
representative: any representative `t` of the same coset as `qout` gives the same
value, because `A` is abelian and the two reps differ by conjugation by
`k = t⁻¹·qout ∈ K`. Enabling step of the once-per-family unfolding. -/
theorem section_independence {G : Type u} [Group G] {A : Type v} [CommGroup A]
    (K : Subgroup G) (l : K →* A) (h qout t : G)
    (hqt : t⁻¹ * qout ∈ K)
    (ha : qout⁻¹ * h * qout ∈ K) (hb : t⁻¹ * h * t ∈ K) :
    l ⟨qout⁻¹ * h * qout, ha⟩ = l ⟨t⁻¹ * h * t, hb⟩ := by
  set k : K := ⟨t⁻¹ * qout, hqt⟩ with hk
  have hconj : (⟨qout⁻¹ * h * qout, ha⟩ : K)
      = k⁻¹ * ⟨t⁻¹ * h * t, hb⟩ * k := by
    apply Subtype.ext
    change qout⁻¹ * h * qout = (t⁻¹ * qout)⁻¹ * (t⁻¹ * h * t) * (t⁻¹ * qout)
    group
  rw [hconj, map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]

namespace DRing

open MonGSet MonRing

variable {G : Type u} [Group G] [Fintype G]

/-- Canonical (noncomputable) `Fintype` on the `H`-fixed cosets of `K` in `G`,
so the transversal count `hcard` elaborates with one fixed instance. -/
noncomputable instance instFintypeFixedQuot (K H : Subgroup G) :
    Fintype (fixedPoints H (G ⧸ K)) :=
  Fintype.ofFinite _

/-! ## Müller's formula over a concrete transversal -/

/-- **Müller's species formula over a concrete transversal.** Given a bijection
`e : T ≃ (G/K)^H` whose representatives are the supplied `t i`, the species entry
is the finite sum over `T` of the character at the conjugated representative:
`φ_{H,h}[K,λ] = ∑_i (l ⟨t(i)⁻¹·h·t(i)⟩ : ℂ)`. -/
theorem species_basisElt_transversal (K : Subgroup G) (l : K →* ℂˣ)
    (H : Subgroup G) (h : H)
    {T : Type*} [Fintype T] (t : T → G)
    (e : T ≃ fixedPoints H (induced K l : MonGSet G ℂˣ).carrier)
    (he : ∀ i, ((e i).1 : G ⧸ K) = ((t i : G) : G ⧸ K))
    (hb : ∀ i, (t i)⁻¹ * (h : G) * (t i) ∈ K) :
    species H h (basisElt K l) =
      ∑ i : T, ((l ⟨(t i)⁻¹ * (h : G) * (t i), hb i⟩ : ℂˣ) : ℂ) := by
  rw [species_basisElt]
  refine (Fintype.sum_equiv e
    (fun i => ((l ⟨(t i)⁻¹ * (h : G) * (t i), hb i⟩ : ℂˣ) : ℂ))
    (fun q => ((l ⟨q.1.out⁻¹ * (h : G) * q.1.out,
        sectionConj_mem K H h q.1 (q.2 h)⟩ : ℂˣ) : ℂ)) ?_).symm
  intro i
  -- the two representatives `(e i).1.out` and `t i` name the same coset
  have hqt : (t i)⁻¹ * (e i).1.out ∈ K := by
    have h1 : ((t i : G) : G ⧸ K) = (((e i).1.out : G) : G ⧸ K) := by
      rw [QuotientGroup.out_eq']; exact (he i).symm
    exact (QuotientGroup.eq).mp h1
  exact congrArg (Units.val)
    (section_independence K l (h : G) (e i).1.out (t i) hqt
      (sectionConj_mem K H h (e i).1 ((e i).2 h)) (hb i)).symm

/-! ## The transversal-bijection builder from decidable data -/

/-- **The transversal bijection**, built from `siftB`-decidable data: an
injective-mod-`K` family of `H`-fixed cosets whose count matches the fixed-point
count is a bijection `T ≃ (G/K)^H`. The cardinality hypothesis is the
completeness input, discharged for the concrete transversals in
`Twin2/EntryTransA.lean`. -/
noncomputable def transversalEquiv (K H : Subgroup G)
    {T : Type*} [Fintype T] (t : T → G)
    (hfix : ∀ i, ((t i : G) : G ⧸ K) ∈ fixedPoints H (G ⧸ K))
    (hinj : Function.Injective (fun i => ((t i : G) : G ⧸ K)))
    (hcard : Fintype.card T = Fintype.card (fixedPoints H (G ⧸ K))) :
    T ≃ fixedPoints H (G ⧸ K) :=
  Equiv.ofBijective (fun i => ⟨((t i : G) : G ⧸ K), hfix i⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun _a _b hab => hinj (Subtype.ext_iff.mp hab), hcard⟩)

/-- **The entry over a certified transversal**, all hypotheses discharged: the
membership `hb` for the RHS is derived from the fixedness. -/
theorem species_basisElt_of_transversal (K H : Subgroup G) (l : K →* ℂˣ) (h : H)
    {T : Type*} [Fintype T] (t : T → G)
    (hfix : ∀ i, ((t i : G) : G ⧸ K) ∈ fixedPoints H (G ⧸ K))
    (hinj : Function.Injective (fun i => ((t i : G) : G ⧸ K)))
    (hcard : Fintype.card T = Fintype.card (fixedPoints H (G ⧸ K)))
    (hb : ∀ i, (t i)⁻¹ * (h : G) * (t i) ∈ K) :
    species H h (basisElt K l) =
      ∑ i : T, ((l ⟨(t i)⁻¹ * (h : G) * (t i), hb i⟩ : ℂˣ) : ℂ) :=
  species_basisElt_transversal K l H h t
    (transversalEquiv K H t hfix hinj hcard)
    (fun _ => rfl) hb

end DRing

/-! ## Concrete layer: `Coordinate 1` species entries as `ζ₂₅`-power sums -/

namespace P5Presentation

open LeanDring.DRing LeanDring.MonGSet

/-- **The summand bridge.** A certified character's value, coerced to `ℂ`, is a
literal power of the fixed primitive root: `(charOfVec r e he x : ℂ)
= ζ₂₅ ^ (charForm (basisAt r) e x).val`. -/
theorem charOfVec_val_summand (r : Fin 148) (e : List (ZMod 25))
    (he : charOK (basisAt r) e = true) (x : ↥(reps r)) :
    ((charOfVec r e he x : ℂˣ) : ℂ)
      = ((zeta25 : ℂˣ) : ℂ) ^ (charForm (basisAt r) e (x : Coordinate 1)).val := by
  rw [charOfVec_apply]
  change ((zeta25 ^ (charForm (basisAt r) e (x : Coordinate 1)).val : ℂˣ) : ℂ)
    = ((zeta25 : ℂˣ) : ℂ) ^ (charForm (basisAt r) e (x : Coordinate 1)).val
  rw [Units.val_pow_eq_pow_val]

/-- **The kernel-computable entry exponent list.** For the row `[reps rK, e]`,
column `(reps rH, h)`, and transversal `t : T → Coordinate 1`, the exponent at
index `i` is `(charForm (basisAt rK) e (t(i)⁻¹·h·t(i))).val` — built from the
group product (`mulC`/`invC`) and the certified character vector `e`. -/
def entryExp (rK : Fin 148) (e : List (ZMod 25)) (h : Coordinate 1)
    {T : Type*} (t : T → Coordinate 1) (i : T) : ℕ :=
  (charForm (basisAt rK) e ((t i)⁻¹ * h * (t i))).val

/-- **The entry as a `ζ₂₅`-power sum** (the once-per-family unfolding, concrete).
Given a certified transversal of the `H`-fixed cosets of `K = reps rK`, the
species entry `φ_{H,h}[K, charOfVec rK e]` equals the finite sum of `ζ₂₅`-powers
with the kernel-computable exponent list `entryExp`. -/
theorem species_entry_eq_sum (rK rH : Fin 148) (e : List (ZMod 25))
    (heK : charOK (basisAt rK) e = true) (h : ↥(reps rH))
    {T : Type*} [Fintype T] (t : T → Coordinate 1)
    (hfix : ∀ i, ((t i : Coordinate 1) : Coordinate 1 ⧸ reps rK)
      ∈ fixedPoints (reps rH) (Coordinate 1 ⧸ reps rK))
    (hinj : Function.Injective
      (fun i => ((t i : Coordinate 1) : Coordinate 1 ⧸ reps rK)))
    (hcard : Fintype.card T
      = Fintype.card (fixedPoints (reps rH) (Coordinate 1 ⧸ reps rK)))
    (hb : ∀ i, (t i)⁻¹ * (h : Coordinate 1) * (t i) ∈ reps rK) :
    species (reps rH) h (basisElt (reps rK) (charOfVec rK e heK))
      = ∑ i : T, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK e (h : Coordinate 1) t i := by
  rw [species_basisElt_of_transversal (reps rK) (reps rH) (charOfVec rK e heK)
    h t hfix hinj hcard hb]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [charOfVec_val_summand]
  rfl

/-- **The `Code`-format entry.** The exact length-20 integer array whose complex
evaluation at `ζ₂₅` is the species entry value. -/
def entryCode (rK : Fin 148) (e : List (ZMod 25)) (h : Coordinate 1)
    {T : Type*} [Fintype T] (t : T → Coordinate 1) : P5CyclotomicCode.Code :=
  P5CyclotomicCode.sumPowers (entryExp rK e h t)

/-- **The headline once-lemma.** Equality of the executable entry codes of two
cells is *exactly* equality of the two species values — no external table is
trusted. Instantiates `P5CyclotomicCode.sumPowers_eq_iff_value_eq` through the
`species_entry_eq_sum` chain. -/
theorem entryCode_eq_species
    (rK rH : Fin 148) (e : List (ZMod 25)) (heK : charOK (basisAt rK) e = true)
    (h : ↥(reps rH)) {T : Type*} [Fintype T] (t : T → Coordinate 1)
    (hfix : ∀ i, ((t i : Coordinate 1) : Coordinate 1 ⧸ reps rK)
      ∈ fixedPoints (reps rH) (Coordinate 1 ⧸ reps rK))
    (hinj : Function.Injective
      (fun i => ((t i : Coordinate 1) : Coordinate 1 ⧸ reps rK)))
    (hcard : Fintype.card T
      = Fintype.card (fixedPoints (reps rH) (Coordinate 1 ⧸ reps rK)))
    (hb : ∀ i, (t i)⁻¹ * (h : Coordinate 1) * (t i) ∈ reps rK)
    (rK' rH' : Fin 148) (e' : List (ZMod 25)) (heK' : charOK (basisAt rK') e' = true)
    (h' : ↥(reps rH')) {T' : Type*} [Fintype T'] (t' : T' → Coordinate 1)
    (hfix' : ∀ i, ((t' i : Coordinate 1) : Coordinate 1 ⧸ reps rK')
      ∈ fixedPoints (reps rH') (Coordinate 1 ⧸ reps rK'))
    (hinj' : Function.Injective
      (fun i => ((t' i : Coordinate 1) : Coordinate 1 ⧸ reps rK')))
    (hcard' : Fintype.card T'
      = Fintype.card (fixedPoints (reps rH') (Coordinate 1 ⧸ reps rK')))
    (hb' : ∀ i, (t' i)⁻¹ * (h' : Coordinate 1) * (t' i) ∈ reps rK') :
    entryCode rK e (h : Coordinate 1) t = entryCode rK' e' (h' : Coordinate 1) t'
      ↔ species (reps rH) h (basisElt (reps rK) (charOfVec rK e heK))
          = species (reps rH') h' (basisElt (reps rK') (charOfVec rK' e' heK')) := by
  apply P5CyclotomicCode.sumPowers_eq_iff_value_eq zeta25_prim
  · exact species_entry_eq_sum rK rH e heK h t hfix hinj hcard hb
  · exact species_entry_eq_sum rK' rH' e' heK' h' t' hfix' hinj' hcard' hb'

end P5Presentation

end LeanDring
