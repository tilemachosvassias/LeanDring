/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.Characters.Twin2.CharExtend

/-!
# The species-entry-code machinery (`Coordinate 2` twin)

The `q = 2` mirror of the concrete layer of `Twin1/EntryCore.lean`.  The *generic*
content (`section_independence`, `DRing.species_basisElt_transversal`,
`DRing.transversalEquiv`, `DRing.species_basisElt_of_transversal`) is group-agnostic
and lives there; it serves both twins unchanged.  This file supplies the
`Coordinate 2` concrete instances, a token-transform mirror of the `Coordinate 1`
half (`charOfVec2`/`charForm2`/`basisAt2` from
`LeanDring/P5/Certificate/Characters/Twin2/CharExtend.lean`, sharing
`zeta25`/`zexp` and the generic `P5CyclotomicCode.sumPowers`):

* `charOfVec2_val_summand` — a certified `q=2` character's value, coerced to `ℂ`, is
  a literal power of `ζ₂₅`.
* `Q2.species_entry_eq_sum` — the `Coordinate 2` entry as a finite sum of
  `ζ₂₅`-powers with kernel-computable exponent list `entryExp2`.
* `Q2.entryCode` / `Q2.entryCode_eq_species` — the `Code`-format entry and the
  headline once-lemma feeding `P5CyclotomicCode.sumPowers_eq_iff_value_eq`.
-/

namespace LeanDring

namespace P5Presentation

namespace Q2

open MulAction Finset
open LeanDring.DRing LeanDring.MonGSet

/-! ## Concrete layer: `Coordinate 2` species entries as `ζ₂₅`-power sums -/

/-- **The summand bridge (`q=2`).** A certified character's value, coerced to `ℂ`,
is a literal power of the fixed primitive root: `(charOfVec2 r e he x : ℂ)
= ζ₂₅ ^ (charForm2 (basisAt2 r) e x).val`.  Twin of `charOfVec_val_summand`. -/
theorem charOfVec2_val_summand (r : Fin 148) (e : List (ZMod 25))
    (he : charOK2 (basisAt2 r) e = true) (x : ↥(reps r)) :
    ((charOfVec2 r e he x : ℂˣ) : ℂ)
      = ((zeta25 : ℂˣ) : ℂ) ^ (charForm2 (basisAt2 r) e (x : Coordinate 2)).val := by
  rw [charOfVec2_apply]
  change ((zeta25 ^ (charForm2 (basisAt2 r) e (x : Coordinate 2)).val : ℂˣ) : ℂ)
    = ((zeta25 : ℂˣ) : ℂ) ^ (charForm2 (basisAt2 r) e (x : Coordinate 2)).val
  rw [Units.val_pow_eq_pow_val]

/-- **The kernel-computable entry exponent list (`q=2`).** For the row
`[reps rK, e]`, column `(reps rH, h)`, and transversal `t : T → Coordinate 2`, the
exponent at index `i` is `(charForm2 (basisAt2 rK) e (t(i)⁻¹·h·t(i))).val`.  Twin of
`entryExp`. -/
def entryExp2 (rK : Fin 148) (e : List (ZMod 25)) (h : Coordinate 2)
    {T : Type*} (t : T → Coordinate 2) (i : T) : ℕ :=
  (charForm2 (basisAt2 rK) e ((t i)⁻¹ * h * (t i))).val

/-- **The entry as a `ζ₂₅`-power sum (`q=2`, the once-per-family unfolding,
concrete).** Given a certified transversal of the `H`-fixed cosets of
`K = reps rK`, the species entry `φ_{H,h}[K, charOfVec2 rK e]` equals the finite
sum of `ζ₂₅`-powers with the kernel-computable exponent list `entryExp2`.  Twin of
`species_entry_eq_sum`. -/
theorem species_entry_eq_sum (rK rH : Fin 148) (e : List (ZMod 25))
    (heK : charOK2 (basisAt2 rK) e = true) (h : ↥(reps rH))
    {T : Type*} [Fintype T] (t : T → Coordinate 2)
    (hfix : ∀ i, ((t i : Coordinate 2) : Coordinate 2 ⧸ reps rK)
      ∈ fixedPoints (reps rH) (Coordinate 2 ⧸ reps rK))
    (hinj : Function.Injective
      (fun i => ((t i : Coordinate 2) : Coordinate 2 ⧸ reps rK)))
    (hcard : Fintype.card T
      = Fintype.card (fixedPoints (reps rH) (Coordinate 2 ⧸ reps rK)))
    (hb : ∀ i, (t i)⁻¹ * (h : Coordinate 2) * (t i) ∈ reps rK) :
    species (reps rH) h (basisElt (reps rK) (charOfVec2 rK e heK))
      = ∑ i : T, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK e (h : Coordinate 2) t i := by
  rw [species_basisElt_of_transversal (reps rK) (reps rH) (charOfVec2 rK e heK)
    h t hfix hinj hcard hb]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [charOfVec2_val_summand]
  rfl

/-- **The `Code`-format entry (`q=2`).** The exact length-20 integer array whose
complex evaluation at `ζ₂₅` is the species entry value.  Twin of `entryCode`. -/
def entryCode (rK : Fin 148) (e : List (ZMod 25)) (h : Coordinate 2)
    {T : Type*} [Fintype T] (t : T → Coordinate 2) : P5CyclotomicCode.Code :=
  P5CyclotomicCode.sumPowers (entryExp2 rK e h t)

/-- **The headline once-lemma (`q=2`).** Equality of the executable entry codes of
two cells is *exactly* equality of the two species values — no external table is
trusted.  Twin of `entryCode_eq_species`. -/
theorem entryCode_eq_species
    (rK rH : Fin 148) (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK) e = true)
    (h : ↥(reps rH)) {T : Type*} [Fintype T] (t : T → Coordinate 2)
    (hfix : ∀ i, ((t i : Coordinate 2) : Coordinate 2 ⧸ reps rK)
      ∈ fixedPoints (reps rH) (Coordinate 2 ⧸ reps rK))
    (hinj : Function.Injective
      (fun i => ((t i : Coordinate 2) : Coordinate 2 ⧸ reps rK)))
    (hcard : Fintype.card T
      = Fintype.card (fixedPoints (reps rH) (Coordinate 2 ⧸ reps rK)))
    (hb : ∀ i, (t i)⁻¹ * (h : Coordinate 2) * (t i) ∈ reps rK)
    (rK' rH' : Fin 148) (e' : List (ZMod 25)) (heK' : charOK2 (basisAt2 rK') e' = true)
    (h' : ↥(reps rH')) {T' : Type*} [Fintype T'] (t' : T' → Coordinate 2)
    (hfix' : ∀ i, ((t' i : Coordinate 2) : Coordinate 2 ⧸ reps rK')
      ∈ fixedPoints (reps rH') (Coordinate 2 ⧸ reps rK'))
    (hinj' : Function.Injective
      (fun i => ((t' i : Coordinate 2) : Coordinate 2 ⧸ reps rK')))
    (hcard' : Fintype.card T'
      = Fintype.card (fixedPoints (reps rH') (Coordinate 2 ⧸ reps rK')))
    (hb' : ∀ i, (t' i)⁻¹ * (h' : Coordinate 2) * (t' i) ∈ reps rK') :
    entryCode rK e (h : Coordinate 2) t = entryCode rK' e' (h' : Coordinate 2) t'
      ↔ species (reps rH) h (basisElt (reps rK) (charOfVec2 rK e heK))
          = species (reps rH') h' (basisElt (reps rK') (charOfVec2 rK' e' heK')) := by
  apply P5CyclotomicCode.sumPowers_eq_iff_value_eq zeta25_prim
  · exact species_entry_eq_sum rK rH e heK h t hfix hinj hcard hb
  · exact species_entry_eq_sum rK' rH' e' heK' h' t' hfix' hinj' hcard' hb'

end Q2

end P5Presentation

end LeanDring
