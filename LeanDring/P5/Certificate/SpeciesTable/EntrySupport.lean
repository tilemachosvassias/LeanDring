/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.EntryFast
import LeanDring.Theory.DRing.Unipotent

/-!
# The generic vanishing theorem and the cross-coordinate reflection

Two once-per-certificate assemblies for the species-table comparison:

* **`species_basisElt_eq_zero_of_not_subconj`** — the *single* generic vanishing
  theorem covering **every** off-support cell: if no conjugate of `H` lies in `K`
  (`H` not subconjugate to `K`) then `φ_{H,h}[K,λ] = 0`. Combined with its twin
  applied at the matched cell, one abstract "0 = 0" discharges each vanishing cell
  with **no `decide`** — the whole off-support mass of the table needs no kernel
  computation. This strengthens the existing `species_basisElt_eq_zero_of_card_lt`
  (which only handles `|K| < |H|`) to the full subconjugacy criterion, so the
  support is exactly the sub-conjugacy order-ideal.

* **`entryCode_cross_eq_species`** — the cross-coordinate reflection: equality of a
  `Coordinate 1` entry code and a `Coordinate 2` entry code is *exactly* equality
  of the two species values across the twins. Assembles `species_entry_eq_sum`
  (q=1) and `Q2.species_entry_eq_sum` (q=2) through
  `sumPowers_eq_iff_value_eq`; the same-coordinate `entryCode_eq_species` is the
  template.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring

section Vanishing

open MulAction Finset DRing MonGSet MonRing

variable {G : Type*} [_root_.Group G] [Fintype G]

/-- **The generic vanishing theorem.** The `(H,h)`-entry of `[K,λ]` is zero
whenever `H` is *not* subconjugate to `K` (no conjugate of `H` lies inside `K`) —
there are then no `H`-fixed cosets in `G/K`, so Müller's sum is empty. One
theorem covers every off-support cell of the species table; the twin instance at
the matched cell gives an abstract `0 = 0` with no `decide`. -/
theorem DRing.species_basisElt_eq_zero_of_not_subconj {H K : Subgroup G} (h : H)
    (l : K →* ℂˣ) (hns : ¬ ∃ g : G, ∀ x ∈ H, g⁻¹ * x * g ∈ K) :
    species H h (basisElt K l) = 0 := by
  classical
  rw [species_basisElt]
  haveI : IsEmpty (MulAction.fixedPoints H
      (induced K l : MonGSet G ℂˣ).carrier) := by
    constructor
    rintro ⟨q, hq⟩
    have hne : Nat.card (MulAction.fixedPoints H (G ⧸ K)) ≠ 0 :=
      Nat.card_ne_zero.mpr ⟨⟨⟨q, hq⟩⟩, Subtype.finite⟩
    exact hns ((mark_ne_zero_iff H K).mp hne)
  rw [Finset.univ_eq_empty, Finset.sum_empty]

end Vanishing

namespace P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

/-- **The cross-coordinate reflection.** Equality of the `Coordinate 1` entry code
of a cell and the `Coordinate 2` entry code of its matched cell is exactly
equality of the two species values across the twins — no external table is
trusted. Cross-twin analogue of `entryCode_eq_species`, feeding
`P5CyclotomicCode.sumPowers_eq_iff_value_eq` from the two once-lemmas
`species_entry_eq_sum` (q=1) and `Q2.species_entry_eq_sum` (q=2). -/
theorem entryCode_cross_eq_species
    (rK rH : Fin 148) (e : List (ZMod 25)) (heK : charOK (basisAt rK) e = true)
    (h : ↥(reps rH)) {T : Type*} [Fintype T] (t : T → Coordinate 1)
    (hfix : ∀ i, ((t i : Coordinate 1) : Coordinate 1 ⧸ reps rK)
      ∈ fixedPoints (reps rH) (Coordinate 1 ⧸ reps rK))
    (hinj : Function.Injective
      (fun i => ((t i : Coordinate 1) : Coordinate 1 ⧸ reps rK)))
    (hcard : Fintype.card T
      = Fintype.card (fixedPoints (reps rH) (Coordinate 1 ⧸ reps rK)))
    (hb : ∀ i, (t i)⁻¹ * (h : Coordinate 1) * (t i) ∈ reps rK)
    (rK' rH' : Fin 148) (e' : List (ZMod 25)) (heK' : Q2.charOK2 (Q2.basisAt2 rK') e' = true)
    (h' : ↥(Q2.reps rH')) {T' : Type*} [Fintype T'] (t' : T' → Coordinate 2)
    (hfix' : ∀ i, ((t' i : Coordinate 2) : Coordinate 2 ⧸ Q2.reps rK')
      ∈ fixedPoints (Q2.reps rH') (Coordinate 2 ⧸ Q2.reps rK'))
    (hinj' : Function.Injective
      (fun i => ((t' i : Coordinate 2) : Coordinate 2 ⧸ Q2.reps rK')))
    (hcard' : Fintype.card T'
      = Fintype.card (fixedPoints (Q2.reps rH') (Coordinate 2 ⧸ Q2.reps rK')))
    (hb' : ∀ i, (t' i)⁻¹ * (h' : Coordinate 2) * (t' i) ∈ Q2.reps rK') :
    entryCode rK e (h : Coordinate 1) t = Q2.entryCode rK' e' (h' : Coordinate 2) t'
      ↔ species (reps rH) h (basisElt (reps rK) (charOfVec rK e heK))
          = species (Q2.reps rH') h' (basisElt (Q2.reps rK') (Q2.charOfVec2 rK' e' heK')) := by
  apply P5CyclotomicCode.sumPowers_eq_iff_value_eq zeta25_prim
  · exact species_entry_eq_sum rK rH e heK h t hfix hinj hcard hb
  · exact Q2.species_entry_eq_sum rK' rH' e' heK' h' t' hfix' hinj' hcard' hb'

/-- **The generic data-equality cell discharge.** If the column data `D` and the row data `e`
are identically equal (e.g., syntactically equal terms for twin-equal cells), their species
values are equal by `rfl` on the fast code, completely bypassing genuine computation. -/
theorem species_eq_of_data_eq
    (rK rH : Fin 148) (e : List (ZMod 25)) (heK : charOK (basisAt rK) e = true)
    (h : ↥(reps rH)) {T : Type*} [Fintype T] (t : T → Coordinate 1)
    (hfix : ∀ i, ((t i : Coordinate 1) : Coordinate 1 ⧸ reps rK)
      ∈ fixedPoints (reps rH) (Coordinate 1 ⧸ reps rK))
    (hinj : Function.Injective
      (fun i => ((t i : Coordinate 1) : Coordinate 1 ⧸ reps rK)))
    (hcard : Fintype.card T
      = Fintype.card (fixedPoints (reps rH) (Coordinate 1 ⧸ reps rK)))
    (hb : ∀ i, (t i)⁻¹ * (h : Coordinate 1) * (t i) ∈ reps rK)
    (rK' rH' : Fin 148) (e' : List (ZMod 25)) (heK' : Q2.charOK2 (Q2.basisAt2 rK') e' = true)
    (h' : ↥(Q2.reps rH')) (t' : T → Coordinate 2)
    (hfix' : ∀ i, ((t' i : Coordinate 2) : Coordinate 2 ⧸ Q2.reps rK')
      ∈ fixedPoints (Q2.reps rH') (Coordinate 2 ⧸ Q2.reps rK'))
    (hinj' : Function.Injective
      (fun i => ((t' i : Coordinate 2) : Coordinate 2 ⧸ Q2.reps rK')))
    (hcard' : Fintype.card T
      = Fintype.card (fixedPoints (Q2.reps rH') (Coordinate 2 ⧸ Q2.reps rK')))
    (hb' : ∀ i, (t' i)⁻¹ * (h' : Coordinate 2) * (t' i) ∈ Q2.reps rK')
    (hD : colData1 rK h t = colData2 rK' h' t')
    (he : List.map ZMod.val e = List.map ZMod.val e') :
    species (reps rH) h (basisElt (reps rK) (charOfVec rK e heK))
      = species (Q2.reps rH') h' (basisElt (Q2.reps rK') (Q2.charOfVec2 rK' e' heK')) := by
  rw [← entryCode_cross_eq_species rK rH e heK h t hfix hinj hcard hb rK' rH' e' heK' h' t' hfix' hinj' hcard' hb']
  rw [entryCode_eq_fastCode, entryCode2_eq_fastCode]
  exact entry_eq_of_data_eq hD he

/-- **The generic residual-decide cell discharge (divergent columns).** The
divergent counterpart of `species_eq_of_data_eq`: when the twins' column data
differ (`D₁ ≠ D₂`) or the row vectors differ (`e ≠ e'`), the two species values
are nonetheless equal because the *cyclotomic values* of the two fast codes agree.
That single fact — `sumPowers (fastCode D₁ e) = sumPowers (fastCode D₂ e')` over the
embedded per-column data — is supplied by ONE kernel `decide` (`hcode`), and this
lemma reflects it through the proven cross-coordinate bridge to the species
equality.  Every one of the 173,006 residual real-decide cells (τ-moved,
col-data-divergent, row-`e`-divergent) discharges through this engine; the emitter
rewrites `colData1/colData2` to the embedded `colFn D₁/colFn D₂` via the `ColCert`
bindings before firing `hcode`, so the `decide` only touches the embedded exponent
data (cost grows with `|T|`:
`|T|=625`). -/
theorem species_eq_of_fastcode_eq
    (rK rH : Fin 148) (e : List (ZMod 25)) (heK : charOK (basisAt rK) e = true)
    (h : ↥(reps rH)) {T : Type*} [Fintype T] (t : T → Coordinate 1)
    (hfix : ∀ i, ((t i : Coordinate 1) : Coordinate 1 ⧸ reps rK)
      ∈ fixedPoints (reps rH) (Coordinate 1 ⧸ reps rK))
    (hinj : Function.Injective
      (fun i => ((t i : Coordinate 1) : Coordinate 1 ⧸ reps rK)))
    (hcard : Fintype.card T
      = Fintype.card (fixedPoints (reps rH) (Coordinate 1 ⧸ reps rK)))
    (hb : ∀ i, (t i)⁻¹ * (h : Coordinate 1) * (t i) ∈ reps rK)
    (rK' rH' : Fin 148) (e' : List (ZMod 25)) (heK' : Q2.charOK2 (Q2.basisAt2 rK') e' = true)
    (h' : ↥(Q2.reps rH')) {T' : Type*} [Fintype T'] (t' : T' → Coordinate 2)
    (hfix' : ∀ i, ((t' i : Coordinate 2) : Coordinate 2 ⧸ Q2.reps rK')
      ∈ fixedPoints (Q2.reps rH') (Coordinate 2 ⧸ Q2.reps rK'))
    (hinj' : Function.Injective
      (fun i => ((t' i : Coordinate 2) : Coordinate 2 ⧸ Q2.reps rK')))
    (hcard' : Fintype.card T'
      = Fintype.card (fixedPoints (Q2.reps rH') (Coordinate 2 ⧸ Q2.reps rK')))
    (hb' : ∀ i, (t' i)⁻¹ * (h' : Coordinate 2) * (t' i) ∈ Q2.reps rK')
    (hcode : P5CyclotomicCode.sumPowers (fastCode (colData1 rK (h : Coordinate 1) t) (List.map ZMod.val e))
      = P5CyclotomicCode.sumPowers (fastCode (colData2 rK' (h' : Coordinate 2) t') (List.map ZMod.val e'))) :
    species (reps rH) h (basisElt (reps rK) (charOfVec rK e heK))
      = species (Q2.reps rH') h' (basisElt (Q2.reps rK') (Q2.charOfVec2 rK' e' heK')) := by
  rw [← entryCode_cross_eq_species rK rH e heK h t hfix hinj hcard hb rK' rH' e' heK' h' t' hfix' hinj' hcard' hb']
  rw [entryCode_eq_fastCode, entryCode2_eq_fastCode]
  exact hcode

end P5Presentation

end LeanDring
