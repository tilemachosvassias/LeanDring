/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, K-strata data (5^4 stratum, rK 126-127): certified per-cell species-entry instantiations, both
twins.

Covers K-classes 126, 127 (order-5^4 K, |R|=5).  For each nonzero `H`-column
(`(G/K)^H ≠ ∅`), the full coset transversal `R126..` and each `H`-fixed
sub-transversal are embedded as kernel data and re-verified by `decide` through
the `LeanDring/P5/Certificate/SpeciesTable/EntryTransA.lean` adapters, producing a species-entry-as-power-sum theorem
parametric in the certified character `e` and column element `h`.  Transversal
data is SHARED between the twins (`reduceAux` normal forms coincide; verified in
the emitter and re-checked by the q=2 `decide`s).
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false
set_option linter.style.setOption false

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-! # K-class rK = 126  (|G/K| = 5) -/

def rK126 : Fin 148 := ⟨126, by decide⟩

def R126list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def R126 : Fin 5 → Coordinate 1 := fun i => R126list.getD i.val (0,0,0,0,0)

theorem hpxR126 : Function.Injective (fun i => reduceAux 1 (basisAt rK126) (R126 i)) := by decide
theorem hcardq126 : Nat.card (Coordinate 1 ⧸ reps rK126) = 5 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (126, 0): |T| = 5 -/

def T126_0list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T126_0 : Fin 5 → Coordinate 1 := fun i => T126_0list.getD i.val (0,0,0,0,0)

theorem hfix126_0 : ∀ i, ((T126_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK126)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126) :=
  repsFix_of_siftB rK126 ⟨0, by decide⟩ T126_0 (by decide)

theorem hinj126_0 : Function.Injective
    (fun i => ((T126_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK126)) :=
  repsInj_of_reduceAux rK126 T126_0 (by decide)

theorem hcardT126_0 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK126 ⟨0, by decide⟩ R126 hpxR126 hcardq126 (by decide)).symm

/-- **Cell (126, 0).** -/
theorem cell126_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK126) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK126) (charOfVec rK126 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK126 e (h : Coordinate 1) T126_0 i :=
  species_entry_eq_sum rK126 ⟨0, by decide⟩ e heK h T126_0 hfix126_0 hinj126_0 hcardT126_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK126) (T126_0 i) (hfix126_0 i) h)

/-! ## Cell (126, 3): |T| = 5 -/

def T126_3list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T126_3 : Fin 5 → Coordinate 1 := fun i => T126_3list.getD i.val (0,0,0,0,0)

theorem hfix126_3 : ∀ i, ((T126_3 i : Coordinate 1) : Coordinate 1 ⧸ reps rK126)
    ∈ fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126) :=
  repsFix_of_siftB rK126 ⟨3, by decide⟩ T126_3 (by decide)

theorem hinj126_3 : Function.Injective
    (fun i => ((T126_3 i : Coordinate 1) : Coordinate 1 ⧸ reps rK126)) :=
  repsInj_of_reduceAux rK126 T126_3 (by decide)

theorem hcardT126_3 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK126 ⟨3, by decide⟩ R126 hpxR126 hcardq126 (by decide)).symm

/-- **Cell (126, 3).** -/
theorem cell126_3 (e : List (ZMod 25)) (heK : charOK (basisAt rK126) e = true)
    (h : ↥(reps (⟨3, by decide⟩ : Fin 148))) :
    species (reps (⟨3, by decide⟩ : Fin 148)) h (basisElt (reps rK126) (charOfVec rK126 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK126 e (h : Coordinate 1) T126_3 i :=
  species_entry_eq_sum rK126 ⟨3, by decide⟩ e heK h T126_3 hfix126_3 hinj126_3 hcardT126_3
    (fun i => conj_mem_of_fixedPoints (reps ⟨3, by decide⟩) (reps rK126) (T126_3 i) (hfix126_3 i) h)

/-! ## Cell (126, 10): |T| = 5 -/

def T126_10list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T126_10 : Fin 5 → Coordinate 1 := fun i => T126_10list.getD i.val (0,0,0,0,0)

theorem hfix126_10 : ∀ i, ((T126_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK126)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126) :=
  repsFix_of_siftB rK126 ⟨10, by decide⟩ T126_10 (by decide)

theorem hinj126_10 : Function.Injective
    (fun i => ((T126_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK126)) :=
  repsInj_of_reduceAux rK126 T126_10 (by decide)

theorem hcardT126_10 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK126 ⟨10, by decide⟩ R126 hpxR126 hcardq126 (by decide)).symm

/-- **Cell (126, 10).** -/
theorem cell126_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK126) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK126) (charOfVec rK126 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK126 e (h : Coordinate 1) T126_10 i :=
  species_entry_eq_sum rK126 ⟨10, by decide⟩ e heK h T126_10 hfix126_10 hinj126_10 hcardT126_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK126) (T126_10 i) (hfix126_10 i) h)

/-! ## Cell (126, 12): |T| = 5 -/

def T126_12list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T126_12 : Fin 5 → Coordinate 1 := fun i => T126_12list.getD i.val (0,0,0,0,0)

theorem hfix126_12 : ∀ i, ((T126_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK126)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126) :=
  repsFix_of_siftB rK126 ⟨12, by decide⟩ T126_12 (by decide)

theorem hinj126_12 : Function.Injective
    (fun i => ((T126_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK126)) :=
  repsInj_of_reduceAux rK126 T126_12 (by decide)

theorem hcardT126_12 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK126 ⟨12, by decide⟩ R126 hpxR126 hcardq126 (by decide)).symm

/-- **Cell (126, 12).** -/
theorem cell126_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK126) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK126) (charOfVec rK126 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK126 e (h : Coordinate 1) T126_12 i :=
  species_entry_eq_sum rK126 ⟨12, by decide⟩ e heK h T126_12 hfix126_12 hinj126_12 hcardT126_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK126) (T126_12 i) (hfix126_12 i) h)

/-! ## Cell (126, 21): |T| = 5 -/

def T126_21list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T126_21 : Fin 5 → Coordinate 1 := fun i => T126_21list.getD i.val (0,0,0,0,0)

theorem hfix126_21 : ∀ i, ((T126_21 i : Coordinate 1) : Coordinate 1 ⧸ reps rK126)
    ∈ fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126) :=
  repsFix_of_siftB rK126 ⟨21, by decide⟩ T126_21 (by decide)

theorem hinj126_21 : Function.Injective
    (fun i => ((T126_21 i : Coordinate 1) : Coordinate 1 ⧸ reps rK126)) :=
  repsInj_of_reduceAux rK126 T126_21 (by decide)

theorem hcardT126_21 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK126 ⟨21, by decide⟩ R126 hpxR126 hcardq126 (by decide)).symm

/-- **Cell (126, 21).** -/
theorem cell126_21 (e : List (ZMod 25)) (heK : charOK (basisAt rK126) e = true)
    (h : ↥(reps (⟨21, by decide⟩ : Fin 148))) :
    species (reps (⟨21, by decide⟩ : Fin 148)) h (basisElt (reps rK126) (charOfVec rK126 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK126 e (h : Coordinate 1) T126_21 i :=
  species_entry_eq_sum rK126 ⟨21, by decide⟩ e heK h T126_21 hfix126_21 hinj126_21 hcardT126_21
    (fun i => conj_mem_of_fixedPoints (reps ⟨21, by decide⟩) (reps rK126) (T126_21 i) (hfix126_21 i) h)

/-! ## Cell (126, 31): |T| = 5 -/

def T126_31list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T126_31 : Fin 5 → Coordinate 1 := fun i => T126_31list.getD i.val (0,0,0,0,0)

theorem hfix126_31 : ∀ i, ((T126_31 i : Coordinate 1) : Coordinate 1 ⧸ reps rK126)
    ∈ fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126) :=
  repsFix_of_siftB rK126 ⟨31, by decide⟩ T126_31 (by decide)

theorem hinj126_31 : Function.Injective
    (fun i => ((T126_31 i : Coordinate 1) : Coordinate 1 ⧸ reps rK126)) :=
  repsInj_of_reduceAux rK126 T126_31 (by decide)

theorem hcardT126_31 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK126 ⟨31, by decide⟩ R126 hpxR126 hcardq126 (by decide)).symm

/-- **Cell (126, 31).** -/
theorem cell126_31 (e : List (ZMod 25)) (heK : charOK (basisAt rK126) e = true)
    (h : ↥(reps (⟨31, by decide⟩ : Fin 148))) :
    species (reps (⟨31, by decide⟩ : Fin 148)) h (basisElt (reps rK126) (charOfVec rK126 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK126 e (h : Coordinate 1) T126_31 i :=
  species_entry_eq_sum rK126 ⟨31, by decide⟩ e heK h T126_31 hfix126_31 hinj126_31 hcardT126_31
    (fun i => conj_mem_of_fixedPoints (reps ⟨31, by decide⟩) (reps rK126) (T126_31 i) (hfix126_31 i) h)

/-! ## Cell (126, 37): |T| = 5 -/

def T126_37list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T126_37 : Fin 5 → Coordinate 1 := fun i => T126_37list.getD i.val (0,0,0,0,0)

theorem hfix126_37 : ∀ i, ((T126_37 i : Coordinate 1) : Coordinate 1 ⧸ reps rK126)
    ∈ fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126) :=
  repsFix_of_siftB rK126 ⟨37, by decide⟩ T126_37 (by decide)

theorem hinj126_37 : Function.Injective
    (fun i => ((T126_37 i : Coordinate 1) : Coordinate 1 ⧸ reps rK126)) :=
  repsInj_of_reduceAux rK126 T126_37 (by decide)

theorem hcardT126_37 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK126 ⟨37, by decide⟩ R126 hpxR126 hcardq126 (by decide)).symm

/-- **Cell (126, 37).** -/
theorem cell126_37 (e : List (ZMod 25)) (heK : charOK (basisAt rK126) e = true)
    (h : ↥(reps (⟨37, by decide⟩ : Fin 148))) :
    species (reps (⟨37, by decide⟩ : Fin 148)) h (basisElt (reps rK126) (charOfVec rK126 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK126 e (h : Coordinate 1) T126_37 i :=
  species_entry_eq_sum rK126 ⟨37, by decide⟩ e heK h T126_37 hfix126_37 hinj126_37 hcardT126_37
    (fun i => conj_mem_of_fixedPoints (reps ⟨37, by decide⟩) (reps rK126) (T126_37 i) (hfix126_37 i) h)

/-! ## Cell (126, 39): |T| = 5 -/

def T126_39list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T126_39 : Fin 5 → Coordinate 1 := fun i => T126_39list.getD i.val (0,0,0,0,0)

theorem hfix126_39 : ∀ i, ((T126_39 i : Coordinate 1) : Coordinate 1 ⧸ reps rK126)
    ∈ fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126) :=
  repsFix_of_siftB rK126 ⟨39, by decide⟩ T126_39 (by decide)

theorem hinj126_39 : Function.Injective
    (fun i => ((T126_39 i : Coordinate 1) : Coordinate 1 ⧸ reps rK126)) :=
  repsInj_of_reduceAux rK126 T126_39 (by decide)

theorem hcardT126_39 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK126 ⟨39, by decide⟩ R126 hpxR126 hcardq126 (by decide)).symm

/-- **Cell (126, 39).** -/
theorem cell126_39 (e : List (ZMod 25)) (heK : charOK (basisAt rK126) e = true)
    (h : ↥(reps (⟨39, by decide⟩ : Fin 148))) :
    species (reps (⟨39, by decide⟩ : Fin 148)) h (basisElt (reps rK126) (charOfVec rK126 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK126 e (h : Coordinate 1) T126_39 i :=
  species_entry_eq_sum rK126 ⟨39, by decide⟩ e heK h T126_39 hfix126_39 hinj126_39 hcardT126_39
    (fun i => conj_mem_of_fixedPoints (reps ⟨39, by decide⟩) (reps rK126) (T126_39 i) (hfix126_39 i) h)

/-! ## Cell (126, 45): |T| = 5 -/

def T126_45list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T126_45 : Fin 5 → Coordinate 1 := fun i => T126_45list.getD i.val (0,0,0,0,0)

theorem hfix126_45 : ∀ i, ((T126_45 i : Coordinate 1) : Coordinate 1 ⧸ reps rK126)
    ∈ fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126) :=
  repsFix_of_siftB rK126 ⟨45, by decide⟩ T126_45 (by decide)

theorem hinj126_45 : Function.Injective
    (fun i => ((T126_45 i : Coordinate 1) : Coordinate 1 ⧸ reps rK126)) :=
  repsInj_of_reduceAux rK126 T126_45 (by decide)

theorem hcardT126_45 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK126 ⟨45, by decide⟩ R126 hpxR126 hcardq126 (by decide)).symm

/-- **Cell (126, 45).** -/
theorem cell126_45 (e : List (ZMod 25)) (heK : charOK (basisAt rK126) e = true)
    (h : ↥(reps (⟨45, by decide⟩ : Fin 148))) :
    species (reps (⟨45, by decide⟩ : Fin 148)) h (basisElt (reps rK126) (charOfVec rK126 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK126 e (h : Coordinate 1) T126_45 i :=
  species_entry_eq_sum rK126 ⟨45, by decide⟩ e heK h T126_45 hfix126_45 hinj126_45 hcardT126_45
    (fun i => conj_mem_of_fixedPoints (reps ⟨45, by decide⟩) (reps rK126) (T126_45 i) (hfix126_45 i) h)

/-! ## Cell (126, 48): |T| = 5 -/

def T126_48list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T126_48 : Fin 5 → Coordinate 1 := fun i => T126_48list.getD i.val (0,0,0,0,0)

theorem hfix126_48 : ∀ i, ((T126_48 i : Coordinate 1) : Coordinate 1 ⧸ reps rK126)
    ∈ fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126) :=
  repsFix_of_siftB rK126 ⟨48, by decide⟩ T126_48 (by decide)

theorem hinj126_48 : Function.Injective
    (fun i => ((T126_48 i : Coordinate 1) : Coordinate 1 ⧸ reps rK126)) :=
  repsInj_of_reduceAux rK126 T126_48 (by decide)

theorem hcardT126_48 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK126 ⟨48, by decide⟩ R126 hpxR126 hcardq126 (by decide)).symm

/-- **Cell (126, 48).** -/
theorem cell126_48 (e : List (ZMod 25)) (heK : charOK (basisAt rK126) e = true)
    (h : ↥(reps (⟨48, by decide⟩ : Fin 148))) :
    species (reps (⟨48, by decide⟩ : Fin 148)) h (basisElt (reps rK126) (charOfVec rK126 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK126 e (h : Coordinate 1) T126_48 i :=
  species_entry_eq_sum rK126 ⟨48, by decide⟩ e heK h T126_48 hfix126_48 hinj126_48 hcardT126_48
    (fun i => conj_mem_of_fixedPoints (reps ⟨48, by decide⟩) (reps rK126) (T126_48 i) (hfix126_48 i) h)

/-! ## Cell (126, 53): |T| = 5 -/

def T126_53list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T126_53 : Fin 5 → Coordinate 1 := fun i => T126_53list.getD i.val (0,0,0,0,0)

theorem hfix126_53 : ∀ i, ((T126_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK126)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126) :=
  repsFix_of_siftB rK126 ⟨53, by decide⟩ T126_53 (by decide)

theorem hinj126_53 : Function.Injective
    (fun i => ((T126_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK126)) :=
  repsInj_of_reduceAux rK126 T126_53 (by decide)

theorem hcardT126_53 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK126 ⟨53, by decide⟩ R126 hpxR126 hcardq126 (by decide)).symm

/-- **Cell (126, 53).** -/
theorem cell126_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK126) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK126) (charOfVec rK126 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK126 e (h : Coordinate 1) T126_53 i :=
  species_entry_eq_sum rK126 ⟨53, by decide⟩ e heK h T126_53 hfix126_53 hinj126_53 hcardT126_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK126) (T126_53 i) (hfix126_53 i) h)

/-! ## Cell (126, 82): |T| = 5 -/

def T126_82list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T126_82 : Fin 5 → Coordinate 1 := fun i => T126_82list.getD i.val (0,0,0,0,0)

theorem hfix126_82 : ∀ i, ((T126_82 i : Coordinate 1) : Coordinate 1 ⧸ reps rK126)
    ∈ fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126) :=
  repsFix_of_siftB rK126 ⟨82, by decide⟩ T126_82 (by decide)

theorem hinj126_82 : Function.Injective
    (fun i => ((T126_82 i : Coordinate 1) : Coordinate 1 ⧸ reps rK126)) :=
  repsInj_of_reduceAux rK126 T126_82 (by decide)

theorem hcardT126_82 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK126 ⟨82, by decide⟩ R126 hpxR126 hcardq126 (by decide)).symm

/-- **Cell (126, 82).** -/
theorem cell126_82 (e : List (ZMod 25)) (heK : charOK (basisAt rK126) e = true)
    (h : ↥(reps (⟨82, by decide⟩ : Fin 148))) :
    species (reps (⟨82, by decide⟩ : Fin 148)) h (basisElt (reps rK126) (charOfVec rK126 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK126 e (h : Coordinate 1) T126_82 i :=
  species_entry_eq_sum rK126 ⟨82, by decide⟩ e heK h T126_82 hfix126_82 hinj126_82 hcardT126_82
    (fun i => conj_mem_of_fixedPoints (reps ⟨82, by decide⟩) (reps rK126) (T126_82 i) (hfix126_82 i) h)

/-! ## Cell (126, 93): |T| = 5 -/

def T126_93list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T126_93 : Fin 5 → Coordinate 1 := fun i => T126_93list.getD i.val (0,0,0,0,0)

theorem hfix126_93 : ∀ i, ((T126_93 i : Coordinate 1) : Coordinate 1 ⧸ reps rK126)
    ∈ fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126) :=
  repsFix_of_siftB rK126 ⟨93, by decide⟩ T126_93 (by decide)

theorem hinj126_93 : Function.Injective
    (fun i => ((T126_93 i : Coordinate 1) : Coordinate 1 ⧸ reps rK126)) :=
  repsInj_of_reduceAux rK126 T126_93 (by decide)

theorem hcardT126_93 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK126 ⟨93, by decide⟩ R126 hpxR126 hcardq126 (by decide)).symm

/-- **Cell (126, 93).** -/
theorem cell126_93 (e : List (ZMod 25)) (heK : charOK (basisAt rK126) e = true)
    (h : ↥(reps (⟨93, by decide⟩ : Fin 148))) :
    species (reps (⟨93, by decide⟩ : Fin 148)) h (basisElt (reps rK126) (charOfVec rK126 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK126 e (h : Coordinate 1) T126_93 i :=
  species_entry_eq_sum rK126 ⟨93, by decide⟩ e heK h T126_93 hfix126_93 hinj126_93 hcardT126_93
    (fun i => conj_mem_of_fixedPoints (reps ⟨93, by decide⟩) (reps rK126) (T126_93 i) (hfix126_93 i) h)

/-! ## Cell (126, 99): |T| = 5 -/

def T126_99list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T126_99 : Fin 5 → Coordinate 1 := fun i => T126_99list.getD i.val (0,0,0,0,0)

theorem hfix126_99 : ∀ i, ((T126_99 i : Coordinate 1) : Coordinate 1 ⧸ reps rK126)
    ∈ fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126) :=
  repsFix_of_siftB rK126 ⟨99, by decide⟩ T126_99 (by decide)

theorem hinj126_99 : Function.Injective
    (fun i => ((T126_99 i : Coordinate 1) : Coordinate 1 ⧸ reps rK126)) :=
  repsInj_of_reduceAux rK126 T126_99 (by decide)

theorem hcardT126_99 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK126 ⟨99, by decide⟩ R126 hpxR126 hcardq126 (by decide)).symm

/-- **Cell (126, 99).** -/
theorem cell126_99 (e : List (ZMod 25)) (heK : charOK (basisAt rK126) e = true)
    (h : ↥(reps (⟨99, by decide⟩ : Fin 148))) :
    species (reps (⟨99, by decide⟩ : Fin 148)) h (basisElt (reps rK126) (charOfVec rK126 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK126 e (h : Coordinate 1) T126_99 i :=
  species_entry_eq_sum rK126 ⟨99, by decide⟩ e heK h T126_99 hfix126_99 hinj126_99 hcardT126_99
    (fun i => conj_mem_of_fixedPoints (reps ⟨99, by decide⟩) (reps rK126) (T126_99 i) (hfix126_99 i) h)

/-! ## Cell (126, 101): |T| = 5 -/

def T126_101list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T126_101 : Fin 5 → Coordinate 1 := fun i => T126_101list.getD i.val (0,0,0,0,0)

theorem hfix126_101 : ∀ i, ((T126_101 i : Coordinate 1) : Coordinate 1 ⧸ reps rK126)
    ∈ fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126) :=
  repsFix_of_siftB rK126 ⟨101, by decide⟩ T126_101 (by decide)

theorem hinj126_101 : Function.Injective
    (fun i => ((T126_101 i : Coordinate 1) : Coordinate 1 ⧸ reps rK126)) :=
  repsInj_of_reduceAux rK126 T126_101 (by decide)

theorem hcardT126_101 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK126 ⟨101, by decide⟩ R126 hpxR126 hcardq126 (by decide)).symm

/-- **Cell (126, 101).** -/
theorem cell126_101 (e : List (ZMod 25)) (heK : charOK (basisAt rK126) e = true)
    (h : ↥(reps (⟨101, by decide⟩ : Fin 148))) :
    species (reps (⟨101, by decide⟩ : Fin 148)) h (basisElt (reps rK126) (charOfVec rK126 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK126 e (h : Coordinate 1) T126_101 i :=
  species_entry_eq_sum rK126 ⟨101, by decide⟩ e heK h T126_101 hfix126_101 hinj126_101 hcardT126_101
    (fun i => conj_mem_of_fixedPoints (reps ⟨101, by decide⟩) (reps rK126) (T126_101 i) (hfix126_101 i) h)

/-! ## Cell (126, 107): |T| = 5 -/

def T126_107list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T126_107 : Fin 5 → Coordinate 1 := fun i => T126_107list.getD i.val (0,0,0,0,0)

theorem hfix126_107 : ∀ i, ((T126_107 i : Coordinate 1) : Coordinate 1 ⧸ reps rK126)
    ∈ fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126) :=
  repsFix_of_siftB rK126 ⟨107, by decide⟩ T126_107 (by decide)

theorem hinj126_107 : Function.Injective
    (fun i => ((T126_107 i : Coordinate 1) : Coordinate 1 ⧸ reps rK126)) :=
  repsInj_of_reduceAux rK126 T126_107 (by decide)

theorem hcardT126_107 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK126 ⟨107, by decide⟩ R126 hpxR126 hcardq126 (by decide)).symm

/-- **Cell (126, 107).** -/
theorem cell126_107 (e : List (ZMod 25)) (heK : charOK (basisAt rK126) e = true)
    (h : ↥(reps (⟨107, by decide⟩ : Fin 148))) :
    species (reps (⟨107, by decide⟩ : Fin 148)) h (basisElt (reps rK126) (charOfVec rK126 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK126 e (h : Coordinate 1) T126_107 i :=
  species_entry_eq_sum rK126 ⟨107, by decide⟩ e heK h T126_107 hfix126_107 hinj126_107 hcardT126_107
    (fun i => conj_mem_of_fixedPoints (reps ⟨107, by decide⟩) (reps rK126) (T126_107 i) (hfix126_107 i) h)

/-! ## Cell (126, 110): |T| = 5 -/

def T126_110list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T126_110 : Fin 5 → Coordinate 1 := fun i => T126_110list.getD i.val (0,0,0,0,0)

theorem hfix126_110 : ∀ i, ((T126_110 i : Coordinate 1) : Coordinate 1 ⧸ reps rK126)
    ∈ fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126) :=
  repsFix_of_siftB rK126 ⟨110, by decide⟩ T126_110 (by decide)

theorem hinj126_110 : Function.Injective
    (fun i => ((T126_110 i : Coordinate 1) : Coordinate 1 ⧸ reps rK126)) :=
  repsInj_of_reduceAux rK126 T126_110 (by decide)

theorem hcardT126_110 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK126 ⟨110, by decide⟩ R126 hpxR126 hcardq126 (by decide)).symm

/-- **Cell (126, 110).** -/
theorem cell126_110 (e : List (ZMod 25)) (heK : charOK (basisAt rK126) e = true)
    (h : ↥(reps (⟨110, by decide⟩ : Fin 148))) :
    species (reps (⟨110, by decide⟩ : Fin 148)) h (basisElt (reps rK126) (charOfVec rK126 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK126 e (h : Coordinate 1) T126_110 i :=
  species_entry_eq_sum rK126 ⟨110, by decide⟩ e heK h T126_110 hfix126_110 hinj126_110 hcardT126_110
    (fun i => conj_mem_of_fixedPoints (reps ⟨110, by decide⟩) (reps rK126) (T126_110 i) (hfix126_110 i) h)

/-! ## Cell (126, 126): |T| = 5 -/

def T126_126list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T126_126 : Fin 5 → Coordinate 1 := fun i => T126_126list.getD i.val (0,0,0,0,0)

theorem hfix126_126 : ∀ i, ((T126_126 i : Coordinate 1) : Coordinate 1 ⧸ reps rK126)
    ∈ fixedPoints (reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126) :=
  repsFix_of_siftB rK126 ⟨126, by decide⟩ T126_126 (by decide)

theorem hinj126_126 : Function.Injective
    (fun i => ((T126_126 i : Coordinate 1) : Coordinate 1 ⧸ reps rK126)) :=
  repsInj_of_reduceAux rK126 T126_126 (by decide)

theorem hcardT126_126 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK126 ⟨126, by decide⟩ R126 hpxR126 hcardq126 (by decide)).symm

/-- **Cell (126, 126).** -/
theorem cell126_126 (e : List (ZMod 25)) (heK : charOK (basisAt rK126) e = true)
    (h : ↥(reps (⟨126, by decide⟩ : Fin 148))) :
    species (reps (⟨126, by decide⟩ : Fin 148)) h (basisElt (reps rK126) (charOfVec rK126 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK126 e (h : Coordinate 1) T126_126 i :=
  species_entry_eq_sum rK126 ⟨126, by decide⟩ e heK h T126_126 hfix126_126 hinj126_126 hcardT126_126
    (fun i => conj_mem_of_fixedPoints (reps ⟨126, by decide⟩) (reps rK126) (T126_126 i) (hfix126_126 i) h)

namespace Q2

def R126_2 : Fin 5 → Coordinate 2 := fun i => R126list.getD i.val (0,0,0,0,0)
theorem hpxR126_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK126) (R126_2 i)) := by decide
theorem hcardq126_2 : Nat.card (Coordinate 2 ⧸ reps rK126) = 5 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (126, 0) twin -/

def T126_0_2 : Fin 5 → Coordinate 2 := fun i => T126_0list.getD i.val (0,0,0,0,0)

theorem hfix126_0_2 : ∀ i, ((T126_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK126)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK126) :=
  repsFix_of_siftB2 rK126 ⟨0, by decide⟩ T126_0_2 (by decide)

theorem hinj126_0_2 : Function.Injective
    (fun i => ((T126_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK126)) :=
  repsInj_of_reduceAux2 rK126 T126_0_2 (by decide)

theorem hcardT126_0_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK126)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK126 ⟨0, by decide⟩ R126_2 hpxR126_2 hcardq126_2 (by decide)).symm

/-- **Cell (126, 0) twin (q=2).** -/
theorem cell126_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK126) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK126) (charOfVec2 rK126 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK126 e (h : Coordinate 2) T126_0_2 i :=
  species_entry_eq_sum rK126 ⟨0, by decide⟩ e heK h T126_0_2 hfix126_0_2 hinj126_0_2 hcardT126_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK126) (T126_0_2 i) (hfix126_0_2 i) h)

/-! ### Cell (126, 3) twin -/

def T126_3_2 : Fin 5 → Coordinate 2 := fun i => T126_3list.getD i.val (0,0,0,0,0)

theorem hfix126_3_2 : ∀ i, ((T126_3_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK126)
    ∈ fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK126) :=
  repsFix_of_siftB2 rK126 ⟨3, by decide⟩ T126_3_2 (by decide)

theorem hinj126_3_2 : Function.Injective
    (fun i => ((T126_3_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK126)) :=
  repsInj_of_reduceAux2 rK126 T126_3_2 (by decide)

theorem hcardT126_3_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK126)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK126 ⟨3, by decide⟩ R126_2 hpxR126_2 hcardq126_2 (by decide)).symm

/-- **Cell (126, 3) twin (q=2).** -/
theorem cell126_3_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK126) e = true)
    (h : ↥(reps (⟨3, by decide⟩ : Fin 148))) :
    species (reps (⟨3, by decide⟩ : Fin 148)) h (basisElt (reps rK126) (charOfVec2 rK126 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK126 e (h : Coordinate 2) T126_3_2 i :=
  species_entry_eq_sum rK126 ⟨3, by decide⟩ e heK h T126_3_2 hfix126_3_2 hinj126_3_2 hcardT126_3_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨3, by decide⟩) (reps rK126) (T126_3_2 i) (hfix126_3_2 i) h)

/-! ### Cell (126, 10) twin -/

def T126_10_2 : Fin 5 → Coordinate 2 := fun i => T126_10list.getD i.val (0,0,0,0,0)

theorem hfix126_10_2 : ∀ i, ((T126_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK126)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK126) :=
  repsFix_of_siftB2 rK126 ⟨10, by decide⟩ T126_10_2 (by decide)

theorem hinj126_10_2 : Function.Injective
    (fun i => ((T126_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK126)) :=
  repsInj_of_reduceAux2 rK126 T126_10_2 (by decide)

theorem hcardT126_10_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK126)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK126 ⟨10, by decide⟩ R126_2 hpxR126_2 hcardq126_2 (by decide)).symm

/-- **Cell (126, 10) twin (q=2).** -/
theorem cell126_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK126) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK126) (charOfVec2 rK126 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK126 e (h : Coordinate 2) T126_10_2 i :=
  species_entry_eq_sum rK126 ⟨10, by decide⟩ e heK h T126_10_2 hfix126_10_2 hinj126_10_2 hcardT126_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK126) (T126_10_2 i) (hfix126_10_2 i) h)

/-! ### Cell (126, 12) twin -/

def T126_12_2 : Fin 5 → Coordinate 2 := fun i => T126_12list.getD i.val (0,0,0,0,0)

theorem hfix126_12_2 : ∀ i, ((T126_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK126)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK126) :=
  repsFix_of_siftB2 rK126 ⟨12, by decide⟩ T126_12_2 (by decide)

theorem hinj126_12_2 : Function.Injective
    (fun i => ((T126_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK126)) :=
  repsInj_of_reduceAux2 rK126 T126_12_2 (by decide)

theorem hcardT126_12_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK126)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK126 ⟨12, by decide⟩ R126_2 hpxR126_2 hcardq126_2 (by decide)).symm

/-- **Cell (126, 12) twin (q=2).** -/
theorem cell126_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK126) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK126) (charOfVec2 rK126 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK126 e (h : Coordinate 2) T126_12_2 i :=
  species_entry_eq_sum rK126 ⟨12, by decide⟩ e heK h T126_12_2 hfix126_12_2 hinj126_12_2 hcardT126_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK126) (T126_12_2 i) (hfix126_12_2 i) h)

/-! ### Cell (126, 21) twin -/

def T126_21_2 : Fin 5 → Coordinate 2 := fun i => T126_21list.getD i.val (0,0,0,0,0)

theorem hfix126_21_2 : ∀ i, ((T126_21_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK126)
    ∈ fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK126) :=
  repsFix_of_siftB2 rK126 ⟨21, by decide⟩ T126_21_2 (by decide)

theorem hinj126_21_2 : Function.Injective
    (fun i => ((T126_21_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK126)) :=
  repsInj_of_reduceAux2 rK126 T126_21_2 (by decide)

theorem hcardT126_21_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK126)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK126 ⟨21, by decide⟩ R126_2 hpxR126_2 hcardq126_2 (by decide)).symm

/-- **Cell (126, 21) twin (q=2).** -/
theorem cell126_21_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK126) e = true)
    (h : ↥(reps (⟨21, by decide⟩ : Fin 148))) :
    species (reps (⟨21, by decide⟩ : Fin 148)) h (basisElt (reps rK126) (charOfVec2 rK126 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK126 e (h : Coordinate 2) T126_21_2 i :=
  species_entry_eq_sum rK126 ⟨21, by decide⟩ e heK h T126_21_2 hfix126_21_2 hinj126_21_2 hcardT126_21_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨21, by decide⟩) (reps rK126) (T126_21_2 i) (hfix126_21_2 i) h)

/-! ### Cell (126, 31) twin -/

def T126_31_2 : Fin 5 → Coordinate 2 := fun i => T126_31list.getD i.val (0,0,0,0,0)

theorem hfix126_31_2 : ∀ i, ((T126_31_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK126)
    ∈ fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK126) :=
  repsFix_of_siftB2 rK126 ⟨31, by decide⟩ T126_31_2 (by decide)

theorem hinj126_31_2 : Function.Injective
    (fun i => ((T126_31_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK126)) :=
  repsInj_of_reduceAux2 rK126 T126_31_2 (by decide)

theorem hcardT126_31_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK126)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK126 ⟨31, by decide⟩ R126_2 hpxR126_2 hcardq126_2 (by decide)).symm

/-- **Cell (126, 31) twin (q=2).** -/
theorem cell126_31_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK126) e = true)
    (h : ↥(reps (⟨31, by decide⟩ : Fin 148))) :
    species (reps (⟨31, by decide⟩ : Fin 148)) h (basisElt (reps rK126) (charOfVec2 rK126 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK126 e (h : Coordinate 2) T126_31_2 i :=
  species_entry_eq_sum rK126 ⟨31, by decide⟩ e heK h T126_31_2 hfix126_31_2 hinj126_31_2 hcardT126_31_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨31, by decide⟩) (reps rK126) (T126_31_2 i) (hfix126_31_2 i) h)

/-! ### Cell (126, 37) twin -/

def T126_37_2 : Fin 5 → Coordinate 2 := fun i => T126_37list.getD i.val (0,0,0,0,0)

theorem hfix126_37_2 : ∀ i, ((T126_37_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK126)
    ∈ fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK126) :=
  repsFix_of_siftB2 rK126 ⟨37, by decide⟩ T126_37_2 (by decide)

theorem hinj126_37_2 : Function.Injective
    (fun i => ((T126_37_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK126)) :=
  repsInj_of_reduceAux2 rK126 T126_37_2 (by decide)

theorem hcardT126_37_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK126)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK126 ⟨37, by decide⟩ R126_2 hpxR126_2 hcardq126_2 (by decide)).symm

/-- **Cell (126, 37) twin (q=2).** -/
theorem cell126_37_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK126) e = true)
    (h : ↥(reps (⟨37, by decide⟩ : Fin 148))) :
    species (reps (⟨37, by decide⟩ : Fin 148)) h (basisElt (reps rK126) (charOfVec2 rK126 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK126 e (h : Coordinate 2) T126_37_2 i :=
  species_entry_eq_sum rK126 ⟨37, by decide⟩ e heK h T126_37_2 hfix126_37_2 hinj126_37_2 hcardT126_37_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨37, by decide⟩) (reps rK126) (T126_37_2 i) (hfix126_37_2 i) h)

/-! ### Cell (126, 39) twin -/

def T126_39_2 : Fin 5 → Coordinate 2 := fun i => T126_39list.getD i.val (0,0,0,0,0)

theorem hfix126_39_2 : ∀ i, ((T126_39_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK126)
    ∈ fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK126) :=
  repsFix_of_siftB2 rK126 ⟨39, by decide⟩ T126_39_2 (by decide)

theorem hinj126_39_2 : Function.Injective
    (fun i => ((T126_39_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK126)) :=
  repsInj_of_reduceAux2 rK126 T126_39_2 (by decide)

theorem hcardT126_39_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK126)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK126 ⟨39, by decide⟩ R126_2 hpxR126_2 hcardq126_2 (by decide)).symm

/-- **Cell (126, 39) twin (q=2).** -/
theorem cell126_39_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK126) e = true)
    (h : ↥(reps (⟨39, by decide⟩ : Fin 148))) :
    species (reps (⟨39, by decide⟩ : Fin 148)) h (basisElt (reps rK126) (charOfVec2 rK126 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK126 e (h : Coordinate 2) T126_39_2 i :=
  species_entry_eq_sum rK126 ⟨39, by decide⟩ e heK h T126_39_2 hfix126_39_2 hinj126_39_2 hcardT126_39_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨39, by decide⟩) (reps rK126) (T126_39_2 i) (hfix126_39_2 i) h)

/-! ### Cell (126, 45) twin -/

def T126_45_2 : Fin 5 → Coordinate 2 := fun i => T126_45list.getD i.val (0,0,0,0,0)

theorem hfix126_45_2 : ∀ i, ((T126_45_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK126)
    ∈ fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK126) :=
  repsFix_of_siftB2 rK126 ⟨45, by decide⟩ T126_45_2 (by decide)

theorem hinj126_45_2 : Function.Injective
    (fun i => ((T126_45_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK126)) :=
  repsInj_of_reduceAux2 rK126 T126_45_2 (by decide)

theorem hcardT126_45_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK126)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK126 ⟨45, by decide⟩ R126_2 hpxR126_2 hcardq126_2 (by decide)).symm

/-- **Cell (126, 45) twin (q=2).** -/
theorem cell126_45_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK126) e = true)
    (h : ↥(reps (⟨45, by decide⟩ : Fin 148))) :
    species (reps (⟨45, by decide⟩ : Fin 148)) h (basisElt (reps rK126) (charOfVec2 rK126 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK126 e (h : Coordinate 2) T126_45_2 i :=
  species_entry_eq_sum rK126 ⟨45, by decide⟩ e heK h T126_45_2 hfix126_45_2 hinj126_45_2 hcardT126_45_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨45, by decide⟩) (reps rK126) (T126_45_2 i) (hfix126_45_2 i) h)

/-! ### Cell (126, 48) twin -/

def T126_48_2 : Fin 5 → Coordinate 2 := fun i => T126_48list.getD i.val (0,0,0,0,0)

theorem hfix126_48_2 : ∀ i, ((T126_48_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK126)
    ∈ fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK126) :=
  repsFix_of_siftB2 rK126 ⟨48, by decide⟩ T126_48_2 (by decide)

theorem hinj126_48_2 : Function.Injective
    (fun i => ((T126_48_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK126)) :=
  repsInj_of_reduceAux2 rK126 T126_48_2 (by decide)

theorem hcardT126_48_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK126)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK126 ⟨48, by decide⟩ R126_2 hpxR126_2 hcardq126_2 (by decide)).symm

/-- **Cell (126, 48) twin (q=2).** -/
theorem cell126_48_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK126) e = true)
    (h : ↥(reps (⟨48, by decide⟩ : Fin 148))) :
    species (reps (⟨48, by decide⟩ : Fin 148)) h (basisElt (reps rK126) (charOfVec2 rK126 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK126 e (h : Coordinate 2) T126_48_2 i :=
  species_entry_eq_sum rK126 ⟨48, by decide⟩ e heK h T126_48_2 hfix126_48_2 hinj126_48_2 hcardT126_48_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨48, by decide⟩) (reps rK126) (T126_48_2 i) (hfix126_48_2 i) h)

/-! ### Cell (126, 53) twin -/

def T126_53_2 : Fin 5 → Coordinate 2 := fun i => T126_53list.getD i.val (0,0,0,0,0)

theorem hfix126_53_2 : ∀ i, ((T126_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK126)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK126) :=
  repsFix_of_siftB2 rK126 ⟨53, by decide⟩ T126_53_2 (by decide)

theorem hinj126_53_2 : Function.Injective
    (fun i => ((T126_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK126)) :=
  repsInj_of_reduceAux2 rK126 T126_53_2 (by decide)

theorem hcardT126_53_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK126)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK126 ⟨53, by decide⟩ R126_2 hpxR126_2 hcardq126_2 (by decide)).symm

/-- **Cell (126, 53) twin (q=2).** -/
theorem cell126_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK126) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK126) (charOfVec2 rK126 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK126 e (h : Coordinate 2) T126_53_2 i :=
  species_entry_eq_sum rK126 ⟨53, by decide⟩ e heK h T126_53_2 hfix126_53_2 hinj126_53_2 hcardT126_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK126) (T126_53_2 i) (hfix126_53_2 i) h)

/-! ### Cell (126, 82) twin -/

def T126_82_2 : Fin 5 → Coordinate 2 := fun i => T126_82list.getD i.val (0,0,0,0,0)

theorem hfix126_82_2 : ∀ i, ((T126_82_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK126)
    ∈ fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK126) :=
  repsFix_of_siftB2 rK126 ⟨82, by decide⟩ T126_82_2 (by decide)

theorem hinj126_82_2 : Function.Injective
    (fun i => ((T126_82_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK126)) :=
  repsInj_of_reduceAux2 rK126 T126_82_2 (by decide)

theorem hcardT126_82_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK126)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK126 ⟨82, by decide⟩ R126_2 hpxR126_2 hcardq126_2 (by decide)).symm

/-- **Cell (126, 82) twin (q=2).** -/
theorem cell126_82_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK126) e = true)
    (h : ↥(reps (⟨82, by decide⟩ : Fin 148))) :
    species (reps (⟨82, by decide⟩ : Fin 148)) h (basisElt (reps rK126) (charOfVec2 rK126 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK126 e (h : Coordinate 2) T126_82_2 i :=
  species_entry_eq_sum rK126 ⟨82, by decide⟩ e heK h T126_82_2 hfix126_82_2 hinj126_82_2 hcardT126_82_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨82, by decide⟩) (reps rK126) (T126_82_2 i) (hfix126_82_2 i) h)

/-! ### Cell (126, 93) twin -/

def T126_93_2 : Fin 5 → Coordinate 2 := fun i => T126_93list.getD i.val (0,0,0,0,0)

theorem hfix126_93_2 : ∀ i, ((T126_93_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK126)
    ∈ fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK126) :=
  repsFix_of_siftB2 rK126 ⟨93, by decide⟩ T126_93_2 (by decide)

theorem hinj126_93_2 : Function.Injective
    (fun i => ((T126_93_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK126)) :=
  repsInj_of_reduceAux2 rK126 T126_93_2 (by decide)

theorem hcardT126_93_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK126)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK126 ⟨93, by decide⟩ R126_2 hpxR126_2 hcardq126_2 (by decide)).symm

/-- **Cell (126, 93) twin (q=2).** -/
theorem cell126_93_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK126) e = true)
    (h : ↥(reps (⟨93, by decide⟩ : Fin 148))) :
    species (reps (⟨93, by decide⟩ : Fin 148)) h (basisElt (reps rK126) (charOfVec2 rK126 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK126 e (h : Coordinate 2) T126_93_2 i :=
  species_entry_eq_sum rK126 ⟨93, by decide⟩ e heK h T126_93_2 hfix126_93_2 hinj126_93_2 hcardT126_93_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨93, by decide⟩) (reps rK126) (T126_93_2 i) (hfix126_93_2 i) h)

/-! ### Cell (126, 99) twin -/

def T126_99_2 : Fin 5 → Coordinate 2 := fun i => T126_99list.getD i.val (0,0,0,0,0)

theorem hfix126_99_2 : ∀ i, ((T126_99_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK126)
    ∈ fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK126) :=
  repsFix_of_siftB2 rK126 ⟨99, by decide⟩ T126_99_2 (by decide)

theorem hinj126_99_2 : Function.Injective
    (fun i => ((T126_99_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK126)) :=
  repsInj_of_reduceAux2 rK126 T126_99_2 (by decide)

theorem hcardT126_99_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK126)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK126 ⟨99, by decide⟩ R126_2 hpxR126_2 hcardq126_2 (by decide)).symm

/-- **Cell (126, 99) twin (q=2).** -/
theorem cell126_99_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK126) e = true)
    (h : ↥(reps (⟨99, by decide⟩ : Fin 148))) :
    species (reps (⟨99, by decide⟩ : Fin 148)) h (basisElt (reps rK126) (charOfVec2 rK126 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK126 e (h : Coordinate 2) T126_99_2 i :=
  species_entry_eq_sum rK126 ⟨99, by decide⟩ e heK h T126_99_2 hfix126_99_2 hinj126_99_2 hcardT126_99_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨99, by decide⟩) (reps rK126) (T126_99_2 i) (hfix126_99_2 i) h)

/-! ### Cell (126, 101) twin -/

def T126_101_2 : Fin 5 → Coordinate 2 := fun i => T126_101list.getD i.val (0,0,0,0,0)

theorem hfix126_101_2 : ∀ i, ((T126_101_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK126)
    ∈ fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK126) :=
  repsFix_of_siftB2 rK126 ⟨101, by decide⟩ T126_101_2 (by decide)

theorem hinj126_101_2 : Function.Injective
    (fun i => ((T126_101_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK126)) :=
  repsInj_of_reduceAux2 rK126 T126_101_2 (by decide)

theorem hcardT126_101_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK126)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK126 ⟨101, by decide⟩ R126_2 hpxR126_2 hcardq126_2 (by decide)).symm

/-- **Cell (126, 101) twin (q=2).** -/
theorem cell126_101_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK126) e = true)
    (h : ↥(reps (⟨101, by decide⟩ : Fin 148))) :
    species (reps (⟨101, by decide⟩ : Fin 148)) h (basisElt (reps rK126) (charOfVec2 rK126 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK126 e (h : Coordinate 2) T126_101_2 i :=
  species_entry_eq_sum rK126 ⟨101, by decide⟩ e heK h T126_101_2 hfix126_101_2 hinj126_101_2 hcardT126_101_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨101, by decide⟩) (reps rK126) (T126_101_2 i) (hfix126_101_2 i) h)

/-! ### Cell (126, 107) twin -/

def T126_107_2 : Fin 5 → Coordinate 2 := fun i => T126_107list.getD i.val (0,0,0,0,0)

theorem hfix126_107_2 : ∀ i, ((T126_107_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK126)
    ∈ fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK126) :=
  repsFix_of_siftB2 rK126 ⟨107, by decide⟩ T126_107_2 (by decide)

theorem hinj126_107_2 : Function.Injective
    (fun i => ((T126_107_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK126)) :=
  repsInj_of_reduceAux2 rK126 T126_107_2 (by decide)

theorem hcardT126_107_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK126)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK126 ⟨107, by decide⟩ R126_2 hpxR126_2 hcardq126_2 (by decide)).symm

/-- **Cell (126, 107) twin (q=2).** -/
theorem cell126_107_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK126) e = true)
    (h : ↥(reps (⟨107, by decide⟩ : Fin 148))) :
    species (reps (⟨107, by decide⟩ : Fin 148)) h (basisElt (reps rK126) (charOfVec2 rK126 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK126 e (h : Coordinate 2) T126_107_2 i :=
  species_entry_eq_sum rK126 ⟨107, by decide⟩ e heK h T126_107_2 hfix126_107_2 hinj126_107_2 hcardT126_107_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨107, by decide⟩) (reps rK126) (T126_107_2 i) (hfix126_107_2 i) h)

/-! ### Cell (126, 110) twin -/

def T126_110_2 : Fin 5 → Coordinate 2 := fun i => T126_110list.getD i.val (0,0,0,0,0)

theorem hfix126_110_2 : ∀ i, ((T126_110_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK126)
    ∈ fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK126) :=
  repsFix_of_siftB2 rK126 ⟨110, by decide⟩ T126_110_2 (by decide)

theorem hinj126_110_2 : Function.Injective
    (fun i => ((T126_110_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK126)) :=
  repsInj_of_reduceAux2 rK126 T126_110_2 (by decide)

theorem hcardT126_110_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK126)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK126 ⟨110, by decide⟩ R126_2 hpxR126_2 hcardq126_2 (by decide)).symm

/-- **Cell (126, 110) twin (q=2).** -/
theorem cell126_110_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK126) e = true)
    (h : ↥(reps (⟨110, by decide⟩ : Fin 148))) :
    species (reps (⟨110, by decide⟩ : Fin 148)) h (basisElt (reps rK126) (charOfVec2 rK126 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK126 e (h : Coordinate 2) T126_110_2 i :=
  species_entry_eq_sum rK126 ⟨110, by decide⟩ e heK h T126_110_2 hfix126_110_2 hinj126_110_2 hcardT126_110_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨110, by decide⟩) (reps rK126) (T126_110_2 i) (hfix126_110_2 i) h)

/-! ### Cell (126, 126) twin -/

def T126_126_2 : Fin 5 → Coordinate 2 := fun i => T126_126list.getD i.val (0,0,0,0,0)

theorem hfix126_126_2 : ∀ i, ((T126_126_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK126)
    ∈ fixedPoints (reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK126) :=
  repsFix_of_siftB2 rK126 ⟨126, by decide⟩ T126_126_2 (by decide)

theorem hinj126_126_2 : Function.Injective
    (fun i => ((T126_126_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK126)) :=
  repsInj_of_reduceAux2 rK126 T126_126_2 (by decide)

theorem hcardT126_126_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK126)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK126 ⟨126, by decide⟩ R126_2 hpxR126_2 hcardq126_2 (by decide)).symm

/-- **Cell (126, 126) twin (q=2).** -/
theorem cell126_126_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK126) e = true)
    (h : ↥(reps (⟨126, by decide⟩ : Fin 148))) :
    species (reps (⟨126, by decide⟩ : Fin 148)) h (basisElt (reps rK126) (charOfVec2 rK126 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK126 e (h : Coordinate 2) T126_126_2 i :=
  species_entry_eq_sum rK126 ⟨126, by decide⟩ e heK h T126_126_2 hfix126_126_2 hinj126_126_2 hcardT126_126_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨126, by decide⟩) (reps rK126) (T126_126_2 i) (hfix126_126_2 i) h)

end Q2

/-! # K-class rK = 127  (|G/K| = 5) -/

def rK127 : Fin 148 := ⟨127, by decide⟩

def R127list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def R127 : Fin 5 → Coordinate 1 := fun i => R127list.getD i.val (0,0,0,0,0)

theorem hpxR127 : Function.Injective (fun i => reduceAux 1 (basisAt rK127) (R127 i)) := by decide
theorem hcardq127 : Nat.card (Coordinate 1 ⧸ reps rK127) = 5 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (127, 0): |T| = 5 -/

def T127_0list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T127_0 : Fin 5 → Coordinate 1 := fun i => T127_0list.getD i.val (0,0,0,0,0)

theorem hfix127_0 : ∀ i, ((T127_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK127)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127) :=
  repsFix_of_siftB rK127 ⟨0, by decide⟩ T127_0 (by decide)

theorem hinj127_0 : Function.Injective
    (fun i => ((T127_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK127)) :=
  repsInj_of_reduceAux rK127 T127_0 (by decide)

theorem hcardT127_0 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK127 ⟨0, by decide⟩ R127 hpxR127 hcardq127 (by decide)).symm

/-- **Cell (127, 0).** -/
theorem cell127_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK127) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK127) (charOfVec rK127 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK127 e (h : Coordinate 1) T127_0 i :=
  species_entry_eq_sum rK127 ⟨0, by decide⟩ e heK h T127_0 hfix127_0 hinj127_0 hcardT127_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK127) (T127_0 i) (hfix127_0 i) h)

/-! ## Cell (127, 3): |T| = 5 -/

def T127_3list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T127_3 : Fin 5 → Coordinate 1 := fun i => T127_3list.getD i.val (0,0,0,0,0)

theorem hfix127_3 : ∀ i, ((T127_3 i : Coordinate 1) : Coordinate 1 ⧸ reps rK127)
    ∈ fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127) :=
  repsFix_of_siftB rK127 ⟨3, by decide⟩ T127_3 (by decide)

theorem hinj127_3 : Function.Injective
    (fun i => ((T127_3 i : Coordinate 1) : Coordinate 1 ⧸ reps rK127)) :=
  repsInj_of_reduceAux rK127 T127_3 (by decide)

theorem hcardT127_3 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK127 ⟨3, by decide⟩ R127 hpxR127 hcardq127 (by decide)).symm

/-- **Cell (127, 3).** -/
theorem cell127_3 (e : List (ZMod 25)) (heK : charOK (basisAt rK127) e = true)
    (h : ↥(reps (⟨3, by decide⟩ : Fin 148))) :
    species (reps (⟨3, by decide⟩ : Fin 148)) h (basisElt (reps rK127) (charOfVec rK127 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK127 e (h : Coordinate 1) T127_3 i :=
  species_entry_eq_sum rK127 ⟨3, by decide⟩ e heK h T127_3 hfix127_3 hinj127_3 hcardT127_3
    (fun i => conj_mem_of_fixedPoints (reps ⟨3, by decide⟩) (reps rK127) (T127_3 i) (hfix127_3 i) h)

/-! ## Cell (127, 10): |T| = 5 -/

def T127_10list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T127_10 : Fin 5 → Coordinate 1 := fun i => T127_10list.getD i.val (0,0,0,0,0)

theorem hfix127_10 : ∀ i, ((T127_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK127)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127) :=
  repsFix_of_siftB rK127 ⟨10, by decide⟩ T127_10 (by decide)

theorem hinj127_10 : Function.Injective
    (fun i => ((T127_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK127)) :=
  repsInj_of_reduceAux rK127 T127_10 (by decide)

theorem hcardT127_10 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK127 ⟨10, by decide⟩ R127 hpxR127 hcardq127 (by decide)).symm

/-- **Cell (127, 10).** -/
theorem cell127_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK127) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK127) (charOfVec rK127 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK127 e (h : Coordinate 1) T127_10 i :=
  species_entry_eq_sum rK127 ⟨10, by decide⟩ e heK h T127_10 hfix127_10 hinj127_10 hcardT127_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK127) (T127_10 i) (hfix127_10 i) h)

/-! ## Cell (127, 12): |T| = 5 -/

def T127_12list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T127_12 : Fin 5 → Coordinate 1 := fun i => T127_12list.getD i.val (0,0,0,0,0)

theorem hfix127_12 : ∀ i, ((T127_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK127)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127) :=
  repsFix_of_siftB rK127 ⟨12, by decide⟩ T127_12 (by decide)

theorem hinj127_12 : Function.Injective
    (fun i => ((T127_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK127)) :=
  repsInj_of_reduceAux rK127 T127_12 (by decide)

theorem hcardT127_12 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK127 ⟨12, by decide⟩ R127 hpxR127 hcardq127 (by decide)).symm

/-- **Cell (127, 12).** -/
theorem cell127_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK127) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK127) (charOfVec rK127 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK127 e (h : Coordinate 1) T127_12 i :=
  species_entry_eq_sum rK127 ⟨12, by decide⟩ e heK h T127_12 hfix127_12 hinj127_12 hcardT127_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK127) (T127_12 i) (hfix127_12 i) h)

/-! ## Cell (127, 21): |T| = 5 -/

def T127_21list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T127_21 : Fin 5 → Coordinate 1 := fun i => T127_21list.getD i.val (0,0,0,0,0)

theorem hfix127_21 : ∀ i, ((T127_21 i : Coordinate 1) : Coordinate 1 ⧸ reps rK127)
    ∈ fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127) :=
  repsFix_of_siftB rK127 ⟨21, by decide⟩ T127_21 (by decide)

theorem hinj127_21 : Function.Injective
    (fun i => ((T127_21 i : Coordinate 1) : Coordinate 1 ⧸ reps rK127)) :=
  repsInj_of_reduceAux rK127 T127_21 (by decide)

theorem hcardT127_21 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK127 ⟨21, by decide⟩ R127 hpxR127 hcardq127 (by decide)).symm

/-- **Cell (127, 21).** -/
theorem cell127_21 (e : List (ZMod 25)) (heK : charOK (basisAt rK127) e = true)
    (h : ↥(reps (⟨21, by decide⟩ : Fin 148))) :
    species (reps (⟨21, by decide⟩ : Fin 148)) h (basisElt (reps rK127) (charOfVec rK127 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK127 e (h : Coordinate 1) T127_21 i :=
  species_entry_eq_sum rK127 ⟨21, by decide⟩ e heK h T127_21 hfix127_21 hinj127_21 hcardT127_21
    (fun i => conj_mem_of_fixedPoints (reps ⟨21, by decide⟩) (reps rK127) (T127_21 i) (hfix127_21 i) h)

/-! ## Cell (127, 32): |T| = 5 -/

def T127_32list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T127_32 : Fin 5 → Coordinate 1 := fun i => T127_32list.getD i.val (0,0,0,0,0)

theorem hfix127_32 : ∀ i, ((T127_32 i : Coordinate 1) : Coordinate 1 ⧸ reps rK127)
    ∈ fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127) :=
  repsFix_of_siftB rK127 ⟨32, by decide⟩ T127_32 (by decide)

theorem hinj127_32 : Function.Injective
    (fun i => ((T127_32 i : Coordinate 1) : Coordinate 1 ⧸ reps rK127)) :=
  repsInj_of_reduceAux rK127 T127_32 (by decide)

theorem hcardT127_32 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK127 ⟨32, by decide⟩ R127 hpxR127 hcardq127 (by decide)).symm

/-- **Cell (127, 32).** -/
theorem cell127_32 (e : List (ZMod 25)) (heK : charOK (basisAt rK127) e = true)
    (h : ↥(reps (⟨32, by decide⟩ : Fin 148))) :
    species (reps (⟨32, by decide⟩ : Fin 148)) h (basisElt (reps rK127) (charOfVec rK127 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK127 e (h : Coordinate 1) T127_32 i :=
  species_entry_eq_sum rK127 ⟨32, by decide⟩ e heK h T127_32 hfix127_32 hinj127_32 hcardT127_32
    (fun i => conj_mem_of_fixedPoints (reps ⟨32, by decide⟩) (reps rK127) (T127_32 i) (hfix127_32 i) h)

/-! ## Cell (127, 33): |T| = 5 -/

def T127_33list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T127_33 : Fin 5 → Coordinate 1 := fun i => T127_33list.getD i.val (0,0,0,0,0)

theorem hfix127_33 : ∀ i, ((T127_33 i : Coordinate 1) : Coordinate 1 ⧸ reps rK127)
    ∈ fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127) :=
  repsFix_of_siftB rK127 ⟨33, by decide⟩ T127_33 (by decide)

theorem hinj127_33 : Function.Injective
    (fun i => ((T127_33 i : Coordinate 1) : Coordinate 1 ⧸ reps rK127)) :=
  repsInj_of_reduceAux rK127 T127_33 (by decide)

theorem hcardT127_33 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK127 ⟨33, by decide⟩ R127 hpxR127 hcardq127 (by decide)).symm

/-- **Cell (127, 33).** -/
theorem cell127_33 (e : List (ZMod 25)) (heK : charOK (basisAt rK127) e = true)
    (h : ↥(reps (⟨33, by decide⟩ : Fin 148))) :
    species (reps (⟨33, by decide⟩ : Fin 148)) h (basisElt (reps rK127) (charOfVec rK127 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK127 e (h : Coordinate 1) T127_33 i :=
  species_entry_eq_sum rK127 ⟨33, by decide⟩ e heK h T127_33 hfix127_33 hinj127_33 hcardT127_33
    (fun i => conj_mem_of_fixedPoints (reps ⟨33, by decide⟩) (reps rK127) (T127_33 i) (hfix127_33 i) h)

/-! ## Cell (127, 40): |T| = 5 -/

def T127_40list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T127_40 : Fin 5 → Coordinate 1 := fun i => T127_40list.getD i.val (0,0,0,0,0)

theorem hfix127_40 : ∀ i, ((T127_40 i : Coordinate 1) : Coordinate 1 ⧸ reps rK127)
    ∈ fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127) :=
  repsFix_of_siftB rK127 ⟨40, by decide⟩ T127_40 (by decide)

theorem hinj127_40 : Function.Injective
    (fun i => ((T127_40 i : Coordinate 1) : Coordinate 1 ⧸ reps rK127)) :=
  repsInj_of_reduceAux rK127 T127_40 (by decide)

theorem hcardT127_40 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK127 ⟨40, by decide⟩ R127 hpxR127 hcardq127 (by decide)).symm

/-- **Cell (127, 40).** -/
theorem cell127_40 (e : List (ZMod 25)) (heK : charOK (basisAt rK127) e = true)
    (h : ↥(reps (⟨40, by decide⟩ : Fin 148))) :
    species (reps (⟨40, by decide⟩ : Fin 148)) h (basisElt (reps rK127) (charOfVec rK127 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK127 e (h : Coordinate 1) T127_40 i :=
  species_entry_eq_sum rK127 ⟨40, by decide⟩ e heK h T127_40 hfix127_40 hinj127_40 hcardT127_40
    (fun i => conj_mem_of_fixedPoints (reps ⟨40, by decide⟩) (reps rK127) (T127_40 i) (hfix127_40 i) h)

/-! ## Cell (127, 46): |T| = 5 -/

def T127_46list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T127_46 : Fin 5 → Coordinate 1 := fun i => T127_46list.getD i.val (0,0,0,0,0)

theorem hfix127_46 : ∀ i, ((T127_46 i : Coordinate 1) : Coordinate 1 ⧸ reps rK127)
    ∈ fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127) :=
  repsFix_of_siftB rK127 ⟨46, by decide⟩ T127_46 (by decide)

theorem hinj127_46 : Function.Injective
    (fun i => ((T127_46 i : Coordinate 1) : Coordinate 1 ⧸ reps rK127)) :=
  repsInj_of_reduceAux rK127 T127_46 (by decide)

theorem hcardT127_46 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK127 ⟨46, by decide⟩ R127 hpxR127 hcardq127 (by decide)).symm

/-- **Cell (127, 46).** -/
theorem cell127_46 (e : List (ZMod 25)) (heK : charOK (basisAt rK127) e = true)
    (h : ↥(reps (⟨46, by decide⟩ : Fin 148))) :
    species (reps (⟨46, by decide⟩ : Fin 148)) h (basisElt (reps rK127) (charOfVec rK127 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK127 e (h : Coordinate 1) T127_46 i :=
  species_entry_eq_sum rK127 ⟨46, by decide⟩ e heK h T127_46 hfix127_46 hinj127_46 hcardT127_46
    (fun i => conj_mem_of_fixedPoints (reps ⟨46, by decide⟩) (reps rK127) (T127_46 i) (hfix127_46 i) h)

/-! ## Cell (127, 49): |T| = 5 -/

def T127_49list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T127_49 : Fin 5 → Coordinate 1 := fun i => T127_49list.getD i.val (0,0,0,0,0)

theorem hfix127_49 : ∀ i, ((T127_49 i : Coordinate 1) : Coordinate 1 ⧸ reps rK127)
    ∈ fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127) :=
  repsFix_of_siftB rK127 ⟨49, by decide⟩ T127_49 (by decide)

theorem hinj127_49 : Function.Injective
    (fun i => ((T127_49 i : Coordinate 1) : Coordinate 1 ⧸ reps rK127)) :=
  repsInj_of_reduceAux rK127 T127_49 (by decide)

theorem hcardT127_49 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK127 ⟨49, by decide⟩ R127 hpxR127 hcardq127 (by decide)).symm

/-- **Cell (127, 49).** -/
theorem cell127_49 (e : List (ZMod 25)) (heK : charOK (basisAt rK127) e = true)
    (h : ↥(reps (⟨49, by decide⟩ : Fin 148))) :
    species (reps (⟨49, by decide⟩ : Fin 148)) h (basisElt (reps rK127) (charOfVec rK127 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK127 e (h : Coordinate 1) T127_49 i :=
  species_entry_eq_sum rK127 ⟨49, by decide⟩ e heK h T127_49 hfix127_49 hinj127_49 hcardT127_49
    (fun i => conj_mem_of_fixedPoints (reps ⟨49, by decide⟩) (reps rK127) (T127_49 i) (hfix127_49 i) h)

/-! ## Cell (127, 53): |T| = 5 -/

def T127_53list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T127_53 : Fin 5 → Coordinate 1 := fun i => T127_53list.getD i.val (0,0,0,0,0)

theorem hfix127_53 : ∀ i, ((T127_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK127)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127) :=
  repsFix_of_siftB rK127 ⟨53, by decide⟩ T127_53 (by decide)

theorem hinj127_53 : Function.Injective
    (fun i => ((T127_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK127)) :=
  repsInj_of_reduceAux rK127 T127_53 (by decide)

theorem hcardT127_53 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK127 ⟨53, by decide⟩ R127 hpxR127 hcardq127 (by decide)).symm

/-- **Cell (127, 53).** -/
theorem cell127_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK127) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK127) (charOfVec rK127 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK127 e (h : Coordinate 1) T127_53 i :=
  species_entry_eq_sum rK127 ⟨53, by decide⟩ e heK h T127_53 hfix127_53 hinj127_53 hcardT127_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK127) (T127_53 i) (hfix127_53 i) h)

/-! ## Cell (127, 82): |T| = 5 -/

def T127_82list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T127_82 : Fin 5 → Coordinate 1 := fun i => T127_82list.getD i.val (0,0,0,0,0)

theorem hfix127_82 : ∀ i, ((T127_82 i : Coordinate 1) : Coordinate 1 ⧸ reps rK127)
    ∈ fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127) :=
  repsFix_of_siftB rK127 ⟨82, by decide⟩ T127_82 (by decide)

theorem hinj127_82 : Function.Injective
    (fun i => ((T127_82 i : Coordinate 1) : Coordinate 1 ⧸ reps rK127)) :=
  repsInj_of_reduceAux rK127 T127_82 (by decide)

theorem hcardT127_82 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK127 ⟨82, by decide⟩ R127 hpxR127 hcardq127 (by decide)).symm

/-- **Cell (127, 82).** -/
theorem cell127_82 (e : List (ZMod 25)) (heK : charOK (basisAt rK127) e = true)
    (h : ↥(reps (⟨82, by decide⟩ : Fin 148))) :
    species (reps (⟨82, by decide⟩ : Fin 148)) h (basisElt (reps rK127) (charOfVec rK127 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK127 e (h : Coordinate 1) T127_82 i :=
  species_entry_eq_sum rK127 ⟨82, by decide⟩ e heK h T127_82 hfix127_82 hinj127_82 hcardT127_82
    (fun i => conj_mem_of_fixedPoints (reps ⟨82, by decide⟩) (reps rK127) (T127_82 i) (hfix127_82 i) h)

/-! ## Cell (127, 94): |T| = 5 -/

def T127_94list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T127_94 : Fin 5 → Coordinate 1 := fun i => T127_94list.getD i.val (0,0,0,0,0)

theorem hfix127_94 : ∀ i, ((T127_94 i : Coordinate 1) : Coordinate 1 ⧸ reps rK127)
    ∈ fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127) :=
  repsFix_of_siftB rK127 ⟨94, by decide⟩ T127_94 (by decide)

theorem hinj127_94 : Function.Injective
    (fun i => ((T127_94 i : Coordinate 1) : Coordinate 1 ⧸ reps rK127)) :=
  repsInj_of_reduceAux rK127 T127_94 (by decide)

theorem hcardT127_94 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK127 ⟨94, by decide⟩ R127 hpxR127 hcardq127 (by decide)).symm

/-- **Cell (127, 94).** -/
theorem cell127_94 (e : List (ZMod 25)) (heK : charOK (basisAt rK127) e = true)
    (h : ↥(reps (⟨94, by decide⟩ : Fin 148))) :
    species (reps (⟨94, by decide⟩ : Fin 148)) h (basisElt (reps rK127) (charOfVec rK127 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK127 e (h : Coordinate 1) T127_94 i :=
  species_entry_eq_sum rK127 ⟨94, by decide⟩ e heK h T127_94 hfix127_94 hinj127_94 hcardT127_94
    (fun i => conj_mem_of_fixedPoints (reps ⟨94, by decide⟩) (reps rK127) (T127_94 i) (hfix127_94 i) h)

/-! ## Cell (127, 95): |T| = 5 -/

def T127_95list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T127_95 : Fin 5 → Coordinate 1 := fun i => T127_95list.getD i.val (0,0,0,0,0)

theorem hfix127_95 : ∀ i, ((T127_95 i : Coordinate 1) : Coordinate 1 ⧸ reps rK127)
    ∈ fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127) :=
  repsFix_of_siftB rK127 ⟨95, by decide⟩ T127_95 (by decide)

theorem hinj127_95 : Function.Injective
    (fun i => ((T127_95 i : Coordinate 1) : Coordinate 1 ⧸ reps rK127)) :=
  repsInj_of_reduceAux rK127 T127_95 (by decide)

theorem hcardT127_95 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK127 ⟨95, by decide⟩ R127 hpxR127 hcardq127 (by decide)).symm

/-- **Cell (127, 95).** -/
theorem cell127_95 (e : List (ZMod 25)) (heK : charOK (basisAt rK127) e = true)
    (h : ↥(reps (⟨95, by decide⟩ : Fin 148))) :
    species (reps (⟨95, by decide⟩ : Fin 148)) h (basisElt (reps rK127) (charOfVec rK127 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK127 e (h : Coordinate 1) T127_95 i :=
  species_entry_eq_sum rK127 ⟨95, by decide⟩ e heK h T127_95 hfix127_95 hinj127_95 hcardT127_95
    (fun i => conj_mem_of_fixedPoints (reps ⟨95, by decide⟩) (reps rK127) (T127_95 i) (hfix127_95 i) h)

/-! ## Cell (127, 102): |T| = 5 -/

def T127_102list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T127_102 : Fin 5 → Coordinate 1 := fun i => T127_102list.getD i.val (0,0,0,0,0)

theorem hfix127_102 : ∀ i, ((T127_102 i : Coordinate 1) : Coordinate 1 ⧸ reps rK127)
    ∈ fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127) :=
  repsFix_of_siftB rK127 ⟨102, by decide⟩ T127_102 (by decide)

theorem hinj127_102 : Function.Injective
    (fun i => ((T127_102 i : Coordinate 1) : Coordinate 1 ⧸ reps rK127)) :=
  repsInj_of_reduceAux rK127 T127_102 (by decide)

theorem hcardT127_102 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK127 ⟨102, by decide⟩ R127 hpxR127 hcardq127 (by decide)).symm

/-- **Cell (127, 102).** -/
theorem cell127_102 (e : List (ZMod 25)) (heK : charOK (basisAt rK127) e = true)
    (h : ↥(reps (⟨102, by decide⟩ : Fin 148))) :
    species (reps (⟨102, by decide⟩ : Fin 148)) h (basisElt (reps rK127) (charOfVec rK127 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK127 e (h : Coordinate 1) T127_102 i :=
  species_entry_eq_sum rK127 ⟨102, by decide⟩ e heK h T127_102 hfix127_102 hinj127_102 hcardT127_102
    (fun i => conj_mem_of_fixedPoints (reps ⟨102, by decide⟩) (reps rK127) (T127_102 i) (hfix127_102 i) h)

/-! ## Cell (127, 108): |T| = 5 -/

def T127_108list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T127_108 : Fin 5 → Coordinate 1 := fun i => T127_108list.getD i.val (0,0,0,0,0)

theorem hfix127_108 : ∀ i, ((T127_108 i : Coordinate 1) : Coordinate 1 ⧸ reps rK127)
    ∈ fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127) :=
  repsFix_of_siftB rK127 ⟨108, by decide⟩ T127_108 (by decide)

theorem hinj127_108 : Function.Injective
    (fun i => ((T127_108 i : Coordinate 1) : Coordinate 1 ⧸ reps rK127)) :=
  repsInj_of_reduceAux rK127 T127_108 (by decide)

theorem hcardT127_108 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK127 ⟨108, by decide⟩ R127 hpxR127 hcardq127 (by decide)).symm

/-- **Cell (127, 108).** -/
theorem cell127_108 (e : List (ZMod 25)) (heK : charOK (basisAt rK127) e = true)
    (h : ↥(reps (⟨108, by decide⟩ : Fin 148))) :
    species (reps (⟨108, by decide⟩ : Fin 148)) h (basisElt (reps rK127) (charOfVec rK127 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK127 e (h : Coordinate 1) T127_108 i :=
  species_entry_eq_sum rK127 ⟨108, by decide⟩ e heK h T127_108 hfix127_108 hinj127_108 hcardT127_108
    (fun i => conj_mem_of_fixedPoints (reps ⟨108, by decide⟩) (reps rK127) (T127_108 i) (hfix127_108 i) h)

/-! ## Cell (127, 111): |T| = 5 -/

def T127_111list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T127_111 : Fin 5 → Coordinate 1 := fun i => T127_111list.getD i.val (0,0,0,0,0)

theorem hfix127_111 : ∀ i, ((T127_111 i : Coordinate 1) : Coordinate 1 ⧸ reps rK127)
    ∈ fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127) :=
  repsFix_of_siftB rK127 ⟨111, by decide⟩ T127_111 (by decide)

theorem hinj127_111 : Function.Injective
    (fun i => ((T127_111 i : Coordinate 1) : Coordinate 1 ⧸ reps rK127)) :=
  repsInj_of_reduceAux rK127 T127_111 (by decide)

theorem hcardT127_111 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK127 ⟨111, by decide⟩ R127 hpxR127 hcardq127 (by decide)).symm

/-- **Cell (127, 111).** -/
theorem cell127_111 (e : List (ZMod 25)) (heK : charOK (basisAt rK127) e = true)
    (h : ↥(reps (⟨111, by decide⟩ : Fin 148))) :
    species (reps (⟨111, by decide⟩ : Fin 148)) h (basisElt (reps rK127) (charOfVec rK127 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK127 e (h : Coordinate 1) T127_111 i :=
  species_entry_eq_sum rK127 ⟨111, by decide⟩ e heK h T127_111 hfix127_111 hinj127_111 hcardT127_111
    (fun i => conj_mem_of_fixedPoints (reps ⟨111, by decide⟩) (reps rK127) (T127_111 i) (hfix127_111 i) h)

/-! ## Cell (127, 127): |T| = 5 -/

def T127_127list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T127_127 : Fin 5 → Coordinate 1 := fun i => T127_127list.getD i.val (0,0,0,0,0)

theorem hfix127_127 : ∀ i, ((T127_127 i : Coordinate 1) : Coordinate 1 ⧸ reps rK127)
    ∈ fixedPoints (reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127) :=
  repsFix_of_siftB rK127 ⟨127, by decide⟩ T127_127 (by decide)

theorem hinj127_127 : Function.Injective
    (fun i => ((T127_127 i : Coordinate 1) : Coordinate 1 ⧸ reps rK127)) :=
  repsInj_of_reduceAux rK127 T127_127 (by decide)

theorem hcardT127_127 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK127 ⟨127, by decide⟩ R127 hpxR127 hcardq127 (by decide)).symm

/-- **Cell (127, 127).** -/
theorem cell127_127 (e : List (ZMod 25)) (heK : charOK (basisAt rK127) e = true)
    (h : ↥(reps (⟨127, by decide⟩ : Fin 148))) :
    species (reps (⟨127, by decide⟩ : Fin 148)) h (basisElt (reps rK127) (charOfVec rK127 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK127 e (h : Coordinate 1) T127_127 i :=
  species_entry_eq_sum rK127 ⟨127, by decide⟩ e heK h T127_127 hfix127_127 hinj127_127 hcardT127_127
    (fun i => conj_mem_of_fixedPoints (reps ⟨127, by decide⟩) (reps rK127) (T127_127 i) (hfix127_127 i) h)

namespace Q2

def R127_2 : Fin 5 → Coordinate 2 := fun i => R127list.getD i.val (0,0,0,0,0)
theorem hpxR127_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK127) (R127_2 i)) := by decide
theorem hcardq127_2 : Nat.card (Coordinate 2 ⧸ reps rK127) = 5 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (127, 0) twin -/

def T127_0_2 : Fin 5 → Coordinate 2 := fun i => T127_0list.getD i.val (0,0,0,0,0)

theorem hfix127_0_2 : ∀ i, ((T127_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK127)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK127) :=
  repsFix_of_siftB2 rK127 ⟨0, by decide⟩ T127_0_2 (by decide)

theorem hinj127_0_2 : Function.Injective
    (fun i => ((T127_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK127)) :=
  repsInj_of_reduceAux2 rK127 T127_0_2 (by decide)

theorem hcardT127_0_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK127)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK127 ⟨0, by decide⟩ R127_2 hpxR127_2 hcardq127_2 (by decide)).symm

/-- **Cell (127, 0) twin (q=2).** -/
theorem cell127_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK127) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK127) (charOfVec2 rK127 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK127 e (h : Coordinate 2) T127_0_2 i :=
  species_entry_eq_sum rK127 ⟨0, by decide⟩ e heK h T127_0_2 hfix127_0_2 hinj127_0_2 hcardT127_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK127) (T127_0_2 i) (hfix127_0_2 i) h)

/-! ### Cell (127, 3) twin -/

def T127_3_2 : Fin 5 → Coordinate 2 := fun i => T127_3list.getD i.val (0,0,0,0,0)

theorem hfix127_3_2 : ∀ i, ((T127_3_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK127)
    ∈ fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK127) :=
  repsFix_of_siftB2 rK127 ⟨3, by decide⟩ T127_3_2 (by decide)

theorem hinj127_3_2 : Function.Injective
    (fun i => ((T127_3_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK127)) :=
  repsInj_of_reduceAux2 rK127 T127_3_2 (by decide)

theorem hcardT127_3_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK127)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK127 ⟨3, by decide⟩ R127_2 hpxR127_2 hcardq127_2 (by decide)).symm

/-- **Cell (127, 3) twin (q=2).** -/
theorem cell127_3_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK127) e = true)
    (h : ↥(reps (⟨3, by decide⟩ : Fin 148))) :
    species (reps (⟨3, by decide⟩ : Fin 148)) h (basisElt (reps rK127) (charOfVec2 rK127 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK127 e (h : Coordinate 2) T127_3_2 i :=
  species_entry_eq_sum rK127 ⟨3, by decide⟩ e heK h T127_3_2 hfix127_3_2 hinj127_3_2 hcardT127_3_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨3, by decide⟩) (reps rK127) (T127_3_2 i) (hfix127_3_2 i) h)

/-! ### Cell (127, 10) twin -/

def T127_10_2 : Fin 5 → Coordinate 2 := fun i => T127_10list.getD i.val (0,0,0,0,0)

theorem hfix127_10_2 : ∀ i, ((T127_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK127)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK127) :=
  repsFix_of_siftB2 rK127 ⟨10, by decide⟩ T127_10_2 (by decide)

theorem hinj127_10_2 : Function.Injective
    (fun i => ((T127_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK127)) :=
  repsInj_of_reduceAux2 rK127 T127_10_2 (by decide)

theorem hcardT127_10_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK127)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK127 ⟨10, by decide⟩ R127_2 hpxR127_2 hcardq127_2 (by decide)).symm

/-- **Cell (127, 10) twin (q=2).** -/
theorem cell127_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK127) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK127) (charOfVec2 rK127 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK127 e (h : Coordinate 2) T127_10_2 i :=
  species_entry_eq_sum rK127 ⟨10, by decide⟩ e heK h T127_10_2 hfix127_10_2 hinj127_10_2 hcardT127_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK127) (T127_10_2 i) (hfix127_10_2 i) h)

/-! ### Cell (127, 12) twin -/

def T127_12_2 : Fin 5 → Coordinate 2 := fun i => T127_12list.getD i.val (0,0,0,0,0)

theorem hfix127_12_2 : ∀ i, ((T127_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK127)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK127) :=
  repsFix_of_siftB2 rK127 ⟨12, by decide⟩ T127_12_2 (by decide)

theorem hinj127_12_2 : Function.Injective
    (fun i => ((T127_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK127)) :=
  repsInj_of_reduceAux2 rK127 T127_12_2 (by decide)

theorem hcardT127_12_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK127)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK127 ⟨12, by decide⟩ R127_2 hpxR127_2 hcardq127_2 (by decide)).symm

/-- **Cell (127, 12) twin (q=2).** -/
theorem cell127_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK127) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK127) (charOfVec2 rK127 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK127 e (h : Coordinate 2) T127_12_2 i :=
  species_entry_eq_sum rK127 ⟨12, by decide⟩ e heK h T127_12_2 hfix127_12_2 hinj127_12_2 hcardT127_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK127) (T127_12_2 i) (hfix127_12_2 i) h)

/-! ### Cell (127, 21) twin -/

def T127_21_2 : Fin 5 → Coordinate 2 := fun i => T127_21list.getD i.val (0,0,0,0,0)

theorem hfix127_21_2 : ∀ i, ((T127_21_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK127)
    ∈ fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK127) :=
  repsFix_of_siftB2 rK127 ⟨21, by decide⟩ T127_21_2 (by decide)

theorem hinj127_21_2 : Function.Injective
    (fun i => ((T127_21_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK127)) :=
  repsInj_of_reduceAux2 rK127 T127_21_2 (by decide)

theorem hcardT127_21_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK127)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK127 ⟨21, by decide⟩ R127_2 hpxR127_2 hcardq127_2 (by decide)).symm

/-- **Cell (127, 21) twin (q=2).** -/
theorem cell127_21_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK127) e = true)
    (h : ↥(reps (⟨21, by decide⟩ : Fin 148))) :
    species (reps (⟨21, by decide⟩ : Fin 148)) h (basisElt (reps rK127) (charOfVec2 rK127 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK127 e (h : Coordinate 2) T127_21_2 i :=
  species_entry_eq_sum rK127 ⟨21, by decide⟩ e heK h T127_21_2 hfix127_21_2 hinj127_21_2 hcardT127_21_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨21, by decide⟩) (reps rK127) (T127_21_2 i) (hfix127_21_2 i) h)

/-! ### Cell (127, 32) twin -/

def T127_32_2 : Fin 5 → Coordinate 2 := fun i => T127_32list.getD i.val (0,0,0,0,0)

theorem hfix127_32_2 : ∀ i, ((T127_32_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK127)
    ∈ fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK127) :=
  repsFix_of_siftB2 rK127 ⟨32, by decide⟩ T127_32_2 (by decide)

theorem hinj127_32_2 : Function.Injective
    (fun i => ((T127_32_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK127)) :=
  repsInj_of_reduceAux2 rK127 T127_32_2 (by decide)

theorem hcardT127_32_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK127)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK127 ⟨32, by decide⟩ R127_2 hpxR127_2 hcardq127_2 (by decide)).symm

/-- **Cell (127, 32) twin (q=2).** -/
theorem cell127_32_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK127) e = true)
    (h : ↥(reps (⟨32, by decide⟩ : Fin 148))) :
    species (reps (⟨32, by decide⟩ : Fin 148)) h (basisElt (reps rK127) (charOfVec2 rK127 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK127 e (h : Coordinate 2) T127_32_2 i :=
  species_entry_eq_sum rK127 ⟨32, by decide⟩ e heK h T127_32_2 hfix127_32_2 hinj127_32_2 hcardT127_32_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨32, by decide⟩) (reps rK127) (T127_32_2 i) (hfix127_32_2 i) h)

/-! ### Cell (127, 33) twin -/

def T127_33_2 : Fin 5 → Coordinate 2 := fun i => T127_33list.getD i.val (0,0,0,0,0)

theorem hfix127_33_2 : ∀ i, ((T127_33_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK127)
    ∈ fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK127) :=
  repsFix_of_siftB2 rK127 ⟨33, by decide⟩ T127_33_2 (by decide)

theorem hinj127_33_2 : Function.Injective
    (fun i => ((T127_33_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK127)) :=
  repsInj_of_reduceAux2 rK127 T127_33_2 (by decide)

theorem hcardT127_33_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK127)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK127 ⟨33, by decide⟩ R127_2 hpxR127_2 hcardq127_2 (by decide)).symm

/-- **Cell (127, 33) twin (q=2).** -/
theorem cell127_33_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK127) e = true)
    (h : ↥(reps (⟨33, by decide⟩ : Fin 148))) :
    species (reps (⟨33, by decide⟩ : Fin 148)) h (basisElt (reps rK127) (charOfVec2 rK127 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK127 e (h : Coordinate 2) T127_33_2 i :=
  species_entry_eq_sum rK127 ⟨33, by decide⟩ e heK h T127_33_2 hfix127_33_2 hinj127_33_2 hcardT127_33_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨33, by decide⟩) (reps rK127) (T127_33_2 i) (hfix127_33_2 i) h)

/-! ### Cell (127, 40) twin -/

def T127_40_2 : Fin 5 → Coordinate 2 := fun i => T127_40list.getD i.val (0,0,0,0,0)

theorem hfix127_40_2 : ∀ i, ((T127_40_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK127)
    ∈ fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK127) :=
  repsFix_of_siftB2 rK127 ⟨40, by decide⟩ T127_40_2 (by decide)

theorem hinj127_40_2 : Function.Injective
    (fun i => ((T127_40_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK127)) :=
  repsInj_of_reduceAux2 rK127 T127_40_2 (by decide)

theorem hcardT127_40_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK127)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK127 ⟨40, by decide⟩ R127_2 hpxR127_2 hcardq127_2 (by decide)).symm

/-- **Cell (127, 40) twin (q=2).** -/
theorem cell127_40_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK127) e = true)
    (h : ↥(reps (⟨40, by decide⟩ : Fin 148))) :
    species (reps (⟨40, by decide⟩ : Fin 148)) h (basisElt (reps rK127) (charOfVec2 rK127 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK127 e (h : Coordinate 2) T127_40_2 i :=
  species_entry_eq_sum rK127 ⟨40, by decide⟩ e heK h T127_40_2 hfix127_40_2 hinj127_40_2 hcardT127_40_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨40, by decide⟩) (reps rK127) (T127_40_2 i) (hfix127_40_2 i) h)

/-! ### Cell (127, 46) twin -/

def T127_46_2 : Fin 5 → Coordinate 2 := fun i => T127_46list.getD i.val (0,0,0,0,0)

theorem hfix127_46_2 : ∀ i, ((T127_46_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK127)
    ∈ fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK127) :=
  repsFix_of_siftB2 rK127 ⟨46, by decide⟩ T127_46_2 (by decide)

theorem hinj127_46_2 : Function.Injective
    (fun i => ((T127_46_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK127)) :=
  repsInj_of_reduceAux2 rK127 T127_46_2 (by decide)

theorem hcardT127_46_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK127)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK127 ⟨46, by decide⟩ R127_2 hpxR127_2 hcardq127_2 (by decide)).symm

/-- **Cell (127, 46) twin (q=2).** -/
theorem cell127_46_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK127) e = true)
    (h : ↥(reps (⟨46, by decide⟩ : Fin 148))) :
    species (reps (⟨46, by decide⟩ : Fin 148)) h (basisElt (reps rK127) (charOfVec2 rK127 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK127 e (h : Coordinate 2) T127_46_2 i :=
  species_entry_eq_sum rK127 ⟨46, by decide⟩ e heK h T127_46_2 hfix127_46_2 hinj127_46_2 hcardT127_46_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨46, by decide⟩) (reps rK127) (T127_46_2 i) (hfix127_46_2 i) h)

/-! ### Cell (127, 49) twin -/

def T127_49_2 : Fin 5 → Coordinate 2 := fun i => T127_49list.getD i.val (0,0,0,0,0)

theorem hfix127_49_2 : ∀ i, ((T127_49_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK127)
    ∈ fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK127) :=
  repsFix_of_siftB2 rK127 ⟨49, by decide⟩ T127_49_2 (by decide)

theorem hinj127_49_2 : Function.Injective
    (fun i => ((T127_49_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK127)) :=
  repsInj_of_reduceAux2 rK127 T127_49_2 (by decide)

theorem hcardT127_49_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK127)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK127 ⟨49, by decide⟩ R127_2 hpxR127_2 hcardq127_2 (by decide)).symm

/-- **Cell (127, 49) twin (q=2).** -/
theorem cell127_49_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK127) e = true)
    (h : ↥(reps (⟨49, by decide⟩ : Fin 148))) :
    species (reps (⟨49, by decide⟩ : Fin 148)) h (basisElt (reps rK127) (charOfVec2 rK127 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK127 e (h : Coordinate 2) T127_49_2 i :=
  species_entry_eq_sum rK127 ⟨49, by decide⟩ e heK h T127_49_2 hfix127_49_2 hinj127_49_2 hcardT127_49_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨49, by decide⟩) (reps rK127) (T127_49_2 i) (hfix127_49_2 i) h)

/-! ### Cell (127, 53) twin -/

def T127_53_2 : Fin 5 → Coordinate 2 := fun i => T127_53list.getD i.val (0,0,0,0,0)

theorem hfix127_53_2 : ∀ i, ((T127_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK127)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK127) :=
  repsFix_of_siftB2 rK127 ⟨53, by decide⟩ T127_53_2 (by decide)

theorem hinj127_53_2 : Function.Injective
    (fun i => ((T127_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK127)) :=
  repsInj_of_reduceAux2 rK127 T127_53_2 (by decide)

theorem hcardT127_53_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK127)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK127 ⟨53, by decide⟩ R127_2 hpxR127_2 hcardq127_2 (by decide)).symm

/-- **Cell (127, 53) twin (q=2).** -/
theorem cell127_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK127) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK127) (charOfVec2 rK127 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK127 e (h : Coordinate 2) T127_53_2 i :=
  species_entry_eq_sum rK127 ⟨53, by decide⟩ e heK h T127_53_2 hfix127_53_2 hinj127_53_2 hcardT127_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK127) (T127_53_2 i) (hfix127_53_2 i) h)

/-! ### Cell (127, 82) twin -/

def T127_82_2 : Fin 5 → Coordinate 2 := fun i => T127_82list.getD i.val (0,0,0,0,0)

theorem hfix127_82_2 : ∀ i, ((T127_82_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK127)
    ∈ fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK127) :=
  repsFix_of_siftB2 rK127 ⟨82, by decide⟩ T127_82_2 (by decide)

theorem hinj127_82_2 : Function.Injective
    (fun i => ((T127_82_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK127)) :=
  repsInj_of_reduceAux2 rK127 T127_82_2 (by decide)

theorem hcardT127_82_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK127)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK127 ⟨82, by decide⟩ R127_2 hpxR127_2 hcardq127_2 (by decide)).symm

/-- **Cell (127, 82) twin (q=2).** -/
theorem cell127_82_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK127) e = true)
    (h : ↥(reps (⟨82, by decide⟩ : Fin 148))) :
    species (reps (⟨82, by decide⟩ : Fin 148)) h (basisElt (reps rK127) (charOfVec2 rK127 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK127 e (h : Coordinate 2) T127_82_2 i :=
  species_entry_eq_sum rK127 ⟨82, by decide⟩ e heK h T127_82_2 hfix127_82_2 hinj127_82_2 hcardT127_82_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨82, by decide⟩) (reps rK127) (T127_82_2 i) (hfix127_82_2 i) h)

/-! ### Cell (127, 94) twin -/

def T127_94_2 : Fin 5 → Coordinate 2 := fun i => T127_94list.getD i.val (0,0,0,0,0)

theorem hfix127_94_2 : ∀ i, ((T127_94_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK127)
    ∈ fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK127) :=
  repsFix_of_siftB2 rK127 ⟨94, by decide⟩ T127_94_2 (by decide)

theorem hinj127_94_2 : Function.Injective
    (fun i => ((T127_94_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK127)) :=
  repsInj_of_reduceAux2 rK127 T127_94_2 (by decide)

theorem hcardT127_94_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK127)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK127 ⟨94, by decide⟩ R127_2 hpxR127_2 hcardq127_2 (by decide)).symm

/-- **Cell (127, 94) twin (q=2).** -/
theorem cell127_94_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK127) e = true)
    (h : ↥(reps (⟨94, by decide⟩ : Fin 148))) :
    species (reps (⟨94, by decide⟩ : Fin 148)) h (basisElt (reps rK127) (charOfVec2 rK127 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK127 e (h : Coordinate 2) T127_94_2 i :=
  species_entry_eq_sum rK127 ⟨94, by decide⟩ e heK h T127_94_2 hfix127_94_2 hinj127_94_2 hcardT127_94_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨94, by decide⟩) (reps rK127) (T127_94_2 i) (hfix127_94_2 i) h)

/-! ### Cell (127, 95) twin -/

def T127_95_2 : Fin 5 → Coordinate 2 := fun i => T127_95list.getD i.val (0,0,0,0,0)

theorem hfix127_95_2 : ∀ i, ((T127_95_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK127)
    ∈ fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK127) :=
  repsFix_of_siftB2 rK127 ⟨95, by decide⟩ T127_95_2 (by decide)

theorem hinj127_95_2 : Function.Injective
    (fun i => ((T127_95_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK127)) :=
  repsInj_of_reduceAux2 rK127 T127_95_2 (by decide)

theorem hcardT127_95_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK127)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK127 ⟨95, by decide⟩ R127_2 hpxR127_2 hcardq127_2 (by decide)).symm

/-- **Cell (127, 95) twin (q=2).** -/
theorem cell127_95_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK127) e = true)
    (h : ↥(reps (⟨95, by decide⟩ : Fin 148))) :
    species (reps (⟨95, by decide⟩ : Fin 148)) h (basisElt (reps rK127) (charOfVec2 rK127 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK127 e (h : Coordinate 2) T127_95_2 i :=
  species_entry_eq_sum rK127 ⟨95, by decide⟩ e heK h T127_95_2 hfix127_95_2 hinj127_95_2 hcardT127_95_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨95, by decide⟩) (reps rK127) (T127_95_2 i) (hfix127_95_2 i) h)

/-! ### Cell (127, 102) twin -/

def T127_102_2 : Fin 5 → Coordinate 2 := fun i => T127_102list.getD i.val (0,0,0,0,0)

theorem hfix127_102_2 : ∀ i, ((T127_102_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK127)
    ∈ fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK127) :=
  repsFix_of_siftB2 rK127 ⟨102, by decide⟩ T127_102_2 (by decide)

theorem hinj127_102_2 : Function.Injective
    (fun i => ((T127_102_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK127)) :=
  repsInj_of_reduceAux2 rK127 T127_102_2 (by decide)

theorem hcardT127_102_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK127)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK127 ⟨102, by decide⟩ R127_2 hpxR127_2 hcardq127_2 (by decide)).symm

/-- **Cell (127, 102) twin (q=2).** -/
theorem cell127_102_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK127) e = true)
    (h : ↥(reps (⟨102, by decide⟩ : Fin 148))) :
    species (reps (⟨102, by decide⟩ : Fin 148)) h (basisElt (reps rK127) (charOfVec2 rK127 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK127 e (h : Coordinate 2) T127_102_2 i :=
  species_entry_eq_sum rK127 ⟨102, by decide⟩ e heK h T127_102_2 hfix127_102_2 hinj127_102_2 hcardT127_102_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨102, by decide⟩) (reps rK127) (T127_102_2 i) (hfix127_102_2 i) h)

/-! ### Cell (127, 108) twin -/

def T127_108_2 : Fin 5 → Coordinate 2 := fun i => T127_108list.getD i.val (0,0,0,0,0)

theorem hfix127_108_2 : ∀ i, ((T127_108_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK127)
    ∈ fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK127) :=
  repsFix_of_siftB2 rK127 ⟨108, by decide⟩ T127_108_2 (by decide)

theorem hinj127_108_2 : Function.Injective
    (fun i => ((T127_108_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK127)) :=
  repsInj_of_reduceAux2 rK127 T127_108_2 (by decide)

theorem hcardT127_108_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK127)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK127 ⟨108, by decide⟩ R127_2 hpxR127_2 hcardq127_2 (by decide)).symm

/-- **Cell (127, 108) twin (q=2).** -/
theorem cell127_108_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK127) e = true)
    (h : ↥(reps (⟨108, by decide⟩ : Fin 148))) :
    species (reps (⟨108, by decide⟩ : Fin 148)) h (basisElt (reps rK127) (charOfVec2 rK127 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK127 e (h : Coordinate 2) T127_108_2 i :=
  species_entry_eq_sum rK127 ⟨108, by decide⟩ e heK h T127_108_2 hfix127_108_2 hinj127_108_2 hcardT127_108_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨108, by decide⟩) (reps rK127) (T127_108_2 i) (hfix127_108_2 i) h)

/-! ### Cell (127, 111) twin -/

def T127_111_2 : Fin 5 → Coordinate 2 := fun i => T127_111list.getD i.val (0,0,0,0,0)

theorem hfix127_111_2 : ∀ i, ((T127_111_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK127)
    ∈ fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK127) :=
  repsFix_of_siftB2 rK127 ⟨111, by decide⟩ T127_111_2 (by decide)

theorem hinj127_111_2 : Function.Injective
    (fun i => ((T127_111_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK127)) :=
  repsInj_of_reduceAux2 rK127 T127_111_2 (by decide)

theorem hcardT127_111_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK127)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK127 ⟨111, by decide⟩ R127_2 hpxR127_2 hcardq127_2 (by decide)).symm

/-- **Cell (127, 111) twin (q=2).** -/
theorem cell127_111_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK127) e = true)
    (h : ↥(reps (⟨111, by decide⟩ : Fin 148))) :
    species (reps (⟨111, by decide⟩ : Fin 148)) h (basisElt (reps rK127) (charOfVec2 rK127 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK127 e (h : Coordinate 2) T127_111_2 i :=
  species_entry_eq_sum rK127 ⟨111, by decide⟩ e heK h T127_111_2 hfix127_111_2 hinj127_111_2 hcardT127_111_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨111, by decide⟩) (reps rK127) (T127_111_2 i) (hfix127_111_2 i) h)

/-! ### Cell (127, 127) twin -/

def T127_127_2 : Fin 5 → Coordinate 2 := fun i => T127_127list.getD i.val (0,0,0,0,0)

theorem hfix127_127_2 : ∀ i, ((T127_127_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK127)
    ∈ fixedPoints (reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK127) :=
  repsFix_of_siftB2 rK127 ⟨127, by decide⟩ T127_127_2 (by decide)

theorem hinj127_127_2 : Function.Injective
    (fun i => ((T127_127_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK127)) :=
  repsInj_of_reduceAux2 rK127 T127_127_2 (by decide)

theorem hcardT127_127_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK127)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK127 ⟨127, by decide⟩ R127_2 hpxR127_2 hcardq127_2 (by decide)).symm

/-- **Cell (127, 127) twin (q=2).** -/
theorem cell127_127_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK127) e = true)
    (h : ↥(reps (⟨127, by decide⟩ : Fin 148))) :
    species (reps (⟨127, by decide⟩ : Fin 148)) h (basisElt (reps rK127) (charOfVec2 rK127 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK127 e (h : Coordinate 2) T127_127_2 i :=
  species_entry_eq_sum rK127 ⟨127, by decide⟩ e heK h T127_127_2 hfix127_127_2 hinj127_127_2 hcardT127_127_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨127, by decide⟩) (reps rK127) (T127_127_2 i) (hfix127_127_2 i) h)

end Q2

end LeanDring.P5Presentation
