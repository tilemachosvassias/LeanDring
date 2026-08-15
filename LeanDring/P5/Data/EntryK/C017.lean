/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, K-strata data (5^3 stratum, rK 70-74): certified per-cell species-entry instantiations, both
twins.

Covers K-classes 70, 71, 72, 73, 74 (order-5^3 K, |R|=25).  For each nonzero `H`-column
(`(G/K)^H ≠ ∅`), the full coset transversal `R70..` and each `H`-fixed
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

/-! # K-class rK = 70  (|G/K| = 25) -/

def rK70 : Fin 148 := ⟨70, by decide⟩

def R70list : List Coordinates := [(0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0)]
def R70 : Fin 25 → Coordinate 1 := fun i => R70list.getD i.val (0,0,0,0,0)

theorem hpxR70 : Function.Injective (fun i => reduceAux 1 (basisAt rK70) (R70 i)) := by decide
theorem hcardq70 : Nat.card (Coordinate 1 ⧸ reps rK70) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (70, 0): |T| = 25 -/

def T70_0list : List Coordinates := [(0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0)]
def T70_0 : Fin 25 → Coordinate 1 := fun i => T70_0list.getD i.val (0,0,0,0,0)

theorem hfix70_0 : ∀ i, ((T70_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK70)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70) :=
  repsFix_of_siftB rK70 ⟨0, by decide⟩ T70_0 (by decide)

theorem hinj70_0 : Function.Injective
    (fun i => ((T70_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK70)) :=
  repsInj_of_reduceAux rK70 T70_0 (by decide)

theorem hcardT70_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK70 ⟨0, by decide⟩ R70 hpxR70 hcardq70 (by decide)).symm

/-- **Cell (70, 0).** -/
theorem cell70_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK70) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK70) (charOfVec rK70 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK70 e (h : Coordinate 1) T70_0 i :=
  species_entry_eq_sum rK70 ⟨0, by decide⟩ e heK h T70_0 hfix70_0 hinj70_0 hcardT70_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK70) (T70_0 i) (hfix70_0 i) h)

/-! ## Cell (70, 9): |T| = 25 -/

def T70_9list : List Coordinates := [(0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0)]
def T70_9 : Fin 25 → Coordinate 1 := fun i => T70_9list.getD i.val (0,0,0,0,0)

theorem hfix70_9 : ∀ i, ((T70_9 i : Coordinate 1) : Coordinate 1 ⧸ reps rK70)
    ∈ fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70) :=
  repsFix_of_siftB rK70 ⟨9, by decide⟩ T70_9 (by decide)

theorem hinj70_9 : Function.Injective
    (fun i => ((T70_9 i : Coordinate 1) : Coordinate 1 ⧸ reps rK70)) :=
  repsInj_of_reduceAux rK70 T70_9 (by decide)

theorem hcardT70_9 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK70 ⟨9, by decide⟩ R70 hpxR70 hcardq70 (by decide)).symm

/-- **Cell (70, 9).** -/
theorem cell70_9 (e : List (ZMod 25)) (heK : charOK (basisAt rK70) e = true)
    (h : ↥(reps (⟨9, by decide⟩ : Fin 148))) :
    species (reps (⟨9, by decide⟩ : Fin 148)) h (basisElt (reps rK70) (charOfVec rK70 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK70 e (h : Coordinate 1) T70_9 i :=
  species_entry_eq_sum rK70 ⟨9, by decide⟩ e heK h T70_9 hfix70_9 hinj70_9 hcardT70_9
    (fun i => conj_mem_of_fixedPoints (reps ⟨9, by decide⟩) (reps rK70) (T70_9 i) (hfix70_9 i) h)

/-! ## Cell (70, 12): |T| = 25 -/

def T70_12list : List Coordinates := [(0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0)]
def T70_12 : Fin 25 → Coordinate 1 := fun i => T70_12list.getD i.val (0,0,0,0,0)

theorem hfix70_12 : ∀ i, ((T70_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK70)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70) :=
  repsFix_of_siftB rK70 ⟨12, by decide⟩ T70_12 (by decide)

theorem hinj70_12 : Function.Injective
    (fun i => ((T70_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK70)) :=
  repsInj_of_reduceAux rK70 T70_12 (by decide)

theorem hcardT70_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK70 ⟨12, by decide⟩ R70 hpxR70 hcardq70 (by decide)).symm

/-- **Cell (70, 12).** -/
theorem cell70_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK70) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK70) (charOfVec rK70 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK70 e (h : Coordinate 1) T70_12 i :=
  species_entry_eq_sum rK70 ⟨12, by decide⟩ e heK h T70_12 hfix70_12 hinj70_12 hcardT70_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK70) (T70_12 i) (hfix70_12 i) h)

/-! ## Cell (70, 27): |T| = 25 -/

def T70_27list : List Coordinates := [(0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0)]
def T70_27 : Fin 25 → Coordinate 1 := fun i => T70_27list.getD i.val (0,0,0,0,0)

theorem hfix70_27 : ∀ i, ((T70_27 i : Coordinate 1) : Coordinate 1 ⧸ reps rK70)
    ∈ fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70) :=
  repsFix_of_siftB rK70 ⟨27, by decide⟩ T70_27 (by decide)

theorem hinj70_27 : Function.Injective
    (fun i => ((T70_27 i : Coordinate 1) : Coordinate 1 ⧸ reps rK70)) :=
  repsInj_of_reduceAux rK70 T70_27 (by decide)

theorem hcardT70_27 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK70 ⟨27, by decide⟩ R70 hpxR70 hcardq70 (by decide)).symm

/-- **Cell (70, 27).** -/
theorem cell70_27 (e : List (ZMod 25)) (heK : charOK (basisAt rK70) e = true)
    (h : ↥(reps (⟨27, by decide⟩ : Fin 148))) :
    species (reps (⟨27, by decide⟩ : Fin 148)) h (basisElt (reps rK70) (charOfVec rK70 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK70 e (h : Coordinate 1) T70_27 i :=
  species_entry_eq_sum rK70 ⟨27, by decide⟩ e heK h T70_27 hfix70_27 hinj70_27 hcardT70_27
    (fun i => conj_mem_of_fixedPoints (reps ⟨27, by decide⟩) (reps rK70) (T70_27 i) (hfix70_27 i) h)

/-! ## Cell (70, 31): |T| = 5 -/

def T70_31list : List Coordinates := [(0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0)]
def T70_31 : Fin 5 → Coordinate 1 := fun i => T70_31list.getD i.val (0,0,0,0,0)

theorem hfix70_31 : ∀ i, ((T70_31 i : Coordinate 1) : Coordinate 1 ⧸ reps rK70)
    ∈ fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70) :=
  repsFix_of_siftB rK70 ⟨31, by decide⟩ T70_31 (by decide)

theorem hinj70_31 : Function.Injective
    (fun i => ((T70_31 i : Coordinate 1) : Coordinate 1 ⧸ reps rK70)) :=
  repsInj_of_reduceAux rK70 T70_31 (by decide)

theorem hcardT70_31 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK70 ⟨31, by decide⟩ R70 hpxR70 hcardq70 (by decide)).symm

/-- **Cell (70, 31).** -/
theorem cell70_31 (e : List (ZMod 25)) (heK : charOK (basisAt rK70) e = true)
    (h : ↥(reps (⟨31, by decide⟩ : Fin 148))) :
    species (reps (⟨31, by decide⟩ : Fin 148)) h (basisElt (reps rK70) (charOfVec rK70 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK70 e (h : Coordinate 1) T70_31 i :=
  species_entry_eq_sum rK70 ⟨31, by decide⟩ e heK h T70_31 hfix70_31 hinj70_31 hcardT70_31
    (fun i => conj_mem_of_fixedPoints (reps ⟨31, by decide⟩) (reps rK70) (T70_31 i) (hfix70_31 i) h)

/-! ## Cell (70, 36): |T| = 5 -/

def T70_36list : List Coordinates := [(0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0)]
def T70_36 : Fin 5 → Coordinate 1 := fun i => T70_36list.getD i.val (0,0,0,0,0)

theorem hfix70_36 : ∀ i, ((T70_36 i : Coordinate 1) : Coordinate 1 ⧸ reps rK70)
    ∈ fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70) :=
  repsFix_of_siftB rK70 ⟨36, by decide⟩ T70_36 (by decide)

theorem hinj70_36 : Function.Injective
    (fun i => ((T70_36 i : Coordinate 1) : Coordinate 1 ⧸ reps rK70)) :=
  repsInj_of_reduceAux rK70 T70_36 (by decide)

theorem hcardT70_36 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK70 ⟨36, by decide⟩ R70 hpxR70 hcardq70 (by decide)).symm

/-- **Cell (70, 36).** -/
theorem cell70_36 (e : List (ZMod 25)) (heK : charOK (basisAt rK70) e = true)
    (h : ↥(reps (⟨36, by decide⟩ : Fin 148))) :
    species (reps (⟨36, by decide⟩ : Fin 148)) h (basisElt (reps rK70) (charOfVec rK70 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK70 e (h : Coordinate 1) T70_36 i :=
  species_entry_eq_sum rK70 ⟨36, by decide⟩ e heK h T70_36 hfix70_36 hinj70_36 hcardT70_36
    (fun i => conj_mem_of_fixedPoints (reps ⟨36, by decide⟩) (reps rK70) (T70_36 i) (hfix70_36 i) h)

/-! ## Cell (70, 41): |T| = 5 -/

def T70_41list : List Coordinates := [(0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0)]
def T70_41 : Fin 5 → Coordinate 1 := fun i => T70_41list.getD i.val (0,0,0,0,0)

theorem hfix70_41 : ∀ i, ((T70_41 i : Coordinate 1) : Coordinate 1 ⧸ reps rK70)
    ∈ fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70) :=
  repsFix_of_siftB rK70 ⟨41, by decide⟩ T70_41 (by decide)

theorem hinj70_41 : Function.Injective
    (fun i => ((T70_41 i : Coordinate 1) : Coordinate 1 ⧸ reps rK70)) :=
  repsInj_of_reduceAux rK70 T70_41 (by decide)

theorem hcardT70_41 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK70 ⟨41, by decide⟩ R70 hpxR70 hcardq70 (by decide)).symm

/-- **Cell (70, 41).** -/
theorem cell70_41 (e : List (ZMod 25)) (heK : charOK (basisAt rK70) e = true)
    (h : ↥(reps (⟨41, by decide⟩ : Fin 148))) :
    species (reps (⟨41, by decide⟩ : Fin 148)) h (basisElt (reps rK70) (charOfVec rK70 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK70 e (h : Coordinate 1) T70_41 i :=
  species_entry_eq_sum rK70 ⟨41, by decide⟩ e heK h T70_41 hfix70_41 hinj70_41 hcardT70_41
    (fun i => conj_mem_of_fixedPoints (reps ⟨41, by decide⟩) (reps rK70) (T70_41 i) (hfix70_41 i) h)

/-! ## Cell (70, 46): |T| = 5 -/

def T70_46list : List Coordinates := [(0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0)]
def T70_46 : Fin 5 → Coordinate 1 := fun i => T70_46list.getD i.val (0,0,0,0,0)

theorem hfix70_46 : ∀ i, ((T70_46 i : Coordinate 1) : Coordinate 1 ⧸ reps rK70)
    ∈ fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70) :=
  repsFix_of_siftB rK70 ⟨46, by decide⟩ T70_46 (by decide)

theorem hinj70_46 : Function.Injective
    (fun i => ((T70_46 i : Coordinate 1) : Coordinate 1 ⧸ reps rK70)) :=
  repsInj_of_reduceAux rK70 T70_46 (by decide)

theorem hcardT70_46 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK70 ⟨46, by decide⟩ R70 hpxR70 hcardq70 (by decide)).symm

/-- **Cell (70, 46).** -/
theorem cell70_46 (e : List (ZMod 25)) (heK : charOK (basisAt rK70) e = true)
    (h : ↥(reps (⟨46, by decide⟩ : Fin 148))) :
    species (reps (⟨46, by decide⟩ : Fin 148)) h (basisElt (reps rK70) (charOfVec rK70 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK70 e (h : Coordinate 1) T70_46 i :=
  species_entry_eq_sum rK70 ⟨46, by decide⟩ e heK h T70_46 hfix70_46 hinj70_46 hcardT70_46
    (fun i => conj_mem_of_fixedPoints (reps ⟨46, by decide⟩) (reps rK70) (T70_46 i) (hfix70_46 i) h)

/-! ## Cell (70, 51): |T| = 5 -/

def T70_51list : List Coordinates := [(0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0)]
def T70_51 : Fin 5 → Coordinate 1 := fun i => T70_51list.getD i.val (0,0,0,0,0)

theorem hfix70_51 : ∀ i, ((T70_51 i : Coordinate 1) : Coordinate 1 ⧸ reps rK70)
    ∈ fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70) :=
  repsFix_of_siftB rK70 ⟨51, by decide⟩ T70_51 (by decide)

theorem hinj70_51 : Function.Injective
    (fun i => ((T70_51 i : Coordinate 1) : Coordinate 1 ⧸ reps rK70)) :=
  repsInj_of_reduceAux rK70 T70_51 (by decide)

theorem hcardT70_51 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK70 ⟨51, by decide⟩ R70 hpxR70 hcardq70 (by decide)).symm

/-- **Cell (70, 51).** -/
theorem cell70_51 (e : List (ZMod 25)) (heK : charOK (basisAt rK70) e = true)
    (h : ↥(reps (⟨51, by decide⟩ : Fin 148))) :
    species (reps (⟨51, by decide⟩ : Fin 148)) h (basisElt (reps rK70) (charOfVec rK70 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK70 e (h : Coordinate 1) T70_51 i :=
  species_entry_eq_sum rK70 ⟨51, by decide⟩ e heK h T70_51 hfix70_51 hinj70_51 hcardT70_51
    (fun i => conj_mem_of_fixedPoints (reps ⟨51, by decide⟩) (reps rK70) (T70_51 i) (hfix70_51 i) h)

/-! ## Cell (70, 70): |T| = 5 -/

def T70_70list : List Coordinates := [(0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0)]
def T70_70 : Fin 5 → Coordinate 1 := fun i => T70_70list.getD i.val (0,0,0,0,0)

theorem hfix70_70 : ∀ i, ((T70_70 i : Coordinate 1) : Coordinate 1 ⧸ reps rK70)
    ∈ fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70) :=
  repsFix_of_siftB rK70 ⟨70, by decide⟩ T70_70 (by decide)

theorem hinj70_70 : Function.Injective
    (fun i => ((T70_70 i : Coordinate 1) : Coordinate 1 ⧸ reps rK70)) :=
  repsInj_of_reduceAux rK70 T70_70 (by decide)

theorem hcardT70_70 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK70 ⟨70, by decide⟩ R70 hpxR70 hcardq70 (by decide)).symm

/-- **Cell (70, 70).** -/
theorem cell70_70 (e : List (ZMod 25)) (heK : charOK (basisAt rK70) e = true)
    (h : ↥(reps (⟨70, by decide⟩ : Fin 148))) :
    species (reps (⟨70, by decide⟩ : Fin 148)) h (basisElt (reps rK70) (charOfVec rK70 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK70 e (h : Coordinate 1) T70_70 i :=
  species_entry_eq_sum rK70 ⟨70, by decide⟩ e heK h T70_70 hfix70_70 hinj70_70 hcardT70_70
    (fun i => conj_mem_of_fixedPoints (reps ⟨70, by decide⟩) (reps rK70) (T70_70 i) (hfix70_70 i) h)

namespace Q2

def R70_2 : Fin 25 → Coordinate 2 := fun i => R70list.getD i.val (0,0,0,0,0)
theorem hpxR70_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK70) (R70_2 i)) := by decide
theorem hcardq70_2 : Nat.card (Coordinate 2 ⧸ reps rK70) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (70, 0) twin -/

def T70_0_2 : Fin 25 → Coordinate 2 := fun i => T70_0list.getD i.val (0,0,0,0,0)

theorem hfix70_0_2 : ∀ i, ((T70_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK70)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK70) :=
  repsFix_of_siftB2 rK70 ⟨0, by decide⟩ T70_0_2 (by decide)

theorem hinj70_0_2 : Function.Injective
    (fun i => ((T70_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK70)) :=
  repsInj_of_reduceAux2 rK70 T70_0_2 (by decide)

theorem hcardT70_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK70)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK70 ⟨0, by decide⟩ R70_2 hpxR70_2 hcardq70_2 (by decide)).symm

/-- **Cell (70, 0) twin (q=2).** -/
theorem cell70_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK70) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK70) (charOfVec2 rK70 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK70 e (h : Coordinate 2) T70_0_2 i :=
  species_entry_eq_sum rK70 ⟨0, by decide⟩ e heK h T70_0_2 hfix70_0_2 hinj70_0_2 hcardT70_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK70) (T70_0_2 i) (hfix70_0_2 i) h)

/-! ### Cell (70, 9) twin -/

def T70_9_2 : Fin 25 → Coordinate 2 := fun i => T70_9list.getD i.val (0,0,0,0,0)

theorem hfix70_9_2 : ∀ i, ((T70_9_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK70)
    ∈ fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK70) :=
  repsFix_of_siftB2 rK70 ⟨9, by decide⟩ T70_9_2 (by decide)

theorem hinj70_9_2 : Function.Injective
    (fun i => ((T70_9_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK70)) :=
  repsInj_of_reduceAux2 rK70 T70_9_2 (by decide)

theorem hcardT70_9_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK70)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK70 ⟨9, by decide⟩ R70_2 hpxR70_2 hcardq70_2 (by decide)).symm

/-- **Cell (70, 9) twin (q=2).** -/
theorem cell70_9_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK70) e = true)
    (h : ↥(reps (⟨9, by decide⟩ : Fin 148))) :
    species (reps (⟨9, by decide⟩ : Fin 148)) h (basisElt (reps rK70) (charOfVec2 rK70 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK70 e (h : Coordinate 2) T70_9_2 i :=
  species_entry_eq_sum rK70 ⟨9, by decide⟩ e heK h T70_9_2 hfix70_9_2 hinj70_9_2 hcardT70_9_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨9, by decide⟩) (reps rK70) (T70_9_2 i) (hfix70_9_2 i) h)

/-! ### Cell (70, 12) twin -/

def T70_12_2 : Fin 25 → Coordinate 2 := fun i => T70_12list.getD i.val (0,0,0,0,0)

theorem hfix70_12_2 : ∀ i, ((T70_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK70)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK70) :=
  repsFix_of_siftB2 rK70 ⟨12, by decide⟩ T70_12_2 (by decide)

theorem hinj70_12_2 : Function.Injective
    (fun i => ((T70_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK70)) :=
  repsInj_of_reduceAux2 rK70 T70_12_2 (by decide)

theorem hcardT70_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK70)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK70 ⟨12, by decide⟩ R70_2 hpxR70_2 hcardq70_2 (by decide)).symm

/-- **Cell (70, 12) twin (q=2).** -/
theorem cell70_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK70) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK70) (charOfVec2 rK70 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK70 e (h : Coordinate 2) T70_12_2 i :=
  species_entry_eq_sum rK70 ⟨12, by decide⟩ e heK h T70_12_2 hfix70_12_2 hinj70_12_2 hcardT70_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK70) (T70_12_2 i) (hfix70_12_2 i) h)

/-! ### Cell (70, 27) twin -/

def T70_27_2 : Fin 25 → Coordinate 2 := fun i => T70_27list.getD i.val (0,0,0,0,0)

theorem hfix70_27_2 : ∀ i, ((T70_27_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK70)
    ∈ fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK70) :=
  repsFix_of_siftB2 rK70 ⟨27, by decide⟩ T70_27_2 (by decide)

theorem hinj70_27_2 : Function.Injective
    (fun i => ((T70_27_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK70)) :=
  repsInj_of_reduceAux2 rK70 T70_27_2 (by decide)

theorem hcardT70_27_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK70)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK70 ⟨27, by decide⟩ R70_2 hpxR70_2 hcardq70_2 (by decide)).symm

/-- **Cell (70, 27) twin (q=2).** -/
theorem cell70_27_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK70) e = true)
    (h : ↥(reps (⟨27, by decide⟩ : Fin 148))) :
    species (reps (⟨27, by decide⟩ : Fin 148)) h (basisElt (reps rK70) (charOfVec2 rK70 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK70 e (h : Coordinate 2) T70_27_2 i :=
  species_entry_eq_sum rK70 ⟨27, by decide⟩ e heK h T70_27_2 hfix70_27_2 hinj70_27_2 hcardT70_27_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨27, by decide⟩) (reps rK70) (T70_27_2 i) (hfix70_27_2 i) h)

/-! ### Cell (70, 31) twin -/

def T70_31_2 : Fin 5 → Coordinate 2 := fun i => T70_31list.getD i.val (0,0,0,0,0)

theorem hfix70_31_2 : ∀ i, ((T70_31_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK70)
    ∈ fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK70) :=
  repsFix_of_siftB2 rK70 ⟨31, by decide⟩ T70_31_2 (by decide)

theorem hinj70_31_2 : Function.Injective
    (fun i => ((T70_31_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK70)) :=
  repsInj_of_reduceAux2 rK70 T70_31_2 (by decide)

theorem hcardT70_31_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK70)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK70 ⟨31, by decide⟩ R70_2 hpxR70_2 hcardq70_2 (by decide)).symm

/-- **Cell (70, 31) twin (q=2).** -/
theorem cell70_31_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK70) e = true)
    (h : ↥(reps (⟨31, by decide⟩ : Fin 148))) :
    species (reps (⟨31, by decide⟩ : Fin 148)) h (basisElt (reps rK70) (charOfVec2 rK70 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK70 e (h : Coordinate 2) T70_31_2 i :=
  species_entry_eq_sum rK70 ⟨31, by decide⟩ e heK h T70_31_2 hfix70_31_2 hinj70_31_2 hcardT70_31_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨31, by decide⟩) (reps rK70) (T70_31_2 i) (hfix70_31_2 i) h)

/-! ### Cell (70, 36) twin -/

def T70_36_2 : Fin 5 → Coordinate 2 := fun i => T70_36list.getD i.val (0,0,0,0,0)

theorem hfix70_36_2 : ∀ i, ((T70_36_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK70)
    ∈ fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK70) :=
  repsFix_of_siftB2 rK70 ⟨36, by decide⟩ T70_36_2 (by decide)

theorem hinj70_36_2 : Function.Injective
    (fun i => ((T70_36_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK70)) :=
  repsInj_of_reduceAux2 rK70 T70_36_2 (by decide)

theorem hcardT70_36_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK70)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK70 ⟨36, by decide⟩ R70_2 hpxR70_2 hcardq70_2 (by decide)).symm

/-- **Cell (70, 36) twin (q=2).** -/
theorem cell70_36_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK70) e = true)
    (h : ↥(reps (⟨36, by decide⟩ : Fin 148))) :
    species (reps (⟨36, by decide⟩ : Fin 148)) h (basisElt (reps rK70) (charOfVec2 rK70 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK70 e (h : Coordinate 2) T70_36_2 i :=
  species_entry_eq_sum rK70 ⟨36, by decide⟩ e heK h T70_36_2 hfix70_36_2 hinj70_36_2 hcardT70_36_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨36, by decide⟩) (reps rK70) (T70_36_2 i) (hfix70_36_2 i) h)

/-! ### Cell (70, 41) twin -/

def T70_41_2 : Fin 5 → Coordinate 2 := fun i => T70_41list.getD i.val (0,0,0,0,0)

theorem hfix70_41_2 : ∀ i, ((T70_41_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK70)
    ∈ fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK70) :=
  repsFix_of_siftB2 rK70 ⟨41, by decide⟩ T70_41_2 (by decide)

theorem hinj70_41_2 : Function.Injective
    (fun i => ((T70_41_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK70)) :=
  repsInj_of_reduceAux2 rK70 T70_41_2 (by decide)

theorem hcardT70_41_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK70)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK70 ⟨41, by decide⟩ R70_2 hpxR70_2 hcardq70_2 (by decide)).symm

/-- **Cell (70, 41) twin (q=2).** -/
theorem cell70_41_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK70) e = true)
    (h : ↥(reps (⟨41, by decide⟩ : Fin 148))) :
    species (reps (⟨41, by decide⟩ : Fin 148)) h (basisElt (reps rK70) (charOfVec2 rK70 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK70 e (h : Coordinate 2) T70_41_2 i :=
  species_entry_eq_sum rK70 ⟨41, by decide⟩ e heK h T70_41_2 hfix70_41_2 hinj70_41_2 hcardT70_41_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨41, by decide⟩) (reps rK70) (T70_41_2 i) (hfix70_41_2 i) h)

/-! ### Cell (70, 46) twin -/

def T70_46_2 : Fin 5 → Coordinate 2 := fun i => T70_46list.getD i.val (0,0,0,0,0)

theorem hfix70_46_2 : ∀ i, ((T70_46_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK70)
    ∈ fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK70) :=
  repsFix_of_siftB2 rK70 ⟨46, by decide⟩ T70_46_2 (by decide)

theorem hinj70_46_2 : Function.Injective
    (fun i => ((T70_46_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK70)) :=
  repsInj_of_reduceAux2 rK70 T70_46_2 (by decide)

theorem hcardT70_46_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK70)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK70 ⟨46, by decide⟩ R70_2 hpxR70_2 hcardq70_2 (by decide)).symm

/-- **Cell (70, 46) twin (q=2).** -/
theorem cell70_46_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK70) e = true)
    (h : ↥(reps (⟨46, by decide⟩ : Fin 148))) :
    species (reps (⟨46, by decide⟩ : Fin 148)) h (basisElt (reps rK70) (charOfVec2 rK70 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK70 e (h : Coordinate 2) T70_46_2 i :=
  species_entry_eq_sum rK70 ⟨46, by decide⟩ e heK h T70_46_2 hfix70_46_2 hinj70_46_2 hcardT70_46_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨46, by decide⟩) (reps rK70) (T70_46_2 i) (hfix70_46_2 i) h)

/-! ### Cell (70, 51) twin -/

def T70_51_2 : Fin 5 → Coordinate 2 := fun i => T70_51list.getD i.val (0,0,0,0,0)

theorem hfix70_51_2 : ∀ i, ((T70_51_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK70)
    ∈ fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK70) :=
  repsFix_of_siftB2 rK70 ⟨51, by decide⟩ T70_51_2 (by decide)

theorem hinj70_51_2 : Function.Injective
    (fun i => ((T70_51_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK70)) :=
  repsInj_of_reduceAux2 rK70 T70_51_2 (by decide)

theorem hcardT70_51_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK70)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK70 ⟨51, by decide⟩ R70_2 hpxR70_2 hcardq70_2 (by decide)).symm

/-- **Cell (70, 51) twin (q=2).** -/
theorem cell70_51_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK70) e = true)
    (h : ↥(reps (⟨51, by decide⟩ : Fin 148))) :
    species (reps (⟨51, by decide⟩ : Fin 148)) h (basisElt (reps rK70) (charOfVec2 rK70 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK70 e (h : Coordinate 2) T70_51_2 i :=
  species_entry_eq_sum rK70 ⟨51, by decide⟩ e heK h T70_51_2 hfix70_51_2 hinj70_51_2 hcardT70_51_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨51, by decide⟩) (reps rK70) (T70_51_2 i) (hfix70_51_2 i) h)

/-! ### Cell (70, 70) twin -/

def T70_70_2 : Fin 5 → Coordinate 2 := fun i => T70_70list.getD i.val (0,0,0,0,0)

theorem hfix70_70_2 : ∀ i, ((T70_70_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK70)
    ∈ fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK70) :=
  repsFix_of_siftB2 rK70 ⟨70, by decide⟩ T70_70_2 (by decide)

theorem hinj70_70_2 : Function.Injective
    (fun i => ((T70_70_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK70)) :=
  repsInj_of_reduceAux2 rK70 T70_70_2 (by decide)

theorem hcardT70_70_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK70)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK70 ⟨70, by decide⟩ R70_2 hpxR70_2 hcardq70_2 (by decide)).symm

/-- **Cell (70, 70) twin (q=2).** -/
theorem cell70_70_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK70) e = true)
    (h : ↥(reps (⟨70, by decide⟩ : Fin 148))) :
    species (reps (⟨70, by decide⟩ : Fin 148)) h (basisElt (reps rK70) (charOfVec2 rK70 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK70 e (h : Coordinate 2) T70_70_2 i :=
  species_entry_eq_sum rK70 ⟨70, by decide⟩ e heK h T70_70_2 hfix70_70_2 hinj70_70_2 hcardT70_70_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨70, by decide⟩) (reps rK70) (T70_70_2 i) (hfix70_70_2 i) h)

end Q2

/-! # K-class rK = 71  (|G/K| = 25) -/

def rK71 : Fin 148 := ⟨71, by decide⟩

def R71list : List Coordinates := [(0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0)]
def R71 : Fin 25 → Coordinate 1 := fun i => R71list.getD i.val (0,0,0,0,0)

theorem hpxR71 : Function.Injective (fun i => reduceAux 1 (basisAt rK71) (R71 i)) := by decide
theorem hcardq71 : Nat.card (Coordinate 1 ⧸ reps rK71) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (71, 0): |T| = 25 -/

def T71_0list : List Coordinates := [(0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0)]
def T71_0 : Fin 25 → Coordinate 1 := fun i => T71_0list.getD i.val (0,0,0,0,0)

theorem hfix71_0 : ∀ i, ((T71_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK71)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71) :=
  repsFix_of_siftB rK71 ⟨0, by decide⟩ T71_0 (by decide)

theorem hinj71_0 : Function.Injective
    (fun i => ((T71_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK71)) :=
  repsInj_of_reduceAux rK71 T71_0 (by decide)

theorem hcardT71_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK71 ⟨0, by decide⟩ R71 hpxR71 hcardq71 (by decide)).symm

/-- **Cell (71, 0).** -/
theorem cell71_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK71) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK71) (charOfVec rK71 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK71 e (h : Coordinate 1) T71_0 i :=
  species_entry_eq_sum rK71 ⟨0, by decide⟩ e heK h T71_0 hfix71_0 hinj71_0 hcardT71_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK71) (T71_0 i) (hfix71_0 i) h)

/-! ## Cell (71, 1): |T| = 25 -/

def T71_1list : List Coordinates := [(0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0)]
def T71_1 : Fin 25 → Coordinate 1 := fun i => T71_1list.getD i.val (0,0,0,0,0)

theorem hfix71_1 : ∀ i, ((T71_1 i : Coordinate 1) : Coordinate 1 ⧸ reps rK71)
    ∈ fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71) :=
  repsFix_of_siftB rK71 ⟨1, by decide⟩ T71_1 (by decide)

theorem hinj71_1 : Function.Injective
    (fun i => ((T71_1 i : Coordinate 1) : Coordinate 1 ⧸ reps rK71)) :=
  repsInj_of_reduceAux rK71 T71_1 (by decide)

theorem hcardT71_1 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK71 ⟨1, by decide⟩ R71 hpxR71 hcardq71 (by decide)).symm

/-- **Cell (71, 1).** -/
theorem cell71_1 (e : List (ZMod 25)) (heK : charOK (basisAt rK71) e = true)
    (h : ↥(reps (⟨1, by decide⟩ : Fin 148))) :
    species (reps (⟨1, by decide⟩ : Fin 148)) h (basisElt (reps rK71) (charOfVec rK71 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK71 e (h : Coordinate 1) T71_1 i :=
  species_entry_eq_sum rK71 ⟨1, by decide⟩ e heK h T71_1 hfix71_1 hinj71_1 hcardT71_1
    (fun i => conj_mem_of_fixedPoints (reps ⟨1, by decide⟩) (reps rK71) (T71_1 i) (hfix71_1 i) h)

/-! ## Cell (71, 12): |T| = 25 -/

def T71_12list : List Coordinates := [(0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0)]
def T71_12 : Fin 25 → Coordinate 1 := fun i => T71_12list.getD i.val (0,0,0,0,0)

theorem hfix71_12 : ∀ i, ((T71_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK71)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71) :=
  repsFix_of_siftB rK71 ⟨12, by decide⟩ T71_12 (by decide)

theorem hinj71_12 : Function.Injective
    (fun i => ((T71_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK71)) :=
  repsInj_of_reduceAux rK71 T71_12 (by decide)

theorem hcardT71_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK71 ⟨12, by decide⟩ R71 hpxR71 hcardq71 (by decide)).symm

/-- **Cell (71, 12).** -/
theorem cell71_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK71) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK71) (charOfVec rK71 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK71 e (h : Coordinate 1) T71_12 i :=
  species_entry_eq_sum rK71 ⟨12, by decide⟩ e heK h T71_12 hfix71_12 hinj71_12 hcardT71_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK71) (T71_12 i) (hfix71_12 i) h)

/-! ## Cell (71, 19): |T| = 25 -/

def T71_19list : List Coordinates := [(0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0)]
def T71_19 : Fin 25 → Coordinate 1 := fun i => T71_19list.getD i.val (0,0,0,0,0)

theorem hfix71_19 : ∀ i, ((T71_19 i : Coordinate 1) : Coordinate 1 ⧸ reps rK71)
    ∈ fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71) :=
  repsFix_of_siftB rK71 ⟨19, by decide⟩ T71_19 (by decide)

theorem hinj71_19 : Function.Injective
    (fun i => ((T71_19 i : Coordinate 1) : Coordinate 1 ⧸ reps rK71)) :=
  repsInj_of_reduceAux rK71 T71_19 (by decide)

theorem hcardT71_19 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK71 ⟨19, by decide⟩ R71 hpxR71 hcardq71 (by decide)).symm

/-- **Cell (71, 19).** -/
theorem cell71_19 (e : List (ZMod 25)) (heK : charOK (basisAt rK71) e = true)
    (h : ↥(reps (⟨19, by decide⟩ : Fin 148))) :
    species (reps (⟨19, by decide⟩ : Fin 148)) h (basisElt (reps rK71) (charOfVec rK71 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK71 e (h : Coordinate 1) T71_19 i :=
  species_entry_eq_sum rK71 ⟨19, by decide⟩ e heK h T71_19 hfix71_19 hinj71_19 hcardT71_19
    (fun i => conj_mem_of_fixedPoints (reps ⟨19, by decide⟩) (reps rK71) (T71_19 i) (hfix71_19 i) h)

/-! ## Cell (71, 31): |T| = 5 -/

def T71_31list : List Coordinates := [(0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0)]
def T71_31 : Fin 5 → Coordinate 1 := fun i => T71_31list.getD i.val (0,0,0,0,0)

theorem hfix71_31 : ∀ i, ((T71_31 i : Coordinate 1) : Coordinate 1 ⧸ reps rK71)
    ∈ fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71) :=
  repsFix_of_siftB rK71 ⟨31, by decide⟩ T71_31 (by decide)

theorem hinj71_31 : Function.Injective
    (fun i => ((T71_31 i : Coordinate 1) : Coordinate 1 ⧸ reps rK71)) :=
  repsInj_of_reduceAux rK71 T71_31 (by decide)

theorem hcardT71_31 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK71 ⟨31, by decide⟩ R71 hpxR71 hcardq71 (by decide)).symm

/-- **Cell (71, 31).** -/
theorem cell71_31 (e : List (ZMod 25)) (heK : charOK (basisAt rK71) e = true)
    (h : ↥(reps (⟨31, by decide⟩ : Fin 148))) :
    species (reps (⟨31, by decide⟩ : Fin 148)) h (basisElt (reps rK71) (charOfVec rK71 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK71 e (h : Coordinate 1) T71_31 i :=
  species_entry_eq_sum rK71 ⟨31, by decide⟩ e heK h T71_31 hfix71_31 hinj71_31 hcardT71_31
    (fun i => conj_mem_of_fixedPoints (reps ⟨31, by decide⟩) (reps rK71) (T71_31 i) (hfix71_31 i) h)

/-! ## Cell (71, 36): |T| = 5 -/

def T71_36list : List Coordinates := [(0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0)]
def T71_36 : Fin 5 → Coordinate 1 := fun i => T71_36list.getD i.val (0,0,0,0,0)

theorem hfix71_36 : ∀ i, ((T71_36 i : Coordinate 1) : Coordinate 1 ⧸ reps rK71)
    ∈ fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71) :=
  repsFix_of_siftB rK71 ⟨36, by decide⟩ T71_36 (by decide)

theorem hinj71_36 : Function.Injective
    (fun i => ((T71_36 i : Coordinate 1) : Coordinate 1 ⧸ reps rK71)) :=
  repsInj_of_reduceAux rK71 T71_36 (by decide)

theorem hcardT71_36 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK71 ⟨36, by decide⟩ R71 hpxR71 hcardq71 (by decide)).symm

/-- **Cell (71, 36).** -/
theorem cell71_36 (e : List (ZMod 25)) (heK : charOK (basisAt rK71) e = true)
    (h : ↥(reps (⟨36, by decide⟩ : Fin 148))) :
    species (reps (⟨36, by decide⟩ : Fin 148)) h (basisElt (reps rK71) (charOfVec rK71 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK71 e (h : Coordinate 1) T71_36 i :=
  species_entry_eq_sum rK71 ⟨36, by decide⟩ e heK h T71_36 hfix71_36 hinj71_36 hcardT71_36
    (fun i => conj_mem_of_fixedPoints (reps ⟨36, by decide⟩) (reps rK71) (T71_36 i) (hfix71_36 i) h)

/-! ## Cell (71, 41): |T| = 5 -/

def T71_41list : List Coordinates := [(0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0)]
def T71_41 : Fin 5 → Coordinate 1 := fun i => T71_41list.getD i.val (0,0,0,0,0)

theorem hfix71_41 : ∀ i, ((T71_41 i : Coordinate 1) : Coordinate 1 ⧸ reps rK71)
    ∈ fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71) :=
  repsFix_of_siftB rK71 ⟨41, by decide⟩ T71_41 (by decide)

theorem hinj71_41 : Function.Injective
    (fun i => ((T71_41 i : Coordinate 1) : Coordinate 1 ⧸ reps rK71)) :=
  repsInj_of_reduceAux rK71 T71_41 (by decide)

theorem hcardT71_41 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK71 ⟨41, by decide⟩ R71 hpxR71 hcardq71 (by decide)).symm

/-- **Cell (71, 41).** -/
theorem cell71_41 (e : List (ZMod 25)) (heK : charOK (basisAt rK71) e = true)
    (h : ↥(reps (⟨41, by decide⟩ : Fin 148))) :
    species (reps (⟨41, by decide⟩ : Fin 148)) h (basisElt (reps rK71) (charOfVec rK71 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK71 e (h : Coordinate 1) T71_41 i :=
  species_entry_eq_sum rK71 ⟨41, by decide⟩ e heK h T71_41 hfix71_41 hinj71_41 hcardT71_41
    (fun i => conj_mem_of_fixedPoints (reps ⟨41, by decide⟩) (reps rK71) (T71_41 i) (hfix71_41 i) h)

/-! ## Cell (71, 46): |T| = 5 -/

def T71_46list : List Coordinates := [(0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0)]
def T71_46 : Fin 5 → Coordinate 1 := fun i => T71_46list.getD i.val (0,0,0,0,0)

theorem hfix71_46 : ∀ i, ((T71_46 i : Coordinate 1) : Coordinate 1 ⧸ reps rK71)
    ∈ fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71) :=
  repsFix_of_siftB rK71 ⟨46, by decide⟩ T71_46 (by decide)

theorem hinj71_46 : Function.Injective
    (fun i => ((T71_46 i : Coordinate 1) : Coordinate 1 ⧸ reps rK71)) :=
  repsInj_of_reduceAux rK71 T71_46 (by decide)

theorem hcardT71_46 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK71 ⟨46, by decide⟩ R71 hpxR71 hcardq71 (by decide)).symm

/-- **Cell (71, 46).** -/
theorem cell71_46 (e : List (ZMod 25)) (heK : charOK (basisAt rK71) e = true)
    (h : ↥(reps (⟨46, by decide⟩ : Fin 148))) :
    species (reps (⟨46, by decide⟩ : Fin 148)) h (basisElt (reps rK71) (charOfVec rK71 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK71 e (h : Coordinate 1) T71_46 i :=
  species_entry_eq_sum rK71 ⟨46, by decide⟩ e heK h T71_46 hfix71_46 hinj71_46 hcardT71_46
    (fun i => conj_mem_of_fixedPoints (reps ⟨46, by decide⟩) (reps rK71) (T71_46 i) (hfix71_46 i) h)

/-! ## Cell (71, 51): |T| = 5 -/

def T71_51list : List Coordinates := [(0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0)]
def T71_51 : Fin 5 → Coordinate 1 := fun i => T71_51list.getD i.val (0,0,0,0,0)

theorem hfix71_51 : ∀ i, ((T71_51 i : Coordinate 1) : Coordinate 1 ⧸ reps rK71)
    ∈ fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71) :=
  repsFix_of_siftB rK71 ⟨51, by decide⟩ T71_51 (by decide)

theorem hinj71_51 : Function.Injective
    (fun i => ((T71_51 i : Coordinate 1) : Coordinate 1 ⧸ reps rK71)) :=
  repsInj_of_reduceAux rK71 T71_51 (by decide)

theorem hcardT71_51 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK71 ⟨51, by decide⟩ R71 hpxR71 hcardq71 (by decide)).symm

/-- **Cell (71, 51).** -/
theorem cell71_51 (e : List (ZMod 25)) (heK : charOK (basisAt rK71) e = true)
    (h : ↥(reps (⟨51, by decide⟩ : Fin 148))) :
    species (reps (⟨51, by decide⟩ : Fin 148)) h (basisElt (reps rK71) (charOfVec rK71 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK71 e (h : Coordinate 1) T71_51 i :=
  species_entry_eq_sum rK71 ⟨51, by decide⟩ e heK h T71_51 hfix71_51 hinj71_51 hcardT71_51
    (fun i => conj_mem_of_fixedPoints (reps ⟨51, by decide⟩) (reps rK71) (T71_51 i) (hfix71_51 i) h)

/-! ## Cell (71, 71): |T| = 5 -/

def T71_71list : List Coordinates := [(0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0)]
def T71_71 : Fin 5 → Coordinate 1 := fun i => T71_71list.getD i.val (0,0,0,0,0)

theorem hfix71_71 : ∀ i, ((T71_71 i : Coordinate 1) : Coordinate 1 ⧸ reps rK71)
    ∈ fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71) :=
  repsFix_of_siftB rK71 ⟨71, by decide⟩ T71_71 (by decide)

theorem hinj71_71 : Function.Injective
    (fun i => ((T71_71 i : Coordinate 1) : Coordinate 1 ⧸ reps rK71)) :=
  repsInj_of_reduceAux rK71 T71_71 (by decide)

theorem hcardT71_71 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK71 ⟨71, by decide⟩ R71 hpxR71 hcardq71 (by decide)).symm

/-- **Cell (71, 71).** -/
theorem cell71_71 (e : List (ZMod 25)) (heK : charOK (basisAt rK71) e = true)
    (h : ↥(reps (⟨71, by decide⟩ : Fin 148))) :
    species (reps (⟨71, by decide⟩ : Fin 148)) h (basisElt (reps rK71) (charOfVec rK71 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK71 e (h : Coordinate 1) T71_71 i :=
  species_entry_eq_sum rK71 ⟨71, by decide⟩ e heK h T71_71 hfix71_71 hinj71_71 hcardT71_71
    (fun i => conj_mem_of_fixedPoints (reps ⟨71, by decide⟩) (reps rK71) (T71_71 i) (hfix71_71 i) h)

namespace Q2

def R71_2 : Fin 25 → Coordinate 2 := fun i => R71list.getD i.val (0,0,0,0,0)
theorem hpxR71_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK71) (R71_2 i)) := by decide
theorem hcardq71_2 : Nat.card (Coordinate 2 ⧸ reps rK71) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (71, 0) twin -/

def T71_0_2 : Fin 25 → Coordinate 2 := fun i => T71_0list.getD i.val (0,0,0,0,0)

theorem hfix71_0_2 : ∀ i, ((T71_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK71)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK71) :=
  repsFix_of_siftB2 rK71 ⟨0, by decide⟩ T71_0_2 (by decide)

theorem hinj71_0_2 : Function.Injective
    (fun i => ((T71_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK71)) :=
  repsInj_of_reduceAux2 rK71 T71_0_2 (by decide)

theorem hcardT71_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK71)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK71 ⟨0, by decide⟩ R71_2 hpxR71_2 hcardq71_2 (by decide)).symm

/-- **Cell (71, 0) twin (q=2).** -/
theorem cell71_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK71) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK71) (charOfVec2 rK71 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK71 e (h : Coordinate 2) T71_0_2 i :=
  species_entry_eq_sum rK71 ⟨0, by decide⟩ e heK h T71_0_2 hfix71_0_2 hinj71_0_2 hcardT71_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK71) (T71_0_2 i) (hfix71_0_2 i) h)

/-! ### Cell (71, 1) twin -/

def T71_1_2 : Fin 25 → Coordinate 2 := fun i => T71_1list.getD i.val (0,0,0,0,0)

theorem hfix71_1_2 : ∀ i, ((T71_1_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK71)
    ∈ fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK71) :=
  repsFix_of_siftB2 rK71 ⟨1, by decide⟩ T71_1_2 (by decide)

theorem hinj71_1_2 : Function.Injective
    (fun i => ((T71_1_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK71)) :=
  repsInj_of_reduceAux2 rK71 T71_1_2 (by decide)

theorem hcardT71_1_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK71)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK71 ⟨1, by decide⟩ R71_2 hpxR71_2 hcardq71_2 (by decide)).symm

/-- **Cell (71, 1) twin (q=2).** -/
theorem cell71_1_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK71) e = true)
    (h : ↥(reps (⟨1, by decide⟩ : Fin 148))) :
    species (reps (⟨1, by decide⟩ : Fin 148)) h (basisElt (reps rK71) (charOfVec2 rK71 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK71 e (h : Coordinate 2) T71_1_2 i :=
  species_entry_eq_sum rK71 ⟨1, by decide⟩ e heK h T71_1_2 hfix71_1_2 hinj71_1_2 hcardT71_1_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨1, by decide⟩) (reps rK71) (T71_1_2 i) (hfix71_1_2 i) h)

/-! ### Cell (71, 12) twin -/

def T71_12_2 : Fin 25 → Coordinate 2 := fun i => T71_12list.getD i.val (0,0,0,0,0)

theorem hfix71_12_2 : ∀ i, ((T71_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK71)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK71) :=
  repsFix_of_siftB2 rK71 ⟨12, by decide⟩ T71_12_2 (by decide)

theorem hinj71_12_2 : Function.Injective
    (fun i => ((T71_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK71)) :=
  repsInj_of_reduceAux2 rK71 T71_12_2 (by decide)

theorem hcardT71_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK71)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK71 ⟨12, by decide⟩ R71_2 hpxR71_2 hcardq71_2 (by decide)).symm

/-- **Cell (71, 12) twin (q=2).** -/
theorem cell71_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK71) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK71) (charOfVec2 rK71 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK71 e (h : Coordinate 2) T71_12_2 i :=
  species_entry_eq_sum rK71 ⟨12, by decide⟩ e heK h T71_12_2 hfix71_12_2 hinj71_12_2 hcardT71_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK71) (T71_12_2 i) (hfix71_12_2 i) h)

/-! ### Cell (71, 19) twin -/

def T71_19_2 : Fin 25 → Coordinate 2 := fun i => T71_19list.getD i.val (0,0,0,0,0)

theorem hfix71_19_2 : ∀ i, ((T71_19_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK71)
    ∈ fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK71) :=
  repsFix_of_siftB2 rK71 ⟨19, by decide⟩ T71_19_2 (by decide)

theorem hinj71_19_2 : Function.Injective
    (fun i => ((T71_19_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK71)) :=
  repsInj_of_reduceAux2 rK71 T71_19_2 (by decide)

theorem hcardT71_19_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK71)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK71 ⟨19, by decide⟩ R71_2 hpxR71_2 hcardq71_2 (by decide)).symm

/-- **Cell (71, 19) twin (q=2).** -/
theorem cell71_19_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK71) e = true)
    (h : ↥(reps (⟨19, by decide⟩ : Fin 148))) :
    species (reps (⟨19, by decide⟩ : Fin 148)) h (basisElt (reps rK71) (charOfVec2 rK71 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK71 e (h : Coordinate 2) T71_19_2 i :=
  species_entry_eq_sum rK71 ⟨19, by decide⟩ e heK h T71_19_2 hfix71_19_2 hinj71_19_2 hcardT71_19_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨19, by decide⟩) (reps rK71) (T71_19_2 i) (hfix71_19_2 i) h)

/-! ### Cell (71, 31) twin -/

def T71_31_2 : Fin 5 → Coordinate 2 := fun i => T71_31list.getD i.val (0,0,0,0,0)

theorem hfix71_31_2 : ∀ i, ((T71_31_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK71)
    ∈ fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK71) :=
  repsFix_of_siftB2 rK71 ⟨31, by decide⟩ T71_31_2 (by decide)

theorem hinj71_31_2 : Function.Injective
    (fun i => ((T71_31_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK71)) :=
  repsInj_of_reduceAux2 rK71 T71_31_2 (by decide)

theorem hcardT71_31_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK71)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK71 ⟨31, by decide⟩ R71_2 hpxR71_2 hcardq71_2 (by decide)).symm

/-- **Cell (71, 31) twin (q=2).** -/
theorem cell71_31_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK71) e = true)
    (h : ↥(reps (⟨31, by decide⟩ : Fin 148))) :
    species (reps (⟨31, by decide⟩ : Fin 148)) h (basisElt (reps rK71) (charOfVec2 rK71 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK71 e (h : Coordinate 2) T71_31_2 i :=
  species_entry_eq_sum rK71 ⟨31, by decide⟩ e heK h T71_31_2 hfix71_31_2 hinj71_31_2 hcardT71_31_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨31, by decide⟩) (reps rK71) (T71_31_2 i) (hfix71_31_2 i) h)

/-! ### Cell (71, 36) twin -/

def T71_36_2 : Fin 5 → Coordinate 2 := fun i => T71_36list.getD i.val (0,0,0,0,0)

theorem hfix71_36_2 : ∀ i, ((T71_36_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK71)
    ∈ fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK71) :=
  repsFix_of_siftB2 rK71 ⟨36, by decide⟩ T71_36_2 (by decide)

theorem hinj71_36_2 : Function.Injective
    (fun i => ((T71_36_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK71)) :=
  repsInj_of_reduceAux2 rK71 T71_36_2 (by decide)

theorem hcardT71_36_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK71)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK71 ⟨36, by decide⟩ R71_2 hpxR71_2 hcardq71_2 (by decide)).symm

/-- **Cell (71, 36) twin (q=2).** -/
theorem cell71_36_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK71) e = true)
    (h : ↥(reps (⟨36, by decide⟩ : Fin 148))) :
    species (reps (⟨36, by decide⟩ : Fin 148)) h (basisElt (reps rK71) (charOfVec2 rK71 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK71 e (h : Coordinate 2) T71_36_2 i :=
  species_entry_eq_sum rK71 ⟨36, by decide⟩ e heK h T71_36_2 hfix71_36_2 hinj71_36_2 hcardT71_36_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨36, by decide⟩) (reps rK71) (T71_36_2 i) (hfix71_36_2 i) h)

/-! ### Cell (71, 41) twin -/

def T71_41_2 : Fin 5 → Coordinate 2 := fun i => T71_41list.getD i.val (0,0,0,0,0)

theorem hfix71_41_2 : ∀ i, ((T71_41_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK71)
    ∈ fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK71) :=
  repsFix_of_siftB2 rK71 ⟨41, by decide⟩ T71_41_2 (by decide)

theorem hinj71_41_2 : Function.Injective
    (fun i => ((T71_41_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK71)) :=
  repsInj_of_reduceAux2 rK71 T71_41_2 (by decide)

theorem hcardT71_41_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK71)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK71 ⟨41, by decide⟩ R71_2 hpxR71_2 hcardq71_2 (by decide)).symm

/-- **Cell (71, 41) twin (q=2).** -/
theorem cell71_41_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK71) e = true)
    (h : ↥(reps (⟨41, by decide⟩ : Fin 148))) :
    species (reps (⟨41, by decide⟩ : Fin 148)) h (basisElt (reps rK71) (charOfVec2 rK71 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK71 e (h : Coordinate 2) T71_41_2 i :=
  species_entry_eq_sum rK71 ⟨41, by decide⟩ e heK h T71_41_2 hfix71_41_2 hinj71_41_2 hcardT71_41_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨41, by decide⟩) (reps rK71) (T71_41_2 i) (hfix71_41_2 i) h)

/-! ### Cell (71, 46) twin -/

def T71_46_2 : Fin 5 → Coordinate 2 := fun i => T71_46list.getD i.val (0,0,0,0,0)

theorem hfix71_46_2 : ∀ i, ((T71_46_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK71)
    ∈ fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK71) :=
  repsFix_of_siftB2 rK71 ⟨46, by decide⟩ T71_46_2 (by decide)

theorem hinj71_46_2 : Function.Injective
    (fun i => ((T71_46_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK71)) :=
  repsInj_of_reduceAux2 rK71 T71_46_2 (by decide)

theorem hcardT71_46_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK71)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK71 ⟨46, by decide⟩ R71_2 hpxR71_2 hcardq71_2 (by decide)).symm

/-- **Cell (71, 46) twin (q=2).** -/
theorem cell71_46_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK71) e = true)
    (h : ↥(reps (⟨46, by decide⟩ : Fin 148))) :
    species (reps (⟨46, by decide⟩ : Fin 148)) h (basisElt (reps rK71) (charOfVec2 rK71 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK71 e (h : Coordinate 2) T71_46_2 i :=
  species_entry_eq_sum rK71 ⟨46, by decide⟩ e heK h T71_46_2 hfix71_46_2 hinj71_46_2 hcardT71_46_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨46, by decide⟩) (reps rK71) (T71_46_2 i) (hfix71_46_2 i) h)

/-! ### Cell (71, 51) twin -/

def T71_51_2 : Fin 5 → Coordinate 2 := fun i => T71_51list.getD i.val (0,0,0,0,0)

theorem hfix71_51_2 : ∀ i, ((T71_51_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK71)
    ∈ fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK71) :=
  repsFix_of_siftB2 rK71 ⟨51, by decide⟩ T71_51_2 (by decide)

theorem hinj71_51_2 : Function.Injective
    (fun i => ((T71_51_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK71)) :=
  repsInj_of_reduceAux2 rK71 T71_51_2 (by decide)

theorem hcardT71_51_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK71)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK71 ⟨51, by decide⟩ R71_2 hpxR71_2 hcardq71_2 (by decide)).symm

/-- **Cell (71, 51) twin (q=2).** -/
theorem cell71_51_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK71) e = true)
    (h : ↥(reps (⟨51, by decide⟩ : Fin 148))) :
    species (reps (⟨51, by decide⟩ : Fin 148)) h (basisElt (reps rK71) (charOfVec2 rK71 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK71 e (h : Coordinate 2) T71_51_2 i :=
  species_entry_eq_sum rK71 ⟨51, by decide⟩ e heK h T71_51_2 hfix71_51_2 hinj71_51_2 hcardT71_51_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨51, by decide⟩) (reps rK71) (T71_51_2 i) (hfix71_51_2 i) h)

/-! ### Cell (71, 71) twin -/

def T71_71_2 : Fin 5 → Coordinate 2 := fun i => T71_71list.getD i.val (0,0,0,0,0)

theorem hfix71_71_2 : ∀ i, ((T71_71_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK71)
    ∈ fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK71) :=
  repsFix_of_siftB2 rK71 ⟨71, by decide⟩ T71_71_2 (by decide)

theorem hinj71_71_2 : Function.Injective
    (fun i => ((T71_71_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK71)) :=
  repsInj_of_reduceAux2 rK71 T71_71_2 (by decide)

theorem hcardT71_71_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK71)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK71 ⟨71, by decide⟩ R71_2 hpxR71_2 hcardq71_2 (by decide)).symm

/-- **Cell (71, 71) twin (q=2).** -/
theorem cell71_71_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK71) e = true)
    (h : ↥(reps (⟨71, by decide⟩ : Fin 148))) :
    species (reps (⟨71, by decide⟩ : Fin 148)) h (basisElt (reps rK71) (charOfVec2 rK71 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK71 e (h : Coordinate 2) T71_71_2 i :=
  species_entry_eq_sum rK71 ⟨71, by decide⟩ e heK h T71_71_2 hfix71_71_2 hinj71_71_2 hcardT71_71_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨71, by decide⟩) (reps rK71) (T71_71_2 i) (hfix71_71_2 i) h)

end Q2

/-! # K-class rK = 72  (|G/K| = 25) -/

def rK72 : Fin 148 := ⟨72, by decide⟩

def R72list : List Coordinates := [(0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0)]
def R72 : Fin 25 → Coordinate 1 := fun i => R72list.getD i.val (0,0,0,0,0)

theorem hpxR72 : Function.Injective (fun i => reduceAux 1 (basisAt rK72) (R72 i)) := by decide
theorem hcardq72 : Nat.card (Coordinate 1 ⧸ reps rK72) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (72, 0): |T| = 25 -/

def T72_0list : List Coordinates := [(0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0)]
def T72_0 : Fin 25 → Coordinate 1 := fun i => T72_0list.getD i.val (0,0,0,0,0)

theorem hfix72_0 : ∀ i, ((T72_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK72)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72) :=
  repsFix_of_siftB rK72 ⟨0, by decide⟩ T72_0 (by decide)

theorem hinj72_0 : Function.Injective
    (fun i => ((T72_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK72)) :=
  repsInj_of_reduceAux rK72 T72_0 (by decide)

theorem hcardT72_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK72 ⟨0, by decide⟩ R72 hpxR72 hcardq72 (by decide)).symm

/-- **Cell (72, 0).** -/
theorem cell72_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK72) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK72) (charOfVec rK72 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK72 e (h : Coordinate 1) T72_0 i :=
  species_entry_eq_sum rK72 ⟨0, by decide⟩ e heK h T72_0 hfix72_0 hinj72_0 hcardT72_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK72) (T72_0 i) (hfix72_0 i) h)

/-! ## Cell (72, 7): |T| = 25 -/

def T72_7list : List Coordinates := [(0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0)]
def T72_7 : Fin 25 → Coordinate 1 := fun i => T72_7list.getD i.val (0,0,0,0,0)

theorem hfix72_7 : ∀ i, ((T72_7 i : Coordinate 1) : Coordinate 1 ⧸ reps rK72)
    ∈ fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72) :=
  repsFix_of_siftB rK72 ⟨7, by decide⟩ T72_7 (by decide)

theorem hinj72_7 : Function.Injective
    (fun i => ((T72_7 i : Coordinate 1) : Coordinate 1 ⧸ reps rK72)) :=
  repsInj_of_reduceAux rK72 T72_7 (by decide)

theorem hcardT72_7 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK72 ⟨7, by decide⟩ R72 hpxR72 hcardq72 (by decide)).symm

/-- **Cell (72, 7).** -/
theorem cell72_7 (e : List (ZMod 25)) (heK : charOK (basisAt rK72) e = true)
    (h : ↥(reps (⟨7, by decide⟩ : Fin 148))) :
    species (reps (⟨7, by decide⟩ : Fin 148)) h (basisElt (reps rK72) (charOfVec rK72 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK72 e (h : Coordinate 1) T72_7 i :=
  species_entry_eq_sum rK72 ⟨7, by decide⟩ e heK h T72_7 hfix72_7 hinj72_7 hcardT72_7
    (fun i => conj_mem_of_fixedPoints (reps ⟨7, by decide⟩) (reps rK72) (T72_7 i) (hfix72_7 i) h)

/-! ## Cell (72, 12): |T| = 25 -/

def T72_12list : List Coordinates := [(0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0)]
def T72_12 : Fin 25 → Coordinate 1 := fun i => T72_12list.getD i.val (0,0,0,0,0)

theorem hfix72_12 : ∀ i, ((T72_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK72)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72) :=
  repsFix_of_siftB rK72 ⟨12, by decide⟩ T72_12 (by decide)

theorem hinj72_12 : Function.Injective
    (fun i => ((T72_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK72)) :=
  repsInj_of_reduceAux rK72 T72_12 (by decide)

theorem hcardT72_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK72 ⟨12, by decide⟩ R72 hpxR72 hcardq72 (by decide)).symm

/-- **Cell (72, 12).** -/
theorem cell72_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK72) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK72) (charOfVec rK72 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK72 e (h : Coordinate 1) T72_12 i :=
  species_entry_eq_sum rK72 ⟨12, by decide⟩ e heK h T72_12 hfix72_12 hinj72_12 hcardT72_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK72) (T72_12 i) (hfix72_12 i) h)

/-! ## Cell (72, 25): |T| = 25 -/

def T72_25list : List Coordinates := [(0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0)]
def T72_25 : Fin 25 → Coordinate 1 := fun i => T72_25list.getD i.val (0,0,0,0,0)

theorem hfix72_25 : ∀ i, ((T72_25 i : Coordinate 1) : Coordinate 1 ⧸ reps rK72)
    ∈ fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72) :=
  repsFix_of_siftB rK72 ⟨25, by decide⟩ T72_25 (by decide)

theorem hinj72_25 : Function.Injective
    (fun i => ((T72_25 i : Coordinate 1) : Coordinate 1 ⧸ reps rK72)) :=
  repsInj_of_reduceAux rK72 T72_25 (by decide)

theorem hcardT72_25 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK72 ⟨25, by decide⟩ R72 hpxR72 hcardq72 (by decide)).symm

/-- **Cell (72, 25).** -/
theorem cell72_25 (e : List (ZMod 25)) (heK : charOK (basisAt rK72) e = true)
    (h : ↥(reps (⟨25, by decide⟩ : Fin 148))) :
    species (reps (⟨25, by decide⟩ : Fin 148)) h (basisElt (reps rK72) (charOfVec rK72 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK72 e (h : Coordinate 1) T72_25 i :=
  species_entry_eq_sum rK72 ⟨25, by decide⟩ e heK h T72_25 hfix72_25 hinj72_25 hcardT72_25
    (fun i => conj_mem_of_fixedPoints (reps ⟨25, by decide⟩) (reps rK72) (T72_25 i) (hfix72_25 i) h)

/-! ## Cell (72, 31): |T| = 5 -/

def T72_31list : List Coordinates := [(0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0)]
def T72_31 : Fin 5 → Coordinate 1 := fun i => T72_31list.getD i.val (0,0,0,0,0)

theorem hfix72_31 : ∀ i, ((T72_31 i : Coordinate 1) : Coordinate 1 ⧸ reps rK72)
    ∈ fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72) :=
  repsFix_of_siftB rK72 ⟨31, by decide⟩ T72_31 (by decide)

theorem hinj72_31 : Function.Injective
    (fun i => ((T72_31 i : Coordinate 1) : Coordinate 1 ⧸ reps rK72)) :=
  repsInj_of_reduceAux rK72 T72_31 (by decide)

theorem hcardT72_31 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK72 ⟨31, by decide⟩ R72 hpxR72 hcardq72 (by decide)).symm

/-- **Cell (72, 31).** -/
theorem cell72_31 (e : List (ZMod 25)) (heK : charOK (basisAt rK72) e = true)
    (h : ↥(reps (⟨31, by decide⟩ : Fin 148))) :
    species (reps (⟨31, by decide⟩ : Fin 148)) h (basisElt (reps rK72) (charOfVec rK72 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK72 e (h : Coordinate 1) T72_31 i :=
  species_entry_eq_sum rK72 ⟨31, by decide⟩ e heK h T72_31 hfix72_31 hinj72_31 hcardT72_31
    (fun i => conj_mem_of_fixedPoints (reps ⟨31, by decide⟩) (reps rK72) (T72_31 i) (hfix72_31 i) h)

/-! ## Cell (72, 36): |T| = 5 -/

def T72_36list : List Coordinates := [(0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0)]
def T72_36 : Fin 5 → Coordinate 1 := fun i => T72_36list.getD i.val (0,0,0,0,0)

theorem hfix72_36 : ∀ i, ((T72_36 i : Coordinate 1) : Coordinate 1 ⧸ reps rK72)
    ∈ fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72) :=
  repsFix_of_siftB rK72 ⟨36, by decide⟩ T72_36 (by decide)

theorem hinj72_36 : Function.Injective
    (fun i => ((T72_36 i : Coordinate 1) : Coordinate 1 ⧸ reps rK72)) :=
  repsInj_of_reduceAux rK72 T72_36 (by decide)

theorem hcardT72_36 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK72 ⟨36, by decide⟩ R72 hpxR72 hcardq72 (by decide)).symm

/-- **Cell (72, 36).** -/
theorem cell72_36 (e : List (ZMod 25)) (heK : charOK (basisAt rK72) e = true)
    (h : ↥(reps (⟨36, by decide⟩ : Fin 148))) :
    species (reps (⟨36, by decide⟩ : Fin 148)) h (basisElt (reps rK72) (charOfVec rK72 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK72 e (h : Coordinate 1) T72_36 i :=
  species_entry_eq_sum rK72 ⟨36, by decide⟩ e heK h T72_36 hfix72_36 hinj72_36 hcardT72_36
    (fun i => conj_mem_of_fixedPoints (reps ⟨36, by decide⟩) (reps rK72) (T72_36 i) (hfix72_36 i) h)

/-! ## Cell (72, 41): |T| = 5 -/

def T72_41list : List Coordinates := [(0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0)]
def T72_41 : Fin 5 → Coordinate 1 := fun i => T72_41list.getD i.val (0,0,0,0,0)

theorem hfix72_41 : ∀ i, ((T72_41 i : Coordinate 1) : Coordinate 1 ⧸ reps rK72)
    ∈ fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72) :=
  repsFix_of_siftB rK72 ⟨41, by decide⟩ T72_41 (by decide)

theorem hinj72_41 : Function.Injective
    (fun i => ((T72_41 i : Coordinate 1) : Coordinate 1 ⧸ reps rK72)) :=
  repsInj_of_reduceAux rK72 T72_41 (by decide)

theorem hcardT72_41 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK72 ⟨41, by decide⟩ R72 hpxR72 hcardq72 (by decide)).symm

/-- **Cell (72, 41).** -/
theorem cell72_41 (e : List (ZMod 25)) (heK : charOK (basisAt rK72) e = true)
    (h : ↥(reps (⟨41, by decide⟩ : Fin 148))) :
    species (reps (⟨41, by decide⟩ : Fin 148)) h (basisElt (reps rK72) (charOfVec rK72 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK72 e (h : Coordinate 1) T72_41 i :=
  species_entry_eq_sum rK72 ⟨41, by decide⟩ e heK h T72_41 hfix72_41 hinj72_41 hcardT72_41
    (fun i => conj_mem_of_fixedPoints (reps ⟨41, by decide⟩) (reps rK72) (T72_41 i) (hfix72_41 i) h)

/-! ## Cell (72, 46): |T| = 5 -/

def T72_46list : List Coordinates := [(0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0)]
def T72_46 : Fin 5 → Coordinate 1 := fun i => T72_46list.getD i.val (0,0,0,0,0)

theorem hfix72_46 : ∀ i, ((T72_46 i : Coordinate 1) : Coordinate 1 ⧸ reps rK72)
    ∈ fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72) :=
  repsFix_of_siftB rK72 ⟨46, by decide⟩ T72_46 (by decide)

theorem hinj72_46 : Function.Injective
    (fun i => ((T72_46 i : Coordinate 1) : Coordinate 1 ⧸ reps rK72)) :=
  repsInj_of_reduceAux rK72 T72_46 (by decide)

theorem hcardT72_46 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK72 ⟨46, by decide⟩ R72 hpxR72 hcardq72 (by decide)).symm

/-- **Cell (72, 46).** -/
theorem cell72_46 (e : List (ZMod 25)) (heK : charOK (basisAt rK72) e = true)
    (h : ↥(reps (⟨46, by decide⟩ : Fin 148))) :
    species (reps (⟨46, by decide⟩ : Fin 148)) h (basisElt (reps rK72) (charOfVec rK72 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK72 e (h : Coordinate 1) T72_46 i :=
  species_entry_eq_sum rK72 ⟨46, by decide⟩ e heK h T72_46 hfix72_46 hinj72_46 hcardT72_46
    (fun i => conj_mem_of_fixedPoints (reps ⟨46, by decide⟩) (reps rK72) (T72_46 i) (hfix72_46 i) h)

/-! ## Cell (72, 51): |T| = 5 -/

def T72_51list : List Coordinates := [(0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0)]
def T72_51 : Fin 5 → Coordinate 1 := fun i => T72_51list.getD i.val (0,0,0,0,0)

theorem hfix72_51 : ∀ i, ((T72_51 i : Coordinate 1) : Coordinate 1 ⧸ reps rK72)
    ∈ fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72) :=
  repsFix_of_siftB rK72 ⟨51, by decide⟩ T72_51 (by decide)

theorem hinj72_51 : Function.Injective
    (fun i => ((T72_51 i : Coordinate 1) : Coordinate 1 ⧸ reps rK72)) :=
  repsInj_of_reduceAux rK72 T72_51 (by decide)

theorem hcardT72_51 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK72 ⟨51, by decide⟩ R72 hpxR72 hcardq72 (by decide)).symm

/-- **Cell (72, 51).** -/
theorem cell72_51 (e : List (ZMod 25)) (heK : charOK (basisAt rK72) e = true)
    (h : ↥(reps (⟨51, by decide⟩ : Fin 148))) :
    species (reps (⟨51, by decide⟩ : Fin 148)) h (basisElt (reps rK72) (charOfVec rK72 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK72 e (h : Coordinate 1) T72_51 i :=
  species_entry_eq_sum rK72 ⟨51, by decide⟩ e heK h T72_51 hfix72_51 hinj72_51 hcardT72_51
    (fun i => conj_mem_of_fixedPoints (reps ⟨51, by decide⟩) (reps rK72) (T72_51 i) (hfix72_51 i) h)

/-! ## Cell (72, 72): |T| = 5 -/

def T72_72list : List Coordinates := [(0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0)]
def T72_72 : Fin 5 → Coordinate 1 := fun i => T72_72list.getD i.val (0,0,0,0,0)

theorem hfix72_72 : ∀ i, ((T72_72 i : Coordinate 1) : Coordinate 1 ⧸ reps rK72)
    ∈ fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72) :=
  repsFix_of_siftB rK72 ⟨72, by decide⟩ T72_72 (by decide)

theorem hinj72_72 : Function.Injective
    (fun i => ((T72_72 i : Coordinate 1) : Coordinate 1 ⧸ reps rK72)) :=
  repsInj_of_reduceAux rK72 T72_72 (by decide)

theorem hcardT72_72 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK72 ⟨72, by decide⟩ R72 hpxR72 hcardq72 (by decide)).symm

/-- **Cell (72, 72).** -/
theorem cell72_72 (e : List (ZMod 25)) (heK : charOK (basisAt rK72) e = true)
    (h : ↥(reps (⟨72, by decide⟩ : Fin 148))) :
    species (reps (⟨72, by decide⟩ : Fin 148)) h (basisElt (reps rK72) (charOfVec rK72 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK72 e (h : Coordinate 1) T72_72 i :=
  species_entry_eq_sum rK72 ⟨72, by decide⟩ e heK h T72_72 hfix72_72 hinj72_72 hcardT72_72
    (fun i => conj_mem_of_fixedPoints (reps ⟨72, by decide⟩) (reps rK72) (T72_72 i) (hfix72_72 i) h)

namespace Q2

def R72_2 : Fin 25 → Coordinate 2 := fun i => R72list.getD i.val (0,0,0,0,0)
theorem hpxR72_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK72) (R72_2 i)) := by decide
theorem hcardq72_2 : Nat.card (Coordinate 2 ⧸ reps rK72) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (72, 0) twin -/

def T72_0_2 : Fin 25 → Coordinate 2 := fun i => T72_0list.getD i.val (0,0,0,0,0)

theorem hfix72_0_2 : ∀ i, ((T72_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK72)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK72) :=
  repsFix_of_siftB2 rK72 ⟨0, by decide⟩ T72_0_2 (by decide)

theorem hinj72_0_2 : Function.Injective
    (fun i => ((T72_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK72)) :=
  repsInj_of_reduceAux2 rK72 T72_0_2 (by decide)

theorem hcardT72_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK72)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK72 ⟨0, by decide⟩ R72_2 hpxR72_2 hcardq72_2 (by decide)).symm

/-- **Cell (72, 0) twin (q=2).** -/
theorem cell72_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK72) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK72) (charOfVec2 rK72 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK72 e (h : Coordinate 2) T72_0_2 i :=
  species_entry_eq_sum rK72 ⟨0, by decide⟩ e heK h T72_0_2 hfix72_0_2 hinj72_0_2 hcardT72_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK72) (T72_0_2 i) (hfix72_0_2 i) h)

/-! ### Cell (72, 7) twin -/

def T72_7_2 : Fin 25 → Coordinate 2 := fun i => T72_7list.getD i.val (0,0,0,0,0)

theorem hfix72_7_2 : ∀ i, ((T72_7_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK72)
    ∈ fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK72) :=
  repsFix_of_siftB2 rK72 ⟨7, by decide⟩ T72_7_2 (by decide)

theorem hinj72_7_2 : Function.Injective
    (fun i => ((T72_7_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK72)) :=
  repsInj_of_reduceAux2 rK72 T72_7_2 (by decide)

theorem hcardT72_7_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK72)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK72 ⟨7, by decide⟩ R72_2 hpxR72_2 hcardq72_2 (by decide)).symm

/-- **Cell (72, 7) twin (q=2).** -/
theorem cell72_7_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK72) e = true)
    (h : ↥(reps (⟨7, by decide⟩ : Fin 148))) :
    species (reps (⟨7, by decide⟩ : Fin 148)) h (basisElt (reps rK72) (charOfVec2 rK72 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK72 e (h : Coordinate 2) T72_7_2 i :=
  species_entry_eq_sum rK72 ⟨7, by decide⟩ e heK h T72_7_2 hfix72_7_2 hinj72_7_2 hcardT72_7_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨7, by decide⟩) (reps rK72) (T72_7_2 i) (hfix72_7_2 i) h)

/-! ### Cell (72, 12) twin -/

def T72_12_2 : Fin 25 → Coordinate 2 := fun i => T72_12list.getD i.val (0,0,0,0,0)

theorem hfix72_12_2 : ∀ i, ((T72_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK72)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK72) :=
  repsFix_of_siftB2 rK72 ⟨12, by decide⟩ T72_12_2 (by decide)

theorem hinj72_12_2 : Function.Injective
    (fun i => ((T72_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK72)) :=
  repsInj_of_reduceAux2 rK72 T72_12_2 (by decide)

theorem hcardT72_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK72)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK72 ⟨12, by decide⟩ R72_2 hpxR72_2 hcardq72_2 (by decide)).symm

/-- **Cell (72, 12) twin (q=2).** -/
theorem cell72_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK72) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK72) (charOfVec2 rK72 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK72 e (h : Coordinate 2) T72_12_2 i :=
  species_entry_eq_sum rK72 ⟨12, by decide⟩ e heK h T72_12_2 hfix72_12_2 hinj72_12_2 hcardT72_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK72) (T72_12_2 i) (hfix72_12_2 i) h)

/-! ### Cell (72, 25) twin -/

def T72_25_2 : Fin 25 → Coordinate 2 := fun i => T72_25list.getD i.val (0,0,0,0,0)

theorem hfix72_25_2 : ∀ i, ((T72_25_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK72)
    ∈ fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK72) :=
  repsFix_of_siftB2 rK72 ⟨25, by decide⟩ T72_25_2 (by decide)

theorem hinj72_25_2 : Function.Injective
    (fun i => ((T72_25_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK72)) :=
  repsInj_of_reduceAux2 rK72 T72_25_2 (by decide)

theorem hcardT72_25_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK72)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK72 ⟨25, by decide⟩ R72_2 hpxR72_2 hcardq72_2 (by decide)).symm

/-- **Cell (72, 25) twin (q=2).** -/
theorem cell72_25_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK72) e = true)
    (h : ↥(reps (⟨25, by decide⟩ : Fin 148))) :
    species (reps (⟨25, by decide⟩ : Fin 148)) h (basisElt (reps rK72) (charOfVec2 rK72 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK72 e (h : Coordinate 2) T72_25_2 i :=
  species_entry_eq_sum rK72 ⟨25, by decide⟩ e heK h T72_25_2 hfix72_25_2 hinj72_25_2 hcardT72_25_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨25, by decide⟩) (reps rK72) (T72_25_2 i) (hfix72_25_2 i) h)

/-! ### Cell (72, 31) twin -/

def T72_31_2 : Fin 5 → Coordinate 2 := fun i => T72_31list.getD i.val (0,0,0,0,0)

theorem hfix72_31_2 : ∀ i, ((T72_31_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK72)
    ∈ fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK72) :=
  repsFix_of_siftB2 rK72 ⟨31, by decide⟩ T72_31_2 (by decide)

theorem hinj72_31_2 : Function.Injective
    (fun i => ((T72_31_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK72)) :=
  repsInj_of_reduceAux2 rK72 T72_31_2 (by decide)

theorem hcardT72_31_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK72)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK72 ⟨31, by decide⟩ R72_2 hpxR72_2 hcardq72_2 (by decide)).symm

/-- **Cell (72, 31) twin (q=2).** -/
theorem cell72_31_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK72) e = true)
    (h : ↥(reps (⟨31, by decide⟩ : Fin 148))) :
    species (reps (⟨31, by decide⟩ : Fin 148)) h (basisElt (reps rK72) (charOfVec2 rK72 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK72 e (h : Coordinate 2) T72_31_2 i :=
  species_entry_eq_sum rK72 ⟨31, by decide⟩ e heK h T72_31_2 hfix72_31_2 hinj72_31_2 hcardT72_31_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨31, by decide⟩) (reps rK72) (T72_31_2 i) (hfix72_31_2 i) h)

/-! ### Cell (72, 36) twin -/

def T72_36_2 : Fin 5 → Coordinate 2 := fun i => T72_36list.getD i.val (0,0,0,0,0)

theorem hfix72_36_2 : ∀ i, ((T72_36_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK72)
    ∈ fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK72) :=
  repsFix_of_siftB2 rK72 ⟨36, by decide⟩ T72_36_2 (by decide)

theorem hinj72_36_2 : Function.Injective
    (fun i => ((T72_36_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK72)) :=
  repsInj_of_reduceAux2 rK72 T72_36_2 (by decide)

theorem hcardT72_36_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK72)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK72 ⟨36, by decide⟩ R72_2 hpxR72_2 hcardq72_2 (by decide)).symm

/-- **Cell (72, 36) twin (q=2).** -/
theorem cell72_36_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK72) e = true)
    (h : ↥(reps (⟨36, by decide⟩ : Fin 148))) :
    species (reps (⟨36, by decide⟩ : Fin 148)) h (basisElt (reps rK72) (charOfVec2 rK72 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK72 e (h : Coordinate 2) T72_36_2 i :=
  species_entry_eq_sum rK72 ⟨36, by decide⟩ e heK h T72_36_2 hfix72_36_2 hinj72_36_2 hcardT72_36_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨36, by decide⟩) (reps rK72) (T72_36_2 i) (hfix72_36_2 i) h)

/-! ### Cell (72, 41) twin -/

def T72_41_2 : Fin 5 → Coordinate 2 := fun i => T72_41list.getD i.val (0,0,0,0,0)

theorem hfix72_41_2 : ∀ i, ((T72_41_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK72)
    ∈ fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK72) :=
  repsFix_of_siftB2 rK72 ⟨41, by decide⟩ T72_41_2 (by decide)

theorem hinj72_41_2 : Function.Injective
    (fun i => ((T72_41_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK72)) :=
  repsInj_of_reduceAux2 rK72 T72_41_2 (by decide)

theorem hcardT72_41_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK72)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK72 ⟨41, by decide⟩ R72_2 hpxR72_2 hcardq72_2 (by decide)).symm

/-- **Cell (72, 41) twin (q=2).** -/
theorem cell72_41_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK72) e = true)
    (h : ↥(reps (⟨41, by decide⟩ : Fin 148))) :
    species (reps (⟨41, by decide⟩ : Fin 148)) h (basisElt (reps rK72) (charOfVec2 rK72 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK72 e (h : Coordinate 2) T72_41_2 i :=
  species_entry_eq_sum rK72 ⟨41, by decide⟩ e heK h T72_41_2 hfix72_41_2 hinj72_41_2 hcardT72_41_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨41, by decide⟩) (reps rK72) (T72_41_2 i) (hfix72_41_2 i) h)

/-! ### Cell (72, 46) twin -/

def T72_46_2 : Fin 5 → Coordinate 2 := fun i => T72_46list.getD i.val (0,0,0,0,0)

theorem hfix72_46_2 : ∀ i, ((T72_46_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK72)
    ∈ fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK72) :=
  repsFix_of_siftB2 rK72 ⟨46, by decide⟩ T72_46_2 (by decide)

theorem hinj72_46_2 : Function.Injective
    (fun i => ((T72_46_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK72)) :=
  repsInj_of_reduceAux2 rK72 T72_46_2 (by decide)

theorem hcardT72_46_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK72)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK72 ⟨46, by decide⟩ R72_2 hpxR72_2 hcardq72_2 (by decide)).symm

/-- **Cell (72, 46) twin (q=2).** -/
theorem cell72_46_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK72) e = true)
    (h : ↥(reps (⟨46, by decide⟩ : Fin 148))) :
    species (reps (⟨46, by decide⟩ : Fin 148)) h (basisElt (reps rK72) (charOfVec2 rK72 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK72 e (h : Coordinate 2) T72_46_2 i :=
  species_entry_eq_sum rK72 ⟨46, by decide⟩ e heK h T72_46_2 hfix72_46_2 hinj72_46_2 hcardT72_46_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨46, by decide⟩) (reps rK72) (T72_46_2 i) (hfix72_46_2 i) h)

/-! ### Cell (72, 51) twin -/

def T72_51_2 : Fin 5 → Coordinate 2 := fun i => T72_51list.getD i.val (0,0,0,0,0)

theorem hfix72_51_2 : ∀ i, ((T72_51_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK72)
    ∈ fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK72) :=
  repsFix_of_siftB2 rK72 ⟨51, by decide⟩ T72_51_2 (by decide)

theorem hinj72_51_2 : Function.Injective
    (fun i => ((T72_51_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK72)) :=
  repsInj_of_reduceAux2 rK72 T72_51_2 (by decide)

theorem hcardT72_51_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK72)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK72 ⟨51, by decide⟩ R72_2 hpxR72_2 hcardq72_2 (by decide)).symm

/-- **Cell (72, 51) twin (q=2).** -/
theorem cell72_51_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK72) e = true)
    (h : ↥(reps (⟨51, by decide⟩ : Fin 148))) :
    species (reps (⟨51, by decide⟩ : Fin 148)) h (basisElt (reps rK72) (charOfVec2 rK72 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK72 e (h : Coordinate 2) T72_51_2 i :=
  species_entry_eq_sum rK72 ⟨51, by decide⟩ e heK h T72_51_2 hfix72_51_2 hinj72_51_2 hcardT72_51_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨51, by decide⟩) (reps rK72) (T72_51_2 i) (hfix72_51_2 i) h)

/-! ### Cell (72, 72) twin -/

def T72_72_2 : Fin 5 → Coordinate 2 := fun i => T72_72list.getD i.val (0,0,0,0,0)

theorem hfix72_72_2 : ∀ i, ((T72_72_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK72)
    ∈ fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK72) :=
  repsFix_of_siftB2 rK72 ⟨72, by decide⟩ T72_72_2 (by decide)

theorem hinj72_72_2 : Function.Injective
    (fun i => ((T72_72_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK72)) :=
  repsInj_of_reduceAux2 rK72 T72_72_2 (by decide)

theorem hcardT72_72_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK72)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK72 ⟨72, by decide⟩ R72_2 hpxR72_2 hcardq72_2 (by decide)).symm

/-- **Cell (72, 72) twin (q=2).** -/
theorem cell72_72_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK72) e = true)
    (h : ↥(reps (⟨72, by decide⟩ : Fin 148))) :
    species (reps (⟨72, by decide⟩ : Fin 148)) h (basisElt (reps rK72) (charOfVec2 rK72 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK72 e (h : Coordinate 2) T72_72_2 i :=
  species_entry_eq_sum rK72 ⟨72, by decide⟩ e heK h T72_72_2 hfix72_72_2 hinj72_72_2 hcardT72_72_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨72, by decide⟩) (reps rK72) (T72_72_2 i) (hfix72_72_2 i) h)

end Q2

/-! # K-class rK = 73  (|G/K| = 25) -/

def rK73 : Fin 148 := ⟨73, by decide⟩

def R73list : List Coordinates := [(0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0)]
def R73 : Fin 25 → Coordinate 1 := fun i => R73list.getD i.val (0,0,0,0,0)

theorem hpxR73 : Function.Injective (fun i => reduceAux 1 (basisAt rK73) (R73 i)) := by decide
theorem hcardq73 : Nat.card (Coordinate 1 ⧸ reps rK73) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (73, 0): |T| = 25 -/

def T73_0list : List Coordinates := [(0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0)]
def T73_0 : Fin 25 → Coordinate 1 := fun i => T73_0list.getD i.val (0,0,0,0,0)

theorem hfix73_0 : ∀ i, ((T73_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK73)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73) :=
  repsFix_of_siftB rK73 ⟨0, by decide⟩ T73_0 (by decide)

theorem hinj73_0 : Function.Injective
    (fun i => ((T73_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK73)) :=
  repsInj_of_reduceAux rK73 T73_0 (by decide)

theorem hcardT73_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK73 ⟨0, by decide⟩ R73 hpxR73 hcardq73 (by decide)).symm

/-- **Cell (73, 0).** -/
theorem cell73_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK73) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK73) (charOfVec rK73 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK73 e (h : Coordinate 1) T73_0 i :=
  species_entry_eq_sum rK73 ⟨0, by decide⟩ e heK h T73_0 hfix73_0 hinj73_0 hcardT73_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK73) (T73_0 i) (hfix73_0 i) h)

/-! ## Cell (73, 6): |T| = 25 -/

def T73_6list : List Coordinates := [(0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0)]
def T73_6 : Fin 25 → Coordinate 1 := fun i => T73_6list.getD i.val (0,0,0,0,0)

theorem hfix73_6 : ∀ i, ((T73_6 i : Coordinate 1) : Coordinate 1 ⧸ reps rK73)
    ∈ fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73) :=
  repsFix_of_siftB rK73 ⟨6, by decide⟩ T73_6 (by decide)

theorem hinj73_6 : Function.Injective
    (fun i => ((T73_6 i : Coordinate 1) : Coordinate 1 ⧸ reps rK73)) :=
  repsInj_of_reduceAux rK73 T73_6 (by decide)

theorem hcardT73_6 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK73 ⟨6, by decide⟩ R73 hpxR73 hcardq73 (by decide)).symm

/-- **Cell (73, 6).** -/
theorem cell73_6 (e : List (ZMod 25)) (heK : charOK (basisAt rK73) e = true)
    (h : ↥(reps (⟨6, by decide⟩ : Fin 148))) :
    species (reps (⟨6, by decide⟩ : Fin 148)) h (basisElt (reps rK73) (charOfVec rK73 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK73 e (h : Coordinate 1) T73_6 i :=
  species_entry_eq_sum rK73 ⟨6, by decide⟩ e heK h T73_6 hfix73_6 hinj73_6 hcardT73_6
    (fun i => conj_mem_of_fixedPoints (reps ⟨6, by decide⟩) (reps rK73) (T73_6 i) (hfix73_6 i) h)

/-! ## Cell (73, 12): |T| = 25 -/

def T73_12list : List Coordinates := [(0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0)]
def T73_12 : Fin 25 → Coordinate 1 := fun i => T73_12list.getD i.val (0,0,0,0,0)

theorem hfix73_12 : ∀ i, ((T73_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK73)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73) :=
  repsFix_of_siftB rK73 ⟨12, by decide⟩ T73_12 (by decide)

theorem hinj73_12 : Function.Injective
    (fun i => ((T73_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK73)) :=
  repsInj_of_reduceAux rK73 T73_12 (by decide)

theorem hcardT73_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK73 ⟨12, by decide⟩ R73 hpxR73 hcardq73 (by decide)).symm

/-- **Cell (73, 12).** -/
theorem cell73_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK73) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK73) (charOfVec rK73 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK73 e (h : Coordinate 1) T73_12 i :=
  species_entry_eq_sum rK73 ⟨12, by decide⟩ e heK h T73_12 hfix73_12 hinj73_12 hcardT73_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK73) (T73_12 i) (hfix73_12 i) h)

/-! ## Cell (73, 24): |T| = 25 -/

def T73_24list : List Coordinates := [(0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0)]
def T73_24 : Fin 25 → Coordinate 1 := fun i => T73_24list.getD i.val (0,0,0,0,0)

theorem hfix73_24 : ∀ i, ((T73_24 i : Coordinate 1) : Coordinate 1 ⧸ reps rK73)
    ∈ fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73) :=
  repsFix_of_siftB rK73 ⟨24, by decide⟩ T73_24 (by decide)

theorem hinj73_24 : Function.Injective
    (fun i => ((T73_24 i : Coordinate 1) : Coordinate 1 ⧸ reps rK73)) :=
  repsInj_of_reduceAux rK73 T73_24 (by decide)

theorem hcardT73_24 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK73 ⟨24, by decide⟩ R73 hpxR73 hcardq73 (by decide)).symm

/-- **Cell (73, 24).** -/
theorem cell73_24 (e : List (ZMod 25)) (heK : charOK (basisAt rK73) e = true)
    (h : ↥(reps (⟨24, by decide⟩ : Fin 148))) :
    species (reps (⟨24, by decide⟩ : Fin 148)) h (basisElt (reps rK73) (charOfVec rK73 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK73 e (h : Coordinate 1) T73_24 i :=
  species_entry_eq_sum rK73 ⟨24, by decide⟩ e heK h T73_24 hfix73_24 hinj73_24 hcardT73_24
    (fun i => conj_mem_of_fixedPoints (reps ⟨24, by decide⟩) (reps rK73) (T73_24 i) (hfix73_24 i) h)

/-! ## Cell (73, 31): |T| = 5 -/

def T73_31list : List Coordinates := [(0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0)]
def T73_31 : Fin 5 → Coordinate 1 := fun i => T73_31list.getD i.val (0,0,0,0,0)

theorem hfix73_31 : ∀ i, ((T73_31 i : Coordinate 1) : Coordinate 1 ⧸ reps rK73)
    ∈ fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73) :=
  repsFix_of_siftB rK73 ⟨31, by decide⟩ T73_31 (by decide)

theorem hinj73_31 : Function.Injective
    (fun i => ((T73_31 i : Coordinate 1) : Coordinate 1 ⧸ reps rK73)) :=
  repsInj_of_reduceAux rK73 T73_31 (by decide)

theorem hcardT73_31 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK73 ⟨31, by decide⟩ R73 hpxR73 hcardq73 (by decide)).symm

/-- **Cell (73, 31).** -/
theorem cell73_31 (e : List (ZMod 25)) (heK : charOK (basisAt rK73) e = true)
    (h : ↥(reps (⟨31, by decide⟩ : Fin 148))) :
    species (reps (⟨31, by decide⟩ : Fin 148)) h (basisElt (reps rK73) (charOfVec rK73 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK73 e (h : Coordinate 1) T73_31 i :=
  species_entry_eq_sum rK73 ⟨31, by decide⟩ e heK h T73_31 hfix73_31 hinj73_31 hcardT73_31
    (fun i => conj_mem_of_fixedPoints (reps ⟨31, by decide⟩) (reps rK73) (T73_31 i) (hfix73_31 i) h)

/-! ## Cell (73, 36): |T| = 5 -/

def T73_36list : List Coordinates := [(0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0)]
def T73_36 : Fin 5 → Coordinate 1 := fun i => T73_36list.getD i.val (0,0,0,0,0)

theorem hfix73_36 : ∀ i, ((T73_36 i : Coordinate 1) : Coordinate 1 ⧸ reps rK73)
    ∈ fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73) :=
  repsFix_of_siftB rK73 ⟨36, by decide⟩ T73_36 (by decide)

theorem hinj73_36 : Function.Injective
    (fun i => ((T73_36 i : Coordinate 1) : Coordinate 1 ⧸ reps rK73)) :=
  repsInj_of_reduceAux rK73 T73_36 (by decide)

theorem hcardT73_36 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK73 ⟨36, by decide⟩ R73 hpxR73 hcardq73 (by decide)).symm

/-- **Cell (73, 36).** -/
theorem cell73_36 (e : List (ZMod 25)) (heK : charOK (basisAt rK73) e = true)
    (h : ↥(reps (⟨36, by decide⟩ : Fin 148))) :
    species (reps (⟨36, by decide⟩ : Fin 148)) h (basisElt (reps rK73) (charOfVec rK73 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK73 e (h : Coordinate 1) T73_36 i :=
  species_entry_eq_sum rK73 ⟨36, by decide⟩ e heK h T73_36 hfix73_36 hinj73_36 hcardT73_36
    (fun i => conj_mem_of_fixedPoints (reps ⟨36, by decide⟩) (reps rK73) (T73_36 i) (hfix73_36 i) h)

/-! ## Cell (73, 41): |T| = 5 -/

def T73_41list : List Coordinates := [(0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0)]
def T73_41 : Fin 5 → Coordinate 1 := fun i => T73_41list.getD i.val (0,0,0,0,0)

theorem hfix73_41 : ∀ i, ((T73_41 i : Coordinate 1) : Coordinate 1 ⧸ reps rK73)
    ∈ fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73) :=
  repsFix_of_siftB rK73 ⟨41, by decide⟩ T73_41 (by decide)

theorem hinj73_41 : Function.Injective
    (fun i => ((T73_41 i : Coordinate 1) : Coordinate 1 ⧸ reps rK73)) :=
  repsInj_of_reduceAux rK73 T73_41 (by decide)

theorem hcardT73_41 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK73 ⟨41, by decide⟩ R73 hpxR73 hcardq73 (by decide)).symm

/-- **Cell (73, 41).** -/
theorem cell73_41 (e : List (ZMod 25)) (heK : charOK (basisAt rK73) e = true)
    (h : ↥(reps (⟨41, by decide⟩ : Fin 148))) :
    species (reps (⟨41, by decide⟩ : Fin 148)) h (basisElt (reps rK73) (charOfVec rK73 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK73 e (h : Coordinate 1) T73_41 i :=
  species_entry_eq_sum rK73 ⟨41, by decide⟩ e heK h T73_41 hfix73_41 hinj73_41 hcardT73_41
    (fun i => conj_mem_of_fixedPoints (reps ⟨41, by decide⟩) (reps rK73) (T73_41 i) (hfix73_41 i) h)

/-! ## Cell (73, 46): |T| = 5 -/

def T73_46list : List Coordinates := [(0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0)]
def T73_46 : Fin 5 → Coordinate 1 := fun i => T73_46list.getD i.val (0,0,0,0,0)

theorem hfix73_46 : ∀ i, ((T73_46 i : Coordinate 1) : Coordinate 1 ⧸ reps rK73)
    ∈ fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73) :=
  repsFix_of_siftB rK73 ⟨46, by decide⟩ T73_46 (by decide)

theorem hinj73_46 : Function.Injective
    (fun i => ((T73_46 i : Coordinate 1) : Coordinate 1 ⧸ reps rK73)) :=
  repsInj_of_reduceAux rK73 T73_46 (by decide)

theorem hcardT73_46 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK73 ⟨46, by decide⟩ R73 hpxR73 hcardq73 (by decide)).symm

/-- **Cell (73, 46).** -/
theorem cell73_46 (e : List (ZMod 25)) (heK : charOK (basisAt rK73) e = true)
    (h : ↥(reps (⟨46, by decide⟩ : Fin 148))) :
    species (reps (⟨46, by decide⟩ : Fin 148)) h (basisElt (reps rK73) (charOfVec rK73 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK73 e (h : Coordinate 1) T73_46 i :=
  species_entry_eq_sum rK73 ⟨46, by decide⟩ e heK h T73_46 hfix73_46 hinj73_46 hcardT73_46
    (fun i => conj_mem_of_fixedPoints (reps ⟨46, by decide⟩) (reps rK73) (T73_46 i) (hfix73_46 i) h)

/-! ## Cell (73, 51): |T| = 5 -/

def T73_51list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0)]
def T73_51 : Fin 5 → Coordinate 1 := fun i => T73_51list.getD i.val (0,0,0,0,0)

theorem hfix73_51 : ∀ i, ((T73_51 i : Coordinate 1) : Coordinate 1 ⧸ reps rK73)
    ∈ fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73) :=
  repsFix_of_siftB rK73 ⟨51, by decide⟩ T73_51 (by decide)

theorem hinj73_51 : Function.Injective
    (fun i => ((T73_51 i : Coordinate 1) : Coordinate 1 ⧸ reps rK73)) :=
  repsInj_of_reduceAux rK73 T73_51 (by decide)

theorem hcardT73_51 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK73 ⟨51, by decide⟩ R73 hpxR73 hcardq73 (by decide)).symm

/-- **Cell (73, 51).** -/
theorem cell73_51 (e : List (ZMod 25)) (heK : charOK (basisAt rK73) e = true)
    (h : ↥(reps (⟨51, by decide⟩ : Fin 148))) :
    species (reps (⟨51, by decide⟩ : Fin 148)) h (basisElt (reps rK73) (charOfVec rK73 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK73 e (h : Coordinate 1) T73_51 i :=
  species_entry_eq_sum rK73 ⟨51, by decide⟩ e heK h T73_51 hfix73_51 hinj73_51 hcardT73_51
    (fun i => conj_mem_of_fixedPoints (reps ⟨51, by decide⟩) (reps rK73) (T73_51 i) (hfix73_51 i) h)

/-! ## Cell (73, 73): |T| = 5 -/

def T73_73list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0)]
def T73_73 : Fin 5 → Coordinate 1 := fun i => T73_73list.getD i.val (0,0,0,0,0)

theorem hfix73_73 : ∀ i, ((T73_73 i : Coordinate 1) : Coordinate 1 ⧸ reps rK73)
    ∈ fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73) :=
  repsFix_of_siftB rK73 ⟨73, by decide⟩ T73_73 (by decide)

theorem hinj73_73 : Function.Injective
    (fun i => ((T73_73 i : Coordinate 1) : Coordinate 1 ⧸ reps rK73)) :=
  repsInj_of_reduceAux rK73 T73_73 (by decide)

theorem hcardT73_73 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK73 ⟨73, by decide⟩ R73 hpxR73 hcardq73 (by decide)).symm

/-- **Cell (73, 73).** -/
theorem cell73_73 (e : List (ZMod 25)) (heK : charOK (basisAt rK73) e = true)
    (h : ↥(reps (⟨73, by decide⟩ : Fin 148))) :
    species (reps (⟨73, by decide⟩ : Fin 148)) h (basisElt (reps rK73) (charOfVec rK73 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK73 e (h : Coordinate 1) T73_73 i :=
  species_entry_eq_sum rK73 ⟨73, by decide⟩ e heK h T73_73 hfix73_73 hinj73_73 hcardT73_73
    (fun i => conj_mem_of_fixedPoints (reps ⟨73, by decide⟩) (reps rK73) (T73_73 i) (hfix73_73 i) h)

namespace Q2

def R73_2 : Fin 25 → Coordinate 2 := fun i => R73list.getD i.val (0,0,0,0,0)
theorem hpxR73_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK73) (R73_2 i)) := by decide
theorem hcardq73_2 : Nat.card (Coordinate 2 ⧸ reps rK73) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (73, 0) twin -/

def T73_0_2 : Fin 25 → Coordinate 2 := fun i => T73_0list.getD i.val (0,0,0,0,0)

theorem hfix73_0_2 : ∀ i, ((T73_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK73)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK73) :=
  repsFix_of_siftB2 rK73 ⟨0, by decide⟩ T73_0_2 (by decide)

theorem hinj73_0_2 : Function.Injective
    (fun i => ((T73_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK73)) :=
  repsInj_of_reduceAux2 rK73 T73_0_2 (by decide)

theorem hcardT73_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK73)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK73 ⟨0, by decide⟩ R73_2 hpxR73_2 hcardq73_2 (by decide)).symm

/-- **Cell (73, 0) twin (q=2).** -/
theorem cell73_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK73) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK73) (charOfVec2 rK73 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK73 e (h : Coordinate 2) T73_0_2 i :=
  species_entry_eq_sum rK73 ⟨0, by decide⟩ e heK h T73_0_2 hfix73_0_2 hinj73_0_2 hcardT73_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK73) (T73_0_2 i) (hfix73_0_2 i) h)

/-! ### Cell (73, 6) twin -/

def T73_6_2 : Fin 25 → Coordinate 2 := fun i => T73_6list.getD i.val (0,0,0,0,0)

theorem hfix73_6_2 : ∀ i, ((T73_6_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK73)
    ∈ fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK73) :=
  repsFix_of_siftB2 rK73 ⟨6, by decide⟩ T73_6_2 (by decide)

theorem hinj73_6_2 : Function.Injective
    (fun i => ((T73_6_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK73)) :=
  repsInj_of_reduceAux2 rK73 T73_6_2 (by decide)

theorem hcardT73_6_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK73)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK73 ⟨6, by decide⟩ R73_2 hpxR73_2 hcardq73_2 (by decide)).symm

/-- **Cell (73, 6) twin (q=2).** -/
theorem cell73_6_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK73) e = true)
    (h : ↥(reps (⟨6, by decide⟩ : Fin 148))) :
    species (reps (⟨6, by decide⟩ : Fin 148)) h (basisElt (reps rK73) (charOfVec2 rK73 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK73 e (h : Coordinate 2) T73_6_2 i :=
  species_entry_eq_sum rK73 ⟨6, by decide⟩ e heK h T73_6_2 hfix73_6_2 hinj73_6_2 hcardT73_6_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨6, by decide⟩) (reps rK73) (T73_6_2 i) (hfix73_6_2 i) h)

/-! ### Cell (73, 12) twin -/

def T73_12_2 : Fin 25 → Coordinate 2 := fun i => T73_12list.getD i.val (0,0,0,0,0)

theorem hfix73_12_2 : ∀ i, ((T73_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK73)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK73) :=
  repsFix_of_siftB2 rK73 ⟨12, by decide⟩ T73_12_2 (by decide)

theorem hinj73_12_2 : Function.Injective
    (fun i => ((T73_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK73)) :=
  repsInj_of_reduceAux2 rK73 T73_12_2 (by decide)

theorem hcardT73_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK73)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK73 ⟨12, by decide⟩ R73_2 hpxR73_2 hcardq73_2 (by decide)).symm

/-- **Cell (73, 12) twin (q=2).** -/
theorem cell73_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK73) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK73) (charOfVec2 rK73 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK73 e (h : Coordinate 2) T73_12_2 i :=
  species_entry_eq_sum rK73 ⟨12, by decide⟩ e heK h T73_12_2 hfix73_12_2 hinj73_12_2 hcardT73_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK73) (T73_12_2 i) (hfix73_12_2 i) h)

/-! ### Cell (73, 24) twin -/

def T73_24_2 : Fin 25 → Coordinate 2 := fun i => T73_24list.getD i.val (0,0,0,0,0)

theorem hfix73_24_2 : ∀ i, ((T73_24_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK73)
    ∈ fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK73) :=
  repsFix_of_siftB2 rK73 ⟨24, by decide⟩ T73_24_2 (by decide)

theorem hinj73_24_2 : Function.Injective
    (fun i => ((T73_24_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK73)) :=
  repsInj_of_reduceAux2 rK73 T73_24_2 (by decide)

theorem hcardT73_24_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK73)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK73 ⟨24, by decide⟩ R73_2 hpxR73_2 hcardq73_2 (by decide)).symm

/-- **Cell (73, 24) twin (q=2).** -/
theorem cell73_24_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK73) e = true)
    (h : ↥(reps (⟨24, by decide⟩ : Fin 148))) :
    species (reps (⟨24, by decide⟩ : Fin 148)) h (basisElt (reps rK73) (charOfVec2 rK73 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK73 e (h : Coordinate 2) T73_24_2 i :=
  species_entry_eq_sum rK73 ⟨24, by decide⟩ e heK h T73_24_2 hfix73_24_2 hinj73_24_2 hcardT73_24_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨24, by decide⟩) (reps rK73) (T73_24_2 i) (hfix73_24_2 i) h)

/-! ### Cell (73, 31) twin -/

def T73_31_2 : Fin 5 → Coordinate 2 := fun i => T73_31list.getD i.val (0,0,0,0,0)

theorem hfix73_31_2 : ∀ i, ((T73_31_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK73)
    ∈ fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK73) :=
  repsFix_of_siftB2 rK73 ⟨31, by decide⟩ T73_31_2 (by decide)

theorem hinj73_31_2 : Function.Injective
    (fun i => ((T73_31_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK73)) :=
  repsInj_of_reduceAux2 rK73 T73_31_2 (by decide)

theorem hcardT73_31_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK73)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK73 ⟨31, by decide⟩ R73_2 hpxR73_2 hcardq73_2 (by decide)).symm

/-- **Cell (73, 31) twin (q=2).** -/
theorem cell73_31_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK73) e = true)
    (h : ↥(reps (⟨31, by decide⟩ : Fin 148))) :
    species (reps (⟨31, by decide⟩ : Fin 148)) h (basisElt (reps rK73) (charOfVec2 rK73 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK73 e (h : Coordinate 2) T73_31_2 i :=
  species_entry_eq_sum rK73 ⟨31, by decide⟩ e heK h T73_31_2 hfix73_31_2 hinj73_31_2 hcardT73_31_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨31, by decide⟩) (reps rK73) (T73_31_2 i) (hfix73_31_2 i) h)

/-! ### Cell (73, 36) twin -/

def T73_36_2 : Fin 5 → Coordinate 2 := fun i => T73_36list.getD i.val (0,0,0,0,0)

theorem hfix73_36_2 : ∀ i, ((T73_36_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK73)
    ∈ fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK73) :=
  repsFix_of_siftB2 rK73 ⟨36, by decide⟩ T73_36_2 (by decide)

theorem hinj73_36_2 : Function.Injective
    (fun i => ((T73_36_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK73)) :=
  repsInj_of_reduceAux2 rK73 T73_36_2 (by decide)

theorem hcardT73_36_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK73)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK73 ⟨36, by decide⟩ R73_2 hpxR73_2 hcardq73_2 (by decide)).symm

/-- **Cell (73, 36) twin (q=2).** -/
theorem cell73_36_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK73) e = true)
    (h : ↥(reps (⟨36, by decide⟩ : Fin 148))) :
    species (reps (⟨36, by decide⟩ : Fin 148)) h (basisElt (reps rK73) (charOfVec2 rK73 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK73 e (h : Coordinate 2) T73_36_2 i :=
  species_entry_eq_sum rK73 ⟨36, by decide⟩ e heK h T73_36_2 hfix73_36_2 hinj73_36_2 hcardT73_36_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨36, by decide⟩) (reps rK73) (T73_36_2 i) (hfix73_36_2 i) h)

/-! ### Cell (73, 41) twin -/

def T73_41_2 : Fin 5 → Coordinate 2 := fun i => T73_41list.getD i.val (0,0,0,0,0)

theorem hfix73_41_2 : ∀ i, ((T73_41_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK73)
    ∈ fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK73) :=
  repsFix_of_siftB2 rK73 ⟨41, by decide⟩ T73_41_2 (by decide)

theorem hinj73_41_2 : Function.Injective
    (fun i => ((T73_41_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK73)) :=
  repsInj_of_reduceAux2 rK73 T73_41_2 (by decide)

theorem hcardT73_41_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK73)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK73 ⟨41, by decide⟩ R73_2 hpxR73_2 hcardq73_2 (by decide)).symm

/-- **Cell (73, 41) twin (q=2).** -/
theorem cell73_41_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK73) e = true)
    (h : ↥(reps (⟨41, by decide⟩ : Fin 148))) :
    species (reps (⟨41, by decide⟩ : Fin 148)) h (basisElt (reps rK73) (charOfVec2 rK73 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK73 e (h : Coordinate 2) T73_41_2 i :=
  species_entry_eq_sum rK73 ⟨41, by decide⟩ e heK h T73_41_2 hfix73_41_2 hinj73_41_2 hcardT73_41_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨41, by decide⟩) (reps rK73) (T73_41_2 i) (hfix73_41_2 i) h)

/-! ### Cell (73, 46) twin -/

def T73_46_2 : Fin 5 → Coordinate 2 := fun i => T73_46list.getD i.val (0,0,0,0,0)

theorem hfix73_46_2 : ∀ i, ((T73_46_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK73)
    ∈ fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK73) :=
  repsFix_of_siftB2 rK73 ⟨46, by decide⟩ T73_46_2 (by decide)

theorem hinj73_46_2 : Function.Injective
    (fun i => ((T73_46_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK73)) :=
  repsInj_of_reduceAux2 rK73 T73_46_2 (by decide)

theorem hcardT73_46_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK73)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK73 ⟨46, by decide⟩ R73_2 hpxR73_2 hcardq73_2 (by decide)).symm

/-- **Cell (73, 46) twin (q=2).** -/
theorem cell73_46_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK73) e = true)
    (h : ↥(reps (⟨46, by decide⟩ : Fin 148))) :
    species (reps (⟨46, by decide⟩ : Fin 148)) h (basisElt (reps rK73) (charOfVec2 rK73 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK73 e (h : Coordinate 2) T73_46_2 i :=
  species_entry_eq_sum rK73 ⟨46, by decide⟩ e heK h T73_46_2 hfix73_46_2 hinj73_46_2 hcardT73_46_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨46, by decide⟩) (reps rK73) (T73_46_2 i) (hfix73_46_2 i) h)

/-! ### Cell (73, 51) twin -/

def T73_51_2 : Fin 5 → Coordinate 2 := fun i => T73_51list.getD i.val (0,0,0,0,0)

theorem hfix73_51_2 : ∀ i, ((T73_51_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK73)
    ∈ fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK73) :=
  repsFix_of_siftB2 rK73 ⟨51, by decide⟩ T73_51_2 (by decide)

theorem hinj73_51_2 : Function.Injective
    (fun i => ((T73_51_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK73)) :=
  repsInj_of_reduceAux2 rK73 T73_51_2 (by decide)

theorem hcardT73_51_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK73)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK73 ⟨51, by decide⟩ R73_2 hpxR73_2 hcardq73_2 (by decide)).symm

/-- **Cell (73, 51) twin (q=2).** -/
theorem cell73_51_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK73) e = true)
    (h : ↥(reps (⟨51, by decide⟩ : Fin 148))) :
    species (reps (⟨51, by decide⟩ : Fin 148)) h (basisElt (reps rK73) (charOfVec2 rK73 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK73 e (h : Coordinate 2) T73_51_2 i :=
  species_entry_eq_sum rK73 ⟨51, by decide⟩ e heK h T73_51_2 hfix73_51_2 hinj73_51_2 hcardT73_51_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨51, by decide⟩) (reps rK73) (T73_51_2 i) (hfix73_51_2 i) h)

/-! ### Cell (73, 73) twin -/

def T73_73_2 : Fin 5 → Coordinate 2 := fun i => T73_73list.getD i.val (0,0,0,0,0)

theorem hfix73_73_2 : ∀ i, ((T73_73_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK73)
    ∈ fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK73) :=
  repsFix_of_siftB2 rK73 ⟨73, by decide⟩ T73_73_2 (by decide)

theorem hinj73_73_2 : Function.Injective
    (fun i => ((T73_73_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK73)) :=
  repsInj_of_reduceAux2 rK73 T73_73_2 (by decide)

theorem hcardT73_73_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK73)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK73 ⟨73, by decide⟩ R73_2 hpxR73_2 hcardq73_2 (by decide)).symm

/-- **Cell (73, 73) twin (q=2).** -/
theorem cell73_73_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK73) e = true)
    (h : ↥(reps (⟨73, by decide⟩ : Fin 148))) :
    species (reps (⟨73, by decide⟩ : Fin 148)) h (basisElt (reps rK73) (charOfVec2 rK73 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK73 e (h : Coordinate 2) T73_73_2 i :=
  species_entry_eq_sum rK73 ⟨73, by decide⟩ e heK h T73_73_2 hfix73_73_2 hinj73_73_2 hcardT73_73_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨73, by decide⟩) (reps rK73) (T73_73_2 i) (hfix73_73_2 i) h)

end Q2

/-! # K-class rK = 74  (|G/K| = 25) -/

def rK74 : Fin 148 := ⟨74, by decide⟩

def R74list : List Coordinates := [(0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0)]
def R74 : Fin 25 → Coordinate 1 := fun i => R74list.getD i.val (0,0,0,0,0)

theorem hpxR74 : Function.Injective (fun i => reduceAux 1 (basisAt rK74) (R74 i)) := by decide
theorem hcardq74 : Nat.card (Coordinate 1 ⧸ reps rK74) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (74, 0): |T| = 25 -/

def T74_0list : List Coordinates := [(0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0)]
def T74_0 : Fin 25 → Coordinate 1 := fun i => T74_0list.getD i.val (0,0,0,0,0)

theorem hfix74_0 : ∀ i, ((T74_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK74)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74) :=
  repsFix_of_siftB rK74 ⟨0, by decide⟩ T74_0 (by decide)

theorem hinj74_0 : Function.Injective
    (fun i => ((T74_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK74)) :=
  repsInj_of_reduceAux rK74 T74_0 (by decide)

theorem hcardT74_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK74 ⟨0, by decide⟩ R74 hpxR74 hcardq74 (by decide)).symm

/-- **Cell (74, 0).** -/
theorem cell74_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK74) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK74) (charOfVec rK74 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK74 e (h : Coordinate 1) T74_0 i :=
  species_entry_eq_sum rK74 ⟨0, by decide⟩ e heK h T74_0 hfix74_0 hinj74_0 hcardT74_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK74) (T74_0 i) (hfix74_0 i) h)

/-! ## Cell (74, 8): |T| = 25 -/

def T74_8list : List Coordinates := [(0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0)]
def T74_8 : Fin 25 → Coordinate 1 := fun i => T74_8list.getD i.val (0,0,0,0,0)

theorem hfix74_8 : ∀ i, ((T74_8 i : Coordinate 1) : Coordinate 1 ⧸ reps rK74)
    ∈ fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74) :=
  repsFix_of_siftB rK74 ⟨8, by decide⟩ T74_8 (by decide)

theorem hinj74_8 : Function.Injective
    (fun i => ((T74_8 i : Coordinate 1) : Coordinate 1 ⧸ reps rK74)) :=
  repsInj_of_reduceAux rK74 T74_8 (by decide)

theorem hcardT74_8 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK74 ⟨8, by decide⟩ R74 hpxR74 hcardq74 (by decide)).symm

/-- **Cell (74, 8).** -/
theorem cell74_8 (e : List (ZMod 25)) (heK : charOK (basisAt rK74) e = true)
    (h : ↥(reps (⟨8, by decide⟩ : Fin 148))) :
    species (reps (⟨8, by decide⟩ : Fin 148)) h (basisElt (reps rK74) (charOfVec rK74 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK74 e (h : Coordinate 1) T74_8 i :=
  species_entry_eq_sum rK74 ⟨8, by decide⟩ e heK h T74_8 hfix74_8 hinj74_8 hcardT74_8
    (fun i => conj_mem_of_fixedPoints (reps ⟨8, by decide⟩) (reps rK74) (T74_8 i) (hfix74_8 i) h)

/-! ## Cell (74, 12): |T| = 25 -/

def T74_12list : List Coordinates := [(0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0)]
def T74_12 : Fin 25 → Coordinate 1 := fun i => T74_12list.getD i.val (0,0,0,0,0)

theorem hfix74_12 : ∀ i, ((T74_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK74)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74) :=
  repsFix_of_siftB rK74 ⟨12, by decide⟩ T74_12 (by decide)

theorem hinj74_12 : Function.Injective
    (fun i => ((T74_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK74)) :=
  repsInj_of_reduceAux rK74 T74_12 (by decide)

theorem hcardT74_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK74 ⟨12, by decide⟩ R74 hpxR74 hcardq74 (by decide)).symm

/-- **Cell (74, 12).** -/
theorem cell74_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK74) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK74) (charOfVec rK74 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK74 e (h : Coordinate 1) T74_12 i :=
  species_entry_eq_sum rK74 ⟨12, by decide⟩ e heK h T74_12 hfix74_12 hinj74_12 hcardT74_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK74) (T74_12 i) (hfix74_12 i) h)

/-! ## Cell (74, 26): |T| = 25 -/

def T74_26list : List Coordinates := [(0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0)]
def T74_26 : Fin 25 → Coordinate 1 := fun i => T74_26list.getD i.val (0,0,0,0,0)

theorem hfix74_26 : ∀ i, ((T74_26 i : Coordinate 1) : Coordinate 1 ⧸ reps rK74)
    ∈ fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74) :=
  repsFix_of_siftB rK74 ⟨26, by decide⟩ T74_26 (by decide)

theorem hinj74_26 : Function.Injective
    (fun i => ((T74_26 i : Coordinate 1) : Coordinate 1 ⧸ reps rK74)) :=
  repsInj_of_reduceAux rK74 T74_26 (by decide)

theorem hcardT74_26 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK74 ⟨26, by decide⟩ R74 hpxR74 hcardq74 (by decide)).symm

/-- **Cell (74, 26).** -/
theorem cell74_26 (e : List (ZMod 25)) (heK : charOK (basisAt rK74) e = true)
    (h : ↥(reps (⟨26, by decide⟩ : Fin 148))) :
    species (reps (⟨26, by decide⟩ : Fin 148)) h (basisElt (reps rK74) (charOfVec rK74 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK74 e (h : Coordinate 1) T74_26 i :=
  species_entry_eq_sum rK74 ⟨26, by decide⟩ e heK h T74_26 hfix74_26 hinj74_26 hcardT74_26
    (fun i => conj_mem_of_fixedPoints (reps ⟨26, by decide⟩) (reps rK74) (T74_26 i) (hfix74_26 i) h)

/-! ## Cell (74, 31): |T| = 5 -/

def T74_31list : List Coordinates := [(0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0)]
def T74_31 : Fin 5 → Coordinate 1 := fun i => T74_31list.getD i.val (0,0,0,0,0)

theorem hfix74_31 : ∀ i, ((T74_31 i : Coordinate 1) : Coordinate 1 ⧸ reps rK74)
    ∈ fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74) :=
  repsFix_of_siftB rK74 ⟨31, by decide⟩ T74_31 (by decide)

theorem hinj74_31 : Function.Injective
    (fun i => ((T74_31 i : Coordinate 1) : Coordinate 1 ⧸ reps rK74)) :=
  repsInj_of_reduceAux rK74 T74_31 (by decide)

theorem hcardT74_31 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK74 ⟨31, by decide⟩ R74 hpxR74 hcardq74 (by decide)).symm

/-- **Cell (74, 31).** -/
theorem cell74_31 (e : List (ZMod 25)) (heK : charOK (basisAt rK74) e = true)
    (h : ↥(reps (⟨31, by decide⟩ : Fin 148))) :
    species (reps (⟨31, by decide⟩ : Fin 148)) h (basisElt (reps rK74) (charOfVec rK74 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK74 e (h : Coordinate 1) T74_31 i :=
  species_entry_eq_sum rK74 ⟨31, by decide⟩ e heK h T74_31 hfix74_31 hinj74_31 hcardT74_31
    (fun i => conj_mem_of_fixedPoints (reps ⟨31, by decide⟩) (reps rK74) (T74_31 i) (hfix74_31 i) h)

/-! ## Cell (74, 36): |T| = 5 -/

def T74_36list : List Coordinates := [(0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0)]
def T74_36 : Fin 5 → Coordinate 1 := fun i => T74_36list.getD i.val (0,0,0,0,0)

theorem hfix74_36 : ∀ i, ((T74_36 i : Coordinate 1) : Coordinate 1 ⧸ reps rK74)
    ∈ fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74) :=
  repsFix_of_siftB rK74 ⟨36, by decide⟩ T74_36 (by decide)

theorem hinj74_36 : Function.Injective
    (fun i => ((T74_36 i : Coordinate 1) : Coordinate 1 ⧸ reps rK74)) :=
  repsInj_of_reduceAux rK74 T74_36 (by decide)

theorem hcardT74_36 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK74 ⟨36, by decide⟩ R74 hpxR74 hcardq74 (by decide)).symm

/-- **Cell (74, 36).** -/
theorem cell74_36 (e : List (ZMod 25)) (heK : charOK (basisAt rK74) e = true)
    (h : ↥(reps (⟨36, by decide⟩ : Fin 148))) :
    species (reps (⟨36, by decide⟩ : Fin 148)) h (basisElt (reps rK74) (charOfVec rK74 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK74 e (h : Coordinate 1) T74_36 i :=
  species_entry_eq_sum rK74 ⟨36, by decide⟩ e heK h T74_36 hfix74_36 hinj74_36 hcardT74_36
    (fun i => conj_mem_of_fixedPoints (reps ⟨36, by decide⟩) (reps rK74) (T74_36 i) (hfix74_36 i) h)

/-! ## Cell (74, 41): |T| = 5 -/

def T74_41list : List Coordinates := [(0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0)]
def T74_41 : Fin 5 → Coordinate 1 := fun i => T74_41list.getD i.val (0,0,0,0,0)

theorem hfix74_41 : ∀ i, ((T74_41 i : Coordinate 1) : Coordinate 1 ⧸ reps rK74)
    ∈ fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74) :=
  repsFix_of_siftB rK74 ⟨41, by decide⟩ T74_41 (by decide)

theorem hinj74_41 : Function.Injective
    (fun i => ((T74_41 i : Coordinate 1) : Coordinate 1 ⧸ reps rK74)) :=
  repsInj_of_reduceAux rK74 T74_41 (by decide)

theorem hcardT74_41 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK74 ⟨41, by decide⟩ R74 hpxR74 hcardq74 (by decide)).symm

/-- **Cell (74, 41).** -/
theorem cell74_41 (e : List (ZMod 25)) (heK : charOK (basisAt rK74) e = true)
    (h : ↥(reps (⟨41, by decide⟩ : Fin 148))) :
    species (reps (⟨41, by decide⟩ : Fin 148)) h (basisElt (reps rK74) (charOfVec rK74 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK74 e (h : Coordinate 1) T74_41 i :=
  species_entry_eq_sum rK74 ⟨41, by decide⟩ e heK h T74_41 hfix74_41 hinj74_41 hcardT74_41
    (fun i => conj_mem_of_fixedPoints (reps ⟨41, by decide⟩) (reps rK74) (T74_41 i) (hfix74_41 i) h)

/-! ## Cell (74, 46): |T| = 5 -/

def T74_46list : List Coordinates := [(0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0)]
def T74_46 : Fin 5 → Coordinate 1 := fun i => T74_46list.getD i.val (0,0,0,0,0)

theorem hfix74_46 : ∀ i, ((T74_46 i : Coordinate 1) : Coordinate 1 ⧸ reps rK74)
    ∈ fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74) :=
  repsFix_of_siftB rK74 ⟨46, by decide⟩ T74_46 (by decide)

theorem hinj74_46 : Function.Injective
    (fun i => ((T74_46 i : Coordinate 1) : Coordinate 1 ⧸ reps rK74)) :=
  repsInj_of_reduceAux rK74 T74_46 (by decide)

theorem hcardT74_46 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK74 ⟨46, by decide⟩ R74 hpxR74 hcardq74 (by decide)).symm

/-- **Cell (74, 46).** -/
theorem cell74_46 (e : List (ZMod 25)) (heK : charOK (basisAt rK74) e = true)
    (h : ↥(reps (⟨46, by decide⟩ : Fin 148))) :
    species (reps (⟨46, by decide⟩ : Fin 148)) h (basisElt (reps rK74) (charOfVec rK74 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK74 e (h : Coordinate 1) T74_46 i :=
  species_entry_eq_sum rK74 ⟨46, by decide⟩ e heK h T74_46 hfix74_46 hinj74_46 hcardT74_46
    (fun i => conj_mem_of_fixedPoints (reps ⟨46, by decide⟩) (reps rK74) (T74_46 i) (hfix74_46 i) h)

/-! ## Cell (74, 51): |T| = 5 -/

def T74_51list : List Coordinates := [(0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0)]
def T74_51 : Fin 5 → Coordinate 1 := fun i => T74_51list.getD i.val (0,0,0,0,0)

theorem hfix74_51 : ∀ i, ((T74_51 i : Coordinate 1) : Coordinate 1 ⧸ reps rK74)
    ∈ fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74) :=
  repsFix_of_siftB rK74 ⟨51, by decide⟩ T74_51 (by decide)

theorem hinj74_51 : Function.Injective
    (fun i => ((T74_51 i : Coordinate 1) : Coordinate 1 ⧸ reps rK74)) :=
  repsInj_of_reduceAux rK74 T74_51 (by decide)

theorem hcardT74_51 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK74 ⟨51, by decide⟩ R74 hpxR74 hcardq74 (by decide)).symm

/-- **Cell (74, 51).** -/
theorem cell74_51 (e : List (ZMod 25)) (heK : charOK (basisAt rK74) e = true)
    (h : ↥(reps (⟨51, by decide⟩ : Fin 148))) :
    species (reps (⟨51, by decide⟩ : Fin 148)) h (basisElt (reps rK74) (charOfVec rK74 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK74 e (h : Coordinate 1) T74_51 i :=
  species_entry_eq_sum rK74 ⟨51, by decide⟩ e heK h T74_51 hfix74_51 hinj74_51 hcardT74_51
    (fun i => conj_mem_of_fixedPoints (reps ⟨51, by decide⟩) (reps rK74) (T74_51 i) (hfix74_51 i) h)

/-! ## Cell (74, 74): |T| = 5 -/

def T74_74list : List Coordinates := [(0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0)]
def T74_74 : Fin 5 → Coordinate 1 := fun i => T74_74list.getD i.val (0,0,0,0,0)

theorem hfix74_74 : ∀ i, ((T74_74 i : Coordinate 1) : Coordinate 1 ⧸ reps rK74)
    ∈ fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74) :=
  repsFix_of_siftB rK74 ⟨74, by decide⟩ T74_74 (by decide)

theorem hinj74_74 : Function.Injective
    (fun i => ((T74_74 i : Coordinate 1) : Coordinate 1 ⧸ reps rK74)) :=
  repsInj_of_reduceAux rK74 T74_74 (by decide)

theorem hcardT74_74 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK74 ⟨74, by decide⟩ R74 hpxR74 hcardq74 (by decide)).symm

/-- **Cell (74, 74).** -/
theorem cell74_74 (e : List (ZMod 25)) (heK : charOK (basisAt rK74) e = true)
    (h : ↥(reps (⟨74, by decide⟩ : Fin 148))) :
    species (reps (⟨74, by decide⟩ : Fin 148)) h (basisElt (reps rK74) (charOfVec rK74 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK74 e (h : Coordinate 1) T74_74 i :=
  species_entry_eq_sum rK74 ⟨74, by decide⟩ e heK h T74_74 hfix74_74 hinj74_74 hcardT74_74
    (fun i => conj_mem_of_fixedPoints (reps ⟨74, by decide⟩) (reps rK74) (T74_74 i) (hfix74_74 i) h)

namespace Q2

def R74_2 : Fin 25 → Coordinate 2 := fun i => R74list.getD i.val (0,0,0,0,0)
theorem hpxR74_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK74) (R74_2 i)) := by decide
theorem hcardq74_2 : Nat.card (Coordinate 2 ⧸ reps rK74) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (74, 0) twin -/

def T74_0_2 : Fin 25 → Coordinate 2 := fun i => T74_0list.getD i.val (0,0,0,0,0)

theorem hfix74_0_2 : ∀ i, ((T74_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK74)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK74) :=
  repsFix_of_siftB2 rK74 ⟨0, by decide⟩ T74_0_2 (by decide)

theorem hinj74_0_2 : Function.Injective
    (fun i => ((T74_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK74)) :=
  repsInj_of_reduceAux2 rK74 T74_0_2 (by decide)

theorem hcardT74_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK74)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK74 ⟨0, by decide⟩ R74_2 hpxR74_2 hcardq74_2 (by decide)).symm

/-- **Cell (74, 0) twin (q=2).** -/
theorem cell74_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK74) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK74) (charOfVec2 rK74 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK74 e (h : Coordinate 2) T74_0_2 i :=
  species_entry_eq_sum rK74 ⟨0, by decide⟩ e heK h T74_0_2 hfix74_0_2 hinj74_0_2 hcardT74_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK74) (T74_0_2 i) (hfix74_0_2 i) h)

/-! ### Cell (74, 8) twin -/

def T74_8_2 : Fin 25 → Coordinate 2 := fun i => T74_8list.getD i.val (0,0,0,0,0)

theorem hfix74_8_2 : ∀ i, ((T74_8_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK74)
    ∈ fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK74) :=
  repsFix_of_siftB2 rK74 ⟨8, by decide⟩ T74_8_2 (by decide)

theorem hinj74_8_2 : Function.Injective
    (fun i => ((T74_8_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK74)) :=
  repsInj_of_reduceAux2 rK74 T74_8_2 (by decide)

theorem hcardT74_8_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK74)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK74 ⟨8, by decide⟩ R74_2 hpxR74_2 hcardq74_2 (by decide)).symm

/-- **Cell (74, 8) twin (q=2).** -/
theorem cell74_8_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK74) e = true)
    (h : ↥(reps (⟨8, by decide⟩ : Fin 148))) :
    species (reps (⟨8, by decide⟩ : Fin 148)) h (basisElt (reps rK74) (charOfVec2 rK74 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK74 e (h : Coordinate 2) T74_8_2 i :=
  species_entry_eq_sum rK74 ⟨8, by decide⟩ e heK h T74_8_2 hfix74_8_2 hinj74_8_2 hcardT74_8_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨8, by decide⟩) (reps rK74) (T74_8_2 i) (hfix74_8_2 i) h)

/-! ### Cell (74, 12) twin -/

def T74_12_2 : Fin 25 → Coordinate 2 := fun i => T74_12list.getD i.val (0,0,0,0,0)

theorem hfix74_12_2 : ∀ i, ((T74_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK74)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK74) :=
  repsFix_of_siftB2 rK74 ⟨12, by decide⟩ T74_12_2 (by decide)

theorem hinj74_12_2 : Function.Injective
    (fun i => ((T74_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK74)) :=
  repsInj_of_reduceAux2 rK74 T74_12_2 (by decide)

theorem hcardT74_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK74)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK74 ⟨12, by decide⟩ R74_2 hpxR74_2 hcardq74_2 (by decide)).symm

/-- **Cell (74, 12) twin (q=2).** -/
theorem cell74_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK74) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK74) (charOfVec2 rK74 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK74 e (h : Coordinate 2) T74_12_2 i :=
  species_entry_eq_sum rK74 ⟨12, by decide⟩ e heK h T74_12_2 hfix74_12_2 hinj74_12_2 hcardT74_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK74) (T74_12_2 i) (hfix74_12_2 i) h)

/-! ### Cell (74, 26) twin -/

def T74_26_2 : Fin 25 → Coordinate 2 := fun i => T74_26list.getD i.val (0,0,0,0,0)

theorem hfix74_26_2 : ∀ i, ((T74_26_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK74)
    ∈ fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK74) :=
  repsFix_of_siftB2 rK74 ⟨26, by decide⟩ T74_26_2 (by decide)

theorem hinj74_26_2 : Function.Injective
    (fun i => ((T74_26_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK74)) :=
  repsInj_of_reduceAux2 rK74 T74_26_2 (by decide)

theorem hcardT74_26_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK74)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK74 ⟨26, by decide⟩ R74_2 hpxR74_2 hcardq74_2 (by decide)).symm

/-- **Cell (74, 26) twin (q=2).** -/
theorem cell74_26_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK74) e = true)
    (h : ↥(reps (⟨26, by decide⟩ : Fin 148))) :
    species (reps (⟨26, by decide⟩ : Fin 148)) h (basisElt (reps rK74) (charOfVec2 rK74 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK74 e (h : Coordinate 2) T74_26_2 i :=
  species_entry_eq_sum rK74 ⟨26, by decide⟩ e heK h T74_26_2 hfix74_26_2 hinj74_26_2 hcardT74_26_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨26, by decide⟩) (reps rK74) (T74_26_2 i) (hfix74_26_2 i) h)

/-! ### Cell (74, 31) twin -/

def T74_31_2 : Fin 5 → Coordinate 2 := fun i => T74_31list.getD i.val (0,0,0,0,0)

theorem hfix74_31_2 : ∀ i, ((T74_31_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK74)
    ∈ fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK74) :=
  repsFix_of_siftB2 rK74 ⟨31, by decide⟩ T74_31_2 (by decide)

theorem hinj74_31_2 : Function.Injective
    (fun i => ((T74_31_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK74)) :=
  repsInj_of_reduceAux2 rK74 T74_31_2 (by decide)

theorem hcardT74_31_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK74)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK74 ⟨31, by decide⟩ R74_2 hpxR74_2 hcardq74_2 (by decide)).symm

/-- **Cell (74, 31) twin (q=2).** -/
theorem cell74_31_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK74) e = true)
    (h : ↥(reps (⟨31, by decide⟩ : Fin 148))) :
    species (reps (⟨31, by decide⟩ : Fin 148)) h (basisElt (reps rK74) (charOfVec2 rK74 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK74 e (h : Coordinate 2) T74_31_2 i :=
  species_entry_eq_sum rK74 ⟨31, by decide⟩ e heK h T74_31_2 hfix74_31_2 hinj74_31_2 hcardT74_31_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨31, by decide⟩) (reps rK74) (T74_31_2 i) (hfix74_31_2 i) h)

/-! ### Cell (74, 36) twin -/

def T74_36_2 : Fin 5 → Coordinate 2 := fun i => T74_36list.getD i.val (0,0,0,0,0)

theorem hfix74_36_2 : ∀ i, ((T74_36_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK74)
    ∈ fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK74) :=
  repsFix_of_siftB2 rK74 ⟨36, by decide⟩ T74_36_2 (by decide)

theorem hinj74_36_2 : Function.Injective
    (fun i => ((T74_36_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK74)) :=
  repsInj_of_reduceAux2 rK74 T74_36_2 (by decide)

theorem hcardT74_36_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK74)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK74 ⟨36, by decide⟩ R74_2 hpxR74_2 hcardq74_2 (by decide)).symm

/-- **Cell (74, 36) twin (q=2).** -/
theorem cell74_36_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK74) e = true)
    (h : ↥(reps (⟨36, by decide⟩ : Fin 148))) :
    species (reps (⟨36, by decide⟩ : Fin 148)) h (basisElt (reps rK74) (charOfVec2 rK74 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK74 e (h : Coordinate 2) T74_36_2 i :=
  species_entry_eq_sum rK74 ⟨36, by decide⟩ e heK h T74_36_2 hfix74_36_2 hinj74_36_2 hcardT74_36_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨36, by decide⟩) (reps rK74) (T74_36_2 i) (hfix74_36_2 i) h)

/-! ### Cell (74, 41) twin -/

def T74_41_2 : Fin 5 → Coordinate 2 := fun i => T74_41list.getD i.val (0,0,0,0,0)

theorem hfix74_41_2 : ∀ i, ((T74_41_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK74)
    ∈ fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK74) :=
  repsFix_of_siftB2 rK74 ⟨41, by decide⟩ T74_41_2 (by decide)

theorem hinj74_41_2 : Function.Injective
    (fun i => ((T74_41_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK74)) :=
  repsInj_of_reduceAux2 rK74 T74_41_2 (by decide)

theorem hcardT74_41_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK74)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK74 ⟨41, by decide⟩ R74_2 hpxR74_2 hcardq74_2 (by decide)).symm

/-- **Cell (74, 41) twin (q=2).** -/
theorem cell74_41_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK74) e = true)
    (h : ↥(reps (⟨41, by decide⟩ : Fin 148))) :
    species (reps (⟨41, by decide⟩ : Fin 148)) h (basisElt (reps rK74) (charOfVec2 rK74 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK74 e (h : Coordinate 2) T74_41_2 i :=
  species_entry_eq_sum rK74 ⟨41, by decide⟩ e heK h T74_41_2 hfix74_41_2 hinj74_41_2 hcardT74_41_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨41, by decide⟩) (reps rK74) (T74_41_2 i) (hfix74_41_2 i) h)

/-! ### Cell (74, 46) twin -/

def T74_46_2 : Fin 5 → Coordinate 2 := fun i => T74_46list.getD i.val (0,0,0,0,0)

theorem hfix74_46_2 : ∀ i, ((T74_46_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK74)
    ∈ fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK74) :=
  repsFix_of_siftB2 rK74 ⟨46, by decide⟩ T74_46_2 (by decide)

theorem hinj74_46_2 : Function.Injective
    (fun i => ((T74_46_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK74)) :=
  repsInj_of_reduceAux2 rK74 T74_46_2 (by decide)

theorem hcardT74_46_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK74)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK74 ⟨46, by decide⟩ R74_2 hpxR74_2 hcardq74_2 (by decide)).symm

/-- **Cell (74, 46) twin (q=2).** -/
theorem cell74_46_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK74) e = true)
    (h : ↥(reps (⟨46, by decide⟩ : Fin 148))) :
    species (reps (⟨46, by decide⟩ : Fin 148)) h (basisElt (reps rK74) (charOfVec2 rK74 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK74 e (h : Coordinate 2) T74_46_2 i :=
  species_entry_eq_sum rK74 ⟨46, by decide⟩ e heK h T74_46_2 hfix74_46_2 hinj74_46_2 hcardT74_46_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨46, by decide⟩) (reps rK74) (T74_46_2 i) (hfix74_46_2 i) h)

/-! ### Cell (74, 51) twin -/

def T74_51_2 : Fin 5 → Coordinate 2 := fun i => T74_51list.getD i.val (0,0,0,0,0)

theorem hfix74_51_2 : ∀ i, ((T74_51_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK74)
    ∈ fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK74) :=
  repsFix_of_siftB2 rK74 ⟨51, by decide⟩ T74_51_2 (by decide)

theorem hinj74_51_2 : Function.Injective
    (fun i => ((T74_51_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK74)) :=
  repsInj_of_reduceAux2 rK74 T74_51_2 (by decide)

theorem hcardT74_51_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK74)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK74 ⟨51, by decide⟩ R74_2 hpxR74_2 hcardq74_2 (by decide)).symm

/-- **Cell (74, 51) twin (q=2).** -/
theorem cell74_51_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK74) e = true)
    (h : ↥(reps (⟨51, by decide⟩ : Fin 148))) :
    species (reps (⟨51, by decide⟩ : Fin 148)) h (basisElt (reps rK74) (charOfVec2 rK74 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK74 e (h : Coordinate 2) T74_51_2 i :=
  species_entry_eq_sum rK74 ⟨51, by decide⟩ e heK h T74_51_2 hfix74_51_2 hinj74_51_2 hcardT74_51_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨51, by decide⟩) (reps rK74) (T74_51_2 i) (hfix74_51_2 i) h)

/-! ### Cell (74, 74) twin -/

def T74_74_2 : Fin 5 → Coordinate 2 := fun i => T74_74list.getD i.val (0,0,0,0,0)

theorem hfix74_74_2 : ∀ i, ((T74_74_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK74)
    ∈ fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK74) :=
  repsFix_of_siftB2 rK74 ⟨74, by decide⟩ T74_74_2 (by decide)

theorem hinj74_74_2 : Function.Injective
    (fun i => ((T74_74_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK74)) :=
  repsInj_of_reduceAux2 rK74 T74_74_2 (by decide)

theorem hcardT74_74_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK74)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK74 ⟨74, by decide⟩ R74_2 hpxR74_2 hcardq74_2 (by decide)).symm

/-- **Cell (74, 74) twin (q=2).** -/
theorem cell74_74_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK74) e = true)
    (h : ↥(reps (⟨74, by decide⟩ : Fin 148))) :
    species (reps (⟨74, by decide⟩ : Fin 148)) h (basisElt (reps rK74) (charOfVec2 rK74 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK74 e (h : Coordinate 2) T74_74_2 i :=
  species_entry_eq_sum rK74 ⟨74, by decide⟩ e heK h T74_74_2 hfix74_74_2 hinj74_74_2 hcardT74_74_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨74, by decide⟩) (reps rK74) (T74_74_2 i) (hfix74_74_2 i) h)

end Q2

end LeanDring.P5Presentation
