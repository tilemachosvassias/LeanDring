/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, K-strata data (5^3 stratum, rK 75-79): certified per-cell species-entry instantiations, both
twins.

Covers K-classes 75, 76, 77, 78, 79 (order-5^3 K, |R|=25).  For each nonzero `H`-column
(`(G/K)^H ≠ ∅`), the full coset transversal `R75..` and each `H`-fixed
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

/-! # K-class rK = 75  (|G/K| = 25) -/

def rK75 : Fin 148 := ⟨75, by decide⟩

def R75list : List Coordinates := [(0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0)]
def R75 : Fin 25 → Coordinate 1 := fun i => R75list.getD i.val (0,0,0,0,0)

theorem hpxR75 : Function.Injective (fun i => reduceAux 1 (basisAt rK75) (R75 i)) := by decide
theorem hcardq75 : Nat.card (Coordinate 1 ⧸ reps rK75) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (75, 0): |T| = 25 -/

def T75_0list : List Coordinates := [(0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0)]
def T75_0 : Fin 25 → Coordinate 1 := fun i => T75_0list.getD i.val (0,0,0,0,0)

theorem hfix75_0 : ∀ i, ((T75_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK75)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75) :=
  repsFix_of_siftB rK75 ⟨0, by decide⟩ T75_0 (by decide)

theorem hinj75_0 : Function.Injective
    (fun i => ((T75_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK75)) :=
  repsInj_of_reduceAux rK75 T75_0 (by decide)

theorem hcardT75_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK75 ⟨0, by decide⟩ R75 hpxR75 hcardq75 (by decide)).symm

/-- **Cell (75, 0).** -/
theorem cell75_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK75) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK75) (charOfVec rK75 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK75 e (h : Coordinate 1) T75_0 i :=
  species_entry_eq_sum rK75 ⟨0, by decide⟩ e heK h T75_0 hfix75_0 hinj75_0 hcardT75_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK75) (T75_0 i) (hfix75_0 i) h)

/-! ## Cell (75, 9): |T| = 25 -/

def T75_9list : List Coordinates := [(0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0)]
def T75_9 : Fin 25 → Coordinate 1 := fun i => T75_9list.getD i.val (0,0,0,0,0)

theorem hfix75_9 : ∀ i, ((T75_9 i : Coordinate 1) : Coordinate 1 ⧸ reps rK75)
    ∈ fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75) :=
  repsFix_of_siftB rK75 ⟨9, by decide⟩ T75_9 (by decide)

theorem hinj75_9 : Function.Injective
    (fun i => ((T75_9 i : Coordinate 1) : Coordinate 1 ⧸ reps rK75)) :=
  repsInj_of_reduceAux rK75 T75_9 (by decide)

theorem hcardT75_9 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK75 ⟨9, by decide⟩ R75 hpxR75 hcardq75 (by decide)).symm

/-- **Cell (75, 9).** -/
theorem cell75_9 (e : List (ZMod 25)) (heK : charOK (basisAt rK75) e = true)
    (h : ↥(reps (⟨9, by decide⟩ : Fin 148))) :
    species (reps (⟨9, by decide⟩ : Fin 148)) h (basisElt (reps rK75) (charOfVec rK75 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK75 e (h : Coordinate 1) T75_9 i :=
  species_entry_eq_sum rK75 ⟨9, by decide⟩ e heK h T75_9 hfix75_9 hinj75_9 hcardT75_9
    (fun i => conj_mem_of_fixedPoints (reps ⟨9, by decide⟩) (reps rK75) (T75_9 i) (hfix75_9 i) h)

/-! ## Cell (75, 12): |T| = 25 -/

def T75_12list : List Coordinates := [(0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0)]
def T75_12 : Fin 25 → Coordinate 1 := fun i => T75_12list.getD i.val (0,0,0,0,0)

theorem hfix75_12 : ∀ i, ((T75_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK75)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75) :=
  repsFix_of_siftB rK75 ⟨12, by decide⟩ T75_12 (by decide)

theorem hinj75_12 : Function.Injective
    (fun i => ((T75_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK75)) :=
  repsInj_of_reduceAux rK75 T75_12 (by decide)

theorem hcardT75_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK75 ⟨12, by decide⟩ R75 hpxR75 hcardq75 (by decide)).symm

/-- **Cell (75, 12).** -/
theorem cell75_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK75) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK75) (charOfVec rK75 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK75 e (h : Coordinate 1) T75_12 i :=
  species_entry_eq_sum rK75 ⟨12, by decide⟩ e heK h T75_12 hfix75_12 hinj75_12 hcardT75_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK75) (T75_12 i) (hfix75_12 i) h)

/-! ## Cell (75, 27): |T| = 25 -/

def T75_27list : List Coordinates := [(0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0)]
def T75_27 : Fin 25 → Coordinate 1 := fun i => T75_27list.getD i.val (0,0,0,0,0)

theorem hfix75_27 : ∀ i, ((T75_27 i : Coordinate 1) : Coordinate 1 ⧸ reps rK75)
    ∈ fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75) :=
  repsFix_of_siftB rK75 ⟨27, by decide⟩ T75_27 (by decide)

theorem hinj75_27 : Function.Injective
    (fun i => ((T75_27 i : Coordinate 1) : Coordinate 1 ⧸ reps rK75)) :=
  repsInj_of_reduceAux rK75 T75_27 (by decide)

theorem hcardT75_27 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK75 ⟨27, by decide⟩ R75 hpxR75 hcardq75 (by decide)).symm

/-- **Cell (75, 27).** -/
theorem cell75_27 (e : List (ZMod 25)) (heK : charOK (basisAt rK75) e = true)
    (h : ↥(reps (⟨27, by decide⟩ : Fin 148))) :
    species (reps (⟨27, by decide⟩ : Fin 148)) h (basisElt (reps rK75) (charOfVec rK75 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK75 e (h : Coordinate 1) T75_27 i :=
  species_entry_eq_sum rK75 ⟨27, by decide⟩ e heK h T75_27 hfix75_27 hinj75_27 hcardT75_27
    (fun i => conj_mem_of_fixedPoints (reps ⟨27, by decide⟩) (reps rK75) (T75_27 i) (hfix75_27 i) h)

/-! ## Cell (75, 32): |T| = 5 -/

def T75_32list : List Coordinates := [(0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0)]
def T75_32 : Fin 5 → Coordinate 1 := fun i => T75_32list.getD i.val (0,0,0,0,0)

theorem hfix75_32 : ∀ i, ((T75_32 i : Coordinate 1) : Coordinate 1 ⧸ reps rK75)
    ∈ fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75) :=
  repsFix_of_siftB rK75 ⟨32, by decide⟩ T75_32 (by decide)

theorem hinj75_32 : Function.Injective
    (fun i => ((T75_32 i : Coordinate 1) : Coordinate 1 ⧸ reps rK75)) :=
  repsInj_of_reduceAux rK75 T75_32 (by decide)

theorem hcardT75_32 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK75 ⟨32, by decide⟩ R75 hpxR75 hcardq75 (by decide)).symm

/-- **Cell (75, 32).** -/
theorem cell75_32 (e : List (ZMod 25)) (heK : charOK (basisAt rK75) e = true)
    (h : ↥(reps (⟨32, by decide⟩ : Fin 148))) :
    species (reps (⟨32, by decide⟩ : Fin 148)) h (basisElt (reps rK75) (charOfVec rK75 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK75 e (h : Coordinate 1) T75_32 i :=
  species_entry_eq_sum rK75 ⟨32, by decide⟩ e heK h T75_32 hfix75_32 hinj75_32 hcardT75_32
    (fun i => conj_mem_of_fixedPoints (reps ⟨32, by decide⟩) (reps rK75) (T75_32 i) (hfix75_32 i) h)

/-! ## Cell (75, 37): |T| = 5 -/

def T75_37list : List Coordinates := [(0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0)]
def T75_37 : Fin 5 → Coordinate 1 := fun i => T75_37list.getD i.val (0,0,0,0,0)

theorem hfix75_37 : ∀ i, ((T75_37 i : Coordinate 1) : Coordinate 1 ⧸ reps rK75)
    ∈ fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75) :=
  repsFix_of_siftB rK75 ⟨37, by decide⟩ T75_37 (by decide)

theorem hinj75_37 : Function.Injective
    (fun i => ((T75_37 i : Coordinate 1) : Coordinate 1 ⧸ reps rK75)) :=
  repsInj_of_reduceAux rK75 T75_37 (by decide)

theorem hcardT75_37 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK75 ⟨37, by decide⟩ R75 hpxR75 hcardq75 (by decide)).symm

/-- **Cell (75, 37).** -/
theorem cell75_37 (e : List (ZMod 25)) (heK : charOK (basisAt rK75) e = true)
    (h : ↥(reps (⟨37, by decide⟩ : Fin 148))) :
    species (reps (⟨37, by decide⟩ : Fin 148)) h (basisElt (reps rK75) (charOfVec rK75 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK75 e (h : Coordinate 1) T75_37 i :=
  species_entry_eq_sum rK75 ⟨37, by decide⟩ e heK h T75_37 hfix75_37 hinj75_37 hcardT75_37
    (fun i => conj_mem_of_fixedPoints (reps ⟨37, by decide⟩) (reps rK75) (T75_37 i) (hfix75_37 i) h)

/-! ## Cell (75, 42): |T| = 5 -/

def T75_42list : List Coordinates := [(0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0)]
def T75_42 : Fin 5 → Coordinate 1 := fun i => T75_42list.getD i.val (0,0,0,0,0)

theorem hfix75_42 : ∀ i, ((T75_42 i : Coordinate 1) : Coordinate 1 ⧸ reps rK75)
    ∈ fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75) :=
  repsFix_of_siftB rK75 ⟨42, by decide⟩ T75_42 (by decide)

theorem hinj75_42 : Function.Injective
    (fun i => ((T75_42 i : Coordinate 1) : Coordinate 1 ⧸ reps rK75)) :=
  repsInj_of_reduceAux rK75 T75_42 (by decide)

theorem hcardT75_42 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK75 ⟨42, by decide⟩ R75 hpxR75 hcardq75 (by decide)).symm

/-- **Cell (75, 42).** -/
theorem cell75_42 (e : List (ZMod 25)) (heK : charOK (basisAt rK75) e = true)
    (h : ↥(reps (⟨42, by decide⟩ : Fin 148))) :
    species (reps (⟨42, by decide⟩ : Fin 148)) h (basisElt (reps rK75) (charOfVec rK75 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK75 e (h : Coordinate 1) T75_42 i :=
  species_entry_eq_sum rK75 ⟨42, by decide⟩ e heK h T75_42 hfix75_42 hinj75_42 hcardT75_42
    (fun i => conj_mem_of_fixedPoints (reps ⟨42, by decide⟩) (reps rK75) (T75_42 i) (hfix75_42 i) h)

/-! ## Cell (75, 47): |T| = 5 -/

def T75_47list : List Coordinates := [(0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0)]
def T75_47 : Fin 5 → Coordinate 1 := fun i => T75_47list.getD i.val (0,0,0,0,0)

theorem hfix75_47 : ∀ i, ((T75_47 i : Coordinate 1) : Coordinate 1 ⧸ reps rK75)
    ∈ fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75) :=
  repsFix_of_siftB rK75 ⟨47, by decide⟩ T75_47 (by decide)

theorem hinj75_47 : Function.Injective
    (fun i => ((T75_47 i : Coordinate 1) : Coordinate 1 ⧸ reps rK75)) :=
  repsInj_of_reduceAux rK75 T75_47 (by decide)

theorem hcardT75_47 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK75 ⟨47, by decide⟩ R75 hpxR75 hcardq75 (by decide)).symm

/-- **Cell (75, 47).** -/
theorem cell75_47 (e : List (ZMod 25)) (heK : charOK (basisAt rK75) e = true)
    (h : ↥(reps (⟨47, by decide⟩ : Fin 148))) :
    species (reps (⟨47, by decide⟩ : Fin 148)) h (basisElt (reps rK75) (charOfVec rK75 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK75 e (h : Coordinate 1) T75_47 i :=
  species_entry_eq_sum rK75 ⟨47, by decide⟩ e heK h T75_47 hfix75_47 hinj75_47 hcardT75_47
    (fun i => conj_mem_of_fixedPoints (reps ⟨47, by decide⟩) (reps rK75) (T75_47 i) (hfix75_47 i) h)

/-! ## Cell (75, 52): |T| = 5 -/

def T75_52list : List Coordinates := [(0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0)]
def T75_52 : Fin 5 → Coordinate 1 := fun i => T75_52list.getD i.val (0,0,0,0,0)

theorem hfix75_52 : ∀ i, ((T75_52 i : Coordinate 1) : Coordinate 1 ⧸ reps rK75)
    ∈ fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75) :=
  repsFix_of_siftB rK75 ⟨52, by decide⟩ T75_52 (by decide)

theorem hinj75_52 : Function.Injective
    (fun i => ((T75_52 i : Coordinate 1) : Coordinate 1 ⧸ reps rK75)) :=
  repsInj_of_reduceAux rK75 T75_52 (by decide)

theorem hcardT75_52 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK75 ⟨52, by decide⟩ R75 hpxR75 hcardq75 (by decide)).symm

/-- **Cell (75, 52).** -/
theorem cell75_52 (e : List (ZMod 25)) (heK : charOK (basisAt rK75) e = true)
    (h : ↥(reps (⟨52, by decide⟩ : Fin 148))) :
    species (reps (⟨52, by decide⟩ : Fin 148)) h (basisElt (reps rK75) (charOfVec rK75 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK75 e (h : Coordinate 1) T75_52 i :=
  species_entry_eq_sum rK75 ⟨52, by decide⟩ e heK h T75_52 hfix75_52 hinj75_52 hcardT75_52
    (fun i => conj_mem_of_fixedPoints (reps ⟨52, by decide⟩) (reps rK75) (T75_52 i) (hfix75_52 i) h)

/-! ## Cell (75, 75): |T| = 5 -/

def T75_75list : List Coordinates := [(0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0)]
def T75_75 : Fin 5 → Coordinate 1 := fun i => T75_75list.getD i.val (0,0,0,0,0)

theorem hfix75_75 : ∀ i, ((T75_75 i : Coordinate 1) : Coordinate 1 ⧸ reps rK75)
    ∈ fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75) :=
  repsFix_of_siftB rK75 ⟨75, by decide⟩ T75_75 (by decide)

theorem hinj75_75 : Function.Injective
    (fun i => ((T75_75 i : Coordinate 1) : Coordinate 1 ⧸ reps rK75)) :=
  repsInj_of_reduceAux rK75 T75_75 (by decide)

theorem hcardT75_75 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK75 ⟨75, by decide⟩ R75 hpxR75 hcardq75 (by decide)).symm

/-- **Cell (75, 75).** -/
theorem cell75_75 (e : List (ZMod 25)) (heK : charOK (basisAt rK75) e = true)
    (h : ↥(reps (⟨75, by decide⟩ : Fin 148))) :
    species (reps (⟨75, by decide⟩ : Fin 148)) h (basisElt (reps rK75) (charOfVec rK75 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK75 e (h : Coordinate 1) T75_75 i :=
  species_entry_eq_sum rK75 ⟨75, by decide⟩ e heK h T75_75 hfix75_75 hinj75_75 hcardT75_75
    (fun i => conj_mem_of_fixedPoints (reps ⟨75, by decide⟩) (reps rK75) (T75_75 i) (hfix75_75 i) h)

namespace Q2

def R75_2 : Fin 25 → Coordinate 2 := fun i => R75list.getD i.val (0,0,0,0,0)
theorem hpxR75_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK75) (R75_2 i)) := by decide
theorem hcardq75_2 : Nat.card (Coordinate 2 ⧸ reps rK75) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (75, 0) twin -/

def T75_0_2 : Fin 25 → Coordinate 2 := fun i => T75_0list.getD i.val (0,0,0,0,0)

theorem hfix75_0_2 : ∀ i, ((T75_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK75)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK75) :=
  repsFix_of_siftB2 rK75 ⟨0, by decide⟩ T75_0_2 (by decide)

theorem hinj75_0_2 : Function.Injective
    (fun i => ((T75_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK75)) :=
  repsInj_of_reduceAux2 rK75 T75_0_2 (by decide)

theorem hcardT75_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK75)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK75 ⟨0, by decide⟩ R75_2 hpxR75_2 hcardq75_2 (by decide)).symm

/-- **Cell (75, 0) twin (q=2).** -/
theorem cell75_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK75) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK75) (charOfVec2 rK75 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK75 e (h : Coordinate 2) T75_0_2 i :=
  species_entry_eq_sum rK75 ⟨0, by decide⟩ e heK h T75_0_2 hfix75_0_2 hinj75_0_2 hcardT75_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK75) (T75_0_2 i) (hfix75_0_2 i) h)

/-! ### Cell (75, 9) twin -/

def T75_9_2 : Fin 25 → Coordinate 2 := fun i => T75_9list.getD i.val (0,0,0,0,0)

theorem hfix75_9_2 : ∀ i, ((T75_9_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK75)
    ∈ fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK75) :=
  repsFix_of_siftB2 rK75 ⟨9, by decide⟩ T75_9_2 (by decide)

theorem hinj75_9_2 : Function.Injective
    (fun i => ((T75_9_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK75)) :=
  repsInj_of_reduceAux2 rK75 T75_9_2 (by decide)

theorem hcardT75_9_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK75)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK75 ⟨9, by decide⟩ R75_2 hpxR75_2 hcardq75_2 (by decide)).symm

/-- **Cell (75, 9) twin (q=2).** -/
theorem cell75_9_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK75) e = true)
    (h : ↥(reps (⟨9, by decide⟩ : Fin 148))) :
    species (reps (⟨9, by decide⟩ : Fin 148)) h (basisElt (reps rK75) (charOfVec2 rK75 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK75 e (h : Coordinate 2) T75_9_2 i :=
  species_entry_eq_sum rK75 ⟨9, by decide⟩ e heK h T75_9_2 hfix75_9_2 hinj75_9_2 hcardT75_9_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨9, by decide⟩) (reps rK75) (T75_9_2 i) (hfix75_9_2 i) h)

/-! ### Cell (75, 12) twin -/

def T75_12_2 : Fin 25 → Coordinate 2 := fun i => T75_12list.getD i.val (0,0,0,0,0)

theorem hfix75_12_2 : ∀ i, ((T75_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK75)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK75) :=
  repsFix_of_siftB2 rK75 ⟨12, by decide⟩ T75_12_2 (by decide)

theorem hinj75_12_2 : Function.Injective
    (fun i => ((T75_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK75)) :=
  repsInj_of_reduceAux2 rK75 T75_12_2 (by decide)

theorem hcardT75_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK75)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK75 ⟨12, by decide⟩ R75_2 hpxR75_2 hcardq75_2 (by decide)).symm

/-- **Cell (75, 12) twin (q=2).** -/
theorem cell75_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK75) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK75) (charOfVec2 rK75 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK75 e (h : Coordinate 2) T75_12_2 i :=
  species_entry_eq_sum rK75 ⟨12, by decide⟩ e heK h T75_12_2 hfix75_12_2 hinj75_12_2 hcardT75_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK75) (T75_12_2 i) (hfix75_12_2 i) h)

/-! ### Cell (75, 27) twin -/

def T75_27_2 : Fin 25 → Coordinate 2 := fun i => T75_27list.getD i.val (0,0,0,0,0)

theorem hfix75_27_2 : ∀ i, ((T75_27_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK75)
    ∈ fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK75) :=
  repsFix_of_siftB2 rK75 ⟨27, by decide⟩ T75_27_2 (by decide)

theorem hinj75_27_2 : Function.Injective
    (fun i => ((T75_27_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK75)) :=
  repsInj_of_reduceAux2 rK75 T75_27_2 (by decide)

theorem hcardT75_27_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK75)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK75 ⟨27, by decide⟩ R75_2 hpxR75_2 hcardq75_2 (by decide)).symm

/-- **Cell (75, 27) twin (q=2).** -/
theorem cell75_27_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK75) e = true)
    (h : ↥(reps (⟨27, by decide⟩ : Fin 148))) :
    species (reps (⟨27, by decide⟩ : Fin 148)) h (basisElt (reps rK75) (charOfVec2 rK75 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK75 e (h : Coordinate 2) T75_27_2 i :=
  species_entry_eq_sum rK75 ⟨27, by decide⟩ e heK h T75_27_2 hfix75_27_2 hinj75_27_2 hcardT75_27_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨27, by decide⟩) (reps rK75) (T75_27_2 i) (hfix75_27_2 i) h)

/-! ### Cell (75, 32) twin -/

def T75_32_2 : Fin 5 → Coordinate 2 := fun i => T75_32list.getD i.val (0,0,0,0,0)

theorem hfix75_32_2 : ∀ i, ((T75_32_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK75)
    ∈ fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK75) :=
  repsFix_of_siftB2 rK75 ⟨32, by decide⟩ T75_32_2 (by decide)

theorem hinj75_32_2 : Function.Injective
    (fun i => ((T75_32_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK75)) :=
  repsInj_of_reduceAux2 rK75 T75_32_2 (by decide)

theorem hcardT75_32_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK75)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK75 ⟨32, by decide⟩ R75_2 hpxR75_2 hcardq75_2 (by decide)).symm

/-- **Cell (75, 32) twin (q=2).** -/
theorem cell75_32_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK75) e = true)
    (h : ↥(reps (⟨32, by decide⟩ : Fin 148))) :
    species (reps (⟨32, by decide⟩ : Fin 148)) h (basisElt (reps rK75) (charOfVec2 rK75 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK75 e (h : Coordinate 2) T75_32_2 i :=
  species_entry_eq_sum rK75 ⟨32, by decide⟩ e heK h T75_32_2 hfix75_32_2 hinj75_32_2 hcardT75_32_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨32, by decide⟩) (reps rK75) (T75_32_2 i) (hfix75_32_2 i) h)

/-! ### Cell (75, 37) twin -/

def T75_37_2 : Fin 5 → Coordinate 2 := fun i => T75_37list.getD i.val (0,0,0,0,0)

theorem hfix75_37_2 : ∀ i, ((T75_37_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK75)
    ∈ fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK75) :=
  repsFix_of_siftB2 rK75 ⟨37, by decide⟩ T75_37_2 (by decide)

theorem hinj75_37_2 : Function.Injective
    (fun i => ((T75_37_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK75)) :=
  repsInj_of_reduceAux2 rK75 T75_37_2 (by decide)

theorem hcardT75_37_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK75)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK75 ⟨37, by decide⟩ R75_2 hpxR75_2 hcardq75_2 (by decide)).symm

/-- **Cell (75, 37) twin (q=2).** -/
theorem cell75_37_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK75) e = true)
    (h : ↥(reps (⟨37, by decide⟩ : Fin 148))) :
    species (reps (⟨37, by decide⟩ : Fin 148)) h (basisElt (reps rK75) (charOfVec2 rK75 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK75 e (h : Coordinate 2) T75_37_2 i :=
  species_entry_eq_sum rK75 ⟨37, by decide⟩ e heK h T75_37_2 hfix75_37_2 hinj75_37_2 hcardT75_37_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨37, by decide⟩) (reps rK75) (T75_37_2 i) (hfix75_37_2 i) h)

/-! ### Cell (75, 42) twin -/

def T75_42_2 : Fin 5 → Coordinate 2 := fun i => T75_42list.getD i.val (0,0,0,0,0)

theorem hfix75_42_2 : ∀ i, ((T75_42_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK75)
    ∈ fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK75) :=
  repsFix_of_siftB2 rK75 ⟨42, by decide⟩ T75_42_2 (by decide)

theorem hinj75_42_2 : Function.Injective
    (fun i => ((T75_42_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK75)) :=
  repsInj_of_reduceAux2 rK75 T75_42_2 (by decide)

theorem hcardT75_42_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK75)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK75 ⟨42, by decide⟩ R75_2 hpxR75_2 hcardq75_2 (by decide)).symm

/-- **Cell (75, 42) twin (q=2).** -/
theorem cell75_42_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK75) e = true)
    (h : ↥(reps (⟨42, by decide⟩ : Fin 148))) :
    species (reps (⟨42, by decide⟩ : Fin 148)) h (basisElt (reps rK75) (charOfVec2 rK75 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK75 e (h : Coordinate 2) T75_42_2 i :=
  species_entry_eq_sum rK75 ⟨42, by decide⟩ e heK h T75_42_2 hfix75_42_2 hinj75_42_2 hcardT75_42_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨42, by decide⟩) (reps rK75) (T75_42_2 i) (hfix75_42_2 i) h)

/-! ### Cell (75, 47) twin -/

def T75_47_2 : Fin 5 → Coordinate 2 := fun i => T75_47list.getD i.val (0,0,0,0,0)

theorem hfix75_47_2 : ∀ i, ((T75_47_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK75)
    ∈ fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK75) :=
  repsFix_of_siftB2 rK75 ⟨47, by decide⟩ T75_47_2 (by decide)

theorem hinj75_47_2 : Function.Injective
    (fun i => ((T75_47_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK75)) :=
  repsInj_of_reduceAux2 rK75 T75_47_2 (by decide)

theorem hcardT75_47_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK75)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK75 ⟨47, by decide⟩ R75_2 hpxR75_2 hcardq75_2 (by decide)).symm

/-- **Cell (75, 47) twin (q=2).** -/
theorem cell75_47_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK75) e = true)
    (h : ↥(reps (⟨47, by decide⟩ : Fin 148))) :
    species (reps (⟨47, by decide⟩ : Fin 148)) h (basisElt (reps rK75) (charOfVec2 rK75 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK75 e (h : Coordinate 2) T75_47_2 i :=
  species_entry_eq_sum rK75 ⟨47, by decide⟩ e heK h T75_47_2 hfix75_47_2 hinj75_47_2 hcardT75_47_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨47, by decide⟩) (reps rK75) (T75_47_2 i) (hfix75_47_2 i) h)

/-! ### Cell (75, 52) twin -/

def T75_52_2 : Fin 5 → Coordinate 2 := fun i => T75_52list.getD i.val (0,0,0,0,0)

theorem hfix75_52_2 : ∀ i, ((T75_52_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK75)
    ∈ fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK75) :=
  repsFix_of_siftB2 rK75 ⟨52, by decide⟩ T75_52_2 (by decide)

theorem hinj75_52_2 : Function.Injective
    (fun i => ((T75_52_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK75)) :=
  repsInj_of_reduceAux2 rK75 T75_52_2 (by decide)

theorem hcardT75_52_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK75)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK75 ⟨52, by decide⟩ R75_2 hpxR75_2 hcardq75_2 (by decide)).symm

/-- **Cell (75, 52) twin (q=2).** -/
theorem cell75_52_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK75) e = true)
    (h : ↥(reps (⟨52, by decide⟩ : Fin 148))) :
    species (reps (⟨52, by decide⟩ : Fin 148)) h (basisElt (reps rK75) (charOfVec2 rK75 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK75 e (h : Coordinate 2) T75_52_2 i :=
  species_entry_eq_sum rK75 ⟨52, by decide⟩ e heK h T75_52_2 hfix75_52_2 hinj75_52_2 hcardT75_52_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨52, by decide⟩) (reps rK75) (T75_52_2 i) (hfix75_52_2 i) h)

/-! ### Cell (75, 75) twin -/

def T75_75_2 : Fin 5 → Coordinate 2 := fun i => T75_75list.getD i.val (0,0,0,0,0)

theorem hfix75_75_2 : ∀ i, ((T75_75_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK75)
    ∈ fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK75) :=
  repsFix_of_siftB2 rK75 ⟨75, by decide⟩ T75_75_2 (by decide)

theorem hinj75_75_2 : Function.Injective
    (fun i => ((T75_75_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK75)) :=
  repsInj_of_reduceAux2 rK75 T75_75_2 (by decide)

theorem hcardT75_75_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK75)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK75 ⟨75, by decide⟩ R75_2 hpxR75_2 hcardq75_2 (by decide)).symm

/-- **Cell (75, 75) twin (q=2).** -/
theorem cell75_75_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK75) e = true)
    (h : ↥(reps (⟨75, by decide⟩ : Fin 148))) :
    species (reps (⟨75, by decide⟩ : Fin 148)) h (basisElt (reps rK75) (charOfVec2 rK75 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK75 e (h : Coordinate 2) T75_75_2 i :=
  species_entry_eq_sum rK75 ⟨75, by decide⟩ e heK h T75_75_2 hfix75_75_2 hinj75_75_2 hcardT75_75_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨75, by decide⟩) (reps rK75) (T75_75_2 i) (hfix75_75_2 i) h)

end Q2

/-! # K-class rK = 76  (|G/K| = 25) -/

def rK76 : Fin 148 := ⟨76, by decide⟩

def R76list : List Coordinates := [(0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0)]
def R76 : Fin 25 → Coordinate 1 := fun i => R76list.getD i.val (0,0,0,0,0)

theorem hpxR76 : Function.Injective (fun i => reduceAux 1 (basisAt rK76) (R76 i)) := by decide
theorem hcardq76 : Nat.card (Coordinate 1 ⧸ reps rK76) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (76, 0): |T| = 25 -/

def T76_0list : List Coordinates := [(0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0)]
def T76_0 : Fin 25 → Coordinate 1 := fun i => T76_0list.getD i.val (0,0,0,0,0)

theorem hfix76_0 : ∀ i, ((T76_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK76)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76) :=
  repsFix_of_siftB rK76 ⟨0, by decide⟩ T76_0 (by decide)

theorem hinj76_0 : Function.Injective
    (fun i => ((T76_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK76)) :=
  repsInj_of_reduceAux rK76 T76_0 (by decide)

theorem hcardT76_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK76 ⟨0, by decide⟩ R76 hpxR76 hcardq76 (by decide)).symm

/-- **Cell (76, 0).** -/
theorem cell76_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK76) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK76) (charOfVec rK76 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK76 e (h : Coordinate 1) T76_0 i :=
  species_entry_eq_sum rK76 ⟨0, by decide⟩ e heK h T76_0 hfix76_0 hinj76_0 hcardT76_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK76) (T76_0 i) (hfix76_0 i) h)

/-! ## Cell (76, 1): |T| = 25 -/

def T76_1list : List Coordinates := [(0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0)]
def T76_1 : Fin 25 → Coordinate 1 := fun i => T76_1list.getD i.val (0,0,0,0,0)

theorem hfix76_1 : ∀ i, ((T76_1 i : Coordinate 1) : Coordinate 1 ⧸ reps rK76)
    ∈ fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76) :=
  repsFix_of_siftB rK76 ⟨1, by decide⟩ T76_1 (by decide)

theorem hinj76_1 : Function.Injective
    (fun i => ((T76_1 i : Coordinate 1) : Coordinate 1 ⧸ reps rK76)) :=
  repsInj_of_reduceAux rK76 T76_1 (by decide)

theorem hcardT76_1 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK76 ⟨1, by decide⟩ R76 hpxR76 hcardq76 (by decide)).symm

/-- **Cell (76, 1).** -/
theorem cell76_1 (e : List (ZMod 25)) (heK : charOK (basisAt rK76) e = true)
    (h : ↥(reps (⟨1, by decide⟩ : Fin 148))) :
    species (reps (⟨1, by decide⟩ : Fin 148)) h (basisElt (reps rK76) (charOfVec rK76 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK76 e (h : Coordinate 1) T76_1 i :=
  species_entry_eq_sum rK76 ⟨1, by decide⟩ e heK h T76_1 hfix76_1 hinj76_1 hcardT76_1
    (fun i => conj_mem_of_fixedPoints (reps ⟨1, by decide⟩) (reps rK76) (T76_1 i) (hfix76_1 i) h)

/-! ## Cell (76, 12): |T| = 25 -/

def T76_12list : List Coordinates := [(0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0)]
def T76_12 : Fin 25 → Coordinate 1 := fun i => T76_12list.getD i.val (0,0,0,0,0)

theorem hfix76_12 : ∀ i, ((T76_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK76)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76) :=
  repsFix_of_siftB rK76 ⟨12, by decide⟩ T76_12 (by decide)

theorem hinj76_12 : Function.Injective
    (fun i => ((T76_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK76)) :=
  repsInj_of_reduceAux rK76 T76_12 (by decide)

theorem hcardT76_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK76 ⟨12, by decide⟩ R76 hpxR76 hcardq76 (by decide)).symm

/-- **Cell (76, 12).** -/
theorem cell76_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK76) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK76) (charOfVec rK76 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK76 e (h : Coordinate 1) T76_12 i :=
  species_entry_eq_sum rK76 ⟨12, by decide⟩ e heK h T76_12 hfix76_12 hinj76_12 hcardT76_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK76) (T76_12 i) (hfix76_12 i) h)

/-! ## Cell (76, 19): |T| = 25 -/

def T76_19list : List Coordinates := [(0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0)]
def T76_19 : Fin 25 → Coordinate 1 := fun i => T76_19list.getD i.val (0,0,0,0,0)

theorem hfix76_19 : ∀ i, ((T76_19 i : Coordinate 1) : Coordinate 1 ⧸ reps rK76)
    ∈ fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76) :=
  repsFix_of_siftB rK76 ⟨19, by decide⟩ T76_19 (by decide)

theorem hinj76_19 : Function.Injective
    (fun i => ((T76_19 i : Coordinate 1) : Coordinate 1 ⧸ reps rK76)) :=
  repsInj_of_reduceAux rK76 T76_19 (by decide)

theorem hcardT76_19 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK76 ⟨19, by decide⟩ R76 hpxR76 hcardq76 (by decide)).symm

/-- **Cell (76, 19).** -/
theorem cell76_19 (e : List (ZMod 25)) (heK : charOK (basisAt rK76) e = true)
    (h : ↥(reps (⟨19, by decide⟩ : Fin 148))) :
    species (reps (⟨19, by decide⟩ : Fin 148)) h (basisElt (reps rK76) (charOfVec rK76 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK76 e (h : Coordinate 1) T76_19 i :=
  species_entry_eq_sum rK76 ⟨19, by decide⟩ e heK h T76_19 hfix76_19 hinj76_19 hcardT76_19
    (fun i => conj_mem_of_fixedPoints (reps ⟨19, by decide⟩) (reps rK76) (T76_19 i) (hfix76_19 i) h)

/-! ## Cell (76, 32): |T| = 5 -/

def T76_32list : List Coordinates := [(0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0)]
def T76_32 : Fin 5 → Coordinate 1 := fun i => T76_32list.getD i.val (0,0,0,0,0)

theorem hfix76_32 : ∀ i, ((T76_32 i : Coordinate 1) : Coordinate 1 ⧸ reps rK76)
    ∈ fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76) :=
  repsFix_of_siftB rK76 ⟨32, by decide⟩ T76_32 (by decide)

theorem hinj76_32 : Function.Injective
    (fun i => ((T76_32 i : Coordinate 1) : Coordinate 1 ⧸ reps rK76)) :=
  repsInj_of_reduceAux rK76 T76_32 (by decide)

theorem hcardT76_32 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK76 ⟨32, by decide⟩ R76 hpxR76 hcardq76 (by decide)).symm

/-- **Cell (76, 32).** -/
theorem cell76_32 (e : List (ZMod 25)) (heK : charOK (basisAt rK76) e = true)
    (h : ↥(reps (⟨32, by decide⟩ : Fin 148))) :
    species (reps (⟨32, by decide⟩ : Fin 148)) h (basisElt (reps rK76) (charOfVec rK76 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK76 e (h : Coordinate 1) T76_32 i :=
  species_entry_eq_sum rK76 ⟨32, by decide⟩ e heK h T76_32 hfix76_32 hinj76_32 hcardT76_32
    (fun i => conj_mem_of_fixedPoints (reps ⟨32, by decide⟩) (reps rK76) (T76_32 i) (hfix76_32 i) h)

/-! ## Cell (76, 37): |T| = 5 -/

def T76_37list : List Coordinates := [(0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0)]
def T76_37 : Fin 5 → Coordinate 1 := fun i => T76_37list.getD i.val (0,0,0,0,0)

theorem hfix76_37 : ∀ i, ((T76_37 i : Coordinate 1) : Coordinate 1 ⧸ reps rK76)
    ∈ fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76) :=
  repsFix_of_siftB rK76 ⟨37, by decide⟩ T76_37 (by decide)

theorem hinj76_37 : Function.Injective
    (fun i => ((T76_37 i : Coordinate 1) : Coordinate 1 ⧸ reps rK76)) :=
  repsInj_of_reduceAux rK76 T76_37 (by decide)

theorem hcardT76_37 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK76 ⟨37, by decide⟩ R76 hpxR76 hcardq76 (by decide)).symm

/-- **Cell (76, 37).** -/
theorem cell76_37 (e : List (ZMod 25)) (heK : charOK (basisAt rK76) e = true)
    (h : ↥(reps (⟨37, by decide⟩ : Fin 148))) :
    species (reps (⟨37, by decide⟩ : Fin 148)) h (basisElt (reps rK76) (charOfVec rK76 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK76 e (h : Coordinate 1) T76_37 i :=
  species_entry_eq_sum rK76 ⟨37, by decide⟩ e heK h T76_37 hfix76_37 hinj76_37 hcardT76_37
    (fun i => conj_mem_of_fixedPoints (reps ⟨37, by decide⟩) (reps rK76) (T76_37 i) (hfix76_37 i) h)

/-! ## Cell (76, 42): |T| = 5 -/

def T76_42list : List Coordinates := [(0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0)]
def T76_42 : Fin 5 → Coordinate 1 := fun i => T76_42list.getD i.val (0,0,0,0,0)

theorem hfix76_42 : ∀ i, ((T76_42 i : Coordinate 1) : Coordinate 1 ⧸ reps rK76)
    ∈ fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76) :=
  repsFix_of_siftB rK76 ⟨42, by decide⟩ T76_42 (by decide)

theorem hinj76_42 : Function.Injective
    (fun i => ((T76_42 i : Coordinate 1) : Coordinate 1 ⧸ reps rK76)) :=
  repsInj_of_reduceAux rK76 T76_42 (by decide)

theorem hcardT76_42 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK76 ⟨42, by decide⟩ R76 hpxR76 hcardq76 (by decide)).symm

/-- **Cell (76, 42).** -/
theorem cell76_42 (e : List (ZMod 25)) (heK : charOK (basisAt rK76) e = true)
    (h : ↥(reps (⟨42, by decide⟩ : Fin 148))) :
    species (reps (⟨42, by decide⟩ : Fin 148)) h (basisElt (reps rK76) (charOfVec rK76 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK76 e (h : Coordinate 1) T76_42 i :=
  species_entry_eq_sum rK76 ⟨42, by decide⟩ e heK h T76_42 hfix76_42 hinj76_42 hcardT76_42
    (fun i => conj_mem_of_fixedPoints (reps ⟨42, by decide⟩) (reps rK76) (T76_42 i) (hfix76_42 i) h)

/-! ## Cell (76, 47): |T| = 5 -/

def T76_47list : List Coordinates := [(0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0)]
def T76_47 : Fin 5 → Coordinate 1 := fun i => T76_47list.getD i.val (0,0,0,0,0)

theorem hfix76_47 : ∀ i, ((T76_47 i : Coordinate 1) : Coordinate 1 ⧸ reps rK76)
    ∈ fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76) :=
  repsFix_of_siftB rK76 ⟨47, by decide⟩ T76_47 (by decide)

theorem hinj76_47 : Function.Injective
    (fun i => ((T76_47 i : Coordinate 1) : Coordinate 1 ⧸ reps rK76)) :=
  repsInj_of_reduceAux rK76 T76_47 (by decide)

theorem hcardT76_47 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK76 ⟨47, by decide⟩ R76 hpxR76 hcardq76 (by decide)).symm

/-- **Cell (76, 47).** -/
theorem cell76_47 (e : List (ZMod 25)) (heK : charOK (basisAt rK76) e = true)
    (h : ↥(reps (⟨47, by decide⟩ : Fin 148))) :
    species (reps (⟨47, by decide⟩ : Fin 148)) h (basisElt (reps rK76) (charOfVec rK76 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK76 e (h : Coordinate 1) T76_47 i :=
  species_entry_eq_sum rK76 ⟨47, by decide⟩ e heK h T76_47 hfix76_47 hinj76_47 hcardT76_47
    (fun i => conj_mem_of_fixedPoints (reps ⟨47, by decide⟩) (reps rK76) (T76_47 i) (hfix76_47 i) h)

/-! ## Cell (76, 52): |T| = 5 -/

def T76_52list : List Coordinates := [(0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0)]
def T76_52 : Fin 5 → Coordinate 1 := fun i => T76_52list.getD i.val (0,0,0,0,0)

theorem hfix76_52 : ∀ i, ((T76_52 i : Coordinate 1) : Coordinate 1 ⧸ reps rK76)
    ∈ fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76) :=
  repsFix_of_siftB rK76 ⟨52, by decide⟩ T76_52 (by decide)

theorem hinj76_52 : Function.Injective
    (fun i => ((T76_52 i : Coordinate 1) : Coordinate 1 ⧸ reps rK76)) :=
  repsInj_of_reduceAux rK76 T76_52 (by decide)

theorem hcardT76_52 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK76 ⟨52, by decide⟩ R76 hpxR76 hcardq76 (by decide)).symm

/-- **Cell (76, 52).** -/
theorem cell76_52 (e : List (ZMod 25)) (heK : charOK (basisAt rK76) e = true)
    (h : ↥(reps (⟨52, by decide⟩ : Fin 148))) :
    species (reps (⟨52, by decide⟩ : Fin 148)) h (basisElt (reps rK76) (charOfVec rK76 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK76 e (h : Coordinate 1) T76_52 i :=
  species_entry_eq_sum rK76 ⟨52, by decide⟩ e heK h T76_52 hfix76_52 hinj76_52 hcardT76_52
    (fun i => conj_mem_of_fixedPoints (reps ⟨52, by decide⟩) (reps rK76) (T76_52 i) (hfix76_52 i) h)

/-! ## Cell (76, 76): |T| = 5 -/

def T76_76list : List Coordinates := [(0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0)]
def T76_76 : Fin 5 → Coordinate 1 := fun i => T76_76list.getD i.val (0,0,0,0,0)

theorem hfix76_76 : ∀ i, ((T76_76 i : Coordinate 1) : Coordinate 1 ⧸ reps rK76)
    ∈ fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76) :=
  repsFix_of_siftB rK76 ⟨76, by decide⟩ T76_76 (by decide)

theorem hinj76_76 : Function.Injective
    (fun i => ((T76_76 i : Coordinate 1) : Coordinate 1 ⧸ reps rK76)) :=
  repsInj_of_reduceAux rK76 T76_76 (by decide)

theorem hcardT76_76 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK76 ⟨76, by decide⟩ R76 hpxR76 hcardq76 (by decide)).symm

/-- **Cell (76, 76).** -/
theorem cell76_76 (e : List (ZMod 25)) (heK : charOK (basisAt rK76) e = true)
    (h : ↥(reps (⟨76, by decide⟩ : Fin 148))) :
    species (reps (⟨76, by decide⟩ : Fin 148)) h (basisElt (reps rK76) (charOfVec rK76 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK76 e (h : Coordinate 1) T76_76 i :=
  species_entry_eq_sum rK76 ⟨76, by decide⟩ e heK h T76_76 hfix76_76 hinj76_76 hcardT76_76
    (fun i => conj_mem_of_fixedPoints (reps ⟨76, by decide⟩) (reps rK76) (T76_76 i) (hfix76_76 i) h)

namespace Q2

def R76_2 : Fin 25 → Coordinate 2 := fun i => R76list.getD i.val (0,0,0,0,0)
theorem hpxR76_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK76) (R76_2 i)) := by decide
theorem hcardq76_2 : Nat.card (Coordinate 2 ⧸ reps rK76) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (76, 0) twin -/

def T76_0_2 : Fin 25 → Coordinate 2 := fun i => T76_0list.getD i.val (0,0,0,0,0)

theorem hfix76_0_2 : ∀ i, ((T76_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK76)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK76) :=
  repsFix_of_siftB2 rK76 ⟨0, by decide⟩ T76_0_2 (by decide)

theorem hinj76_0_2 : Function.Injective
    (fun i => ((T76_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK76)) :=
  repsInj_of_reduceAux2 rK76 T76_0_2 (by decide)

theorem hcardT76_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK76)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK76 ⟨0, by decide⟩ R76_2 hpxR76_2 hcardq76_2 (by decide)).symm

/-- **Cell (76, 0) twin (q=2).** -/
theorem cell76_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK76) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK76) (charOfVec2 rK76 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK76 e (h : Coordinate 2) T76_0_2 i :=
  species_entry_eq_sum rK76 ⟨0, by decide⟩ e heK h T76_0_2 hfix76_0_2 hinj76_0_2 hcardT76_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK76) (T76_0_2 i) (hfix76_0_2 i) h)

/-! ### Cell (76, 1) twin -/

def T76_1_2 : Fin 25 → Coordinate 2 := fun i => T76_1list.getD i.val (0,0,0,0,0)

theorem hfix76_1_2 : ∀ i, ((T76_1_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK76)
    ∈ fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK76) :=
  repsFix_of_siftB2 rK76 ⟨1, by decide⟩ T76_1_2 (by decide)

theorem hinj76_1_2 : Function.Injective
    (fun i => ((T76_1_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK76)) :=
  repsInj_of_reduceAux2 rK76 T76_1_2 (by decide)

theorem hcardT76_1_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK76)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK76 ⟨1, by decide⟩ R76_2 hpxR76_2 hcardq76_2 (by decide)).symm

/-- **Cell (76, 1) twin (q=2).** -/
theorem cell76_1_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK76) e = true)
    (h : ↥(reps (⟨1, by decide⟩ : Fin 148))) :
    species (reps (⟨1, by decide⟩ : Fin 148)) h (basisElt (reps rK76) (charOfVec2 rK76 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK76 e (h : Coordinate 2) T76_1_2 i :=
  species_entry_eq_sum rK76 ⟨1, by decide⟩ e heK h T76_1_2 hfix76_1_2 hinj76_1_2 hcardT76_1_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨1, by decide⟩) (reps rK76) (T76_1_2 i) (hfix76_1_2 i) h)

/-! ### Cell (76, 12) twin -/

def T76_12_2 : Fin 25 → Coordinate 2 := fun i => T76_12list.getD i.val (0,0,0,0,0)

theorem hfix76_12_2 : ∀ i, ((T76_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK76)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK76) :=
  repsFix_of_siftB2 rK76 ⟨12, by decide⟩ T76_12_2 (by decide)

theorem hinj76_12_2 : Function.Injective
    (fun i => ((T76_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK76)) :=
  repsInj_of_reduceAux2 rK76 T76_12_2 (by decide)

theorem hcardT76_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK76)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK76 ⟨12, by decide⟩ R76_2 hpxR76_2 hcardq76_2 (by decide)).symm

/-- **Cell (76, 12) twin (q=2).** -/
theorem cell76_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK76) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK76) (charOfVec2 rK76 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK76 e (h : Coordinate 2) T76_12_2 i :=
  species_entry_eq_sum rK76 ⟨12, by decide⟩ e heK h T76_12_2 hfix76_12_2 hinj76_12_2 hcardT76_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK76) (T76_12_2 i) (hfix76_12_2 i) h)

/-! ### Cell (76, 19) twin -/

def T76_19_2 : Fin 25 → Coordinate 2 := fun i => T76_19list.getD i.val (0,0,0,0,0)

theorem hfix76_19_2 : ∀ i, ((T76_19_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK76)
    ∈ fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK76) :=
  repsFix_of_siftB2 rK76 ⟨19, by decide⟩ T76_19_2 (by decide)

theorem hinj76_19_2 : Function.Injective
    (fun i => ((T76_19_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK76)) :=
  repsInj_of_reduceAux2 rK76 T76_19_2 (by decide)

theorem hcardT76_19_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK76)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK76 ⟨19, by decide⟩ R76_2 hpxR76_2 hcardq76_2 (by decide)).symm

/-- **Cell (76, 19) twin (q=2).** -/
theorem cell76_19_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK76) e = true)
    (h : ↥(reps (⟨19, by decide⟩ : Fin 148))) :
    species (reps (⟨19, by decide⟩ : Fin 148)) h (basisElt (reps rK76) (charOfVec2 rK76 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK76 e (h : Coordinate 2) T76_19_2 i :=
  species_entry_eq_sum rK76 ⟨19, by decide⟩ e heK h T76_19_2 hfix76_19_2 hinj76_19_2 hcardT76_19_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨19, by decide⟩) (reps rK76) (T76_19_2 i) (hfix76_19_2 i) h)

/-! ### Cell (76, 32) twin -/

def T76_32_2 : Fin 5 → Coordinate 2 := fun i => T76_32list.getD i.val (0,0,0,0,0)

theorem hfix76_32_2 : ∀ i, ((T76_32_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK76)
    ∈ fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK76) :=
  repsFix_of_siftB2 rK76 ⟨32, by decide⟩ T76_32_2 (by decide)

theorem hinj76_32_2 : Function.Injective
    (fun i => ((T76_32_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK76)) :=
  repsInj_of_reduceAux2 rK76 T76_32_2 (by decide)

theorem hcardT76_32_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK76)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK76 ⟨32, by decide⟩ R76_2 hpxR76_2 hcardq76_2 (by decide)).symm

/-- **Cell (76, 32) twin (q=2).** -/
theorem cell76_32_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK76) e = true)
    (h : ↥(reps (⟨32, by decide⟩ : Fin 148))) :
    species (reps (⟨32, by decide⟩ : Fin 148)) h (basisElt (reps rK76) (charOfVec2 rK76 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK76 e (h : Coordinate 2) T76_32_2 i :=
  species_entry_eq_sum rK76 ⟨32, by decide⟩ e heK h T76_32_2 hfix76_32_2 hinj76_32_2 hcardT76_32_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨32, by decide⟩) (reps rK76) (T76_32_2 i) (hfix76_32_2 i) h)

/-! ### Cell (76, 37) twin -/

def T76_37_2 : Fin 5 → Coordinate 2 := fun i => T76_37list.getD i.val (0,0,0,0,0)

theorem hfix76_37_2 : ∀ i, ((T76_37_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK76)
    ∈ fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK76) :=
  repsFix_of_siftB2 rK76 ⟨37, by decide⟩ T76_37_2 (by decide)

theorem hinj76_37_2 : Function.Injective
    (fun i => ((T76_37_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK76)) :=
  repsInj_of_reduceAux2 rK76 T76_37_2 (by decide)

theorem hcardT76_37_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK76)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK76 ⟨37, by decide⟩ R76_2 hpxR76_2 hcardq76_2 (by decide)).symm

/-- **Cell (76, 37) twin (q=2).** -/
theorem cell76_37_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK76) e = true)
    (h : ↥(reps (⟨37, by decide⟩ : Fin 148))) :
    species (reps (⟨37, by decide⟩ : Fin 148)) h (basisElt (reps rK76) (charOfVec2 rK76 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK76 e (h : Coordinate 2) T76_37_2 i :=
  species_entry_eq_sum rK76 ⟨37, by decide⟩ e heK h T76_37_2 hfix76_37_2 hinj76_37_2 hcardT76_37_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨37, by decide⟩) (reps rK76) (T76_37_2 i) (hfix76_37_2 i) h)

/-! ### Cell (76, 42) twin -/

def T76_42_2 : Fin 5 → Coordinate 2 := fun i => T76_42list.getD i.val (0,0,0,0,0)

theorem hfix76_42_2 : ∀ i, ((T76_42_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK76)
    ∈ fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK76) :=
  repsFix_of_siftB2 rK76 ⟨42, by decide⟩ T76_42_2 (by decide)

theorem hinj76_42_2 : Function.Injective
    (fun i => ((T76_42_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK76)) :=
  repsInj_of_reduceAux2 rK76 T76_42_2 (by decide)

theorem hcardT76_42_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK76)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK76 ⟨42, by decide⟩ R76_2 hpxR76_2 hcardq76_2 (by decide)).symm

/-- **Cell (76, 42) twin (q=2).** -/
theorem cell76_42_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK76) e = true)
    (h : ↥(reps (⟨42, by decide⟩ : Fin 148))) :
    species (reps (⟨42, by decide⟩ : Fin 148)) h (basisElt (reps rK76) (charOfVec2 rK76 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK76 e (h : Coordinate 2) T76_42_2 i :=
  species_entry_eq_sum rK76 ⟨42, by decide⟩ e heK h T76_42_2 hfix76_42_2 hinj76_42_2 hcardT76_42_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨42, by decide⟩) (reps rK76) (T76_42_2 i) (hfix76_42_2 i) h)

/-! ### Cell (76, 47) twin -/

def T76_47_2 : Fin 5 → Coordinate 2 := fun i => T76_47list.getD i.val (0,0,0,0,0)

theorem hfix76_47_2 : ∀ i, ((T76_47_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK76)
    ∈ fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK76) :=
  repsFix_of_siftB2 rK76 ⟨47, by decide⟩ T76_47_2 (by decide)

theorem hinj76_47_2 : Function.Injective
    (fun i => ((T76_47_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK76)) :=
  repsInj_of_reduceAux2 rK76 T76_47_2 (by decide)

theorem hcardT76_47_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK76)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK76 ⟨47, by decide⟩ R76_2 hpxR76_2 hcardq76_2 (by decide)).symm

/-- **Cell (76, 47) twin (q=2).** -/
theorem cell76_47_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK76) e = true)
    (h : ↥(reps (⟨47, by decide⟩ : Fin 148))) :
    species (reps (⟨47, by decide⟩ : Fin 148)) h (basisElt (reps rK76) (charOfVec2 rK76 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK76 e (h : Coordinate 2) T76_47_2 i :=
  species_entry_eq_sum rK76 ⟨47, by decide⟩ e heK h T76_47_2 hfix76_47_2 hinj76_47_2 hcardT76_47_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨47, by decide⟩) (reps rK76) (T76_47_2 i) (hfix76_47_2 i) h)

/-! ### Cell (76, 52) twin -/

def T76_52_2 : Fin 5 → Coordinate 2 := fun i => T76_52list.getD i.val (0,0,0,0,0)

theorem hfix76_52_2 : ∀ i, ((T76_52_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK76)
    ∈ fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK76) :=
  repsFix_of_siftB2 rK76 ⟨52, by decide⟩ T76_52_2 (by decide)

theorem hinj76_52_2 : Function.Injective
    (fun i => ((T76_52_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK76)) :=
  repsInj_of_reduceAux2 rK76 T76_52_2 (by decide)

theorem hcardT76_52_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK76)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK76 ⟨52, by decide⟩ R76_2 hpxR76_2 hcardq76_2 (by decide)).symm

/-- **Cell (76, 52) twin (q=2).** -/
theorem cell76_52_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK76) e = true)
    (h : ↥(reps (⟨52, by decide⟩ : Fin 148))) :
    species (reps (⟨52, by decide⟩ : Fin 148)) h (basisElt (reps rK76) (charOfVec2 rK76 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK76 e (h : Coordinate 2) T76_52_2 i :=
  species_entry_eq_sum rK76 ⟨52, by decide⟩ e heK h T76_52_2 hfix76_52_2 hinj76_52_2 hcardT76_52_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨52, by decide⟩) (reps rK76) (T76_52_2 i) (hfix76_52_2 i) h)

/-! ### Cell (76, 76) twin -/

def T76_76_2 : Fin 5 → Coordinate 2 := fun i => T76_76list.getD i.val (0,0,0,0,0)

theorem hfix76_76_2 : ∀ i, ((T76_76_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK76)
    ∈ fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK76) :=
  repsFix_of_siftB2 rK76 ⟨76, by decide⟩ T76_76_2 (by decide)

theorem hinj76_76_2 : Function.Injective
    (fun i => ((T76_76_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK76)) :=
  repsInj_of_reduceAux2 rK76 T76_76_2 (by decide)

theorem hcardT76_76_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK76)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK76 ⟨76, by decide⟩ R76_2 hpxR76_2 hcardq76_2 (by decide)).symm

/-- **Cell (76, 76) twin (q=2).** -/
theorem cell76_76_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK76) e = true)
    (h : ↥(reps (⟨76, by decide⟩ : Fin 148))) :
    species (reps (⟨76, by decide⟩ : Fin 148)) h (basisElt (reps rK76) (charOfVec2 rK76 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK76 e (h : Coordinate 2) T76_76_2 i :=
  species_entry_eq_sum rK76 ⟨76, by decide⟩ e heK h T76_76_2 hfix76_76_2 hinj76_76_2 hcardT76_76_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨76, by decide⟩) (reps rK76) (T76_76_2 i) (hfix76_76_2 i) h)

end Q2

/-! # K-class rK = 77  (|G/K| = 25) -/

def rK77 : Fin 148 := ⟨77, by decide⟩

def R77list : List Coordinates := [(0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0)]
def R77 : Fin 25 → Coordinate 1 := fun i => R77list.getD i.val (0,0,0,0,0)

theorem hpxR77 : Function.Injective (fun i => reduceAux 1 (basisAt rK77) (R77 i)) := by decide
theorem hcardq77 : Nat.card (Coordinate 1 ⧸ reps rK77) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (77, 0): |T| = 25 -/

def T77_0list : List Coordinates := [(0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0)]
def T77_0 : Fin 25 → Coordinate 1 := fun i => T77_0list.getD i.val (0,0,0,0,0)

theorem hfix77_0 : ∀ i, ((T77_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK77)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77) :=
  repsFix_of_siftB rK77 ⟨0, by decide⟩ T77_0 (by decide)

theorem hinj77_0 : Function.Injective
    (fun i => ((T77_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK77)) :=
  repsInj_of_reduceAux rK77 T77_0 (by decide)

theorem hcardT77_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK77 ⟨0, by decide⟩ R77 hpxR77 hcardq77 (by decide)).symm

/-- **Cell (77, 0).** -/
theorem cell77_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK77) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK77) (charOfVec rK77 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK77 e (h : Coordinate 1) T77_0 i :=
  species_entry_eq_sum rK77 ⟨0, by decide⟩ e heK h T77_0 hfix77_0 hinj77_0 hcardT77_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK77) (T77_0 i) (hfix77_0 i) h)

/-! ## Cell (77, 7): |T| = 25 -/

def T77_7list : List Coordinates := [(0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0)]
def T77_7 : Fin 25 → Coordinate 1 := fun i => T77_7list.getD i.val (0,0,0,0,0)

theorem hfix77_7 : ∀ i, ((T77_7 i : Coordinate 1) : Coordinate 1 ⧸ reps rK77)
    ∈ fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77) :=
  repsFix_of_siftB rK77 ⟨7, by decide⟩ T77_7 (by decide)

theorem hinj77_7 : Function.Injective
    (fun i => ((T77_7 i : Coordinate 1) : Coordinate 1 ⧸ reps rK77)) :=
  repsInj_of_reduceAux rK77 T77_7 (by decide)

theorem hcardT77_7 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK77 ⟨7, by decide⟩ R77 hpxR77 hcardq77 (by decide)).symm

/-- **Cell (77, 7).** -/
theorem cell77_7 (e : List (ZMod 25)) (heK : charOK (basisAt rK77) e = true)
    (h : ↥(reps (⟨7, by decide⟩ : Fin 148))) :
    species (reps (⟨7, by decide⟩ : Fin 148)) h (basisElt (reps rK77) (charOfVec rK77 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK77 e (h : Coordinate 1) T77_7 i :=
  species_entry_eq_sum rK77 ⟨7, by decide⟩ e heK h T77_7 hfix77_7 hinj77_7 hcardT77_7
    (fun i => conj_mem_of_fixedPoints (reps ⟨7, by decide⟩) (reps rK77) (T77_7 i) (hfix77_7 i) h)

/-! ## Cell (77, 12): |T| = 25 -/

def T77_12list : List Coordinates := [(0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0)]
def T77_12 : Fin 25 → Coordinate 1 := fun i => T77_12list.getD i.val (0,0,0,0,0)

theorem hfix77_12 : ∀ i, ((T77_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK77)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77) :=
  repsFix_of_siftB rK77 ⟨12, by decide⟩ T77_12 (by decide)

theorem hinj77_12 : Function.Injective
    (fun i => ((T77_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK77)) :=
  repsInj_of_reduceAux rK77 T77_12 (by decide)

theorem hcardT77_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK77 ⟨12, by decide⟩ R77 hpxR77 hcardq77 (by decide)).symm

/-- **Cell (77, 12).** -/
theorem cell77_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK77) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK77) (charOfVec rK77 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK77 e (h : Coordinate 1) T77_12 i :=
  species_entry_eq_sum rK77 ⟨12, by decide⟩ e heK h T77_12 hfix77_12 hinj77_12 hcardT77_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK77) (T77_12 i) (hfix77_12 i) h)

/-! ## Cell (77, 25): |T| = 25 -/

def T77_25list : List Coordinates := [(0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0)]
def T77_25 : Fin 25 → Coordinate 1 := fun i => T77_25list.getD i.val (0,0,0,0,0)

theorem hfix77_25 : ∀ i, ((T77_25 i : Coordinate 1) : Coordinate 1 ⧸ reps rK77)
    ∈ fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77) :=
  repsFix_of_siftB rK77 ⟨25, by decide⟩ T77_25 (by decide)

theorem hinj77_25 : Function.Injective
    (fun i => ((T77_25 i : Coordinate 1) : Coordinate 1 ⧸ reps rK77)) :=
  repsInj_of_reduceAux rK77 T77_25 (by decide)

theorem hcardT77_25 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK77 ⟨25, by decide⟩ R77 hpxR77 hcardq77 (by decide)).symm

/-- **Cell (77, 25).** -/
theorem cell77_25 (e : List (ZMod 25)) (heK : charOK (basisAt rK77) e = true)
    (h : ↥(reps (⟨25, by decide⟩ : Fin 148))) :
    species (reps (⟨25, by decide⟩ : Fin 148)) h (basisElt (reps rK77) (charOfVec rK77 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK77 e (h : Coordinate 1) T77_25 i :=
  species_entry_eq_sum rK77 ⟨25, by decide⟩ e heK h T77_25 hfix77_25 hinj77_25 hcardT77_25
    (fun i => conj_mem_of_fixedPoints (reps ⟨25, by decide⟩) (reps rK77) (T77_25 i) (hfix77_25 i) h)

/-! ## Cell (77, 32): |T| = 5 -/

def T77_32list : List Coordinates := [(0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0)]
def T77_32 : Fin 5 → Coordinate 1 := fun i => T77_32list.getD i.val (0,0,0,0,0)

theorem hfix77_32 : ∀ i, ((T77_32 i : Coordinate 1) : Coordinate 1 ⧸ reps rK77)
    ∈ fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77) :=
  repsFix_of_siftB rK77 ⟨32, by decide⟩ T77_32 (by decide)

theorem hinj77_32 : Function.Injective
    (fun i => ((T77_32 i : Coordinate 1) : Coordinate 1 ⧸ reps rK77)) :=
  repsInj_of_reduceAux rK77 T77_32 (by decide)

theorem hcardT77_32 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK77 ⟨32, by decide⟩ R77 hpxR77 hcardq77 (by decide)).symm

/-- **Cell (77, 32).** -/
theorem cell77_32 (e : List (ZMod 25)) (heK : charOK (basisAt rK77) e = true)
    (h : ↥(reps (⟨32, by decide⟩ : Fin 148))) :
    species (reps (⟨32, by decide⟩ : Fin 148)) h (basisElt (reps rK77) (charOfVec rK77 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK77 e (h : Coordinate 1) T77_32 i :=
  species_entry_eq_sum rK77 ⟨32, by decide⟩ e heK h T77_32 hfix77_32 hinj77_32 hcardT77_32
    (fun i => conj_mem_of_fixedPoints (reps ⟨32, by decide⟩) (reps rK77) (T77_32 i) (hfix77_32 i) h)

/-! ## Cell (77, 37): |T| = 5 -/

def T77_37list : List Coordinates := [(0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0)]
def T77_37 : Fin 5 → Coordinate 1 := fun i => T77_37list.getD i.val (0,0,0,0,0)

theorem hfix77_37 : ∀ i, ((T77_37 i : Coordinate 1) : Coordinate 1 ⧸ reps rK77)
    ∈ fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77) :=
  repsFix_of_siftB rK77 ⟨37, by decide⟩ T77_37 (by decide)

theorem hinj77_37 : Function.Injective
    (fun i => ((T77_37 i : Coordinate 1) : Coordinate 1 ⧸ reps rK77)) :=
  repsInj_of_reduceAux rK77 T77_37 (by decide)

theorem hcardT77_37 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK77 ⟨37, by decide⟩ R77 hpxR77 hcardq77 (by decide)).symm

/-- **Cell (77, 37).** -/
theorem cell77_37 (e : List (ZMod 25)) (heK : charOK (basisAt rK77) e = true)
    (h : ↥(reps (⟨37, by decide⟩ : Fin 148))) :
    species (reps (⟨37, by decide⟩ : Fin 148)) h (basisElt (reps rK77) (charOfVec rK77 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK77 e (h : Coordinate 1) T77_37 i :=
  species_entry_eq_sum rK77 ⟨37, by decide⟩ e heK h T77_37 hfix77_37 hinj77_37 hcardT77_37
    (fun i => conj_mem_of_fixedPoints (reps ⟨37, by decide⟩) (reps rK77) (T77_37 i) (hfix77_37 i) h)

/-! ## Cell (77, 42): |T| = 5 -/

def T77_42list : List Coordinates := [(0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0)]
def T77_42 : Fin 5 → Coordinate 1 := fun i => T77_42list.getD i.val (0,0,0,0,0)

theorem hfix77_42 : ∀ i, ((T77_42 i : Coordinate 1) : Coordinate 1 ⧸ reps rK77)
    ∈ fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77) :=
  repsFix_of_siftB rK77 ⟨42, by decide⟩ T77_42 (by decide)

theorem hinj77_42 : Function.Injective
    (fun i => ((T77_42 i : Coordinate 1) : Coordinate 1 ⧸ reps rK77)) :=
  repsInj_of_reduceAux rK77 T77_42 (by decide)

theorem hcardT77_42 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK77 ⟨42, by decide⟩ R77 hpxR77 hcardq77 (by decide)).symm

/-- **Cell (77, 42).** -/
theorem cell77_42 (e : List (ZMod 25)) (heK : charOK (basisAt rK77) e = true)
    (h : ↥(reps (⟨42, by decide⟩ : Fin 148))) :
    species (reps (⟨42, by decide⟩ : Fin 148)) h (basisElt (reps rK77) (charOfVec rK77 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK77 e (h : Coordinate 1) T77_42 i :=
  species_entry_eq_sum rK77 ⟨42, by decide⟩ e heK h T77_42 hfix77_42 hinj77_42 hcardT77_42
    (fun i => conj_mem_of_fixedPoints (reps ⟨42, by decide⟩) (reps rK77) (T77_42 i) (hfix77_42 i) h)

/-! ## Cell (77, 47): |T| = 5 -/

def T77_47list : List Coordinates := [(0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0)]
def T77_47 : Fin 5 → Coordinate 1 := fun i => T77_47list.getD i.val (0,0,0,0,0)

theorem hfix77_47 : ∀ i, ((T77_47 i : Coordinate 1) : Coordinate 1 ⧸ reps rK77)
    ∈ fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77) :=
  repsFix_of_siftB rK77 ⟨47, by decide⟩ T77_47 (by decide)

theorem hinj77_47 : Function.Injective
    (fun i => ((T77_47 i : Coordinate 1) : Coordinate 1 ⧸ reps rK77)) :=
  repsInj_of_reduceAux rK77 T77_47 (by decide)

theorem hcardT77_47 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK77 ⟨47, by decide⟩ R77 hpxR77 hcardq77 (by decide)).symm

/-- **Cell (77, 47).** -/
theorem cell77_47 (e : List (ZMod 25)) (heK : charOK (basisAt rK77) e = true)
    (h : ↥(reps (⟨47, by decide⟩ : Fin 148))) :
    species (reps (⟨47, by decide⟩ : Fin 148)) h (basisElt (reps rK77) (charOfVec rK77 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK77 e (h : Coordinate 1) T77_47 i :=
  species_entry_eq_sum rK77 ⟨47, by decide⟩ e heK h T77_47 hfix77_47 hinj77_47 hcardT77_47
    (fun i => conj_mem_of_fixedPoints (reps ⟨47, by decide⟩) (reps rK77) (T77_47 i) (hfix77_47 i) h)

/-! ## Cell (77, 52): |T| = 5 -/

def T77_52list : List Coordinates := [(0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0)]
def T77_52 : Fin 5 → Coordinate 1 := fun i => T77_52list.getD i.val (0,0,0,0,0)

theorem hfix77_52 : ∀ i, ((T77_52 i : Coordinate 1) : Coordinate 1 ⧸ reps rK77)
    ∈ fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77) :=
  repsFix_of_siftB rK77 ⟨52, by decide⟩ T77_52 (by decide)

theorem hinj77_52 : Function.Injective
    (fun i => ((T77_52 i : Coordinate 1) : Coordinate 1 ⧸ reps rK77)) :=
  repsInj_of_reduceAux rK77 T77_52 (by decide)

theorem hcardT77_52 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK77 ⟨52, by decide⟩ R77 hpxR77 hcardq77 (by decide)).symm

/-- **Cell (77, 52).** -/
theorem cell77_52 (e : List (ZMod 25)) (heK : charOK (basisAt rK77) e = true)
    (h : ↥(reps (⟨52, by decide⟩ : Fin 148))) :
    species (reps (⟨52, by decide⟩ : Fin 148)) h (basisElt (reps rK77) (charOfVec rK77 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK77 e (h : Coordinate 1) T77_52 i :=
  species_entry_eq_sum rK77 ⟨52, by decide⟩ e heK h T77_52 hfix77_52 hinj77_52 hcardT77_52
    (fun i => conj_mem_of_fixedPoints (reps ⟨52, by decide⟩) (reps rK77) (T77_52 i) (hfix77_52 i) h)

/-! ## Cell (77, 77): |T| = 5 -/

def T77_77list : List Coordinates := [(0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0)]
def T77_77 : Fin 5 → Coordinate 1 := fun i => T77_77list.getD i.val (0,0,0,0,0)

theorem hfix77_77 : ∀ i, ((T77_77 i : Coordinate 1) : Coordinate 1 ⧸ reps rK77)
    ∈ fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77) :=
  repsFix_of_siftB rK77 ⟨77, by decide⟩ T77_77 (by decide)

theorem hinj77_77 : Function.Injective
    (fun i => ((T77_77 i : Coordinate 1) : Coordinate 1 ⧸ reps rK77)) :=
  repsInj_of_reduceAux rK77 T77_77 (by decide)

theorem hcardT77_77 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK77 ⟨77, by decide⟩ R77 hpxR77 hcardq77 (by decide)).symm

/-- **Cell (77, 77).** -/
theorem cell77_77 (e : List (ZMod 25)) (heK : charOK (basisAt rK77) e = true)
    (h : ↥(reps (⟨77, by decide⟩ : Fin 148))) :
    species (reps (⟨77, by decide⟩ : Fin 148)) h (basisElt (reps rK77) (charOfVec rK77 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK77 e (h : Coordinate 1) T77_77 i :=
  species_entry_eq_sum rK77 ⟨77, by decide⟩ e heK h T77_77 hfix77_77 hinj77_77 hcardT77_77
    (fun i => conj_mem_of_fixedPoints (reps ⟨77, by decide⟩) (reps rK77) (T77_77 i) (hfix77_77 i) h)

namespace Q2

def R77_2 : Fin 25 → Coordinate 2 := fun i => R77list.getD i.val (0,0,0,0,0)
theorem hpxR77_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK77) (R77_2 i)) := by decide
theorem hcardq77_2 : Nat.card (Coordinate 2 ⧸ reps rK77) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (77, 0) twin -/

def T77_0_2 : Fin 25 → Coordinate 2 := fun i => T77_0list.getD i.val (0,0,0,0,0)

theorem hfix77_0_2 : ∀ i, ((T77_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK77)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK77) :=
  repsFix_of_siftB2 rK77 ⟨0, by decide⟩ T77_0_2 (by decide)

theorem hinj77_0_2 : Function.Injective
    (fun i => ((T77_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK77)) :=
  repsInj_of_reduceAux2 rK77 T77_0_2 (by decide)

theorem hcardT77_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK77)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK77 ⟨0, by decide⟩ R77_2 hpxR77_2 hcardq77_2 (by decide)).symm

/-- **Cell (77, 0) twin (q=2).** -/
theorem cell77_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK77) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK77) (charOfVec2 rK77 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK77 e (h : Coordinate 2) T77_0_2 i :=
  species_entry_eq_sum rK77 ⟨0, by decide⟩ e heK h T77_0_2 hfix77_0_2 hinj77_0_2 hcardT77_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK77) (T77_0_2 i) (hfix77_0_2 i) h)

/-! ### Cell (77, 7) twin -/

def T77_7_2 : Fin 25 → Coordinate 2 := fun i => T77_7list.getD i.val (0,0,0,0,0)

theorem hfix77_7_2 : ∀ i, ((T77_7_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK77)
    ∈ fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK77) :=
  repsFix_of_siftB2 rK77 ⟨7, by decide⟩ T77_7_2 (by decide)

theorem hinj77_7_2 : Function.Injective
    (fun i => ((T77_7_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK77)) :=
  repsInj_of_reduceAux2 rK77 T77_7_2 (by decide)

theorem hcardT77_7_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK77)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK77 ⟨7, by decide⟩ R77_2 hpxR77_2 hcardq77_2 (by decide)).symm

/-- **Cell (77, 7) twin (q=2).** -/
theorem cell77_7_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK77) e = true)
    (h : ↥(reps (⟨7, by decide⟩ : Fin 148))) :
    species (reps (⟨7, by decide⟩ : Fin 148)) h (basisElt (reps rK77) (charOfVec2 rK77 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK77 e (h : Coordinate 2) T77_7_2 i :=
  species_entry_eq_sum rK77 ⟨7, by decide⟩ e heK h T77_7_2 hfix77_7_2 hinj77_7_2 hcardT77_7_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨7, by decide⟩) (reps rK77) (T77_7_2 i) (hfix77_7_2 i) h)

/-! ### Cell (77, 12) twin -/

def T77_12_2 : Fin 25 → Coordinate 2 := fun i => T77_12list.getD i.val (0,0,0,0,0)

theorem hfix77_12_2 : ∀ i, ((T77_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK77)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK77) :=
  repsFix_of_siftB2 rK77 ⟨12, by decide⟩ T77_12_2 (by decide)

theorem hinj77_12_2 : Function.Injective
    (fun i => ((T77_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK77)) :=
  repsInj_of_reduceAux2 rK77 T77_12_2 (by decide)

theorem hcardT77_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK77)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK77 ⟨12, by decide⟩ R77_2 hpxR77_2 hcardq77_2 (by decide)).symm

/-- **Cell (77, 12) twin (q=2).** -/
theorem cell77_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK77) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK77) (charOfVec2 rK77 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK77 e (h : Coordinate 2) T77_12_2 i :=
  species_entry_eq_sum rK77 ⟨12, by decide⟩ e heK h T77_12_2 hfix77_12_2 hinj77_12_2 hcardT77_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK77) (T77_12_2 i) (hfix77_12_2 i) h)

/-! ### Cell (77, 25) twin -/

def T77_25_2 : Fin 25 → Coordinate 2 := fun i => T77_25list.getD i.val (0,0,0,0,0)

theorem hfix77_25_2 : ∀ i, ((T77_25_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK77)
    ∈ fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK77) :=
  repsFix_of_siftB2 rK77 ⟨25, by decide⟩ T77_25_2 (by decide)

theorem hinj77_25_2 : Function.Injective
    (fun i => ((T77_25_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK77)) :=
  repsInj_of_reduceAux2 rK77 T77_25_2 (by decide)

theorem hcardT77_25_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK77)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK77 ⟨25, by decide⟩ R77_2 hpxR77_2 hcardq77_2 (by decide)).symm

/-- **Cell (77, 25) twin (q=2).** -/
theorem cell77_25_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK77) e = true)
    (h : ↥(reps (⟨25, by decide⟩ : Fin 148))) :
    species (reps (⟨25, by decide⟩ : Fin 148)) h (basisElt (reps rK77) (charOfVec2 rK77 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK77 e (h : Coordinate 2) T77_25_2 i :=
  species_entry_eq_sum rK77 ⟨25, by decide⟩ e heK h T77_25_2 hfix77_25_2 hinj77_25_2 hcardT77_25_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨25, by decide⟩) (reps rK77) (T77_25_2 i) (hfix77_25_2 i) h)

/-! ### Cell (77, 32) twin -/

def T77_32_2 : Fin 5 → Coordinate 2 := fun i => T77_32list.getD i.val (0,0,0,0,0)

theorem hfix77_32_2 : ∀ i, ((T77_32_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK77)
    ∈ fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK77) :=
  repsFix_of_siftB2 rK77 ⟨32, by decide⟩ T77_32_2 (by decide)

theorem hinj77_32_2 : Function.Injective
    (fun i => ((T77_32_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK77)) :=
  repsInj_of_reduceAux2 rK77 T77_32_2 (by decide)

theorem hcardT77_32_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK77)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK77 ⟨32, by decide⟩ R77_2 hpxR77_2 hcardq77_2 (by decide)).symm

/-- **Cell (77, 32) twin (q=2).** -/
theorem cell77_32_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK77) e = true)
    (h : ↥(reps (⟨32, by decide⟩ : Fin 148))) :
    species (reps (⟨32, by decide⟩ : Fin 148)) h (basisElt (reps rK77) (charOfVec2 rK77 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK77 e (h : Coordinate 2) T77_32_2 i :=
  species_entry_eq_sum rK77 ⟨32, by decide⟩ e heK h T77_32_2 hfix77_32_2 hinj77_32_2 hcardT77_32_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨32, by decide⟩) (reps rK77) (T77_32_2 i) (hfix77_32_2 i) h)

/-! ### Cell (77, 37) twin -/

def T77_37_2 : Fin 5 → Coordinate 2 := fun i => T77_37list.getD i.val (0,0,0,0,0)

theorem hfix77_37_2 : ∀ i, ((T77_37_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK77)
    ∈ fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK77) :=
  repsFix_of_siftB2 rK77 ⟨37, by decide⟩ T77_37_2 (by decide)

theorem hinj77_37_2 : Function.Injective
    (fun i => ((T77_37_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK77)) :=
  repsInj_of_reduceAux2 rK77 T77_37_2 (by decide)

theorem hcardT77_37_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK77)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK77 ⟨37, by decide⟩ R77_2 hpxR77_2 hcardq77_2 (by decide)).symm

/-- **Cell (77, 37) twin (q=2).** -/
theorem cell77_37_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK77) e = true)
    (h : ↥(reps (⟨37, by decide⟩ : Fin 148))) :
    species (reps (⟨37, by decide⟩ : Fin 148)) h (basisElt (reps rK77) (charOfVec2 rK77 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK77 e (h : Coordinate 2) T77_37_2 i :=
  species_entry_eq_sum rK77 ⟨37, by decide⟩ e heK h T77_37_2 hfix77_37_2 hinj77_37_2 hcardT77_37_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨37, by decide⟩) (reps rK77) (T77_37_2 i) (hfix77_37_2 i) h)

/-! ### Cell (77, 42) twin -/

def T77_42_2 : Fin 5 → Coordinate 2 := fun i => T77_42list.getD i.val (0,0,0,0,0)

theorem hfix77_42_2 : ∀ i, ((T77_42_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK77)
    ∈ fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK77) :=
  repsFix_of_siftB2 rK77 ⟨42, by decide⟩ T77_42_2 (by decide)

theorem hinj77_42_2 : Function.Injective
    (fun i => ((T77_42_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK77)) :=
  repsInj_of_reduceAux2 rK77 T77_42_2 (by decide)

theorem hcardT77_42_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK77)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK77 ⟨42, by decide⟩ R77_2 hpxR77_2 hcardq77_2 (by decide)).symm

/-- **Cell (77, 42) twin (q=2).** -/
theorem cell77_42_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK77) e = true)
    (h : ↥(reps (⟨42, by decide⟩ : Fin 148))) :
    species (reps (⟨42, by decide⟩ : Fin 148)) h (basisElt (reps rK77) (charOfVec2 rK77 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK77 e (h : Coordinate 2) T77_42_2 i :=
  species_entry_eq_sum rK77 ⟨42, by decide⟩ e heK h T77_42_2 hfix77_42_2 hinj77_42_2 hcardT77_42_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨42, by decide⟩) (reps rK77) (T77_42_2 i) (hfix77_42_2 i) h)

/-! ### Cell (77, 47) twin -/

def T77_47_2 : Fin 5 → Coordinate 2 := fun i => T77_47list.getD i.val (0,0,0,0,0)

theorem hfix77_47_2 : ∀ i, ((T77_47_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK77)
    ∈ fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK77) :=
  repsFix_of_siftB2 rK77 ⟨47, by decide⟩ T77_47_2 (by decide)

theorem hinj77_47_2 : Function.Injective
    (fun i => ((T77_47_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK77)) :=
  repsInj_of_reduceAux2 rK77 T77_47_2 (by decide)

theorem hcardT77_47_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK77)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK77 ⟨47, by decide⟩ R77_2 hpxR77_2 hcardq77_2 (by decide)).symm

/-- **Cell (77, 47) twin (q=2).** -/
theorem cell77_47_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK77) e = true)
    (h : ↥(reps (⟨47, by decide⟩ : Fin 148))) :
    species (reps (⟨47, by decide⟩ : Fin 148)) h (basisElt (reps rK77) (charOfVec2 rK77 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK77 e (h : Coordinate 2) T77_47_2 i :=
  species_entry_eq_sum rK77 ⟨47, by decide⟩ e heK h T77_47_2 hfix77_47_2 hinj77_47_2 hcardT77_47_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨47, by decide⟩) (reps rK77) (T77_47_2 i) (hfix77_47_2 i) h)

/-! ### Cell (77, 52) twin -/

def T77_52_2 : Fin 5 → Coordinate 2 := fun i => T77_52list.getD i.val (0,0,0,0,0)

theorem hfix77_52_2 : ∀ i, ((T77_52_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK77)
    ∈ fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK77) :=
  repsFix_of_siftB2 rK77 ⟨52, by decide⟩ T77_52_2 (by decide)

theorem hinj77_52_2 : Function.Injective
    (fun i => ((T77_52_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK77)) :=
  repsInj_of_reduceAux2 rK77 T77_52_2 (by decide)

theorem hcardT77_52_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK77)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK77 ⟨52, by decide⟩ R77_2 hpxR77_2 hcardq77_2 (by decide)).symm

/-- **Cell (77, 52) twin (q=2).** -/
theorem cell77_52_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK77) e = true)
    (h : ↥(reps (⟨52, by decide⟩ : Fin 148))) :
    species (reps (⟨52, by decide⟩ : Fin 148)) h (basisElt (reps rK77) (charOfVec2 rK77 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK77 e (h : Coordinate 2) T77_52_2 i :=
  species_entry_eq_sum rK77 ⟨52, by decide⟩ e heK h T77_52_2 hfix77_52_2 hinj77_52_2 hcardT77_52_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨52, by decide⟩) (reps rK77) (T77_52_2 i) (hfix77_52_2 i) h)

/-! ### Cell (77, 77) twin -/

def T77_77_2 : Fin 5 → Coordinate 2 := fun i => T77_77list.getD i.val (0,0,0,0,0)

theorem hfix77_77_2 : ∀ i, ((T77_77_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK77)
    ∈ fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK77) :=
  repsFix_of_siftB2 rK77 ⟨77, by decide⟩ T77_77_2 (by decide)

theorem hinj77_77_2 : Function.Injective
    (fun i => ((T77_77_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK77)) :=
  repsInj_of_reduceAux2 rK77 T77_77_2 (by decide)

theorem hcardT77_77_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK77)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK77 ⟨77, by decide⟩ R77_2 hpxR77_2 hcardq77_2 (by decide)).symm

/-- **Cell (77, 77) twin (q=2).** -/
theorem cell77_77_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK77) e = true)
    (h : ↥(reps (⟨77, by decide⟩ : Fin 148))) :
    species (reps (⟨77, by decide⟩ : Fin 148)) h (basisElt (reps rK77) (charOfVec2 rK77 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK77 e (h : Coordinate 2) T77_77_2 i :=
  species_entry_eq_sum rK77 ⟨77, by decide⟩ e heK h T77_77_2 hfix77_77_2 hinj77_77_2 hcardT77_77_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨77, by decide⟩) (reps rK77) (T77_77_2 i) (hfix77_77_2 i) h)

end Q2

/-! # K-class rK = 78  (|G/K| = 25) -/

def rK78 : Fin 148 := ⟨78, by decide⟩

def R78list : List Coordinates := [(0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0)]
def R78 : Fin 25 → Coordinate 1 := fun i => R78list.getD i.val (0,0,0,0,0)

theorem hpxR78 : Function.Injective (fun i => reduceAux 1 (basisAt rK78) (R78 i)) := by decide
theorem hcardq78 : Nat.card (Coordinate 1 ⧸ reps rK78) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (78, 0): |T| = 25 -/

def T78_0list : List Coordinates := [(0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0)]
def T78_0 : Fin 25 → Coordinate 1 := fun i => T78_0list.getD i.val (0,0,0,0,0)

theorem hfix78_0 : ∀ i, ((T78_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK78)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78) :=
  repsFix_of_siftB rK78 ⟨0, by decide⟩ T78_0 (by decide)

theorem hinj78_0 : Function.Injective
    (fun i => ((T78_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK78)) :=
  repsInj_of_reduceAux rK78 T78_0 (by decide)

theorem hcardT78_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK78 ⟨0, by decide⟩ R78 hpxR78 hcardq78 (by decide)).symm

/-- **Cell (78, 0).** -/
theorem cell78_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK78) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK78) (charOfVec rK78 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK78 e (h : Coordinate 1) T78_0 i :=
  species_entry_eq_sum rK78 ⟨0, by decide⟩ e heK h T78_0 hfix78_0 hinj78_0 hcardT78_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK78) (T78_0 i) (hfix78_0 i) h)

/-! ## Cell (78, 6): |T| = 25 -/

def T78_6list : List Coordinates := [(0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0)]
def T78_6 : Fin 25 → Coordinate 1 := fun i => T78_6list.getD i.val (0,0,0,0,0)

theorem hfix78_6 : ∀ i, ((T78_6 i : Coordinate 1) : Coordinate 1 ⧸ reps rK78)
    ∈ fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78) :=
  repsFix_of_siftB rK78 ⟨6, by decide⟩ T78_6 (by decide)

theorem hinj78_6 : Function.Injective
    (fun i => ((T78_6 i : Coordinate 1) : Coordinate 1 ⧸ reps rK78)) :=
  repsInj_of_reduceAux rK78 T78_6 (by decide)

theorem hcardT78_6 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK78 ⟨6, by decide⟩ R78 hpxR78 hcardq78 (by decide)).symm

/-- **Cell (78, 6).** -/
theorem cell78_6 (e : List (ZMod 25)) (heK : charOK (basisAt rK78) e = true)
    (h : ↥(reps (⟨6, by decide⟩ : Fin 148))) :
    species (reps (⟨6, by decide⟩ : Fin 148)) h (basisElt (reps rK78) (charOfVec rK78 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK78 e (h : Coordinate 1) T78_6 i :=
  species_entry_eq_sum rK78 ⟨6, by decide⟩ e heK h T78_6 hfix78_6 hinj78_6 hcardT78_6
    (fun i => conj_mem_of_fixedPoints (reps ⟨6, by decide⟩) (reps rK78) (T78_6 i) (hfix78_6 i) h)

/-! ## Cell (78, 12): |T| = 25 -/

def T78_12list : List Coordinates := [(0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0)]
def T78_12 : Fin 25 → Coordinate 1 := fun i => T78_12list.getD i.val (0,0,0,0,0)

theorem hfix78_12 : ∀ i, ((T78_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK78)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78) :=
  repsFix_of_siftB rK78 ⟨12, by decide⟩ T78_12 (by decide)

theorem hinj78_12 : Function.Injective
    (fun i => ((T78_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK78)) :=
  repsInj_of_reduceAux rK78 T78_12 (by decide)

theorem hcardT78_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK78 ⟨12, by decide⟩ R78 hpxR78 hcardq78 (by decide)).symm

/-- **Cell (78, 12).** -/
theorem cell78_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK78) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK78) (charOfVec rK78 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK78 e (h : Coordinate 1) T78_12 i :=
  species_entry_eq_sum rK78 ⟨12, by decide⟩ e heK h T78_12 hfix78_12 hinj78_12 hcardT78_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK78) (T78_12 i) (hfix78_12 i) h)

/-! ## Cell (78, 24): |T| = 25 -/

def T78_24list : List Coordinates := [(0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0)]
def T78_24 : Fin 25 → Coordinate 1 := fun i => T78_24list.getD i.val (0,0,0,0,0)

theorem hfix78_24 : ∀ i, ((T78_24 i : Coordinate 1) : Coordinate 1 ⧸ reps rK78)
    ∈ fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78) :=
  repsFix_of_siftB rK78 ⟨24, by decide⟩ T78_24 (by decide)

theorem hinj78_24 : Function.Injective
    (fun i => ((T78_24 i : Coordinate 1) : Coordinate 1 ⧸ reps rK78)) :=
  repsInj_of_reduceAux rK78 T78_24 (by decide)

theorem hcardT78_24 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK78 ⟨24, by decide⟩ R78 hpxR78 hcardq78 (by decide)).symm

/-- **Cell (78, 24).** -/
theorem cell78_24 (e : List (ZMod 25)) (heK : charOK (basisAt rK78) e = true)
    (h : ↥(reps (⟨24, by decide⟩ : Fin 148))) :
    species (reps (⟨24, by decide⟩ : Fin 148)) h (basisElt (reps rK78) (charOfVec rK78 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK78 e (h : Coordinate 1) T78_24 i :=
  species_entry_eq_sum rK78 ⟨24, by decide⟩ e heK h T78_24 hfix78_24 hinj78_24 hcardT78_24
    (fun i => conj_mem_of_fixedPoints (reps ⟨24, by decide⟩) (reps rK78) (T78_24 i) (hfix78_24 i) h)

/-! ## Cell (78, 32): |T| = 5 -/

def T78_32list : List Coordinates := [(0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0)]
def T78_32 : Fin 5 → Coordinate 1 := fun i => T78_32list.getD i.val (0,0,0,0,0)

theorem hfix78_32 : ∀ i, ((T78_32 i : Coordinate 1) : Coordinate 1 ⧸ reps rK78)
    ∈ fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78) :=
  repsFix_of_siftB rK78 ⟨32, by decide⟩ T78_32 (by decide)

theorem hinj78_32 : Function.Injective
    (fun i => ((T78_32 i : Coordinate 1) : Coordinate 1 ⧸ reps rK78)) :=
  repsInj_of_reduceAux rK78 T78_32 (by decide)

theorem hcardT78_32 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK78 ⟨32, by decide⟩ R78 hpxR78 hcardq78 (by decide)).symm

/-- **Cell (78, 32).** -/
theorem cell78_32 (e : List (ZMod 25)) (heK : charOK (basisAt rK78) e = true)
    (h : ↥(reps (⟨32, by decide⟩ : Fin 148))) :
    species (reps (⟨32, by decide⟩ : Fin 148)) h (basisElt (reps rK78) (charOfVec rK78 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK78 e (h : Coordinate 1) T78_32 i :=
  species_entry_eq_sum rK78 ⟨32, by decide⟩ e heK h T78_32 hfix78_32 hinj78_32 hcardT78_32
    (fun i => conj_mem_of_fixedPoints (reps ⟨32, by decide⟩) (reps rK78) (T78_32 i) (hfix78_32 i) h)

/-! ## Cell (78, 37): |T| = 5 -/

def T78_37list : List Coordinates := [(0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0)]
def T78_37 : Fin 5 → Coordinate 1 := fun i => T78_37list.getD i.val (0,0,0,0,0)

theorem hfix78_37 : ∀ i, ((T78_37 i : Coordinate 1) : Coordinate 1 ⧸ reps rK78)
    ∈ fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78) :=
  repsFix_of_siftB rK78 ⟨37, by decide⟩ T78_37 (by decide)

theorem hinj78_37 : Function.Injective
    (fun i => ((T78_37 i : Coordinate 1) : Coordinate 1 ⧸ reps rK78)) :=
  repsInj_of_reduceAux rK78 T78_37 (by decide)

theorem hcardT78_37 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK78 ⟨37, by decide⟩ R78 hpxR78 hcardq78 (by decide)).symm

/-- **Cell (78, 37).** -/
theorem cell78_37 (e : List (ZMod 25)) (heK : charOK (basisAt rK78) e = true)
    (h : ↥(reps (⟨37, by decide⟩ : Fin 148))) :
    species (reps (⟨37, by decide⟩ : Fin 148)) h (basisElt (reps rK78) (charOfVec rK78 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK78 e (h : Coordinate 1) T78_37 i :=
  species_entry_eq_sum rK78 ⟨37, by decide⟩ e heK h T78_37 hfix78_37 hinj78_37 hcardT78_37
    (fun i => conj_mem_of_fixedPoints (reps ⟨37, by decide⟩) (reps rK78) (T78_37 i) (hfix78_37 i) h)

/-! ## Cell (78, 42): |T| = 5 -/

def T78_42list : List Coordinates := [(0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0)]
def T78_42 : Fin 5 → Coordinate 1 := fun i => T78_42list.getD i.val (0,0,0,0,0)

theorem hfix78_42 : ∀ i, ((T78_42 i : Coordinate 1) : Coordinate 1 ⧸ reps rK78)
    ∈ fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78) :=
  repsFix_of_siftB rK78 ⟨42, by decide⟩ T78_42 (by decide)

theorem hinj78_42 : Function.Injective
    (fun i => ((T78_42 i : Coordinate 1) : Coordinate 1 ⧸ reps rK78)) :=
  repsInj_of_reduceAux rK78 T78_42 (by decide)

theorem hcardT78_42 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK78 ⟨42, by decide⟩ R78 hpxR78 hcardq78 (by decide)).symm

/-- **Cell (78, 42).** -/
theorem cell78_42 (e : List (ZMod 25)) (heK : charOK (basisAt rK78) e = true)
    (h : ↥(reps (⟨42, by decide⟩ : Fin 148))) :
    species (reps (⟨42, by decide⟩ : Fin 148)) h (basisElt (reps rK78) (charOfVec rK78 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK78 e (h : Coordinate 1) T78_42 i :=
  species_entry_eq_sum rK78 ⟨42, by decide⟩ e heK h T78_42 hfix78_42 hinj78_42 hcardT78_42
    (fun i => conj_mem_of_fixedPoints (reps ⟨42, by decide⟩) (reps rK78) (T78_42 i) (hfix78_42 i) h)

/-! ## Cell (78, 47): |T| = 5 -/

def T78_47list : List Coordinates := [(0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0)]
def T78_47 : Fin 5 → Coordinate 1 := fun i => T78_47list.getD i.val (0,0,0,0,0)

theorem hfix78_47 : ∀ i, ((T78_47 i : Coordinate 1) : Coordinate 1 ⧸ reps rK78)
    ∈ fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78) :=
  repsFix_of_siftB rK78 ⟨47, by decide⟩ T78_47 (by decide)

theorem hinj78_47 : Function.Injective
    (fun i => ((T78_47 i : Coordinate 1) : Coordinate 1 ⧸ reps rK78)) :=
  repsInj_of_reduceAux rK78 T78_47 (by decide)

theorem hcardT78_47 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK78 ⟨47, by decide⟩ R78 hpxR78 hcardq78 (by decide)).symm

/-- **Cell (78, 47).** -/
theorem cell78_47 (e : List (ZMod 25)) (heK : charOK (basisAt rK78) e = true)
    (h : ↥(reps (⟨47, by decide⟩ : Fin 148))) :
    species (reps (⟨47, by decide⟩ : Fin 148)) h (basisElt (reps rK78) (charOfVec rK78 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK78 e (h : Coordinate 1) T78_47 i :=
  species_entry_eq_sum rK78 ⟨47, by decide⟩ e heK h T78_47 hfix78_47 hinj78_47 hcardT78_47
    (fun i => conj_mem_of_fixedPoints (reps ⟨47, by decide⟩) (reps rK78) (T78_47 i) (hfix78_47 i) h)

/-! ## Cell (78, 52): |T| = 5 -/

def T78_52list : List Coordinates := [(0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0)]
def T78_52 : Fin 5 → Coordinate 1 := fun i => T78_52list.getD i.val (0,0,0,0,0)

theorem hfix78_52 : ∀ i, ((T78_52 i : Coordinate 1) : Coordinate 1 ⧸ reps rK78)
    ∈ fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78) :=
  repsFix_of_siftB rK78 ⟨52, by decide⟩ T78_52 (by decide)

theorem hinj78_52 : Function.Injective
    (fun i => ((T78_52 i : Coordinate 1) : Coordinate 1 ⧸ reps rK78)) :=
  repsInj_of_reduceAux rK78 T78_52 (by decide)

theorem hcardT78_52 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK78 ⟨52, by decide⟩ R78 hpxR78 hcardq78 (by decide)).symm

/-- **Cell (78, 52).** -/
theorem cell78_52 (e : List (ZMod 25)) (heK : charOK (basisAt rK78) e = true)
    (h : ↥(reps (⟨52, by decide⟩ : Fin 148))) :
    species (reps (⟨52, by decide⟩ : Fin 148)) h (basisElt (reps rK78) (charOfVec rK78 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK78 e (h : Coordinate 1) T78_52 i :=
  species_entry_eq_sum rK78 ⟨52, by decide⟩ e heK h T78_52 hfix78_52 hinj78_52 hcardT78_52
    (fun i => conj_mem_of_fixedPoints (reps ⟨52, by decide⟩) (reps rK78) (T78_52 i) (hfix78_52 i) h)

/-! ## Cell (78, 78): |T| = 5 -/

def T78_78list : List Coordinates := [(0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0)]
def T78_78 : Fin 5 → Coordinate 1 := fun i => T78_78list.getD i.val (0,0,0,0,0)

theorem hfix78_78 : ∀ i, ((T78_78 i : Coordinate 1) : Coordinate 1 ⧸ reps rK78)
    ∈ fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78) :=
  repsFix_of_siftB rK78 ⟨78, by decide⟩ T78_78 (by decide)

theorem hinj78_78 : Function.Injective
    (fun i => ((T78_78 i : Coordinate 1) : Coordinate 1 ⧸ reps rK78)) :=
  repsInj_of_reduceAux rK78 T78_78 (by decide)

theorem hcardT78_78 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK78 ⟨78, by decide⟩ R78 hpxR78 hcardq78 (by decide)).symm

/-- **Cell (78, 78).** -/
theorem cell78_78 (e : List (ZMod 25)) (heK : charOK (basisAt rK78) e = true)
    (h : ↥(reps (⟨78, by decide⟩ : Fin 148))) :
    species (reps (⟨78, by decide⟩ : Fin 148)) h (basisElt (reps rK78) (charOfVec rK78 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK78 e (h : Coordinate 1) T78_78 i :=
  species_entry_eq_sum rK78 ⟨78, by decide⟩ e heK h T78_78 hfix78_78 hinj78_78 hcardT78_78
    (fun i => conj_mem_of_fixedPoints (reps ⟨78, by decide⟩) (reps rK78) (T78_78 i) (hfix78_78 i) h)

namespace Q2

def R78_2 : Fin 25 → Coordinate 2 := fun i => R78list.getD i.val (0,0,0,0,0)
theorem hpxR78_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK78) (R78_2 i)) := by decide
theorem hcardq78_2 : Nat.card (Coordinate 2 ⧸ reps rK78) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (78, 0) twin -/

def T78_0_2 : Fin 25 → Coordinate 2 := fun i => T78_0list.getD i.val (0,0,0,0,0)

theorem hfix78_0_2 : ∀ i, ((T78_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK78)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK78) :=
  repsFix_of_siftB2 rK78 ⟨0, by decide⟩ T78_0_2 (by decide)

theorem hinj78_0_2 : Function.Injective
    (fun i => ((T78_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK78)) :=
  repsInj_of_reduceAux2 rK78 T78_0_2 (by decide)

theorem hcardT78_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK78)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK78 ⟨0, by decide⟩ R78_2 hpxR78_2 hcardq78_2 (by decide)).symm

/-- **Cell (78, 0) twin (q=2).** -/
theorem cell78_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK78) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK78) (charOfVec2 rK78 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK78 e (h : Coordinate 2) T78_0_2 i :=
  species_entry_eq_sum rK78 ⟨0, by decide⟩ e heK h T78_0_2 hfix78_0_2 hinj78_0_2 hcardT78_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK78) (T78_0_2 i) (hfix78_0_2 i) h)

/-! ### Cell (78, 6) twin -/

def T78_6_2 : Fin 25 → Coordinate 2 := fun i => T78_6list.getD i.val (0,0,0,0,0)

theorem hfix78_6_2 : ∀ i, ((T78_6_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK78)
    ∈ fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK78) :=
  repsFix_of_siftB2 rK78 ⟨6, by decide⟩ T78_6_2 (by decide)

theorem hinj78_6_2 : Function.Injective
    (fun i => ((T78_6_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK78)) :=
  repsInj_of_reduceAux2 rK78 T78_6_2 (by decide)

theorem hcardT78_6_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK78)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK78 ⟨6, by decide⟩ R78_2 hpxR78_2 hcardq78_2 (by decide)).symm

/-- **Cell (78, 6) twin (q=2).** -/
theorem cell78_6_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK78) e = true)
    (h : ↥(reps (⟨6, by decide⟩ : Fin 148))) :
    species (reps (⟨6, by decide⟩ : Fin 148)) h (basisElt (reps rK78) (charOfVec2 rK78 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK78 e (h : Coordinate 2) T78_6_2 i :=
  species_entry_eq_sum rK78 ⟨6, by decide⟩ e heK h T78_6_2 hfix78_6_2 hinj78_6_2 hcardT78_6_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨6, by decide⟩) (reps rK78) (T78_6_2 i) (hfix78_6_2 i) h)

/-! ### Cell (78, 12) twin -/

def T78_12_2 : Fin 25 → Coordinate 2 := fun i => T78_12list.getD i.val (0,0,0,0,0)

theorem hfix78_12_2 : ∀ i, ((T78_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK78)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK78) :=
  repsFix_of_siftB2 rK78 ⟨12, by decide⟩ T78_12_2 (by decide)

theorem hinj78_12_2 : Function.Injective
    (fun i => ((T78_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK78)) :=
  repsInj_of_reduceAux2 rK78 T78_12_2 (by decide)

theorem hcardT78_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK78)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK78 ⟨12, by decide⟩ R78_2 hpxR78_2 hcardq78_2 (by decide)).symm

/-- **Cell (78, 12) twin (q=2).** -/
theorem cell78_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK78) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK78) (charOfVec2 rK78 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK78 e (h : Coordinate 2) T78_12_2 i :=
  species_entry_eq_sum rK78 ⟨12, by decide⟩ e heK h T78_12_2 hfix78_12_2 hinj78_12_2 hcardT78_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK78) (T78_12_2 i) (hfix78_12_2 i) h)

/-! ### Cell (78, 24) twin -/

def T78_24_2 : Fin 25 → Coordinate 2 := fun i => T78_24list.getD i.val (0,0,0,0,0)

theorem hfix78_24_2 : ∀ i, ((T78_24_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK78)
    ∈ fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK78) :=
  repsFix_of_siftB2 rK78 ⟨24, by decide⟩ T78_24_2 (by decide)

theorem hinj78_24_2 : Function.Injective
    (fun i => ((T78_24_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK78)) :=
  repsInj_of_reduceAux2 rK78 T78_24_2 (by decide)

theorem hcardT78_24_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK78)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK78 ⟨24, by decide⟩ R78_2 hpxR78_2 hcardq78_2 (by decide)).symm

/-- **Cell (78, 24) twin (q=2).** -/
theorem cell78_24_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK78) e = true)
    (h : ↥(reps (⟨24, by decide⟩ : Fin 148))) :
    species (reps (⟨24, by decide⟩ : Fin 148)) h (basisElt (reps rK78) (charOfVec2 rK78 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK78 e (h : Coordinate 2) T78_24_2 i :=
  species_entry_eq_sum rK78 ⟨24, by decide⟩ e heK h T78_24_2 hfix78_24_2 hinj78_24_2 hcardT78_24_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨24, by decide⟩) (reps rK78) (T78_24_2 i) (hfix78_24_2 i) h)

/-! ### Cell (78, 32) twin -/

def T78_32_2 : Fin 5 → Coordinate 2 := fun i => T78_32list.getD i.val (0,0,0,0,0)

theorem hfix78_32_2 : ∀ i, ((T78_32_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK78)
    ∈ fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK78) :=
  repsFix_of_siftB2 rK78 ⟨32, by decide⟩ T78_32_2 (by decide)

theorem hinj78_32_2 : Function.Injective
    (fun i => ((T78_32_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK78)) :=
  repsInj_of_reduceAux2 rK78 T78_32_2 (by decide)

theorem hcardT78_32_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK78)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK78 ⟨32, by decide⟩ R78_2 hpxR78_2 hcardq78_2 (by decide)).symm

/-- **Cell (78, 32) twin (q=2).** -/
theorem cell78_32_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK78) e = true)
    (h : ↥(reps (⟨32, by decide⟩ : Fin 148))) :
    species (reps (⟨32, by decide⟩ : Fin 148)) h (basisElt (reps rK78) (charOfVec2 rK78 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK78 e (h : Coordinate 2) T78_32_2 i :=
  species_entry_eq_sum rK78 ⟨32, by decide⟩ e heK h T78_32_2 hfix78_32_2 hinj78_32_2 hcardT78_32_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨32, by decide⟩) (reps rK78) (T78_32_2 i) (hfix78_32_2 i) h)

/-! ### Cell (78, 37) twin -/

def T78_37_2 : Fin 5 → Coordinate 2 := fun i => T78_37list.getD i.val (0,0,0,0,0)

theorem hfix78_37_2 : ∀ i, ((T78_37_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK78)
    ∈ fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK78) :=
  repsFix_of_siftB2 rK78 ⟨37, by decide⟩ T78_37_2 (by decide)

theorem hinj78_37_2 : Function.Injective
    (fun i => ((T78_37_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK78)) :=
  repsInj_of_reduceAux2 rK78 T78_37_2 (by decide)

theorem hcardT78_37_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK78)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK78 ⟨37, by decide⟩ R78_2 hpxR78_2 hcardq78_2 (by decide)).symm

/-- **Cell (78, 37) twin (q=2).** -/
theorem cell78_37_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK78) e = true)
    (h : ↥(reps (⟨37, by decide⟩ : Fin 148))) :
    species (reps (⟨37, by decide⟩ : Fin 148)) h (basisElt (reps rK78) (charOfVec2 rK78 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK78 e (h : Coordinate 2) T78_37_2 i :=
  species_entry_eq_sum rK78 ⟨37, by decide⟩ e heK h T78_37_2 hfix78_37_2 hinj78_37_2 hcardT78_37_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨37, by decide⟩) (reps rK78) (T78_37_2 i) (hfix78_37_2 i) h)

/-! ### Cell (78, 42) twin -/

def T78_42_2 : Fin 5 → Coordinate 2 := fun i => T78_42list.getD i.val (0,0,0,0,0)

theorem hfix78_42_2 : ∀ i, ((T78_42_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK78)
    ∈ fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK78) :=
  repsFix_of_siftB2 rK78 ⟨42, by decide⟩ T78_42_2 (by decide)

theorem hinj78_42_2 : Function.Injective
    (fun i => ((T78_42_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK78)) :=
  repsInj_of_reduceAux2 rK78 T78_42_2 (by decide)

theorem hcardT78_42_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK78)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK78 ⟨42, by decide⟩ R78_2 hpxR78_2 hcardq78_2 (by decide)).symm

/-- **Cell (78, 42) twin (q=2).** -/
theorem cell78_42_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK78) e = true)
    (h : ↥(reps (⟨42, by decide⟩ : Fin 148))) :
    species (reps (⟨42, by decide⟩ : Fin 148)) h (basisElt (reps rK78) (charOfVec2 rK78 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK78 e (h : Coordinate 2) T78_42_2 i :=
  species_entry_eq_sum rK78 ⟨42, by decide⟩ e heK h T78_42_2 hfix78_42_2 hinj78_42_2 hcardT78_42_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨42, by decide⟩) (reps rK78) (T78_42_2 i) (hfix78_42_2 i) h)

/-! ### Cell (78, 47) twin -/

def T78_47_2 : Fin 5 → Coordinate 2 := fun i => T78_47list.getD i.val (0,0,0,0,0)

theorem hfix78_47_2 : ∀ i, ((T78_47_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK78)
    ∈ fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK78) :=
  repsFix_of_siftB2 rK78 ⟨47, by decide⟩ T78_47_2 (by decide)

theorem hinj78_47_2 : Function.Injective
    (fun i => ((T78_47_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK78)) :=
  repsInj_of_reduceAux2 rK78 T78_47_2 (by decide)

theorem hcardT78_47_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK78)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK78 ⟨47, by decide⟩ R78_2 hpxR78_2 hcardq78_2 (by decide)).symm

/-- **Cell (78, 47) twin (q=2).** -/
theorem cell78_47_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK78) e = true)
    (h : ↥(reps (⟨47, by decide⟩ : Fin 148))) :
    species (reps (⟨47, by decide⟩ : Fin 148)) h (basisElt (reps rK78) (charOfVec2 rK78 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK78 e (h : Coordinate 2) T78_47_2 i :=
  species_entry_eq_sum rK78 ⟨47, by decide⟩ e heK h T78_47_2 hfix78_47_2 hinj78_47_2 hcardT78_47_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨47, by decide⟩) (reps rK78) (T78_47_2 i) (hfix78_47_2 i) h)

/-! ### Cell (78, 52) twin -/

def T78_52_2 : Fin 5 → Coordinate 2 := fun i => T78_52list.getD i.val (0,0,0,0,0)

theorem hfix78_52_2 : ∀ i, ((T78_52_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK78)
    ∈ fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK78) :=
  repsFix_of_siftB2 rK78 ⟨52, by decide⟩ T78_52_2 (by decide)

theorem hinj78_52_2 : Function.Injective
    (fun i => ((T78_52_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK78)) :=
  repsInj_of_reduceAux2 rK78 T78_52_2 (by decide)

theorem hcardT78_52_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK78)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK78 ⟨52, by decide⟩ R78_2 hpxR78_2 hcardq78_2 (by decide)).symm

/-- **Cell (78, 52) twin (q=2).** -/
theorem cell78_52_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK78) e = true)
    (h : ↥(reps (⟨52, by decide⟩ : Fin 148))) :
    species (reps (⟨52, by decide⟩ : Fin 148)) h (basisElt (reps rK78) (charOfVec2 rK78 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK78 e (h : Coordinate 2) T78_52_2 i :=
  species_entry_eq_sum rK78 ⟨52, by decide⟩ e heK h T78_52_2 hfix78_52_2 hinj78_52_2 hcardT78_52_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨52, by decide⟩) (reps rK78) (T78_52_2 i) (hfix78_52_2 i) h)

/-! ### Cell (78, 78) twin -/

def T78_78_2 : Fin 5 → Coordinate 2 := fun i => T78_78list.getD i.val (0,0,0,0,0)

theorem hfix78_78_2 : ∀ i, ((T78_78_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK78)
    ∈ fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK78) :=
  repsFix_of_siftB2 rK78 ⟨78, by decide⟩ T78_78_2 (by decide)

theorem hinj78_78_2 : Function.Injective
    (fun i => ((T78_78_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK78)) :=
  repsInj_of_reduceAux2 rK78 T78_78_2 (by decide)

theorem hcardT78_78_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK78)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK78 ⟨78, by decide⟩ R78_2 hpxR78_2 hcardq78_2 (by decide)).symm

/-- **Cell (78, 78) twin (q=2).** -/
theorem cell78_78_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK78) e = true)
    (h : ↥(reps (⟨78, by decide⟩ : Fin 148))) :
    species (reps (⟨78, by decide⟩ : Fin 148)) h (basisElt (reps rK78) (charOfVec2 rK78 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK78 e (h : Coordinate 2) T78_78_2 i :=
  species_entry_eq_sum rK78 ⟨78, by decide⟩ e heK h T78_78_2 hfix78_78_2 hinj78_78_2 hcardT78_78_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨78, by decide⟩) (reps rK78) (T78_78_2 i) (hfix78_78_2 i) h)

end Q2

/-! # K-class rK = 79  (|G/K| = 25) -/

def rK79 : Fin 148 := ⟨79, by decide⟩

def R79list : List Coordinates := [(0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0)]
def R79 : Fin 25 → Coordinate 1 := fun i => R79list.getD i.val (0,0,0,0,0)

theorem hpxR79 : Function.Injective (fun i => reduceAux 1 (basisAt rK79) (R79 i)) := by decide
theorem hcardq79 : Nat.card (Coordinate 1 ⧸ reps rK79) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (79, 0): |T| = 25 -/

def T79_0list : List Coordinates := [(0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0)]
def T79_0 : Fin 25 → Coordinate 1 := fun i => T79_0list.getD i.val (0,0,0,0,0)

theorem hfix79_0 : ∀ i, ((T79_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK79)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79) :=
  repsFix_of_siftB rK79 ⟨0, by decide⟩ T79_0 (by decide)

theorem hinj79_0 : Function.Injective
    (fun i => ((T79_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK79)) :=
  repsInj_of_reduceAux rK79 T79_0 (by decide)

theorem hcardT79_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK79 ⟨0, by decide⟩ R79 hpxR79 hcardq79 (by decide)).symm

/-- **Cell (79, 0).** -/
theorem cell79_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK79) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK79) (charOfVec rK79 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK79 e (h : Coordinate 1) T79_0 i :=
  species_entry_eq_sum rK79 ⟨0, by decide⟩ e heK h T79_0 hfix79_0 hinj79_0 hcardT79_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK79) (T79_0 i) (hfix79_0 i) h)

/-! ## Cell (79, 8): |T| = 25 -/

def T79_8list : List Coordinates := [(0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0)]
def T79_8 : Fin 25 → Coordinate 1 := fun i => T79_8list.getD i.val (0,0,0,0,0)

theorem hfix79_8 : ∀ i, ((T79_8 i : Coordinate 1) : Coordinate 1 ⧸ reps rK79)
    ∈ fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79) :=
  repsFix_of_siftB rK79 ⟨8, by decide⟩ T79_8 (by decide)

theorem hinj79_8 : Function.Injective
    (fun i => ((T79_8 i : Coordinate 1) : Coordinate 1 ⧸ reps rK79)) :=
  repsInj_of_reduceAux rK79 T79_8 (by decide)

theorem hcardT79_8 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK79 ⟨8, by decide⟩ R79 hpxR79 hcardq79 (by decide)).symm

/-- **Cell (79, 8).** -/
theorem cell79_8 (e : List (ZMod 25)) (heK : charOK (basisAt rK79) e = true)
    (h : ↥(reps (⟨8, by decide⟩ : Fin 148))) :
    species (reps (⟨8, by decide⟩ : Fin 148)) h (basisElt (reps rK79) (charOfVec rK79 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK79 e (h : Coordinate 1) T79_8 i :=
  species_entry_eq_sum rK79 ⟨8, by decide⟩ e heK h T79_8 hfix79_8 hinj79_8 hcardT79_8
    (fun i => conj_mem_of_fixedPoints (reps ⟨8, by decide⟩) (reps rK79) (T79_8 i) (hfix79_8 i) h)

/-! ## Cell (79, 12): |T| = 25 -/

def T79_12list : List Coordinates := [(0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0)]
def T79_12 : Fin 25 → Coordinate 1 := fun i => T79_12list.getD i.val (0,0,0,0,0)

theorem hfix79_12 : ∀ i, ((T79_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK79)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79) :=
  repsFix_of_siftB rK79 ⟨12, by decide⟩ T79_12 (by decide)

theorem hinj79_12 : Function.Injective
    (fun i => ((T79_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK79)) :=
  repsInj_of_reduceAux rK79 T79_12 (by decide)

theorem hcardT79_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK79 ⟨12, by decide⟩ R79 hpxR79 hcardq79 (by decide)).symm

/-- **Cell (79, 12).** -/
theorem cell79_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK79) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK79) (charOfVec rK79 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK79 e (h : Coordinate 1) T79_12 i :=
  species_entry_eq_sum rK79 ⟨12, by decide⟩ e heK h T79_12 hfix79_12 hinj79_12 hcardT79_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK79) (T79_12 i) (hfix79_12 i) h)

/-! ## Cell (79, 26): |T| = 25 -/

def T79_26list : List Coordinates := [(0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0)]
def T79_26 : Fin 25 → Coordinate 1 := fun i => T79_26list.getD i.val (0,0,0,0,0)

theorem hfix79_26 : ∀ i, ((T79_26 i : Coordinate 1) : Coordinate 1 ⧸ reps rK79)
    ∈ fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79) :=
  repsFix_of_siftB rK79 ⟨26, by decide⟩ T79_26 (by decide)

theorem hinj79_26 : Function.Injective
    (fun i => ((T79_26 i : Coordinate 1) : Coordinate 1 ⧸ reps rK79)) :=
  repsInj_of_reduceAux rK79 T79_26 (by decide)

theorem hcardT79_26 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK79 ⟨26, by decide⟩ R79 hpxR79 hcardq79 (by decide)).symm

/-- **Cell (79, 26).** -/
theorem cell79_26 (e : List (ZMod 25)) (heK : charOK (basisAt rK79) e = true)
    (h : ↥(reps (⟨26, by decide⟩ : Fin 148))) :
    species (reps (⟨26, by decide⟩ : Fin 148)) h (basisElt (reps rK79) (charOfVec rK79 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK79 e (h : Coordinate 1) T79_26 i :=
  species_entry_eq_sum rK79 ⟨26, by decide⟩ e heK h T79_26 hfix79_26 hinj79_26 hcardT79_26
    (fun i => conj_mem_of_fixedPoints (reps ⟨26, by decide⟩) (reps rK79) (T79_26 i) (hfix79_26 i) h)

/-! ## Cell (79, 32): |T| = 5 -/

def T79_32list : List Coordinates := [(0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0)]
def T79_32 : Fin 5 → Coordinate 1 := fun i => T79_32list.getD i.val (0,0,0,0,0)

theorem hfix79_32 : ∀ i, ((T79_32 i : Coordinate 1) : Coordinate 1 ⧸ reps rK79)
    ∈ fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79) :=
  repsFix_of_siftB rK79 ⟨32, by decide⟩ T79_32 (by decide)

theorem hinj79_32 : Function.Injective
    (fun i => ((T79_32 i : Coordinate 1) : Coordinate 1 ⧸ reps rK79)) :=
  repsInj_of_reduceAux rK79 T79_32 (by decide)

theorem hcardT79_32 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK79 ⟨32, by decide⟩ R79 hpxR79 hcardq79 (by decide)).symm

/-- **Cell (79, 32).** -/
theorem cell79_32 (e : List (ZMod 25)) (heK : charOK (basisAt rK79) e = true)
    (h : ↥(reps (⟨32, by decide⟩ : Fin 148))) :
    species (reps (⟨32, by decide⟩ : Fin 148)) h (basisElt (reps rK79) (charOfVec rK79 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK79 e (h : Coordinate 1) T79_32 i :=
  species_entry_eq_sum rK79 ⟨32, by decide⟩ e heK h T79_32 hfix79_32 hinj79_32 hcardT79_32
    (fun i => conj_mem_of_fixedPoints (reps ⟨32, by decide⟩) (reps rK79) (T79_32 i) (hfix79_32 i) h)

/-! ## Cell (79, 37): |T| = 5 -/

def T79_37list : List Coordinates := [(0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0)]
def T79_37 : Fin 5 → Coordinate 1 := fun i => T79_37list.getD i.val (0,0,0,0,0)

theorem hfix79_37 : ∀ i, ((T79_37 i : Coordinate 1) : Coordinate 1 ⧸ reps rK79)
    ∈ fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79) :=
  repsFix_of_siftB rK79 ⟨37, by decide⟩ T79_37 (by decide)

theorem hinj79_37 : Function.Injective
    (fun i => ((T79_37 i : Coordinate 1) : Coordinate 1 ⧸ reps rK79)) :=
  repsInj_of_reduceAux rK79 T79_37 (by decide)

theorem hcardT79_37 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK79 ⟨37, by decide⟩ R79 hpxR79 hcardq79 (by decide)).symm

/-- **Cell (79, 37).** -/
theorem cell79_37 (e : List (ZMod 25)) (heK : charOK (basisAt rK79) e = true)
    (h : ↥(reps (⟨37, by decide⟩ : Fin 148))) :
    species (reps (⟨37, by decide⟩ : Fin 148)) h (basisElt (reps rK79) (charOfVec rK79 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK79 e (h : Coordinate 1) T79_37 i :=
  species_entry_eq_sum rK79 ⟨37, by decide⟩ e heK h T79_37 hfix79_37 hinj79_37 hcardT79_37
    (fun i => conj_mem_of_fixedPoints (reps ⟨37, by decide⟩) (reps rK79) (T79_37 i) (hfix79_37 i) h)

/-! ## Cell (79, 42): |T| = 5 -/

def T79_42list : List Coordinates := [(0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0)]
def T79_42 : Fin 5 → Coordinate 1 := fun i => T79_42list.getD i.val (0,0,0,0,0)

theorem hfix79_42 : ∀ i, ((T79_42 i : Coordinate 1) : Coordinate 1 ⧸ reps rK79)
    ∈ fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79) :=
  repsFix_of_siftB rK79 ⟨42, by decide⟩ T79_42 (by decide)

theorem hinj79_42 : Function.Injective
    (fun i => ((T79_42 i : Coordinate 1) : Coordinate 1 ⧸ reps rK79)) :=
  repsInj_of_reduceAux rK79 T79_42 (by decide)

theorem hcardT79_42 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK79 ⟨42, by decide⟩ R79 hpxR79 hcardq79 (by decide)).symm

/-- **Cell (79, 42).** -/
theorem cell79_42 (e : List (ZMod 25)) (heK : charOK (basisAt rK79) e = true)
    (h : ↥(reps (⟨42, by decide⟩ : Fin 148))) :
    species (reps (⟨42, by decide⟩ : Fin 148)) h (basisElt (reps rK79) (charOfVec rK79 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK79 e (h : Coordinate 1) T79_42 i :=
  species_entry_eq_sum rK79 ⟨42, by decide⟩ e heK h T79_42 hfix79_42 hinj79_42 hcardT79_42
    (fun i => conj_mem_of_fixedPoints (reps ⟨42, by decide⟩) (reps rK79) (T79_42 i) (hfix79_42 i) h)

/-! ## Cell (79, 47): |T| = 5 -/

def T79_47list : List Coordinates := [(0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0)]
def T79_47 : Fin 5 → Coordinate 1 := fun i => T79_47list.getD i.val (0,0,0,0,0)

theorem hfix79_47 : ∀ i, ((T79_47 i : Coordinate 1) : Coordinate 1 ⧸ reps rK79)
    ∈ fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79) :=
  repsFix_of_siftB rK79 ⟨47, by decide⟩ T79_47 (by decide)

theorem hinj79_47 : Function.Injective
    (fun i => ((T79_47 i : Coordinate 1) : Coordinate 1 ⧸ reps rK79)) :=
  repsInj_of_reduceAux rK79 T79_47 (by decide)

theorem hcardT79_47 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK79 ⟨47, by decide⟩ R79 hpxR79 hcardq79 (by decide)).symm

/-- **Cell (79, 47).** -/
theorem cell79_47 (e : List (ZMod 25)) (heK : charOK (basisAt rK79) e = true)
    (h : ↥(reps (⟨47, by decide⟩ : Fin 148))) :
    species (reps (⟨47, by decide⟩ : Fin 148)) h (basisElt (reps rK79) (charOfVec rK79 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK79 e (h : Coordinate 1) T79_47 i :=
  species_entry_eq_sum rK79 ⟨47, by decide⟩ e heK h T79_47 hfix79_47 hinj79_47 hcardT79_47
    (fun i => conj_mem_of_fixedPoints (reps ⟨47, by decide⟩) (reps rK79) (T79_47 i) (hfix79_47 i) h)

/-! ## Cell (79, 52): |T| = 5 -/

def T79_52list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0)]
def T79_52 : Fin 5 → Coordinate 1 := fun i => T79_52list.getD i.val (0,0,0,0,0)

theorem hfix79_52 : ∀ i, ((T79_52 i : Coordinate 1) : Coordinate 1 ⧸ reps rK79)
    ∈ fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79) :=
  repsFix_of_siftB rK79 ⟨52, by decide⟩ T79_52 (by decide)

theorem hinj79_52 : Function.Injective
    (fun i => ((T79_52 i : Coordinate 1) : Coordinate 1 ⧸ reps rK79)) :=
  repsInj_of_reduceAux rK79 T79_52 (by decide)

theorem hcardT79_52 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK79 ⟨52, by decide⟩ R79 hpxR79 hcardq79 (by decide)).symm

/-- **Cell (79, 52).** -/
theorem cell79_52 (e : List (ZMod 25)) (heK : charOK (basisAt rK79) e = true)
    (h : ↥(reps (⟨52, by decide⟩ : Fin 148))) :
    species (reps (⟨52, by decide⟩ : Fin 148)) h (basisElt (reps rK79) (charOfVec rK79 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK79 e (h : Coordinate 1) T79_52 i :=
  species_entry_eq_sum rK79 ⟨52, by decide⟩ e heK h T79_52 hfix79_52 hinj79_52 hcardT79_52
    (fun i => conj_mem_of_fixedPoints (reps ⟨52, by decide⟩) (reps rK79) (T79_52 i) (hfix79_52 i) h)

/-! ## Cell (79, 79): |T| = 5 -/

def T79_79list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0)]
def T79_79 : Fin 5 → Coordinate 1 := fun i => T79_79list.getD i.val (0,0,0,0,0)

theorem hfix79_79 : ∀ i, ((T79_79 i : Coordinate 1) : Coordinate 1 ⧸ reps rK79)
    ∈ fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79) :=
  repsFix_of_siftB rK79 ⟨79, by decide⟩ T79_79 (by decide)

theorem hinj79_79 : Function.Injective
    (fun i => ((T79_79 i : Coordinate 1) : Coordinate 1 ⧸ reps rK79)) :=
  repsInj_of_reduceAux rK79 T79_79 (by decide)

theorem hcardT79_79 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK79 ⟨79, by decide⟩ R79 hpxR79 hcardq79 (by decide)).symm

/-- **Cell (79, 79).** -/
theorem cell79_79 (e : List (ZMod 25)) (heK : charOK (basisAt rK79) e = true)
    (h : ↥(reps (⟨79, by decide⟩ : Fin 148))) :
    species (reps (⟨79, by decide⟩ : Fin 148)) h (basisElt (reps rK79) (charOfVec rK79 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK79 e (h : Coordinate 1) T79_79 i :=
  species_entry_eq_sum rK79 ⟨79, by decide⟩ e heK h T79_79 hfix79_79 hinj79_79 hcardT79_79
    (fun i => conj_mem_of_fixedPoints (reps ⟨79, by decide⟩) (reps rK79) (T79_79 i) (hfix79_79 i) h)

namespace Q2

def R79_2 : Fin 25 → Coordinate 2 := fun i => R79list.getD i.val (0,0,0,0,0)
theorem hpxR79_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK79) (R79_2 i)) := by decide
theorem hcardq79_2 : Nat.card (Coordinate 2 ⧸ reps rK79) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (79, 0) twin -/

def T79_0_2 : Fin 25 → Coordinate 2 := fun i => T79_0list.getD i.val (0,0,0,0,0)

theorem hfix79_0_2 : ∀ i, ((T79_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK79)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK79) :=
  repsFix_of_siftB2 rK79 ⟨0, by decide⟩ T79_0_2 (by decide)

theorem hinj79_0_2 : Function.Injective
    (fun i => ((T79_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK79)) :=
  repsInj_of_reduceAux2 rK79 T79_0_2 (by decide)

theorem hcardT79_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK79)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK79 ⟨0, by decide⟩ R79_2 hpxR79_2 hcardq79_2 (by decide)).symm

/-- **Cell (79, 0) twin (q=2).** -/
theorem cell79_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK79) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK79) (charOfVec2 rK79 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK79 e (h : Coordinate 2) T79_0_2 i :=
  species_entry_eq_sum rK79 ⟨0, by decide⟩ e heK h T79_0_2 hfix79_0_2 hinj79_0_2 hcardT79_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK79) (T79_0_2 i) (hfix79_0_2 i) h)

/-! ### Cell (79, 8) twin -/

def T79_8_2 : Fin 25 → Coordinate 2 := fun i => T79_8list.getD i.val (0,0,0,0,0)

theorem hfix79_8_2 : ∀ i, ((T79_8_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK79)
    ∈ fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK79) :=
  repsFix_of_siftB2 rK79 ⟨8, by decide⟩ T79_8_2 (by decide)

theorem hinj79_8_2 : Function.Injective
    (fun i => ((T79_8_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK79)) :=
  repsInj_of_reduceAux2 rK79 T79_8_2 (by decide)

theorem hcardT79_8_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK79)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK79 ⟨8, by decide⟩ R79_2 hpxR79_2 hcardq79_2 (by decide)).symm

/-- **Cell (79, 8) twin (q=2).** -/
theorem cell79_8_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK79) e = true)
    (h : ↥(reps (⟨8, by decide⟩ : Fin 148))) :
    species (reps (⟨8, by decide⟩ : Fin 148)) h (basisElt (reps rK79) (charOfVec2 rK79 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK79 e (h : Coordinate 2) T79_8_2 i :=
  species_entry_eq_sum rK79 ⟨8, by decide⟩ e heK h T79_8_2 hfix79_8_2 hinj79_8_2 hcardT79_8_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨8, by decide⟩) (reps rK79) (T79_8_2 i) (hfix79_8_2 i) h)

/-! ### Cell (79, 12) twin -/

def T79_12_2 : Fin 25 → Coordinate 2 := fun i => T79_12list.getD i.val (0,0,0,0,0)

theorem hfix79_12_2 : ∀ i, ((T79_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK79)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK79) :=
  repsFix_of_siftB2 rK79 ⟨12, by decide⟩ T79_12_2 (by decide)

theorem hinj79_12_2 : Function.Injective
    (fun i => ((T79_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK79)) :=
  repsInj_of_reduceAux2 rK79 T79_12_2 (by decide)

theorem hcardT79_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK79)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK79 ⟨12, by decide⟩ R79_2 hpxR79_2 hcardq79_2 (by decide)).symm

/-- **Cell (79, 12) twin (q=2).** -/
theorem cell79_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK79) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK79) (charOfVec2 rK79 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK79 e (h : Coordinate 2) T79_12_2 i :=
  species_entry_eq_sum rK79 ⟨12, by decide⟩ e heK h T79_12_2 hfix79_12_2 hinj79_12_2 hcardT79_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK79) (T79_12_2 i) (hfix79_12_2 i) h)

/-! ### Cell (79, 26) twin -/

def T79_26_2 : Fin 25 → Coordinate 2 := fun i => T79_26list.getD i.val (0,0,0,0,0)

theorem hfix79_26_2 : ∀ i, ((T79_26_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK79)
    ∈ fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK79) :=
  repsFix_of_siftB2 rK79 ⟨26, by decide⟩ T79_26_2 (by decide)

theorem hinj79_26_2 : Function.Injective
    (fun i => ((T79_26_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK79)) :=
  repsInj_of_reduceAux2 rK79 T79_26_2 (by decide)

theorem hcardT79_26_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK79)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK79 ⟨26, by decide⟩ R79_2 hpxR79_2 hcardq79_2 (by decide)).symm

/-- **Cell (79, 26) twin (q=2).** -/
theorem cell79_26_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK79) e = true)
    (h : ↥(reps (⟨26, by decide⟩ : Fin 148))) :
    species (reps (⟨26, by decide⟩ : Fin 148)) h (basisElt (reps rK79) (charOfVec2 rK79 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK79 e (h : Coordinate 2) T79_26_2 i :=
  species_entry_eq_sum rK79 ⟨26, by decide⟩ e heK h T79_26_2 hfix79_26_2 hinj79_26_2 hcardT79_26_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨26, by decide⟩) (reps rK79) (T79_26_2 i) (hfix79_26_2 i) h)

/-! ### Cell (79, 32) twin -/

def T79_32_2 : Fin 5 → Coordinate 2 := fun i => T79_32list.getD i.val (0,0,0,0,0)

theorem hfix79_32_2 : ∀ i, ((T79_32_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK79)
    ∈ fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK79) :=
  repsFix_of_siftB2 rK79 ⟨32, by decide⟩ T79_32_2 (by decide)

theorem hinj79_32_2 : Function.Injective
    (fun i => ((T79_32_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK79)) :=
  repsInj_of_reduceAux2 rK79 T79_32_2 (by decide)

theorem hcardT79_32_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK79)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK79 ⟨32, by decide⟩ R79_2 hpxR79_2 hcardq79_2 (by decide)).symm

/-- **Cell (79, 32) twin (q=2).** -/
theorem cell79_32_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK79) e = true)
    (h : ↥(reps (⟨32, by decide⟩ : Fin 148))) :
    species (reps (⟨32, by decide⟩ : Fin 148)) h (basisElt (reps rK79) (charOfVec2 rK79 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK79 e (h : Coordinate 2) T79_32_2 i :=
  species_entry_eq_sum rK79 ⟨32, by decide⟩ e heK h T79_32_2 hfix79_32_2 hinj79_32_2 hcardT79_32_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨32, by decide⟩) (reps rK79) (T79_32_2 i) (hfix79_32_2 i) h)

/-! ### Cell (79, 37) twin -/

def T79_37_2 : Fin 5 → Coordinate 2 := fun i => T79_37list.getD i.val (0,0,0,0,0)

theorem hfix79_37_2 : ∀ i, ((T79_37_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK79)
    ∈ fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK79) :=
  repsFix_of_siftB2 rK79 ⟨37, by decide⟩ T79_37_2 (by decide)

theorem hinj79_37_2 : Function.Injective
    (fun i => ((T79_37_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK79)) :=
  repsInj_of_reduceAux2 rK79 T79_37_2 (by decide)

theorem hcardT79_37_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK79)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK79 ⟨37, by decide⟩ R79_2 hpxR79_2 hcardq79_2 (by decide)).symm

/-- **Cell (79, 37) twin (q=2).** -/
theorem cell79_37_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK79) e = true)
    (h : ↥(reps (⟨37, by decide⟩ : Fin 148))) :
    species (reps (⟨37, by decide⟩ : Fin 148)) h (basisElt (reps rK79) (charOfVec2 rK79 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK79 e (h : Coordinate 2) T79_37_2 i :=
  species_entry_eq_sum rK79 ⟨37, by decide⟩ e heK h T79_37_2 hfix79_37_2 hinj79_37_2 hcardT79_37_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨37, by decide⟩) (reps rK79) (T79_37_2 i) (hfix79_37_2 i) h)

/-! ### Cell (79, 42) twin -/

def T79_42_2 : Fin 5 → Coordinate 2 := fun i => T79_42list.getD i.val (0,0,0,0,0)

theorem hfix79_42_2 : ∀ i, ((T79_42_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK79)
    ∈ fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK79) :=
  repsFix_of_siftB2 rK79 ⟨42, by decide⟩ T79_42_2 (by decide)

theorem hinj79_42_2 : Function.Injective
    (fun i => ((T79_42_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK79)) :=
  repsInj_of_reduceAux2 rK79 T79_42_2 (by decide)

theorem hcardT79_42_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK79)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK79 ⟨42, by decide⟩ R79_2 hpxR79_2 hcardq79_2 (by decide)).symm

/-- **Cell (79, 42) twin (q=2).** -/
theorem cell79_42_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK79) e = true)
    (h : ↥(reps (⟨42, by decide⟩ : Fin 148))) :
    species (reps (⟨42, by decide⟩ : Fin 148)) h (basisElt (reps rK79) (charOfVec2 rK79 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK79 e (h : Coordinate 2) T79_42_2 i :=
  species_entry_eq_sum rK79 ⟨42, by decide⟩ e heK h T79_42_2 hfix79_42_2 hinj79_42_2 hcardT79_42_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨42, by decide⟩) (reps rK79) (T79_42_2 i) (hfix79_42_2 i) h)

/-! ### Cell (79, 47) twin -/

def T79_47_2 : Fin 5 → Coordinate 2 := fun i => T79_47list.getD i.val (0,0,0,0,0)

theorem hfix79_47_2 : ∀ i, ((T79_47_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK79)
    ∈ fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK79) :=
  repsFix_of_siftB2 rK79 ⟨47, by decide⟩ T79_47_2 (by decide)

theorem hinj79_47_2 : Function.Injective
    (fun i => ((T79_47_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK79)) :=
  repsInj_of_reduceAux2 rK79 T79_47_2 (by decide)

theorem hcardT79_47_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK79)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK79 ⟨47, by decide⟩ R79_2 hpxR79_2 hcardq79_2 (by decide)).symm

/-- **Cell (79, 47) twin (q=2).** -/
theorem cell79_47_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK79) e = true)
    (h : ↥(reps (⟨47, by decide⟩ : Fin 148))) :
    species (reps (⟨47, by decide⟩ : Fin 148)) h (basisElt (reps rK79) (charOfVec2 rK79 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK79 e (h : Coordinate 2) T79_47_2 i :=
  species_entry_eq_sum rK79 ⟨47, by decide⟩ e heK h T79_47_2 hfix79_47_2 hinj79_47_2 hcardT79_47_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨47, by decide⟩) (reps rK79) (T79_47_2 i) (hfix79_47_2 i) h)

/-! ### Cell (79, 52) twin -/

def T79_52_2 : Fin 5 → Coordinate 2 := fun i => T79_52list.getD i.val (0,0,0,0,0)

theorem hfix79_52_2 : ∀ i, ((T79_52_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK79)
    ∈ fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK79) :=
  repsFix_of_siftB2 rK79 ⟨52, by decide⟩ T79_52_2 (by decide)

theorem hinj79_52_2 : Function.Injective
    (fun i => ((T79_52_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK79)) :=
  repsInj_of_reduceAux2 rK79 T79_52_2 (by decide)

theorem hcardT79_52_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK79)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK79 ⟨52, by decide⟩ R79_2 hpxR79_2 hcardq79_2 (by decide)).symm

/-- **Cell (79, 52) twin (q=2).** -/
theorem cell79_52_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK79) e = true)
    (h : ↥(reps (⟨52, by decide⟩ : Fin 148))) :
    species (reps (⟨52, by decide⟩ : Fin 148)) h (basisElt (reps rK79) (charOfVec2 rK79 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK79 e (h : Coordinate 2) T79_52_2 i :=
  species_entry_eq_sum rK79 ⟨52, by decide⟩ e heK h T79_52_2 hfix79_52_2 hinj79_52_2 hcardT79_52_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨52, by decide⟩) (reps rK79) (T79_52_2 i) (hfix79_52_2 i) h)

/-! ### Cell (79, 79) twin -/

def T79_79_2 : Fin 5 → Coordinate 2 := fun i => T79_79list.getD i.val (0,0,0,0,0)

theorem hfix79_79_2 : ∀ i, ((T79_79_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK79)
    ∈ fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK79) :=
  repsFix_of_siftB2 rK79 ⟨79, by decide⟩ T79_79_2 (by decide)

theorem hinj79_79_2 : Function.Injective
    (fun i => ((T79_79_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK79)) :=
  repsInj_of_reduceAux2 rK79 T79_79_2 (by decide)

theorem hcardT79_79_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK79)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK79 ⟨79, by decide⟩ R79_2 hpxR79_2 hcardq79_2 (by decide)).symm

/-- **Cell (79, 79) twin (q=2).** -/
theorem cell79_79_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK79) e = true)
    (h : ↥(reps (⟨79, by decide⟩ : Fin 148))) :
    species (reps (⟨79, by decide⟩ : Fin 148)) h (basisElt (reps rK79) (charOfVec2 rK79 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK79 e (h : Coordinate 2) T79_79_2 i :=
  species_entry_eq_sum rK79 ⟨79, by decide⟩ e heK h T79_79_2 hfix79_79_2 hinj79_79_2 hcardT79_79_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨79, by decide⟩) (reps rK79) (T79_79_2 i) (hfix79_79_2 i) h)

end Q2

end LeanDring.P5Presentation
