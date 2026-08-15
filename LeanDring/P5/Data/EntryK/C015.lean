/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, K-strata data (5^3 stratum, rK 60-64): certified per-cell species-entry instantiations, both
twins.

Covers K-classes 60, 61, 62, 63, 64 (order-5^3 K, |R|=25).  For each nonzero `H`-column
(`(G/K)^H ≠ ∅`), the full coset transversal `R60..` and each `H`-fixed
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

/-! # K-class rK = 60  (|G/K| = 25) -/

def rK60 : Fin 148 := ⟨60, by decide⟩

def R60list : List Coordinates := [(0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0)]
def R60 : Fin 25 → Coordinate 1 := fun i => R60list.getD i.val (0,0,0,0,0)

theorem hpxR60 : Function.Injective (fun i => reduceAux 1 (basisAt rK60) (R60 i)) := by decide
theorem hcardq60 : Nat.card (Coordinate 1 ⧸ reps rK60) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (60, 0): |T| = 25 -/

def T60_0list : List Coordinates := [(0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0)]
def T60_0 : Fin 25 → Coordinate 1 := fun i => T60_0list.getD i.val (0,0,0,0,0)

theorem hfix60_0 : ∀ i, ((T60_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK60)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60) :=
  repsFix_of_siftB rK60 ⟨0, by decide⟩ T60_0 (by decide)

theorem hinj60_0 : Function.Injective
    (fun i => ((T60_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK60)) :=
  repsInj_of_reduceAux rK60 T60_0 (by decide)

theorem hcardT60_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK60 ⟨0, by decide⟩ R60 hpxR60 hcardq60 (by decide)).symm

/-- **Cell (60, 0).** -/
theorem cell60_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK60) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK60) (charOfVec rK60 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK60 e (h : Coordinate 1) T60_0 i :=
  species_entry_eq_sum rK60 ⟨0, by decide⟩ e heK h T60_0 hfix60_0 hinj60_0 hcardT60_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK60) (T60_0 i) (hfix60_0 i) h)

/-! ## Cell (60, 9): |T| = 25 -/

def T60_9list : List Coordinates := [(0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0)]
def T60_9 : Fin 25 → Coordinate 1 := fun i => T60_9list.getD i.val (0,0,0,0,0)

theorem hfix60_9 : ∀ i, ((T60_9 i : Coordinate 1) : Coordinate 1 ⧸ reps rK60)
    ∈ fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60) :=
  repsFix_of_siftB rK60 ⟨9, by decide⟩ T60_9 (by decide)

theorem hinj60_9 : Function.Injective
    (fun i => ((T60_9 i : Coordinate 1) : Coordinate 1 ⧸ reps rK60)) :=
  repsInj_of_reduceAux rK60 T60_9 (by decide)

theorem hcardT60_9 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK60 ⟨9, by decide⟩ R60 hpxR60 hcardq60 (by decide)).symm

/-- **Cell (60, 9).** -/
theorem cell60_9 (e : List (ZMod 25)) (heK : charOK (basisAt rK60) e = true)
    (h : ↥(reps (⟨9, by decide⟩ : Fin 148))) :
    species (reps (⟨9, by decide⟩ : Fin 148)) h (basisElt (reps rK60) (charOfVec rK60 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK60 e (h : Coordinate 1) T60_9 i :=
  species_entry_eq_sum rK60 ⟨9, by decide⟩ e heK h T60_9 hfix60_9 hinj60_9 hcardT60_9
    (fun i => conj_mem_of_fixedPoints (reps ⟨9, by decide⟩) (reps rK60) (T60_9 i) (hfix60_9 i) h)

/-! ## Cell (60, 12): |T| = 25 -/

def T60_12list : List Coordinates := [(0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0)]
def T60_12 : Fin 25 → Coordinate 1 := fun i => T60_12list.getD i.val (0,0,0,0,0)

theorem hfix60_12 : ∀ i, ((T60_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK60)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60) :=
  repsFix_of_siftB rK60 ⟨12, by decide⟩ T60_12 (by decide)

theorem hinj60_12 : Function.Injective
    (fun i => ((T60_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK60)) :=
  repsInj_of_reduceAux rK60 T60_12 (by decide)

theorem hcardT60_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK60 ⟨12, by decide⟩ R60 hpxR60 hcardq60 (by decide)).symm

/-- **Cell (60, 12).** -/
theorem cell60_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK60) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK60) (charOfVec rK60 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK60 e (h : Coordinate 1) T60_12 i :=
  species_entry_eq_sum rK60 ⟨12, by decide⟩ e heK h T60_12 hfix60_12 hinj60_12 hcardT60_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK60) (T60_12 i) (hfix60_12 i) h)

/-! ## Cell (60, 27): |T| = 25 -/

def T60_27list : List Coordinates := [(0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0)]
def T60_27 : Fin 25 → Coordinate 1 := fun i => T60_27list.getD i.val (0,0,0,0,0)

theorem hfix60_27 : ∀ i, ((T60_27 i : Coordinate 1) : Coordinate 1 ⧸ reps rK60)
    ∈ fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60) :=
  repsFix_of_siftB rK60 ⟨27, by decide⟩ T60_27 (by decide)

theorem hinj60_27 : Function.Injective
    (fun i => ((T60_27 i : Coordinate 1) : Coordinate 1 ⧸ reps rK60)) :=
  repsInj_of_reduceAux rK60 T60_27 (by decide)

theorem hcardT60_27 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK60 ⟨27, by decide⟩ R60 hpxR60 hcardq60 (by decide)).symm

/-- **Cell (60, 27).** -/
theorem cell60_27 (e : List (ZMod 25)) (heK : charOK (basisAt rK60) e = true)
    (h : ↥(reps (⟨27, by decide⟩ : Fin 148))) :
    species (reps (⟨27, by decide⟩ : Fin 148)) h (basisElt (reps rK60) (charOfVec rK60 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK60 e (h : Coordinate 1) T60_27 i :=
  species_entry_eq_sum rK60 ⟨27, by decide⟩ e heK h T60_27 hfix60_27 hinj60_27 hcardT60_27
    (fun i => conj_mem_of_fixedPoints (reps ⟨27, by decide⟩) (reps rK60) (T60_27 i) (hfix60_27 i) h)

/-! ## Cell (60, 29): |T| = 5 -/

def T60_29list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0)]
def T60_29 : Fin 5 → Coordinate 1 := fun i => T60_29list.getD i.val (0,0,0,0,0)

theorem hfix60_29 : ∀ i, ((T60_29 i : Coordinate 1) : Coordinate 1 ⧸ reps rK60)
    ∈ fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60) :=
  repsFix_of_siftB rK60 ⟨29, by decide⟩ T60_29 (by decide)

theorem hinj60_29 : Function.Injective
    (fun i => ((T60_29 i : Coordinate 1) : Coordinate 1 ⧸ reps rK60)) :=
  repsInj_of_reduceAux rK60 T60_29 (by decide)

theorem hcardT60_29 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK60 ⟨29, by decide⟩ R60 hpxR60 hcardq60 (by decide)).symm

/-- **Cell (60, 29).** -/
theorem cell60_29 (e : List (ZMod 25)) (heK : charOK (basisAt rK60) e = true)
    (h : ↥(reps (⟨29, by decide⟩ : Fin 148))) :
    species (reps (⟨29, by decide⟩ : Fin 148)) h (basisElt (reps rK60) (charOfVec rK60 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK60 e (h : Coordinate 1) T60_29 i :=
  species_entry_eq_sum rK60 ⟨29, by decide⟩ e heK h T60_29 hfix60_29 hinj60_29 hcardT60_29
    (fun i => conj_mem_of_fixedPoints (reps ⟨29, by decide⟩) (reps rK60) (T60_29 i) (hfix60_29 i) h)

/-! ## Cell (60, 34): |T| = 5 -/

def T60_34list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0)]
def T60_34 : Fin 5 → Coordinate 1 := fun i => T60_34list.getD i.val (0,0,0,0,0)

theorem hfix60_34 : ∀ i, ((T60_34 i : Coordinate 1) : Coordinate 1 ⧸ reps rK60)
    ∈ fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60) :=
  repsFix_of_siftB rK60 ⟨34, by decide⟩ T60_34 (by decide)

theorem hinj60_34 : Function.Injective
    (fun i => ((T60_34 i : Coordinate 1) : Coordinate 1 ⧸ reps rK60)) :=
  repsInj_of_reduceAux rK60 T60_34 (by decide)

theorem hcardT60_34 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK60 ⟨34, by decide⟩ R60 hpxR60 hcardq60 (by decide)).symm

/-- **Cell (60, 34).** -/
theorem cell60_34 (e : List (ZMod 25)) (heK : charOK (basisAt rK60) e = true)
    (h : ↥(reps (⟨34, by decide⟩ : Fin 148))) :
    species (reps (⟨34, by decide⟩ : Fin 148)) h (basisElt (reps rK60) (charOfVec rK60 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK60 e (h : Coordinate 1) T60_34 i :=
  species_entry_eq_sum rK60 ⟨34, by decide⟩ e heK h T60_34 hfix60_34 hinj60_34 hcardT60_34
    (fun i => conj_mem_of_fixedPoints (reps ⟨34, by decide⟩) (reps rK60) (T60_34 i) (hfix60_34 i) h)

/-! ## Cell (60, 39): |T| = 5 -/

def T60_39list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0)]
def T60_39 : Fin 5 → Coordinate 1 := fun i => T60_39list.getD i.val (0,0,0,0,0)

theorem hfix60_39 : ∀ i, ((T60_39 i : Coordinate 1) : Coordinate 1 ⧸ reps rK60)
    ∈ fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60) :=
  repsFix_of_siftB rK60 ⟨39, by decide⟩ T60_39 (by decide)

theorem hinj60_39 : Function.Injective
    (fun i => ((T60_39 i : Coordinate 1) : Coordinate 1 ⧸ reps rK60)) :=
  repsInj_of_reduceAux rK60 T60_39 (by decide)

theorem hcardT60_39 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK60 ⟨39, by decide⟩ R60 hpxR60 hcardq60 (by decide)).symm

/-- **Cell (60, 39).** -/
theorem cell60_39 (e : List (ZMod 25)) (heK : charOK (basisAt rK60) e = true)
    (h : ↥(reps (⟨39, by decide⟩ : Fin 148))) :
    species (reps (⟨39, by decide⟩ : Fin 148)) h (basisElt (reps rK60) (charOfVec rK60 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK60 e (h : Coordinate 1) T60_39 i :=
  species_entry_eq_sum rK60 ⟨39, by decide⟩ e heK h T60_39 hfix60_39 hinj60_39 hcardT60_39
    (fun i => conj_mem_of_fixedPoints (reps ⟨39, by decide⟩) (reps rK60) (T60_39 i) (hfix60_39 i) h)

/-! ## Cell (60, 44): |T| = 5 -/

def T60_44list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0)]
def T60_44 : Fin 5 → Coordinate 1 := fun i => T60_44list.getD i.val (0,0,0,0,0)

theorem hfix60_44 : ∀ i, ((T60_44 i : Coordinate 1) : Coordinate 1 ⧸ reps rK60)
    ∈ fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60) :=
  repsFix_of_siftB rK60 ⟨44, by decide⟩ T60_44 (by decide)

theorem hinj60_44 : Function.Injective
    (fun i => ((T60_44 i : Coordinate 1) : Coordinate 1 ⧸ reps rK60)) :=
  repsInj_of_reduceAux rK60 T60_44 (by decide)

theorem hcardT60_44 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK60 ⟨44, by decide⟩ R60 hpxR60 hcardq60 (by decide)).symm

/-- **Cell (60, 44).** -/
theorem cell60_44 (e : List (ZMod 25)) (heK : charOK (basisAt rK60) e = true)
    (h : ↥(reps (⟨44, by decide⟩ : Fin 148))) :
    species (reps (⟨44, by decide⟩ : Fin 148)) h (basisElt (reps rK60) (charOfVec rK60 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK60 e (h : Coordinate 1) T60_44 i :=
  species_entry_eq_sum rK60 ⟨44, by decide⟩ e heK h T60_44 hfix60_44 hinj60_44 hcardT60_44
    (fun i => conj_mem_of_fixedPoints (reps ⟨44, by decide⟩) (reps rK60) (T60_44 i) (hfix60_44 i) h)

/-! ## Cell (60, 49): |T| = 5 -/

def T60_49list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0)]
def T60_49 : Fin 5 → Coordinate 1 := fun i => T60_49list.getD i.val (0,0,0,0,0)

theorem hfix60_49 : ∀ i, ((T60_49 i : Coordinate 1) : Coordinate 1 ⧸ reps rK60)
    ∈ fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60) :=
  repsFix_of_siftB rK60 ⟨49, by decide⟩ T60_49 (by decide)

theorem hinj60_49 : Function.Injective
    (fun i => ((T60_49 i : Coordinate 1) : Coordinate 1 ⧸ reps rK60)) :=
  repsInj_of_reduceAux rK60 T60_49 (by decide)

theorem hcardT60_49 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK60 ⟨49, by decide⟩ R60 hpxR60 hcardq60 (by decide)).symm

/-- **Cell (60, 49).** -/
theorem cell60_49 (e : List (ZMod 25)) (heK : charOK (basisAt rK60) e = true)
    (h : ↥(reps (⟨49, by decide⟩ : Fin 148))) :
    species (reps (⟨49, by decide⟩ : Fin 148)) h (basisElt (reps rK60) (charOfVec rK60 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK60 e (h : Coordinate 1) T60_49 i :=
  species_entry_eq_sum rK60 ⟨49, by decide⟩ e heK h T60_49 hfix60_49 hinj60_49 hcardT60_49
    (fun i => conj_mem_of_fixedPoints (reps ⟨49, by decide⟩) (reps rK60) (T60_49 i) (hfix60_49 i) h)

/-! ## Cell (60, 60): |T| = 5 -/

def T60_60list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0)]
def T60_60 : Fin 5 → Coordinate 1 := fun i => T60_60list.getD i.val (0,0,0,0,0)

theorem hfix60_60 : ∀ i, ((T60_60 i : Coordinate 1) : Coordinate 1 ⧸ reps rK60)
    ∈ fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60) :=
  repsFix_of_siftB rK60 ⟨60, by decide⟩ T60_60 (by decide)

theorem hinj60_60 : Function.Injective
    (fun i => ((T60_60 i : Coordinate 1) : Coordinate 1 ⧸ reps rK60)) :=
  repsInj_of_reduceAux rK60 T60_60 (by decide)

theorem hcardT60_60 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK60 ⟨60, by decide⟩ R60 hpxR60 hcardq60 (by decide)).symm

/-- **Cell (60, 60).** -/
theorem cell60_60 (e : List (ZMod 25)) (heK : charOK (basisAt rK60) e = true)
    (h : ↥(reps (⟨60, by decide⟩ : Fin 148))) :
    species (reps (⟨60, by decide⟩ : Fin 148)) h (basisElt (reps rK60) (charOfVec rK60 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK60 e (h : Coordinate 1) T60_60 i :=
  species_entry_eq_sum rK60 ⟨60, by decide⟩ e heK h T60_60 hfix60_60 hinj60_60 hcardT60_60
    (fun i => conj_mem_of_fixedPoints (reps ⟨60, by decide⟩) (reps rK60) (T60_60 i) (hfix60_60 i) h)

namespace Q2

def R60_2 : Fin 25 → Coordinate 2 := fun i => R60list.getD i.val (0,0,0,0,0)
theorem hpxR60_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK60) (R60_2 i)) := by decide
theorem hcardq60_2 : Nat.card (Coordinate 2 ⧸ reps rK60) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (60, 0) twin -/

def T60_0_2 : Fin 25 → Coordinate 2 := fun i => T60_0list.getD i.val (0,0,0,0,0)

theorem hfix60_0_2 : ∀ i, ((T60_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK60)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK60) :=
  repsFix_of_siftB2 rK60 ⟨0, by decide⟩ T60_0_2 (by decide)

theorem hinj60_0_2 : Function.Injective
    (fun i => ((T60_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK60)) :=
  repsInj_of_reduceAux2 rK60 T60_0_2 (by decide)

theorem hcardT60_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK60)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK60 ⟨0, by decide⟩ R60_2 hpxR60_2 hcardq60_2 (by decide)).symm

/-- **Cell (60, 0) twin (q=2).** -/
theorem cell60_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK60) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK60) (charOfVec2 rK60 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK60 e (h : Coordinate 2) T60_0_2 i :=
  species_entry_eq_sum rK60 ⟨0, by decide⟩ e heK h T60_0_2 hfix60_0_2 hinj60_0_2 hcardT60_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK60) (T60_0_2 i) (hfix60_0_2 i) h)

/-! ### Cell (60, 9) twin -/

def T60_9_2 : Fin 25 → Coordinate 2 := fun i => T60_9list.getD i.val (0,0,0,0,0)

theorem hfix60_9_2 : ∀ i, ((T60_9_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK60)
    ∈ fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK60) :=
  repsFix_of_siftB2 rK60 ⟨9, by decide⟩ T60_9_2 (by decide)

theorem hinj60_9_2 : Function.Injective
    (fun i => ((T60_9_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK60)) :=
  repsInj_of_reduceAux2 rK60 T60_9_2 (by decide)

theorem hcardT60_9_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK60)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK60 ⟨9, by decide⟩ R60_2 hpxR60_2 hcardq60_2 (by decide)).symm

/-- **Cell (60, 9) twin (q=2).** -/
theorem cell60_9_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK60) e = true)
    (h : ↥(reps (⟨9, by decide⟩ : Fin 148))) :
    species (reps (⟨9, by decide⟩ : Fin 148)) h (basisElt (reps rK60) (charOfVec2 rK60 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK60 e (h : Coordinate 2) T60_9_2 i :=
  species_entry_eq_sum rK60 ⟨9, by decide⟩ e heK h T60_9_2 hfix60_9_2 hinj60_9_2 hcardT60_9_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨9, by decide⟩) (reps rK60) (T60_9_2 i) (hfix60_9_2 i) h)

/-! ### Cell (60, 12) twin -/

def T60_12_2 : Fin 25 → Coordinate 2 := fun i => T60_12list.getD i.val (0,0,0,0,0)

theorem hfix60_12_2 : ∀ i, ((T60_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK60)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK60) :=
  repsFix_of_siftB2 rK60 ⟨12, by decide⟩ T60_12_2 (by decide)

theorem hinj60_12_2 : Function.Injective
    (fun i => ((T60_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK60)) :=
  repsInj_of_reduceAux2 rK60 T60_12_2 (by decide)

theorem hcardT60_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK60)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK60 ⟨12, by decide⟩ R60_2 hpxR60_2 hcardq60_2 (by decide)).symm

/-- **Cell (60, 12) twin (q=2).** -/
theorem cell60_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK60) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK60) (charOfVec2 rK60 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK60 e (h : Coordinate 2) T60_12_2 i :=
  species_entry_eq_sum rK60 ⟨12, by decide⟩ e heK h T60_12_2 hfix60_12_2 hinj60_12_2 hcardT60_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK60) (T60_12_2 i) (hfix60_12_2 i) h)

/-! ### Cell (60, 27) twin -/

def T60_27_2 : Fin 25 → Coordinate 2 := fun i => T60_27list.getD i.val (0,0,0,0,0)

theorem hfix60_27_2 : ∀ i, ((T60_27_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK60)
    ∈ fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK60) :=
  repsFix_of_siftB2 rK60 ⟨27, by decide⟩ T60_27_2 (by decide)

theorem hinj60_27_2 : Function.Injective
    (fun i => ((T60_27_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK60)) :=
  repsInj_of_reduceAux2 rK60 T60_27_2 (by decide)

theorem hcardT60_27_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK60)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK60 ⟨27, by decide⟩ R60_2 hpxR60_2 hcardq60_2 (by decide)).symm

/-- **Cell (60, 27) twin (q=2).** -/
theorem cell60_27_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK60) e = true)
    (h : ↥(reps (⟨27, by decide⟩ : Fin 148))) :
    species (reps (⟨27, by decide⟩ : Fin 148)) h (basisElt (reps rK60) (charOfVec2 rK60 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK60 e (h : Coordinate 2) T60_27_2 i :=
  species_entry_eq_sum rK60 ⟨27, by decide⟩ e heK h T60_27_2 hfix60_27_2 hinj60_27_2 hcardT60_27_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨27, by decide⟩) (reps rK60) (T60_27_2 i) (hfix60_27_2 i) h)

/-! ### Cell (60, 29) twin -/

def T60_29_2 : Fin 5 → Coordinate 2 := fun i => T60_29list.getD i.val (0,0,0,0,0)

theorem hfix60_29_2 : ∀ i, ((T60_29_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK60)
    ∈ fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK60) :=
  repsFix_of_siftB2 rK60 ⟨29, by decide⟩ T60_29_2 (by decide)

theorem hinj60_29_2 : Function.Injective
    (fun i => ((T60_29_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK60)) :=
  repsInj_of_reduceAux2 rK60 T60_29_2 (by decide)

theorem hcardT60_29_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK60)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK60 ⟨29, by decide⟩ R60_2 hpxR60_2 hcardq60_2 (by decide)).symm

/-- **Cell (60, 29) twin (q=2).** -/
theorem cell60_29_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK60) e = true)
    (h : ↥(reps (⟨29, by decide⟩ : Fin 148))) :
    species (reps (⟨29, by decide⟩ : Fin 148)) h (basisElt (reps rK60) (charOfVec2 rK60 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK60 e (h : Coordinate 2) T60_29_2 i :=
  species_entry_eq_sum rK60 ⟨29, by decide⟩ e heK h T60_29_2 hfix60_29_2 hinj60_29_2 hcardT60_29_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨29, by decide⟩) (reps rK60) (T60_29_2 i) (hfix60_29_2 i) h)

/-! ### Cell (60, 34) twin -/

def T60_34_2 : Fin 5 → Coordinate 2 := fun i => T60_34list.getD i.val (0,0,0,0,0)

theorem hfix60_34_2 : ∀ i, ((T60_34_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK60)
    ∈ fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK60) :=
  repsFix_of_siftB2 rK60 ⟨34, by decide⟩ T60_34_2 (by decide)

theorem hinj60_34_2 : Function.Injective
    (fun i => ((T60_34_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK60)) :=
  repsInj_of_reduceAux2 rK60 T60_34_2 (by decide)

theorem hcardT60_34_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK60)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK60 ⟨34, by decide⟩ R60_2 hpxR60_2 hcardq60_2 (by decide)).symm

/-- **Cell (60, 34) twin (q=2).** -/
theorem cell60_34_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK60) e = true)
    (h : ↥(reps (⟨34, by decide⟩ : Fin 148))) :
    species (reps (⟨34, by decide⟩ : Fin 148)) h (basisElt (reps rK60) (charOfVec2 rK60 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK60 e (h : Coordinate 2) T60_34_2 i :=
  species_entry_eq_sum rK60 ⟨34, by decide⟩ e heK h T60_34_2 hfix60_34_2 hinj60_34_2 hcardT60_34_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨34, by decide⟩) (reps rK60) (T60_34_2 i) (hfix60_34_2 i) h)

/-! ### Cell (60, 39) twin -/

def T60_39_2 : Fin 5 → Coordinate 2 := fun i => T60_39list.getD i.val (0,0,0,0,0)

theorem hfix60_39_2 : ∀ i, ((T60_39_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK60)
    ∈ fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK60) :=
  repsFix_of_siftB2 rK60 ⟨39, by decide⟩ T60_39_2 (by decide)

theorem hinj60_39_2 : Function.Injective
    (fun i => ((T60_39_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK60)) :=
  repsInj_of_reduceAux2 rK60 T60_39_2 (by decide)

theorem hcardT60_39_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK60)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK60 ⟨39, by decide⟩ R60_2 hpxR60_2 hcardq60_2 (by decide)).symm

/-- **Cell (60, 39) twin (q=2).** -/
theorem cell60_39_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK60) e = true)
    (h : ↥(reps (⟨39, by decide⟩ : Fin 148))) :
    species (reps (⟨39, by decide⟩ : Fin 148)) h (basisElt (reps rK60) (charOfVec2 rK60 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK60 e (h : Coordinate 2) T60_39_2 i :=
  species_entry_eq_sum rK60 ⟨39, by decide⟩ e heK h T60_39_2 hfix60_39_2 hinj60_39_2 hcardT60_39_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨39, by decide⟩) (reps rK60) (T60_39_2 i) (hfix60_39_2 i) h)

/-! ### Cell (60, 44) twin -/

def T60_44_2 : Fin 5 → Coordinate 2 := fun i => T60_44list.getD i.val (0,0,0,0,0)

theorem hfix60_44_2 : ∀ i, ((T60_44_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK60)
    ∈ fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK60) :=
  repsFix_of_siftB2 rK60 ⟨44, by decide⟩ T60_44_2 (by decide)

theorem hinj60_44_2 : Function.Injective
    (fun i => ((T60_44_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK60)) :=
  repsInj_of_reduceAux2 rK60 T60_44_2 (by decide)

theorem hcardT60_44_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK60)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK60 ⟨44, by decide⟩ R60_2 hpxR60_2 hcardq60_2 (by decide)).symm

/-- **Cell (60, 44) twin (q=2).** -/
theorem cell60_44_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK60) e = true)
    (h : ↥(reps (⟨44, by decide⟩ : Fin 148))) :
    species (reps (⟨44, by decide⟩ : Fin 148)) h (basisElt (reps rK60) (charOfVec2 rK60 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK60 e (h : Coordinate 2) T60_44_2 i :=
  species_entry_eq_sum rK60 ⟨44, by decide⟩ e heK h T60_44_2 hfix60_44_2 hinj60_44_2 hcardT60_44_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨44, by decide⟩) (reps rK60) (T60_44_2 i) (hfix60_44_2 i) h)

/-! ### Cell (60, 49) twin -/

def T60_49_2 : Fin 5 → Coordinate 2 := fun i => T60_49list.getD i.val (0,0,0,0,0)

theorem hfix60_49_2 : ∀ i, ((T60_49_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK60)
    ∈ fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK60) :=
  repsFix_of_siftB2 rK60 ⟨49, by decide⟩ T60_49_2 (by decide)

theorem hinj60_49_2 : Function.Injective
    (fun i => ((T60_49_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK60)) :=
  repsInj_of_reduceAux2 rK60 T60_49_2 (by decide)

theorem hcardT60_49_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK60)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK60 ⟨49, by decide⟩ R60_2 hpxR60_2 hcardq60_2 (by decide)).symm

/-- **Cell (60, 49) twin (q=2).** -/
theorem cell60_49_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK60) e = true)
    (h : ↥(reps (⟨49, by decide⟩ : Fin 148))) :
    species (reps (⟨49, by decide⟩ : Fin 148)) h (basisElt (reps rK60) (charOfVec2 rK60 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK60 e (h : Coordinate 2) T60_49_2 i :=
  species_entry_eq_sum rK60 ⟨49, by decide⟩ e heK h T60_49_2 hfix60_49_2 hinj60_49_2 hcardT60_49_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨49, by decide⟩) (reps rK60) (T60_49_2 i) (hfix60_49_2 i) h)

/-! ### Cell (60, 60) twin -/

def T60_60_2 : Fin 5 → Coordinate 2 := fun i => T60_60list.getD i.val (0,0,0,0,0)

theorem hfix60_60_2 : ∀ i, ((T60_60_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK60)
    ∈ fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK60) :=
  repsFix_of_siftB2 rK60 ⟨60, by decide⟩ T60_60_2 (by decide)

theorem hinj60_60_2 : Function.Injective
    (fun i => ((T60_60_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK60)) :=
  repsInj_of_reduceAux2 rK60 T60_60_2 (by decide)

theorem hcardT60_60_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK60)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK60 ⟨60, by decide⟩ R60_2 hpxR60_2 hcardq60_2 (by decide)).symm

/-- **Cell (60, 60) twin (q=2).** -/
theorem cell60_60_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK60) e = true)
    (h : ↥(reps (⟨60, by decide⟩ : Fin 148))) :
    species (reps (⟨60, by decide⟩ : Fin 148)) h (basisElt (reps rK60) (charOfVec2 rK60 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK60 e (h : Coordinate 2) T60_60_2 i :=
  species_entry_eq_sum rK60 ⟨60, by decide⟩ e heK h T60_60_2 hfix60_60_2 hinj60_60_2 hcardT60_60_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨60, by decide⟩) (reps rK60) (T60_60_2 i) (hfix60_60_2 i) h)

end Q2

/-! # K-class rK = 61  (|G/K| = 25) -/

def rK61 : Fin 148 := ⟨61, by decide⟩

def R61list : List Coordinates := [(0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0)]
def R61 : Fin 25 → Coordinate 1 := fun i => R61list.getD i.val (0,0,0,0,0)

theorem hpxR61 : Function.Injective (fun i => reduceAux 1 (basisAt rK61) (R61 i)) := by decide
theorem hcardq61 : Nat.card (Coordinate 1 ⧸ reps rK61) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (61, 0): |T| = 25 -/

def T61_0list : List Coordinates := [(0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0)]
def T61_0 : Fin 25 → Coordinate 1 := fun i => T61_0list.getD i.val (0,0,0,0,0)

theorem hfix61_0 : ∀ i, ((T61_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK61)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61) :=
  repsFix_of_siftB rK61 ⟨0, by decide⟩ T61_0 (by decide)

theorem hinj61_0 : Function.Injective
    (fun i => ((T61_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK61)) :=
  repsInj_of_reduceAux rK61 T61_0 (by decide)

theorem hcardT61_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK61 ⟨0, by decide⟩ R61 hpxR61 hcardq61 (by decide)).symm

/-- **Cell (61, 0).** -/
theorem cell61_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK61) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK61) (charOfVec rK61 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK61 e (h : Coordinate 1) T61_0 i :=
  species_entry_eq_sum rK61 ⟨0, by decide⟩ e heK h T61_0 hfix61_0 hinj61_0 hcardT61_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK61) (T61_0 i) (hfix61_0 i) h)

/-! ## Cell (61, 1): |T| = 25 -/

def T61_1list : List Coordinates := [(0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0)]
def T61_1 : Fin 25 → Coordinate 1 := fun i => T61_1list.getD i.val (0,0,0,0,0)

theorem hfix61_1 : ∀ i, ((T61_1 i : Coordinate 1) : Coordinate 1 ⧸ reps rK61)
    ∈ fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61) :=
  repsFix_of_siftB rK61 ⟨1, by decide⟩ T61_1 (by decide)

theorem hinj61_1 : Function.Injective
    (fun i => ((T61_1 i : Coordinate 1) : Coordinate 1 ⧸ reps rK61)) :=
  repsInj_of_reduceAux rK61 T61_1 (by decide)

theorem hcardT61_1 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK61 ⟨1, by decide⟩ R61 hpxR61 hcardq61 (by decide)).symm

/-- **Cell (61, 1).** -/
theorem cell61_1 (e : List (ZMod 25)) (heK : charOK (basisAt rK61) e = true)
    (h : ↥(reps (⟨1, by decide⟩ : Fin 148))) :
    species (reps (⟨1, by decide⟩ : Fin 148)) h (basisElt (reps rK61) (charOfVec rK61 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK61 e (h : Coordinate 1) T61_1 i :=
  species_entry_eq_sum rK61 ⟨1, by decide⟩ e heK h T61_1 hfix61_1 hinj61_1 hcardT61_1
    (fun i => conj_mem_of_fixedPoints (reps ⟨1, by decide⟩) (reps rK61) (T61_1 i) (hfix61_1 i) h)

/-! ## Cell (61, 12): |T| = 25 -/

def T61_12list : List Coordinates := [(0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0)]
def T61_12 : Fin 25 → Coordinate 1 := fun i => T61_12list.getD i.val (0,0,0,0,0)

theorem hfix61_12 : ∀ i, ((T61_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK61)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61) :=
  repsFix_of_siftB rK61 ⟨12, by decide⟩ T61_12 (by decide)

theorem hinj61_12 : Function.Injective
    (fun i => ((T61_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK61)) :=
  repsInj_of_reduceAux rK61 T61_12 (by decide)

theorem hcardT61_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK61 ⟨12, by decide⟩ R61 hpxR61 hcardq61 (by decide)).symm

/-- **Cell (61, 12).** -/
theorem cell61_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK61) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK61) (charOfVec rK61 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK61 e (h : Coordinate 1) T61_12 i :=
  species_entry_eq_sum rK61 ⟨12, by decide⟩ e heK h T61_12 hfix61_12 hinj61_12 hcardT61_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK61) (T61_12 i) (hfix61_12 i) h)

/-! ## Cell (61, 19): |T| = 25 -/

def T61_19list : List Coordinates := [(0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0)]
def T61_19 : Fin 25 → Coordinate 1 := fun i => T61_19list.getD i.val (0,0,0,0,0)

theorem hfix61_19 : ∀ i, ((T61_19 i : Coordinate 1) : Coordinate 1 ⧸ reps rK61)
    ∈ fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61) :=
  repsFix_of_siftB rK61 ⟨19, by decide⟩ T61_19 (by decide)

theorem hinj61_19 : Function.Injective
    (fun i => ((T61_19 i : Coordinate 1) : Coordinate 1 ⧸ reps rK61)) :=
  repsInj_of_reduceAux rK61 T61_19 (by decide)

theorem hcardT61_19 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK61 ⟨19, by decide⟩ R61 hpxR61 hcardq61 (by decide)).symm

/-- **Cell (61, 19).** -/
theorem cell61_19 (e : List (ZMod 25)) (heK : charOK (basisAt rK61) e = true)
    (h : ↥(reps (⟨19, by decide⟩ : Fin 148))) :
    species (reps (⟨19, by decide⟩ : Fin 148)) h (basisElt (reps rK61) (charOfVec rK61 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK61 e (h : Coordinate 1) T61_19 i :=
  species_entry_eq_sum rK61 ⟨19, by decide⟩ e heK h T61_19 hfix61_19 hinj61_19 hcardT61_19
    (fun i => conj_mem_of_fixedPoints (reps ⟨19, by decide⟩) (reps rK61) (T61_19 i) (hfix61_19 i) h)

/-! ## Cell (61, 29): |T| = 5 -/

def T61_29list : List Coordinates := [(0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0)]
def T61_29 : Fin 5 → Coordinate 1 := fun i => T61_29list.getD i.val (0,0,0,0,0)

theorem hfix61_29 : ∀ i, ((T61_29 i : Coordinate 1) : Coordinate 1 ⧸ reps rK61)
    ∈ fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61) :=
  repsFix_of_siftB rK61 ⟨29, by decide⟩ T61_29 (by decide)

theorem hinj61_29 : Function.Injective
    (fun i => ((T61_29 i : Coordinate 1) : Coordinate 1 ⧸ reps rK61)) :=
  repsInj_of_reduceAux rK61 T61_29 (by decide)

theorem hcardT61_29 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK61 ⟨29, by decide⟩ R61 hpxR61 hcardq61 (by decide)).symm

/-- **Cell (61, 29).** -/
theorem cell61_29 (e : List (ZMod 25)) (heK : charOK (basisAt rK61) e = true)
    (h : ↥(reps (⟨29, by decide⟩ : Fin 148))) :
    species (reps (⟨29, by decide⟩ : Fin 148)) h (basisElt (reps rK61) (charOfVec rK61 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK61 e (h : Coordinate 1) T61_29 i :=
  species_entry_eq_sum rK61 ⟨29, by decide⟩ e heK h T61_29 hfix61_29 hinj61_29 hcardT61_29
    (fun i => conj_mem_of_fixedPoints (reps ⟨29, by decide⟩) (reps rK61) (T61_29 i) (hfix61_29 i) h)

/-! ## Cell (61, 34): |T| = 5 -/

def T61_34list : List Coordinates := [(0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0)]
def T61_34 : Fin 5 → Coordinate 1 := fun i => T61_34list.getD i.val (0,0,0,0,0)

theorem hfix61_34 : ∀ i, ((T61_34 i : Coordinate 1) : Coordinate 1 ⧸ reps rK61)
    ∈ fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61) :=
  repsFix_of_siftB rK61 ⟨34, by decide⟩ T61_34 (by decide)

theorem hinj61_34 : Function.Injective
    (fun i => ((T61_34 i : Coordinate 1) : Coordinate 1 ⧸ reps rK61)) :=
  repsInj_of_reduceAux rK61 T61_34 (by decide)

theorem hcardT61_34 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK61 ⟨34, by decide⟩ R61 hpxR61 hcardq61 (by decide)).symm

/-- **Cell (61, 34).** -/
theorem cell61_34 (e : List (ZMod 25)) (heK : charOK (basisAt rK61) e = true)
    (h : ↥(reps (⟨34, by decide⟩ : Fin 148))) :
    species (reps (⟨34, by decide⟩ : Fin 148)) h (basisElt (reps rK61) (charOfVec rK61 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK61 e (h : Coordinate 1) T61_34 i :=
  species_entry_eq_sum rK61 ⟨34, by decide⟩ e heK h T61_34 hfix61_34 hinj61_34 hcardT61_34
    (fun i => conj_mem_of_fixedPoints (reps ⟨34, by decide⟩) (reps rK61) (T61_34 i) (hfix61_34 i) h)

/-! ## Cell (61, 39): |T| = 5 -/

def T61_39list : List Coordinates := [(0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0)]
def T61_39 : Fin 5 → Coordinate 1 := fun i => T61_39list.getD i.val (0,0,0,0,0)

theorem hfix61_39 : ∀ i, ((T61_39 i : Coordinate 1) : Coordinate 1 ⧸ reps rK61)
    ∈ fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61) :=
  repsFix_of_siftB rK61 ⟨39, by decide⟩ T61_39 (by decide)

theorem hinj61_39 : Function.Injective
    (fun i => ((T61_39 i : Coordinate 1) : Coordinate 1 ⧸ reps rK61)) :=
  repsInj_of_reduceAux rK61 T61_39 (by decide)

theorem hcardT61_39 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK61 ⟨39, by decide⟩ R61 hpxR61 hcardq61 (by decide)).symm

/-- **Cell (61, 39).** -/
theorem cell61_39 (e : List (ZMod 25)) (heK : charOK (basisAt rK61) e = true)
    (h : ↥(reps (⟨39, by decide⟩ : Fin 148))) :
    species (reps (⟨39, by decide⟩ : Fin 148)) h (basisElt (reps rK61) (charOfVec rK61 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK61 e (h : Coordinate 1) T61_39 i :=
  species_entry_eq_sum rK61 ⟨39, by decide⟩ e heK h T61_39 hfix61_39 hinj61_39 hcardT61_39
    (fun i => conj_mem_of_fixedPoints (reps ⟨39, by decide⟩) (reps rK61) (T61_39 i) (hfix61_39 i) h)

/-! ## Cell (61, 44): |T| = 5 -/

def T61_44list : List Coordinates := [(0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0)]
def T61_44 : Fin 5 → Coordinate 1 := fun i => T61_44list.getD i.val (0,0,0,0,0)

theorem hfix61_44 : ∀ i, ((T61_44 i : Coordinate 1) : Coordinate 1 ⧸ reps rK61)
    ∈ fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61) :=
  repsFix_of_siftB rK61 ⟨44, by decide⟩ T61_44 (by decide)

theorem hinj61_44 : Function.Injective
    (fun i => ((T61_44 i : Coordinate 1) : Coordinate 1 ⧸ reps rK61)) :=
  repsInj_of_reduceAux rK61 T61_44 (by decide)

theorem hcardT61_44 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK61 ⟨44, by decide⟩ R61 hpxR61 hcardq61 (by decide)).symm

/-- **Cell (61, 44).** -/
theorem cell61_44 (e : List (ZMod 25)) (heK : charOK (basisAt rK61) e = true)
    (h : ↥(reps (⟨44, by decide⟩ : Fin 148))) :
    species (reps (⟨44, by decide⟩ : Fin 148)) h (basisElt (reps rK61) (charOfVec rK61 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK61 e (h : Coordinate 1) T61_44 i :=
  species_entry_eq_sum rK61 ⟨44, by decide⟩ e heK h T61_44 hfix61_44 hinj61_44 hcardT61_44
    (fun i => conj_mem_of_fixedPoints (reps ⟨44, by decide⟩) (reps rK61) (T61_44 i) (hfix61_44 i) h)

/-! ## Cell (61, 49): |T| = 5 -/

def T61_49list : List Coordinates := [(0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0)]
def T61_49 : Fin 5 → Coordinate 1 := fun i => T61_49list.getD i.val (0,0,0,0,0)

theorem hfix61_49 : ∀ i, ((T61_49 i : Coordinate 1) : Coordinate 1 ⧸ reps rK61)
    ∈ fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61) :=
  repsFix_of_siftB rK61 ⟨49, by decide⟩ T61_49 (by decide)

theorem hinj61_49 : Function.Injective
    (fun i => ((T61_49 i : Coordinate 1) : Coordinate 1 ⧸ reps rK61)) :=
  repsInj_of_reduceAux rK61 T61_49 (by decide)

theorem hcardT61_49 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK61 ⟨49, by decide⟩ R61 hpxR61 hcardq61 (by decide)).symm

/-- **Cell (61, 49).** -/
theorem cell61_49 (e : List (ZMod 25)) (heK : charOK (basisAt rK61) e = true)
    (h : ↥(reps (⟨49, by decide⟩ : Fin 148))) :
    species (reps (⟨49, by decide⟩ : Fin 148)) h (basisElt (reps rK61) (charOfVec rK61 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK61 e (h : Coordinate 1) T61_49 i :=
  species_entry_eq_sum rK61 ⟨49, by decide⟩ e heK h T61_49 hfix61_49 hinj61_49 hcardT61_49
    (fun i => conj_mem_of_fixedPoints (reps ⟨49, by decide⟩) (reps rK61) (T61_49 i) (hfix61_49 i) h)

/-! ## Cell (61, 61): |T| = 5 -/

def T61_61list : List Coordinates := [(0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0)]
def T61_61 : Fin 5 → Coordinate 1 := fun i => T61_61list.getD i.val (0,0,0,0,0)

theorem hfix61_61 : ∀ i, ((T61_61 i : Coordinate 1) : Coordinate 1 ⧸ reps rK61)
    ∈ fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61) :=
  repsFix_of_siftB rK61 ⟨61, by decide⟩ T61_61 (by decide)

theorem hinj61_61 : Function.Injective
    (fun i => ((T61_61 i : Coordinate 1) : Coordinate 1 ⧸ reps rK61)) :=
  repsInj_of_reduceAux rK61 T61_61 (by decide)

theorem hcardT61_61 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK61 ⟨61, by decide⟩ R61 hpxR61 hcardq61 (by decide)).symm

/-- **Cell (61, 61).** -/
theorem cell61_61 (e : List (ZMod 25)) (heK : charOK (basisAt rK61) e = true)
    (h : ↥(reps (⟨61, by decide⟩ : Fin 148))) :
    species (reps (⟨61, by decide⟩ : Fin 148)) h (basisElt (reps rK61) (charOfVec rK61 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK61 e (h : Coordinate 1) T61_61 i :=
  species_entry_eq_sum rK61 ⟨61, by decide⟩ e heK h T61_61 hfix61_61 hinj61_61 hcardT61_61
    (fun i => conj_mem_of_fixedPoints (reps ⟨61, by decide⟩) (reps rK61) (T61_61 i) (hfix61_61 i) h)

namespace Q2

def R61_2 : Fin 25 → Coordinate 2 := fun i => R61list.getD i.val (0,0,0,0,0)
theorem hpxR61_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK61) (R61_2 i)) := by decide
theorem hcardq61_2 : Nat.card (Coordinate 2 ⧸ reps rK61) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (61, 0) twin -/

def T61_0_2 : Fin 25 → Coordinate 2 := fun i => T61_0list.getD i.val (0,0,0,0,0)

theorem hfix61_0_2 : ∀ i, ((T61_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK61)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK61) :=
  repsFix_of_siftB2 rK61 ⟨0, by decide⟩ T61_0_2 (by decide)

theorem hinj61_0_2 : Function.Injective
    (fun i => ((T61_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK61)) :=
  repsInj_of_reduceAux2 rK61 T61_0_2 (by decide)

theorem hcardT61_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK61)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK61 ⟨0, by decide⟩ R61_2 hpxR61_2 hcardq61_2 (by decide)).symm

/-- **Cell (61, 0) twin (q=2).** -/
theorem cell61_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK61) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK61) (charOfVec2 rK61 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK61 e (h : Coordinate 2) T61_0_2 i :=
  species_entry_eq_sum rK61 ⟨0, by decide⟩ e heK h T61_0_2 hfix61_0_2 hinj61_0_2 hcardT61_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK61) (T61_0_2 i) (hfix61_0_2 i) h)

/-! ### Cell (61, 1) twin -/

def T61_1_2 : Fin 25 → Coordinate 2 := fun i => T61_1list.getD i.val (0,0,0,0,0)

theorem hfix61_1_2 : ∀ i, ((T61_1_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK61)
    ∈ fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK61) :=
  repsFix_of_siftB2 rK61 ⟨1, by decide⟩ T61_1_2 (by decide)

theorem hinj61_1_2 : Function.Injective
    (fun i => ((T61_1_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK61)) :=
  repsInj_of_reduceAux2 rK61 T61_1_2 (by decide)

theorem hcardT61_1_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK61)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK61 ⟨1, by decide⟩ R61_2 hpxR61_2 hcardq61_2 (by decide)).symm

/-- **Cell (61, 1) twin (q=2).** -/
theorem cell61_1_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK61) e = true)
    (h : ↥(reps (⟨1, by decide⟩ : Fin 148))) :
    species (reps (⟨1, by decide⟩ : Fin 148)) h (basisElt (reps rK61) (charOfVec2 rK61 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK61 e (h : Coordinate 2) T61_1_2 i :=
  species_entry_eq_sum rK61 ⟨1, by decide⟩ e heK h T61_1_2 hfix61_1_2 hinj61_1_2 hcardT61_1_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨1, by decide⟩) (reps rK61) (T61_1_2 i) (hfix61_1_2 i) h)

/-! ### Cell (61, 12) twin -/

def T61_12_2 : Fin 25 → Coordinate 2 := fun i => T61_12list.getD i.val (0,0,0,0,0)

theorem hfix61_12_2 : ∀ i, ((T61_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK61)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK61) :=
  repsFix_of_siftB2 rK61 ⟨12, by decide⟩ T61_12_2 (by decide)

theorem hinj61_12_2 : Function.Injective
    (fun i => ((T61_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK61)) :=
  repsInj_of_reduceAux2 rK61 T61_12_2 (by decide)

theorem hcardT61_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK61)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK61 ⟨12, by decide⟩ R61_2 hpxR61_2 hcardq61_2 (by decide)).symm

/-- **Cell (61, 12) twin (q=2).** -/
theorem cell61_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK61) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK61) (charOfVec2 rK61 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK61 e (h : Coordinate 2) T61_12_2 i :=
  species_entry_eq_sum rK61 ⟨12, by decide⟩ e heK h T61_12_2 hfix61_12_2 hinj61_12_2 hcardT61_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK61) (T61_12_2 i) (hfix61_12_2 i) h)

/-! ### Cell (61, 19) twin -/

def T61_19_2 : Fin 25 → Coordinate 2 := fun i => T61_19list.getD i.val (0,0,0,0,0)

theorem hfix61_19_2 : ∀ i, ((T61_19_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK61)
    ∈ fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK61) :=
  repsFix_of_siftB2 rK61 ⟨19, by decide⟩ T61_19_2 (by decide)

theorem hinj61_19_2 : Function.Injective
    (fun i => ((T61_19_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK61)) :=
  repsInj_of_reduceAux2 rK61 T61_19_2 (by decide)

theorem hcardT61_19_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK61)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK61 ⟨19, by decide⟩ R61_2 hpxR61_2 hcardq61_2 (by decide)).symm

/-- **Cell (61, 19) twin (q=2).** -/
theorem cell61_19_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK61) e = true)
    (h : ↥(reps (⟨19, by decide⟩ : Fin 148))) :
    species (reps (⟨19, by decide⟩ : Fin 148)) h (basisElt (reps rK61) (charOfVec2 rK61 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK61 e (h : Coordinate 2) T61_19_2 i :=
  species_entry_eq_sum rK61 ⟨19, by decide⟩ e heK h T61_19_2 hfix61_19_2 hinj61_19_2 hcardT61_19_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨19, by decide⟩) (reps rK61) (T61_19_2 i) (hfix61_19_2 i) h)

/-! ### Cell (61, 29) twin -/

def T61_29_2 : Fin 5 → Coordinate 2 := fun i => T61_29list.getD i.val (0,0,0,0,0)

theorem hfix61_29_2 : ∀ i, ((T61_29_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK61)
    ∈ fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK61) :=
  repsFix_of_siftB2 rK61 ⟨29, by decide⟩ T61_29_2 (by decide)

theorem hinj61_29_2 : Function.Injective
    (fun i => ((T61_29_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK61)) :=
  repsInj_of_reduceAux2 rK61 T61_29_2 (by decide)

theorem hcardT61_29_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK61)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK61 ⟨29, by decide⟩ R61_2 hpxR61_2 hcardq61_2 (by decide)).symm

/-- **Cell (61, 29) twin (q=2).** -/
theorem cell61_29_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK61) e = true)
    (h : ↥(reps (⟨29, by decide⟩ : Fin 148))) :
    species (reps (⟨29, by decide⟩ : Fin 148)) h (basisElt (reps rK61) (charOfVec2 rK61 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK61 e (h : Coordinate 2) T61_29_2 i :=
  species_entry_eq_sum rK61 ⟨29, by decide⟩ e heK h T61_29_2 hfix61_29_2 hinj61_29_2 hcardT61_29_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨29, by decide⟩) (reps rK61) (T61_29_2 i) (hfix61_29_2 i) h)

/-! ### Cell (61, 34) twin -/

def T61_34_2 : Fin 5 → Coordinate 2 := fun i => T61_34list.getD i.val (0,0,0,0,0)

theorem hfix61_34_2 : ∀ i, ((T61_34_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK61)
    ∈ fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK61) :=
  repsFix_of_siftB2 rK61 ⟨34, by decide⟩ T61_34_2 (by decide)

theorem hinj61_34_2 : Function.Injective
    (fun i => ((T61_34_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK61)) :=
  repsInj_of_reduceAux2 rK61 T61_34_2 (by decide)

theorem hcardT61_34_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK61)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK61 ⟨34, by decide⟩ R61_2 hpxR61_2 hcardq61_2 (by decide)).symm

/-- **Cell (61, 34) twin (q=2).** -/
theorem cell61_34_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK61) e = true)
    (h : ↥(reps (⟨34, by decide⟩ : Fin 148))) :
    species (reps (⟨34, by decide⟩ : Fin 148)) h (basisElt (reps rK61) (charOfVec2 rK61 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK61 e (h : Coordinate 2) T61_34_2 i :=
  species_entry_eq_sum rK61 ⟨34, by decide⟩ e heK h T61_34_2 hfix61_34_2 hinj61_34_2 hcardT61_34_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨34, by decide⟩) (reps rK61) (T61_34_2 i) (hfix61_34_2 i) h)

/-! ### Cell (61, 39) twin -/

def T61_39_2 : Fin 5 → Coordinate 2 := fun i => T61_39list.getD i.val (0,0,0,0,0)

theorem hfix61_39_2 : ∀ i, ((T61_39_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK61)
    ∈ fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK61) :=
  repsFix_of_siftB2 rK61 ⟨39, by decide⟩ T61_39_2 (by decide)

theorem hinj61_39_2 : Function.Injective
    (fun i => ((T61_39_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK61)) :=
  repsInj_of_reduceAux2 rK61 T61_39_2 (by decide)

theorem hcardT61_39_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK61)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK61 ⟨39, by decide⟩ R61_2 hpxR61_2 hcardq61_2 (by decide)).symm

/-- **Cell (61, 39) twin (q=2).** -/
theorem cell61_39_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK61) e = true)
    (h : ↥(reps (⟨39, by decide⟩ : Fin 148))) :
    species (reps (⟨39, by decide⟩ : Fin 148)) h (basisElt (reps rK61) (charOfVec2 rK61 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK61 e (h : Coordinate 2) T61_39_2 i :=
  species_entry_eq_sum rK61 ⟨39, by decide⟩ e heK h T61_39_2 hfix61_39_2 hinj61_39_2 hcardT61_39_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨39, by decide⟩) (reps rK61) (T61_39_2 i) (hfix61_39_2 i) h)

/-! ### Cell (61, 44) twin -/

def T61_44_2 : Fin 5 → Coordinate 2 := fun i => T61_44list.getD i.val (0,0,0,0,0)

theorem hfix61_44_2 : ∀ i, ((T61_44_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK61)
    ∈ fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK61) :=
  repsFix_of_siftB2 rK61 ⟨44, by decide⟩ T61_44_2 (by decide)

theorem hinj61_44_2 : Function.Injective
    (fun i => ((T61_44_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK61)) :=
  repsInj_of_reduceAux2 rK61 T61_44_2 (by decide)

theorem hcardT61_44_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK61)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK61 ⟨44, by decide⟩ R61_2 hpxR61_2 hcardq61_2 (by decide)).symm

/-- **Cell (61, 44) twin (q=2).** -/
theorem cell61_44_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK61) e = true)
    (h : ↥(reps (⟨44, by decide⟩ : Fin 148))) :
    species (reps (⟨44, by decide⟩ : Fin 148)) h (basisElt (reps rK61) (charOfVec2 rK61 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK61 e (h : Coordinate 2) T61_44_2 i :=
  species_entry_eq_sum rK61 ⟨44, by decide⟩ e heK h T61_44_2 hfix61_44_2 hinj61_44_2 hcardT61_44_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨44, by decide⟩) (reps rK61) (T61_44_2 i) (hfix61_44_2 i) h)

/-! ### Cell (61, 49) twin -/

def T61_49_2 : Fin 5 → Coordinate 2 := fun i => T61_49list.getD i.val (0,0,0,0,0)

theorem hfix61_49_2 : ∀ i, ((T61_49_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK61)
    ∈ fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK61) :=
  repsFix_of_siftB2 rK61 ⟨49, by decide⟩ T61_49_2 (by decide)

theorem hinj61_49_2 : Function.Injective
    (fun i => ((T61_49_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK61)) :=
  repsInj_of_reduceAux2 rK61 T61_49_2 (by decide)

theorem hcardT61_49_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK61)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK61 ⟨49, by decide⟩ R61_2 hpxR61_2 hcardq61_2 (by decide)).symm

/-- **Cell (61, 49) twin (q=2).** -/
theorem cell61_49_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK61) e = true)
    (h : ↥(reps (⟨49, by decide⟩ : Fin 148))) :
    species (reps (⟨49, by decide⟩ : Fin 148)) h (basisElt (reps rK61) (charOfVec2 rK61 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK61 e (h : Coordinate 2) T61_49_2 i :=
  species_entry_eq_sum rK61 ⟨49, by decide⟩ e heK h T61_49_2 hfix61_49_2 hinj61_49_2 hcardT61_49_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨49, by decide⟩) (reps rK61) (T61_49_2 i) (hfix61_49_2 i) h)

/-! ### Cell (61, 61) twin -/

def T61_61_2 : Fin 5 → Coordinate 2 := fun i => T61_61list.getD i.val (0,0,0,0,0)

theorem hfix61_61_2 : ∀ i, ((T61_61_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK61)
    ∈ fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK61) :=
  repsFix_of_siftB2 rK61 ⟨61, by decide⟩ T61_61_2 (by decide)

theorem hinj61_61_2 : Function.Injective
    (fun i => ((T61_61_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK61)) :=
  repsInj_of_reduceAux2 rK61 T61_61_2 (by decide)

theorem hcardT61_61_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK61)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK61 ⟨61, by decide⟩ R61_2 hpxR61_2 hcardq61_2 (by decide)).symm

/-- **Cell (61, 61) twin (q=2).** -/
theorem cell61_61_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK61) e = true)
    (h : ↥(reps (⟨61, by decide⟩ : Fin 148))) :
    species (reps (⟨61, by decide⟩ : Fin 148)) h (basisElt (reps rK61) (charOfVec2 rK61 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK61 e (h : Coordinate 2) T61_61_2 i :=
  species_entry_eq_sum rK61 ⟨61, by decide⟩ e heK h T61_61_2 hfix61_61_2 hinj61_61_2 hcardT61_61_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨61, by decide⟩) (reps rK61) (T61_61_2 i) (hfix61_61_2 i) h)

end Q2

/-! # K-class rK = 62  (|G/K| = 25) -/

def rK62 : Fin 148 := ⟨62, by decide⟩

def R62list : List Coordinates := [(0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0)]
def R62 : Fin 25 → Coordinate 1 := fun i => R62list.getD i.val (0,0,0,0,0)

theorem hpxR62 : Function.Injective (fun i => reduceAux 1 (basisAt rK62) (R62 i)) := by decide
theorem hcardq62 : Nat.card (Coordinate 1 ⧸ reps rK62) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (62, 0): |T| = 25 -/

def T62_0list : List Coordinates := [(0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0)]
def T62_0 : Fin 25 → Coordinate 1 := fun i => T62_0list.getD i.val (0,0,0,0,0)

theorem hfix62_0 : ∀ i, ((T62_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK62)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62) :=
  repsFix_of_siftB rK62 ⟨0, by decide⟩ T62_0 (by decide)

theorem hinj62_0 : Function.Injective
    (fun i => ((T62_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK62)) :=
  repsInj_of_reduceAux rK62 T62_0 (by decide)

theorem hcardT62_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK62 ⟨0, by decide⟩ R62 hpxR62 hcardq62 (by decide)).symm

/-- **Cell (62, 0).** -/
theorem cell62_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK62) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK62) (charOfVec rK62 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK62 e (h : Coordinate 1) T62_0 i :=
  species_entry_eq_sum rK62 ⟨0, by decide⟩ e heK h T62_0 hfix62_0 hinj62_0 hcardT62_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK62) (T62_0 i) (hfix62_0 i) h)

/-! ## Cell (62, 7): |T| = 25 -/

def T62_7list : List Coordinates := [(0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0)]
def T62_7 : Fin 25 → Coordinate 1 := fun i => T62_7list.getD i.val (0,0,0,0,0)

theorem hfix62_7 : ∀ i, ((T62_7 i : Coordinate 1) : Coordinate 1 ⧸ reps rK62)
    ∈ fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62) :=
  repsFix_of_siftB rK62 ⟨7, by decide⟩ T62_7 (by decide)

theorem hinj62_7 : Function.Injective
    (fun i => ((T62_7 i : Coordinate 1) : Coordinate 1 ⧸ reps rK62)) :=
  repsInj_of_reduceAux rK62 T62_7 (by decide)

theorem hcardT62_7 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK62 ⟨7, by decide⟩ R62 hpxR62 hcardq62 (by decide)).symm

/-- **Cell (62, 7).** -/
theorem cell62_7 (e : List (ZMod 25)) (heK : charOK (basisAt rK62) e = true)
    (h : ↥(reps (⟨7, by decide⟩ : Fin 148))) :
    species (reps (⟨7, by decide⟩ : Fin 148)) h (basisElt (reps rK62) (charOfVec rK62 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK62 e (h : Coordinate 1) T62_7 i :=
  species_entry_eq_sum rK62 ⟨7, by decide⟩ e heK h T62_7 hfix62_7 hinj62_7 hcardT62_7
    (fun i => conj_mem_of_fixedPoints (reps ⟨7, by decide⟩) (reps rK62) (T62_7 i) (hfix62_7 i) h)

/-! ## Cell (62, 12): |T| = 25 -/

def T62_12list : List Coordinates := [(0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0)]
def T62_12 : Fin 25 → Coordinate 1 := fun i => T62_12list.getD i.val (0,0,0,0,0)

theorem hfix62_12 : ∀ i, ((T62_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK62)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62) :=
  repsFix_of_siftB rK62 ⟨12, by decide⟩ T62_12 (by decide)

theorem hinj62_12 : Function.Injective
    (fun i => ((T62_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK62)) :=
  repsInj_of_reduceAux rK62 T62_12 (by decide)

theorem hcardT62_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK62 ⟨12, by decide⟩ R62 hpxR62 hcardq62 (by decide)).symm

/-- **Cell (62, 12).** -/
theorem cell62_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK62) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK62) (charOfVec rK62 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK62 e (h : Coordinate 1) T62_12 i :=
  species_entry_eq_sum rK62 ⟨12, by decide⟩ e heK h T62_12 hfix62_12 hinj62_12 hcardT62_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK62) (T62_12 i) (hfix62_12 i) h)

/-! ## Cell (62, 25): |T| = 25 -/

def T62_25list : List Coordinates := [(0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0)]
def T62_25 : Fin 25 → Coordinate 1 := fun i => T62_25list.getD i.val (0,0,0,0,0)

theorem hfix62_25 : ∀ i, ((T62_25 i : Coordinate 1) : Coordinate 1 ⧸ reps rK62)
    ∈ fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62) :=
  repsFix_of_siftB rK62 ⟨25, by decide⟩ T62_25 (by decide)

theorem hinj62_25 : Function.Injective
    (fun i => ((T62_25 i : Coordinate 1) : Coordinate 1 ⧸ reps rK62)) :=
  repsInj_of_reduceAux rK62 T62_25 (by decide)

theorem hcardT62_25 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK62 ⟨25, by decide⟩ R62 hpxR62 hcardq62 (by decide)).symm

/-- **Cell (62, 25).** -/
theorem cell62_25 (e : List (ZMod 25)) (heK : charOK (basisAt rK62) e = true)
    (h : ↥(reps (⟨25, by decide⟩ : Fin 148))) :
    species (reps (⟨25, by decide⟩ : Fin 148)) h (basisElt (reps rK62) (charOfVec rK62 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK62 e (h : Coordinate 1) T62_25 i :=
  species_entry_eq_sum rK62 ⟨25, by decide⟩ e heK h T62_25 hfix62_25 hinj62_25 hcardT62_25
    (fun i => conj_mem_of_fixedPoints (reps ⟨25, by decide⟩) (reps rK62) (T62_25 i) (hfix62_25 i) h)

/-! ## Cell (62, 29): |T| = 5 -/

def T62_29list : List Coordinates := [(0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0)]
def T62_29 : Fin 5 → Coordinate 1 := fun i => T62_29list.getD i.val (0,0,0,0,0)

theorem hfix62_29 : ∀ i, ((T62_29 i : Coordinate 1) : Coordinate 1 ⧸ reps rK62)
    ∈ fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62) :=
  repsFix_of_siftB rK62 ⟨29, by decide⟩ T62_29 (by decide)

theorem hinj62_29 : Function.Injective
    (fun i => ((T62_29 i : Coordinate 1) : Coordinate 1 ⧸ reps rK62)) :=
  repsInj_of_reduceAux rK62 T62_29 (by decide)

theorem hcardT62_29 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK62 ⟨29, by decide⟩ R62 hpxR62 hcardq62 (by decide)).symm

/-- **Cell (62, 29).** -/
theorem cell62_29 (e : List (ZMod 25)) (heK : charOK (basisAt rK62) e = true)
    (h : ↥(reps (⟨29, by decide⟩ : Fin 148))) :
    species (reps (⟨29, by decide⟩ : Fin 148)) h (basisElt (reps rK62) (charOfVec rK62 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK62 e (h : Coordinate 1) T62_29 i :=
  species_entry_eq_sum rK62 ⟨29, by decide⟩ e heK h T62_29 hfix62_29 hinj62_29 hcardT62_29
    (fun i => conj_mem_of_fixedPoints (reps ⟨29, by decide⟩) (reps rK62) (T62_29 i) (hfix62_29 i) h)

/-! ## Cell (62, 34): |T| = 5 -/

def T62_34list : List Coordinates := [(0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0)]
def T62_34 : Fin 5 → Coordinate 1 := fun i => T62_34list.getD i.val (0,0,0,0,0)

theorem hfix62_34 : ∀ i, ((T62_34 i : Coordinate 1) : Coordinate 1 ⧸ reps rK62)
    ∈ fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62) :=
  repsFix_of_siftB rK62 ⟨34, by decide⟩ T62_34 (by decide)

theorem hinj62_34 : Function.Injective
    (fun i => ((T62_34 i : Coordinate 1) : Coordinate 1 ⧸ reps rK62)) :=
  repsInj_of_reduceAux rK62 T62_34 (by decide)

theorem hcardT62_34 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK62 ⟨34, by decide⟩ R62 hpxR62 hcardq62 (by decide)).symm

/-- **Cell (62, 34).** -/
theorem cell62_34 (e : List (ZMod 25)) (heK : charOK (basisAt rK62) e = true)
    (h : ↥(reps (⟨34, by decide⟩ : Fin 148))) :
    species (reps (⟨34, by decide⟩ : Fin 148)) h (basisElt (reps rK62) (charOfVec rK62 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK62 e (h : Coordinate 1) T62_34 i :=
  species_entry_eq_sum rK62 ⟨34, by decide⟩ e heK h T62_34 hfix62_34 hinj62_34 hcardT62_34
    (fun i => conj_mem_of_fixedPoints (reps ⟨34, by decide⟩) (reps rK62) (T62_34 i) (hfix62_34 i) h)

/-! ## Cell (62, 39): |T| = 5 -/

def T62_39list : List Coordinates := [(0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0)]
def T62_39 : Fin 5 → Coordinate 1 := fun i => T62_39list.getD i.val (0,0,0,0,0)

theorem hfix62_39 : ∀ i, ((T62_39 i : Coordinate 1) : Coordinate 1 ⧸ reps rK62)
    ∈ fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62) :=
  repsFix_of_siftB rK62 ⟨39, by decide⟩ T62_39 (by decide)

theorem hinj62_39 : Function.Injective
    (fun i => ((T62_39 i : Coordinate 1) : Coordinate 1 ⧸ reps rK62)) :=
  repsInj_of_reduceAux rK62 T62_39 (by decide)

theorem hcardT62_39 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK62 ⟨39, by decide⟩ R62 hpxR62 hcardq62 (by decide)).symm

/-- **Cell (62, 39).** -/
theorem cell62_39 (e : List (ZMod 25)) (heK : charOK (basisAt rK62) e = true)
    (h : ↥(reps (⟨39, by decide⟩ : Fin 148))) :
    species (reps (⟨39, by decide⟩ : Fin 148)) h (basisElt (reps rK62) (charOfVec rK62 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK62 e (h : Coordinate 1) T62_39 i :=
  species_entry_eq_sum rK62 ⟨39, by decide⟩ e heK h T62_39 hfix62_39 hinj62_39 hcardT62_39
    (fun i => conj_mem_of_fixedPoints (reps ⟨39, by decide⟩) (reps rK62) (T62_39 i) (hfix62_39 i) h)

/-! ## Cell (62, 44): |T| = 5 -/

def T62_44list : List Coordinates := [(0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0)]
def T62_44 : Fin 5 → Coordinate 1 := fun i => T62_44list.getD i.val (0,0,0,0,0)

theorem hfix62_44 : ∀ i, ((T62_44 i : Coordinate 1) : Coordinate 1 ⧸ reps rK62)
    ∈ fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62) :=
  repsFix_of_siftB rK62 ⟨44, by decide⟩ T62_44 (by decide)

theorem hinj62_44 : Function.Injective
    (fun i => ((T62_44 i : Coordinate 1) : Coordinate 1 ⧸ reps rK62)) :=
  repsInj_of_reduceAux rK62 T62_44 (by decide)

theorem hcardT62_44 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK62 ⟨44, by decide⟩ R62 hpxR62 hcardq62 (by decide)).symm

/-- **Cell (62, 44).** -/
theorem cell62_44 (e : List (ZMod 25)) (heK : charOK (basisAt rK62) e = true)
    (h : ↥(reps (⟨44, by decide⟩ : Fin 148))) :
    species (reps (⟨44, by decide⟩ : Fin 148)) h (basisElt (reps rK62) (charOfVec rK62 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK62 e (h : Coordinate 1) T62_44 i :=
  species_entry_eq_sum rK62 ⟨44, by decide⟩ e heK h T62_44 hfix62_44 hinj62_44 hcardT62_44
    (fun i => conj_mem_of_fixedPoints (reps ⟨44, by decide⟩) (reps rK62) (T62_44 i) (hfix62_44 i) h)

/-! ## Cell (62, 49): |T| = 5 -/

def T62_49list : List Coordinates := [(0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0)]
def T62_49 : Fin 5 → Coordinate 1 := fun i => T62_49list.getD i.val (0,0,0,0,0)

theorem hfix62_49 : ∀ i, ((T62_49 i : Coordinate 1) : Coordinate 1 ⧸ reps rK62)
    ∈ fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62) :=
  repsFix_of_siftB rK62 ⟨49, by decide⟩ T62_49 (by decide)

theorem hinj62_49 : Function.Injective
    (fun i => ((T62_49 i : Coordinate 1) : Coordinate 1 ⧸ reps rK62)) :=
  repsInj_of_reduceAux rK62 T62_49 (by decide)

theorem hcardT62_49 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK62 ⟨49, by decide⟩ R62 hpxR62 hcardq62 (by decide)).symm

/-- **Cell (62, 49).** -/
theorem cell62_49 (e : List (ZMod 25)) (heK : charOK (basisAt rK62) e = true)
    (h : ↥(reps (⟨49, by decide⟩ : Fin 148))) :
    species (reps (⟨49, by decide⟩ : Fin 148)) h (basisElt (reps rK62) (charOfVec rK62 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK62 e (h : Coordinate 1) T62_49 i :=
  species_entry_eq_sum rK62 ⟨49, by decide⟩ e heK h T62_49 hfix62_49 hinj62_49 hcardT62_49
    (fun i => conj_mem_of_fixedPoints (reps ⟨49, by decide⟩) (reps rK62) (T62_49 i) (hfix62_49 i) h)

/-! ## Cell (62, 62): |T| = 5 -/

def T62_62list : List Coordinates := [(0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0)]
def T62_62 : Fin 5 → Coordinate 1 := fun i => T62_62list.getD i.val (0,0,0,0,0)

theorem hfix62_62 : ∀ i, ((T62_62 i : Coordinate 1) : Coordinate 1 ⧸ reps rK62)
    ∈ fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62) :=
  repsFix_of_siftB rK62 ⟨62, by decide⟩ T62_62 (by decide)

theorem hinj62_62 : Function.Injective
    (fun i => ((T62_62 i : Coordinate 1) : Coordinate 1 ⧸ reps rK62)) :=
  repsInj_of_reduceAux rK62 T62_62 (by decide)

theorem hcardT62_62 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK62 ⟨62, by decide⟩ R62 hpxR62 hcardq62 (by decide)).symm

/-- **Cell (62, 62).** -/
theorem cell62_62 (e : List (ZMod 25)) (heK : charOK (basisAt rK62) e = true)
    (h : ↥(reps (⟨62, by decide⟩ : Fin 148))) :
    species (reps (⟨62, by decide⟩ : Fin 148)) h (basisElt (reps rK62) (charOfVec rK62 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK62 e (h : Coordinate 1) T62_62 i :=
  species_entry_eq_sum rK62 ⟨62, by decide⟩ e heK h T62_62 hfix62_62 hinj62_62 hcardT62_62
    (fun i => conj_mem_of_fixedPoints (reps ⟨62, by decide⟩) (reps rK62) (T62_62 i) (hfix62_62 i) h)

namespace Q2

def R62_2 : Fin 25 → Coordinate 2 := fun i => R62list.getD i.val (0,0,0,0,0)
theorem hpxR62_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK62) (R62_2 i)) := by decide
theorem hcardq62_2 : Nat.card (Coordinate 2 ⧸ reps rK62) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (62, 0) twin -/

def T62_0_2 : Fin 25 → Coordinate 2 := fun i => T62_0list.getD i.val (0,0,0,0,0)

theorem hfix62_0_2 : ∀ i, ((T62_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK62)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK62) :=
  repsFix_of_siftB2 rK62 ⟨0, by decide⟩ T62_0_2 (by decide)

theorem hinj62_0_2 : Function.Injective
    (fun i => ((T62_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK62)) :=
  repsInj_of_reduceAux2 rK62 T62_0_2 (by decide)

theorem hcardT62_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK62)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK62 ⟨0, by decide⟩ R62_2 hpxR62_2 hcardq62_2 (by decide)).symm

/-- **Cell (62, 0) twin (q=2).** -/
theorem cell62_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK62) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK62) (charOfVec2 rK62 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK62 e (h : Coordinate 2) T62_0_2 i :=
  species_entry_eq_sum rK62 ⟨0, by decide⟩ e heK h T62_0_2 hfix62_0_2 hinj62_0_2 hcardT62_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK62) (T62_0_2 i) (hfix62_0_2 i) h)

/-! ### Cell (62, 7) twin -/

def T62_7_2 : Fin 25 → Coordinate 2 := fun i => T62_7list.getD i.val (0,0,0,0,0)

theorem hfix62_7_2 : ∀ i, ((T62_7_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK62)
    ∈ fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK62) :=
  repsFix_of_siftB2 rK62 ⟨7, by decide⟩ T62_7_2 (by decide)

theorem hinj62_7_2 : Function.Injective
    (fun i => ((T62_7_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK62)) :=
  repsInj_of_reduceAux2 rK62 T62_7_2 (by decide)

theorem hcardT62_7_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK62)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK62 ⟨7, by decide⟩ R62_2 hpxR62_2 hcardq62_2 (by decide)).symm

/-- **Cell (62, 7) twin (q=2).** -/
theorem cell62_7_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK62) e = true)
    (h : ↥(reps (⟨7, by decide⟩ : Fin 148))) :
    species (reps (⟨7, by decide⟩ : Fin 148)) h (basisElt (reps rK62) (charOfVec2 rK62 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK62 e (h : Coordinate 2) T62_7_2 i :=
  species_entry_eq_sum rK62 ⟨7, by decide⟩ e heK h T62_7_2 hfix62_7_2 hinj62_7_2 hcardT62_7_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨7, by decide⟩) (reps rK62) (T62_7_2 i) (hfix62_7_2 i) h)

/-! ### Cell (62, 12) twin -/

def T62_12_2 : Fin 25 → Coordinate 2 := fun i => T62_12list.getD i.val (0,0,0,0,0)

theorem hfix62_12_2 : ∀ i, ((T62_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK62)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK62) :=
  repsFix_of_siftB2 rK62 ⟨12, by decide⟩ T62_12_2 (by decide)

theorem hinj62_12_2 : Function.Injective
    (fun i => ((T62_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK62)) :=
  repsInj_of_reduceAux2 rK62 T62_12_2 (by decide)

theorem hcardT62_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK62)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK62 ⟨12, by decide⟩ R62_2 hpxR62_2 hcardq62_2 (by decide)).symm

/-- **Cell (62, 12) twin (q=2).** -/
theorem cell62_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK62) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK62) (charOfVec2 rK62 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK62 e (h : Coordinate 2) T62_12_2 i :=
  species_entry_eq_sum rK62 ⟨12, by decide⟩ e heK h T62_12_2 hfix62_12_2 hinj62_12_2 hcardT62_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK62) (T62_12_2 i) (hfix62_12_2 i) h)

/-! ### Cell (62, 25) twin -/

def T62_25_2 : Fin 25 → Coordinate 2 := fun i => T62_25list.getD i.val (0,0,0,0,0)

theorem hfix62_25_2 : ∀ i, ((T62_25_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK62)
    ∈ fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK62) :=
  repsFix_of_siftB2 rK62 ⟨25, by decide⟩ T62_25_2 (by decide)

theorem hinj62_25_2 : Function.Injective
    (fun i => ((T62_25_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK62)) :=
  repsInj_of_reduceAux2 rK62 T62_25_2 (by decide)

theorem hcardT62_25_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK62)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK62 ⟨25, by decide⟩ R62_2 hpxR62_2 hcardq62_2 (by decide)).symm

/-- **Cell (62, 25) twin (q=2).** -/
theorem cell62_25_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK62) e = true)
    (h : ↥(reps (⟨25, by decide⟩ : Fin 148))) :
    species (reps (⟨25, by decide⟩ : Fin 148)) h (basisElt (reps rK62) (charOfVec2 rK62 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK62 e (h : Coordinate 2) T62_25_2 i :=
  species_entry_eq_sum rK62 ⟨25, by decide⟩ e heK h T62_25_2 hfix62_25_2 hinj62_25_2 hcardT62_25_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨25, by decide⟩) (reps rK62) (T62_25_2 i) (hfix62_25_2 i) h)

/-! ### Cell (62, 29) twin -/

def T62_29_2 : Fin 5 → Coordinate 2 := fun i => T62_29list.getD i.val (0,0,0,0,0)

theorem hfix62_29_2 : ∀ i, ((T62_29_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK62)
    ∈ fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK62) :=
  repsFix_of_siftB2 rK62 ⟨29, by decide⟩ T62_29_2 (by decide)

theorem hinj62_29_2 : Function.Injective
    (fun i => ((T62_29_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK62)) :=
  repsInj_of_reduceAux2 rK62 T62_29_2 (by decide)

theorem hcardT62_29_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK62)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK62 ⟨29, by decide⟩ R62_2 hpxR62_2 hcardq62_2 (by decide)).symm

/-- **Cell (62, 29) twin (q=2).** -/
theorem cell62_29_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK62) e = true)
    (h : ↥(reps (⟨29, by decide⟩ : Fin 148))) :
    species (reps (⟨29, by decide⟩ : Fin 148)) h (basisElt (reps rK62) (charOfVec2 rK62 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK62 e (h : Coordinate 2) T62_29_2 i :=
  species_entry_eq_sum rK62 ⟨29, by decide⟩ e heK h T62_29_2 hfix62_29_2 hinj62_29_2 hcardT62_29_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨29, by decide⟩) (reps rK62) (T62_29_2 i) (hfix62_29_2 i) h)

/-! ### Cell (62, 34) twin -/

def T62_34_2 : Fin 5 → Coordinate 2 := fun i => T62_34list.getD i.val (0,0,0,0,0)

theorem hfix62_34_2 : ∀ i, ((T62_34_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK62)
    ∈ fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK62) :=
  repsFix_of_siftB2 rK62 ⟨34, by decide⟩ T62_34_2 (by decide)

theorem hinj62_34_2 : Function.Injective
    (fun i => ((T62_34_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK62)) :=
  repsInj_of_reduceAux2 rK62 T62_34_2 (by decide)

theorem hcardT62_34_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK62)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK62 ⟨34, by decide⟩ R62_2 hpxR62_2 hcardq62_2 (by decide)).symm

/-- **Cell (62, 34) twin (q=2).** -/
theorem cell62_34_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK62) e = true)
    (h : ↥(reps (⟨34, by decide⟩ : Fin 148))) :
    species (reps (⟨34, by decide⟩ : Fin 148)) h (basisElt (reps rK62) (charOfVec2 rK62 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK62 e (h : Coordinate 2) T62_34_2 i :=
  species_entry_eq_sum rK62 ⟨34, by decide⟩ e heK h T62_34_2 hfix62_34_2 hinj62_34_2 hcardT62_34_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨34, by decide⟩) (reps rK62) (T62_34_2 i) (hfix62_34_2 i) h)

/-! ### Cell (62, 39) twin -/

def T62_39_2 : Fin 5 → Coordinate 2 := fun i => T62_39list.getD i.val (0,0,0,0,0)

theorem hfix62_39_2 : ∀ i, ((T62_39_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK62)
    ∈ fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK62) :=
  repsFix_of_siftB2 rK62 ⟨39, by decide⟩ T62_39_2 (by decide)

theorem hinj62_39_2 : Function.Injective
    (fun i => ((T62_39_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK62)) :=
  repsInj_of_reduceAux2 rK62 T62_39_2 (by decide)

theorem hcardT62_39_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK62)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK62 ⟨39, by decide⟩ R62_2 hpxR62_2 hcardq62_2 (by decide)).symm

/-- **Cell (62, 39) twin (q=2).** -/
theorem cell62_39_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK62) e = true)
    (h : ↥(reps (⟨39, by decide⟩ : Fin 148))) :
    species (reps (⟨39, by decide⟩ : Fin 148)) h (basisElt (reps rK62) (charOfVec2 rK62 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK62 e (h : Coordinate 2) T62_39_2 i :=
  species_entry_eq_sum rK62 ⟨39, by decide⟩ e heK h T62_39_2 hfix62_39_2 hinj62_39_2 hcardT62_39_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨39, by decide⟩) (reps rK62) (T62_39_2 i) (hfix62_39_2 i) h)

/-! ### Cell (62, 44) twin -/

def T62_44_2 : Fin 5 → Coordinate 2 := fun i => T62_44list.getD i.val (0,0,0,0,0)

theorem hfix62_44_2 : ∀ i, ((T62_44_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK62)
    ∈ fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK62) :=
  repsFix_of_siftB2 rK62 ⟨44, by decide⟩ T62_44_2 (by decide)

theorem hinj62_44_2 : Function.Injective
    (fun i => ((T62_44_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK62)) :=
  repsInj_of_reduceAux2 rK62 T62_44_2 (by decide)

theorem hcardT62_44_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK62)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK62 ⟨44, by decide⟩ R62_2 hpxR62_2 hcardq62_2 (by decide)).symm

/-- **Cell (62, 44) twin (q=2).** -/
theorem cell62_44_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK62) e = true)
    (h : ↥(reps (⟨44, by decide⟩ : Fin 148))) :
    species (reps (⟨44, by decide⟩ : Fin 148)) h (basisElt (reps rK62) (charOfVec2 rK62 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK62 e (h : Coordinate 2) T62_44_2 i :=
  species_entry_eq_sum rK62 ⟨44, by decide⟩ e heK h T62_44_2 hfix62_44_2 hinj62_44_2 hcardT62_44_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨44, by decide⟩) (reps rK62) (T62_44_2 i) (hfix62_44_2 i) h)

/-! ### Cell (62, 49) twin -/

def T62_49_2 : Fin 5 → Coordinate 2 := fun i => T62_49list.getD i.val (0,0,0,0,0)

theorem hfix62_49_2 : ∀ i, ((T62_49_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK62)
    ∈ fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK62) :=
  repsFix_of_siftB2 rK62 ⟨49, by decide⟩ T62_49_2 (by decide)

theorem hinj62_49_2 : Function.Injective
    (fun i => ((T62_49_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK62)) :=
  repsInj_of_reduceAux2 rK62 T62_49_2 (by decide)

theorem hcardT62_49_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK62)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK62 ⟨49, by decide⟩ R62_2 hpxR62_2 hcardq62_2 (by decide)).symm

/-- **Cell (62, 49) twin (q=2).** -/
theorem cell62_49_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK62) e = true)
    (h : ↥(reps (⟨49, by decide⟩ : Fin 148))) :
    species (reps (⟨49, by decide⟩ : Fin 148)) h (basisElt (reps rK62) (charOfVec2 rK62 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK62 e (h : Coordinate 2) T62_49_2 i :=
  species_entry_eq_sum rK62 ⟨49, by decide⟩ e heK h T62_49_2 hfix62_49_2 hinj62_49_2 hcardT62_49_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨49, by decide⟩) (reps rK62) (T62_49_2 i) (hfix62_49_2 i) h)

/-! ### Cell (62, 62) twin -/

def T62_62_2 : Fin 5 → Coordinate 2 := fun i => T62_62list.getD i.val (0,0,0,0,0)

theorem hfix62_62_2 : ∀ i, ((T62_62_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK62)
    ∈ fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK62) :=
  repsFix_of_siftB2 rK62 ⟨62, by decide⟩ T62_62_2 (by decide)

theorem hinj62_62_2 : Function.Injective
    (fun i => ((T62_62_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK62)) :=
  repsInj_of_reduceAux2 rK62 T62_62_2 (by decide)

theorem hcardT62_62_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK62)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK62 ⟨62, by decide⟩ R62_2 hpxR62_2 hcardq62_2 (by decide)).symm

/-- **Cell (62, 62) twin (q=2).** -/
theorem cell62_62_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK62) e = true)
    (h : ↥(reps (⟨62, by decide⟩ : Fin 148))) :
    species (reps (⟨62, by decide⟩ : Fin 148)) h (basisElt (reps rK62) (charOfVec2 rK62 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK62 e (h : Coordinate 2) T62_62_2 i :=
  species_entry_eq_sum rK62 ⟨62, by decide⟩ e heK h T62_62_2 hfix62_62_2 hinj62_62_2 hcardT62_62_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨62, by decide⟩) (reps rK62) (T62_62_2 i) (hfix62_62_2 i) h)

end Q2

/-! # K-class rK = 63  (|G/K| = 25) -/

def rK63 : Fin 148 := ⟨63, by decide⟩

def R63list : List Coordinates := [(0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0)]
def R63 : Fin 25 → Coordinate 1 := fun i => R63list.getD i.val (0,0,0,0,0)

theorem hpxR63 : Function.Injective (fun i => reduceAux 1 (basisAt rK63) (R63 i)) := by decide
theorem hcardq63 : Nat.card (Coordinate 1 ⧸ reps rK63) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (63, 0): |T| = 25 -/

def T63_0list : List Coordinates := [(0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0)]
def T63_0 : Fin 25 → Coordinate 1 := fun i => T63_0list.getD i.val (0,0,0,0,0)

theorem hfix63_0 : ∀ i, ((T63_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK63)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63) :=
  repsFix_of_siftB rK63 ⟨0, by decide⟩ T63_0 (by decide)

theorem hinj63_0 : Function.Injective
    (fun i => ((T63_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK63)) :=
  repsInj_of_reduceAux rK63 T63_0 (by decide)

theorem hcardT63_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK63 ⟨0, by decide⟩ R63 hpxR63 hcardq63 (by decide)).symm

/-- **Cell (63, 0).** -/
theorem cell63_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK63) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK63) (charOfVec rK63 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK63 e (h : Coordinate 1) T63_0 i :=
  species_entry_eq_sum rK63 ⟨0, by decide⟩ e heK h T63_0 hfix63_0 hinj63_0 hcardT63_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK63) (T63_0 i) (hfix63_0 i) h)

/-! ## Cell (63, 6): |T| = 25 -/

def T63_6list : List Coordinates := [(0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0)]
def T63_6 : Fin 25 → Coordinate 1 := fun i => T63_6list.getD i.val (0,0,0,0,0)

theorem hfix63_6 : ∀ i, ((T63_6 i : Coordinate 1) : Coordinate 1 ⧸ reps rK63)
    ∈ fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63) :=
  repsFix_of_siftB rK63 ⟨6, by decide⟩ T63_6 (by decide)

theorem hinj63_6 : Function.Injective
    (fun i => ((T63_6 i : Coordinate 1) : Coordinate 1 ⧸ reps rK63)) :=
  repsInj_of_reduceAux rK63 T63_6 (by decide)

theorem hcardT63_6 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK63 ⟨6, by decide⟩ R63 hpxR63 hcardq63 (by decide)).symm

/-- **Cell (63, 6).** -/
theorem cell63_6 (e : List (ZMod 25)) (heK : charOK (basisAt rK63) e = true)
    (h : ↥(reps (⟨6, by decide⟩ : Fin 148))) :
    species (reps (⟨6, by decide⟩ : Fin 148)) h (basisElt (reps rK63) (charOfVec rK63 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK63 e (h : Coordinate 1) T63_6 i :=
  species_entry_eq_sum rK63 ⟨6, by decide⟩ e heK h T63_6 hfix63_6 hinj63_6 hcardT63_6
    (fun i => conj_mem_of_fixedPoints (reps ⟨6, by decide⟩) (reps rK63) (T63_6 i) (hfix63_6 i) h)

/-! ## Cell (63, 12): |T| = 25 -/

def T63_12list : List Coordinates := [(0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0)]
def T63_12 : Fin 25 → Coordinate 1 := fun i => T63_12list.getD i.val (0,0,0,0,0)

theorem hfix63_12 : ∀ i, ((T63_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK63)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63) :=
  repsFix_of_siftB rK63 ⟨12, by decide⟩ T63_12 (by decide)

theorem hinj63_12 : Function.Injective
    (fun i => ((T63_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK63)) :=
  repsInj_of_reduceAux rK63 T63_12 (by decide)

theorem hcardT63_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK63 ⟨12, by decide⟩ R63 hpxR63 hcardq63 (by decide)).symm

/-- **Cell (63, 12).** -/
theorem cell63_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK63) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK63) (charOfVec rK63 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK63 e (h : Coordinate 1) T63_12 i :=
  species_entry_eq_sum rK63 ⟨12, by decide⟩ e heK h T63_12 hfix63_12 hinj63_12 hcardT63_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK63) (T63_12 i) (hfix63_12 i) h)

/-! ## Cell (63, 24): |T| = 25 -/

def T63_24list : List Coordinates := [(0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0)]
def T63_24 : Fin 25 → Coordinate 1 := fun i => T63_24list.getD i.val (0,0,0,0,0)

theorem hfix63_24 : ∀ i, ((T63_24 i : Coordinate 1) : Coordinate 1 ⧸ reps rK63)
    ∈ fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63) :=
  repsFix_of_siftB rK63 ⟨24, by decide⟩ T63_24 (by decide)

theorem hinj63_24 : Function.Injective
    (fun i => ((T63_24 i : Coordinate 1) : Coordinate 1 ⧸ reps rK63)) :=
  repsInj_of_reduceAux rK63 T63_24 (by decide)

theorem hcardT63_24 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK63 ⟨24, by decide⟩ R63 hpxR63 hcardq63 (by decide)).symm

/-- **Cell (63, 24).** -/
theorem cell63_24 (e : List (ZMod 25)) (heK : charOK (basisAt rK63) e = true)
    (h : ↥(reps (⟨24, by decide⟩ : Fin 148))) :
    species (reps (⟨24, by decide⟩ : Fin 148)) h (basisElt (reps rK63) (charOfVec rK63 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK63 e (h : Coordinate 1) T63_24 i :=
  species_entry_eq_sum rK63 ⟨24, by decide⟩ e heK h T63_24 hfix63_24 hinj63_24 hcardT63_24
    (fun i => conj_mem_of_fixedPoints (reps ⟨24, by decide⟩) (reps rK63) (T63_24 i) (hfix63_24 i) h)

/-! ## Cell (63, 29): |T| = 5 -/

def T63_29list : List Coordinates := [(0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0)]
def T63_29 : Fin 5 → Coordinate 1 := fun i => T63_29list.getD i.val (0,0,0,0,0)

theorem hfix63_29 : ∀ i, ((T63_29 i : Coordinate 1) : Coordinate 1 ⧸ reps rK63)
    ∈ fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63) :=
  repsFix_of_siftB rK63 ⟨29, by decide⟩ T63_29 (by decide)

theorem hinj63_29 : Function.Injective
    (fun i => ((T63_29 i : Coordinate 1) : Coordinate 1 ⧸ reps rK63)) :=
  repsInj_of_reduceAux rK63 T63_29 (by decide)

theorem hcardT63_29 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK63 ⟨29, by decide⟩ R63 hpxR63 hcardq63 (by decide)).symm

/-- **Cell (63, 29).** -/
theorem cell63_29 (e : List (ZMod 25)) (heK : charOK (basisAt rK63) e = true)
    (h : ↥(reps (⟨29, by decide⟩ : Fin 148))) :
    species (reps (⟨29, by decide⟩ : Fin 148)) h (basisElt (reps rK63) (charOfVec rK63 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK63 e (h : Coordinate 1) T63_29 i :=
  species_entry_eq_sum rK63 ⟨29, by decide⟩ e heK h T63_29 hfix63_29 hinj63_29 hcardT63_29
    (fun i => conj_mem_of_fixedPoints (reps ⟨29, by decide⟩) (reps rK63) (T63_29 i) (hfix63_29 i) h)

/-! ## Cell (63, 34): |T| = 5 -/

def T63_34list : List Coordinates := [(0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0)]
def T63_34 : Fin 5 → Coordinate 1 := fun i => T63_34list.getD i.val (0,0,0,0,0)

theorem hfix63_34 : ∀ i, ((T63_34 i : Coordinate 1) : Coordinate 1 ⧸ reps rK63)
    ∈ fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63) :=
  repsFix_of_siftB rK63 ⟨34, by decide⟩ T63_34 (by decide)

theorem hinj63_34 : Function.Injective
    (fun i => ((T63_34 i : Coordinate 1) : Coordinate 1 ⧸ reps rK63)) :=
  repsInj_of_reduceAux rK63 T63_34 (by decide)

theorem hcardT63_34 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK63 ⟨34, by decide⟩ R63 hpxR63 hcardq63 (by decide)).symm

/-- **Cell (63, 34).** -/
theorem cell63_34 (e : List (ZMod 25)) (heK : charOK (basisAt rK63) e = true)
    (h : ↥(reps (⟨34, by decide⟩ : Fin 148))) :
    species (reps (⟨34, by decide⟩ : Fin 148)) h (basisElt (reps rK63) (charOfVec rK63 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK63 e (h : Coordinate 1) T63_34 i :=
  species_entry_eq_sum rK63 ⟨34, by decide⟩ e heK h T63_34 hfix63_34 hinj63_34 hcardT63_34
    (fun i => conj_mem_of_fixedPoints (reps ⟨34, by decide⟩) (reps rK63) (T63_34 i) (hfix63_34 i) h)

/-! ## Cell (63, 39): |T| = 5 -/

def T63_39list : List Coordinates := [(0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0)]
def T63_39 : Fin 5 → Coordinate 1 := fun i => T63_39list.getD i.val (0,0,0,0,0)

theorem hfix63_39 : ∀ i, ((T63_39 i : Coordinate 1) : Coordinate 1 ⧸ reps rK63)
    ∈ fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63) :=
  repsFix_of_siftB rK63 ⟨39, by decide⟩ T63_39 (by decide)

theorem hinj63_39 : Function.Injective
    (fun i => ((T63_39 i : Coordinate 1) : Coordinate 1 ⧸ reps rK63)) :=
  repsInj_of_reduceAux rK63 T63_39 (by decide)

theorem hcardT63_39 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK63 ⟨39, by decide⟩ R63 hpxR63 hcardq63 (by decide)).symm

/-- **Cell (63, 39).** -/
theorem cell63_39 (e : List (ZMod 25)) (heK : charOK (basisAt rK63) e = true)
    (h : ↥(reps (⟨39, by decide⟩ : Fin 148))) :
    species (reps (⟨39, by decide⟩ : Fin 148)) h (basisElt (reps rK63) (charOfVec rK63 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK63 e (h : Coordinate 1) T63_39 i :=
  species_entry_eq_sum rK63 ⟨39, by decide⟩ e heK h T63_39 hfix63_39 hinj63_39 hcardT63_39
    (fun i => conj_mem_of_fixedPoints (reps ⟨39, by decide⟩) (reps rK63) (T63_39 i) (hfix63_39 i) h)

/-! ## Cell (63, 44): |T| = 5 -/

def T63_44list : List Coordinates := [(0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0)]
def T63_44 : Fin 5 → Coordinate 1 := fun i => T63_44list.getD i.val (0,0,0,0,0)

theorem hfix63_44 : ∀ i, ((T63_44 i : Coordinate 1) : Coordinate 1 ⧸ reps rK63)
    ∈ fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63) :=
  repsFix_of_siftB rK63 ⟨44, by decide⟩ T63_44 (by decide)

theorem hinj63_44 : Function.Injective
    (fun i => ((T63_44 i : Coordinate 1) : Coordinate 1 ⧸ reps rK63)) :=
  repsInj_of_reduceAux rK63 T63_44 (by decide)

theorem hcardT63_44 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK63 ⟨44, by decide⟩ R63 hpxR63 hcardq63 (by decide)).symm

/-- **Cell (63, 44).** -/
theorem cell63_44 (e : List (ZMod 25)) (heK : charOK (basisAt rK63) e = true)
    (h : ↥(reps (⟨44, by decide⟩ : Fin 148))) :
    species (reps (⟨44, by decide⟩ : Fin 148)) h (basisElt (reps rK63) (charOfVec rK63 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK63 e (h : Coordinate 1) T63_44 i :=
  species_entry_eq_sum rK63 ⟨44, by decide⟩ e heK h T63_44 hfix63_44 hinj63_44 hcardT63_44
    (fun i => conj_mem_of_fixedPoints (reps ⟨44, by decide⟩) (reps rK63) (T63_44 i) (hfix63_44 i) h)

/-! ## Cell (63, 49): |T| = 5 -/

def T63_49list : List Coordinates := [(0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0)]
def T63_49 : Fin 5 → Coordinate 1 := fun i => T63_49list.getD i.val (0,0,0,0,0)

theorem hfix63_49 : ∀ i, ((T63_49 i : Coordinate 1) : Coordinate 1 ⧸ reps rK63)
    ∈ fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63) :=
  repsFix_of_siftB rK63 ⟨49, by decide⟩ T63_49 (by decide)

theorem hinj63_49 : Function.Injective
    (fun i => ((T63_49 i : Coordinate 1) : Coordinate 1 ⧸ reps rK63)) :=
  repsInj_of_reduceAux rK63 T63_49 (by decide)

theorem hcardT63_49 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK63 ⟨49, by decide⟩ R63 hpxR63 hcardq63 (by decide)).symm

/-- **Cell (63, 49).** -/
theorem cell63_49 (e : List (ZMod 25)) (heK : charOK (basisAt rK63) e = true)
    (h : ↥(reps (⟨49, by decide⟩ : Fin 148))) :
    species (reps (⟨49, by decide⟩ : Fin 148)) h (basisElt (reps rK63) (charOfVec rK63 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK63 e (h : Coordinate 1) T63_49 i :=
  species_entry_eq_sum rK63 ⟨49, by decide⟩ e heK h T63_49 hfix63_49 hinj63_49 hcardT63_49
    (fun i => conj_mem_of_fixedPoints (reps ⟨49, by decide⟩) (reps rK63) (T63_49 i) (hfix63_49 i) h)

/-! ## Cell (63, 63): |T| = 5 -/

def T63_63list : List Coordinates := [(0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0)]
def T63_63 : Fin 5 → Coordinate 1 := fun i => T63_63list.getD i.val (0,0,0,0,0)

theorem hfix63_63 : ∀ i, ((T63_63 i : Coordinate 1) : Coordinate 1 ⧸ reps rK63)
    ∈ fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63) :=
  repsFix_of_siftB rK63 ⟨63, by decide⟩ T63_63 (by decide)

theorem hinj63_63 : Function.Injective
    (fun i => ((T63_63 i : Coordinate 1) : Coordinate 1 ⧸ reps rK63)) :=
  repsInj_of_reduceAux rK63 T63_63 (by decide)

theorem hcardT63_63 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK63 ⟨63, by decide⟩ R63 hpxR63 hcardq63 (by decide)).symm

/-- **Cell (63, 63).** -/
theorem cell63_63 (e : List (ZMod 25)) (heK : charOK (basisAt rK63) e = true)
    (h : ↥(reps (⟨63, by decide⟩ : Fin 148))) :
    species (reps (⟨63, by decide⟩ : Fin 148)) h (basisElt (reps rK63) (charOfVec rK63 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK63 e (h : Coordinate 1) T63_63 i :=
  species_entry_eq_sum rK63 ⟨63, by decide⟩ e heK h T63_63 hfix63_63 hinj63_63 hcardT63_63
    (fun i => conj_mem_of_fixedPoints (reps ⟨63, by decide⟩) (reps rK63) (T63_63 i) (hfix63_63 i) h)

namespace Q2

def R63_2 : Fin 25 → Coordinate 2 := fun i => R63list.getD i.val (0,0,0,0,0)
theorem hpxR63_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK63) (R63_2 i)) := by decide
theorem hcardq63_2 : Nat.card (Coordinate 2 ⧸ reps rK63) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (63, 0) twin -/

def T63_0_2 : Fin 25 → Coordinate 2 := fun i => T63_0list.getD i.val (0,0,0,0,0)

theorem hfix63_0_2 : ∀ i, ((T63_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK63)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK63) :=
  repsFix_of_siftB2 rK63 ⟨0, by decide⟩ T63_0_2 (by decide)

theorem hinj63_0_2 : Function.Injective
    (fun i => ((T63_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK63)) :=
  repsInj_of_reduceAux2 rK63 T63_0_2 (by decide)

theorem hcardT63_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK63)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK63 ⟨0, by decide⟩ R63_2 hpxR63_2 hcardq63_2 (by decide)).symm

/-- **Cell (63, 0) twin (q=2).** -/
theorem cell63_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK63) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK63) (charOfVec2 rK63 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK63 e (h : Coordinate 2) T63_0_2 i :=
  species_entry_eq_sum rK63 ⟨0, by decide⟩ e heK h T63_0_2 hfix63_0_2 hinj63_0_2 hcardT63_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK63) (T63_0_2 i) (hfix63_0_2 i) h)

/-! ### Cell (63, 6) twin -/

def T63_6_2 : Fin 25 → Coordinate 2 := fun i => T63_6list.getD i.val (0,0,0,0,0)

theorem hfix63_6_2 : ∀ i, ((T63_6_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK63)
    ∈ fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK63) :=
  repsFix_of_siftB2 rK63 ⟨6, by decide⟩ T63_6_2 (by decide)

theorem hinj63_6_2 : Function.Injective
    (fun i => ((T63_6_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK63)) :=
  repsInj_of_reduceAux2 rK63 T63_6_2 (by decide)

theorem hcardT63_6_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK63)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK63 ⟨6, by decide⟩ R63_2 hpxR63_2 hcardq63_2 (by decide)).symm

/-- **Cell (63, 6) twin (q=2).** -/
theorem cell63_6_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK63) e = true)
    (h : ↥(reps (⟨6, by decide⟩ : Fin 148))) :
    species (reps (⟨6, by decide⟩ : Fin 148)) h (basisElt (reps rK63) (charOfVec2 rK63 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK63 e (h : Coordinate 2) T63_6_2 i :=
  species_entry_eq_sum rK63 ⟨6, by decide⟩ e heK h T63_6_2 hfix63_6_2 hinj63_6_2 hcardT63_6_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨6, by decide⟩) (reps rK63) (T63_6_2 i) (hfix63_6_2 i) h)

/-! ### Cell (63, 12) twin -/

def T63_12_2 : Fin 25 → Coordinate 2 := fun i => T63_12list.getD i.val (0,0,0,0,0)

theorem hfix63_12_2 : ∀ i, ((T63_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK63)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK63) :=
  repsFix_of_siftB2 rK63 ⟨12, by decide⟩ T63_12_2 (by decide)

theorem hinj63_12_2 : Function.Injective
    (fun i => ((T63_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK63)) :=
  repsInj_of_reduceAux2 rK63 T63_12_2 (by decide)

theorem hcardT63_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK63)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK63 ⟨12, by decide⟩ R63_2 hpxR63_2 hcardq63_2 (by decide)).symm

/-- **Cell (63, 12) twin (q=2).** -/
theorem cell63_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK63) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK63) (charOfVec2 rK63 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK63 e (h : Coordinate 2) T63_12_2 i :=
  species_entry_eq_sum rK63 ⟨12, by decide⟩ e heK h T63_12_2 hfix63_12_2 hinj63_12_2 hcardT63_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK63) (T63_12_2 i) (hfix63_12_2 i) h)

/-! ### Cell (63, 24) twin -/

def T63_24_2 : Fin 25 → Coordinate 2 := fun i => T63_24list.getD i.val (0,0,0,0,0)

theorem hfix63_24_2 : ∀ i, ((T63_24_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK63)
    ∈ fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK63) :=
  repsFix_of_siftB2 rK63 ⟨24, by decide⟩ T63_24_2 (by decide)

theorem hinj63_24_2 : Function.Injective
    (fun i => ((T63_24_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK63)) :=
  repsInj_of_reduceAux2 rK63 T63_24_2 (by decide)

theorem hcardT63_24_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK63)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK63 ⟨24, by decide⟩ R63_2 hpxR63_2 hcardq63_2 (by decide)).symm

/-- **Cell (63, 24) twin (q=2).** -/
theorem cell63_24_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK63) e = true)
    (h : ↥(reps (⟨24, by decide⟩ : Fin 148))) :
    species (reps (⟨24, by decide⟩ : Fin 148)) h (basisElt (reps rK63) (charOfVec2 rK63 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK63 e (h : Coordinate 2) T63_24_2 i :=
  species_entry_eq_sum rK63 ⟨24, by decide⟩ e heK h T63_24_2 hfix63_24_2 hinj63_24_2 hcardT63_24_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨24, by decide⟩) (reps rK63) (T63_24_2 i) (hfix63_24_2 i) h)

/-! ### Cell (63, 29) twin -/

def T63_29_2 : Fin 5 → Coordinate 2 := fun i => T63_29list.getD i.val (0,0,0,0,0)

theorem hfix63_29_2 : ∀ i, ((T63_29_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK63)
    ∈ fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK63) :=
  repsFix_of_siftB2 rK63 ⟨29, by decide⟩ T63_29_2 (by decide)

theorem hinj63_29_2 : Function.Injective
    (fun i => ((T63_29_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK63)) :=
  repsInj_of_reduceAux2 rK63 T63_29_2 (by decide)

theorem hcardT63_29_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK63)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK63 ⟨29, by decide⟩ R63_2 hpxR63_2 hcardq63_2 (by decide)).symm

/-- **Cell (63, 29) twin (q=2).** -/
theorem cell63_29_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK63) e = true)
    (h : ↥(reps (⟨29, by decide⟩ : Fin 148))) :
    species (reps (⟨29, by decide⟩ : Fin 148)) h (basisElt (reps rK63) (charOfVec2 rK63 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK63 e (h : Coordinate 2) T63_29_2 i :=
  species_entry_eq_sum rK63 ⟨29, by decide⟩ e heK h T63_29_2 hfix63_29_2 hinj63_29_2 hcardT63_29_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨29, by decide⟩) (reps rK63) (T63_29_2 i) (hfix63_29_2 i) h)

/-! ### Cell (63, 34) twin -/

def T63_34_2 : Fin 5 → Coordinate 2 := fun i => T63_34list.getD i.val (0,0,0,0,0)

theorem hfix63_34_2 : ∀ i, ((T63_34_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK63)
    ∈ fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK63) :=
  repsFix_of_siftB2 rK63 ⟨34, by decide⟩ T63_34_2 (by decide)

theorem hinj63_34_2 : Function.Injective
    (fun i => ((T63_34_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK63)) :=
  repsInj_of_reduceAux2 rK63 T63_34_2 (by decide)

theorem hcardT63_34_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK63)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK63 ⟨34, by decide⟩ R63_2 hpxR63_2 hcardq63_2 (by decide)).symm

/-- **Cell (63, 34) twin (q=2).** -/
theorem cell63_34_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK63) e = true)
    (h : ↥(reps (⟨34, by decide⟩ : Fin 148))) :
    species (reps (⟨34, by decide⟩ : Fin 148)) h (basisElt (reps rK63) (charOfVec2 rK63 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK63 e (h : Coordinate 2) T63_34_2 i :=
  species_entry_eq_sum rK63 ⟨34, by decide⟩ e heK h T63_34_2 hfix63_34_2 hinj63_34_2 hcardT63_34_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨34, by decide⟩) (reps rK63) (T63_34_2 i) (hfix63_34_2 i) h)

/-! ### Cell (63, 39) twin -/

def T63_39_2 : Fin 5 → Coordinate 2 := fun i => T63_39list.getD i.val (0,0,0,0,0)

theorem hfix63_39_2 : ∀ i, ((T63_39_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK63)
    ∈ fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK63) :=
  repsFix_of_siftB2 rK63 ⟨39, by decide⟩ T63_39_2 (by decide)

theorem hinj63_39_2 : Function.Injective
    (fun i => ((T63_39_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK63)) :=
  repsInj_of_reduceAux2 rK63 T63_39_2 (by decide)

theorem hcardT63_39_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK63)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK63 ⟨39, by decide⟩ R63_2 hpxR63_2 hcardq63_2 (by decide)).symm

/-- **Cell (63, 39) twin (q=2).** -/
theorem cell63_39_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK63) e = true)
    (h : ↥(reps (⟨39, by decide⟩ : Fin 148))) :
    species (reps (⟨39, by decide⟩ : Fin 148)) h (basisElt (reps rK63) (charOfVec2 rK63 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK63 e (h : Coordinate 2) T63_39_2 i :=
  species_entry_eq_sum rK63 ⟨39, by decide⟩ e heK h T63_39_2 hfix63_39_2 hinj63_39_2 hcardT63_39_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨39, by decide⟩) (reps rK63) (T63_39_2 i) (hfix63_39_2 i) h)

/-! ### Cell (63, 44) twin -/

def T63_44_2 : Fin 5 → Coordinate 2 := fun i => T63_44list.getD i.val (0,0,0,0,0)

theorem hfix63_44_2 : ∀ i, ((T63_44_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK63)
    ∈ fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK63) :=
  repsFix_of_siftB2 rK63 ⟨44, by decide⟩ T63_44_2 (by decide)

theorem hinj63_44_2 : Function.Injective
    (fun i => ((T63_44_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK63)) :=
  repsInj_of_reduceAux2 rK63 T63_44_2 (by decide)

theorem hcardT63_44_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK63)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK63 ⟨44, by decide⟩ R63_2 hpxR63_2 hcardq63_2 (by decide)).symm

/-- **Cell (63, 44) twin (q=2).** -/
theorem cell63_44_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK63) e = true)
    (h : ↥(reps (⟨44, by decide⟩ : Fin 148))) :
    species (reps (⟨44, by decide⟩ : Fin 148)) h (basisElt (reps rK63) (charOfVec2 rK63 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK63 e (h : Coordinate 2) T63_44_2 i :=
  species_entry_eq_sum rK63 ⟨44, by decide⟩ e heK h T63_44_2 hfix63_44_2 hinj63_44_2 hcardT63_44_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨44, by decide⟩) (reps rK63) (T63_44_2 i) (hfix63_44_2 i) h)

/-! ### Cell (63, 49) twin -/

def T63_49_2 : Fin 5 → Coordinate 2 := fun i => T63_49list.getD i.val (0,0,0,0,0)

theorem hfix63_49_2 : ∀ i, ((T63_49_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK63)
    ∈ fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK63) :=
  repsFix_of_siftB2 rK63 ⟨49, by decide⟩ T63_49_2 (by decide)

theorem hinj63_49_2 : Function.Injective
    (fun i => ((T63_49_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK63)) :=
  repsInj_of_reduceAux2 rK63 T63_49_2 (by decide)

theorem hcardT63_49_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK63)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK63 ⟨49, by decide⟩ R63_2 hpxR63_2 hcardq63_2 (by decide)).symm

/-- **Cell (63, 49) twin (q=2).** -/
theorem cell63_49_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK63) e = true)
    (h : ↥(reps (⟨49, by decide⟩ : Fin 148))) :
    species (reps (⟨49, by decide⟩ : Fin 148)) h (basisElt (reps rK63) (charOfVec2 rK63 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK63 e (h : Coordinate 2) T63_49_2 i :=
  species_entry_eq_sum rK63 ⟨49, by decide⟩ e heK h T63_49_2 hfix63_49_2 hinj63_49_2 hcardT63_49_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨49, by decide⟩) (reps rK63) (T63_49_2 i) (hfix63_49_2 i) h)

/-! ### Cell (63, 63) twin -/

def T63_63_2 : Fin 5 → Coordinate 2 := fun i => T63_63list.getD i.val (0,0,0,0,0)

theorem hfix63_63_2 : ∀ i, ((T63_63_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK63)
    ∈ fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK63) :=
  repsFix_of_siftB2 rK63 ⟨63, by decide⟩ T63_63_2 (by decide)

theorem hinj63_63_2 : Function.Injective
    (fun i => ((T63_63_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK63)) :=
  repsInj_of_reduceAux2 rK63 T63_63_2 (by decide)

theorem hcardT63_63_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK63)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK63 ⟨63, by decide⟩ R63_2 hpxR63_2 hcardq63_2 (by decide)).symm

/-- **Cell (63, 63) twin (q=2).** -/
theorem cell63_63_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK63) e = true)
    (h : ↥(reps (⟨63, by decide⟩ : Fin 148))) :
    species (reps (⟨63, by decide⟩ : Fin 148)) h (basisElt (reps rK63) (charOfVec2 rK63 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK63 e (h : Coordinate 2) T63_63_2 i :=
  species_entry_eq_sum rK63 ⟨63, by decide⟩ e heK h T63_63_2 hfix63_63_2 hinj63_63_2 hcardT63_63_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨63, by decide⟩) (reps rK63) (T63_63_2 i) (hfix63_63_2 i) h)

end Q2

/-! # K-class rK = 64  (|G/K| = 25) -/

def rK64 : Fin 148 := ⟨64, by decide⟩

def R64list : List Coordinates := [(0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0)]
def R64 : Fin 25 → Coordinate 1 := fun i => R64list.getD i.val (0,0,0,0,0)

theorem hpxR64 : Function.Injective (fun i => reduceAux 1 (basisAt rK64) (R64 i)) := by decide
theorem hcardq64 : Nat.card (Coordinate 1 ⧸ reps rK64) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (64, 0): |T| = 25 -/

def T64_0list : List Coordinates := [(0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0)]
def T64_0 : Fin 25 → Coordinate 1 := fun i => T64_0list.getD i.val (0,0,0,0,0)

theorem hfix64_0 : ∀ i, ((T64_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK64)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64) :=
  repsFix_of_siftB rK64 ⟨0, by decide⟩ T64_0 (by decide)

theorem hinj64_0 : Function.Injective
    (fun i => ((T64_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK64)) :=
  repsInj_of_reduceAux rK64 T64_0 (by decide)

theorem hcardT64_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK64 ⟨0, by decide⟩ R64 hpxR64 hcardq64 (by decide)).symm

/-- **Cell (64, 0).** -/
theorem cell64_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK64) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK64) (charOfVec rK64 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK64 e (h : Coordinate 1) T64_0 i :=
  species_entry_eq_sum rK64 ⟨0, by decide⟩ e heK h T64_0 hfix64_0 hinj64_0 hcardT64_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK64) (T64_0 i) (hfix64_0 i) h)

/-! ## Cell (64, 8): |T| = 25 -/

def T64_8list : List Coordinates := [(0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0)]
def T64_8 : Fin 25 → Coordinate 1 := fun i => T64_8list.getD i.val (0,0,0,0,0)

theorem hfix64_8 : ∀ i, ((T64_8 i : Coordinate 1) : Coordinate 1 ⧸ reps rK64)
    ∈ fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64) :=
  repsFix_of_siftB rK64 ⟨8, by decide⟩ T64_8 (by decide)

theorem hinj64_8 : Function.Injective
    (fun i => ((T64_8 i : Coordinate 1) : Coordinate 1 ⧸ reps rK64)) :=
  repsInj_of_reduceAux rK64 T64_8 (by decide)

theorem hcardT64_8 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK64 ⟨8, by decide⟩ R64 hpxR64 hcardq64 (by decide)).symm

/-- **Cell (64, 8).** -/
theorem cell64_8 (e : List (ZMod 25)) (heK : charOK (basisAt rK64) e = true)
    (h : ↥(reps (⟨8, by decide⟩ : Fin 148))) :
    species (reps (⟨8, by decide⟩ : Fin 148)) h (basisElt (reps rK64) (charOfVec rK64 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK64 e (h : Coordinate 1) T64_8 i :=
  species_entry_eq_sum rK64 ⟨8, by decide⟩ e heK h T64_8 hfix64_8 hinj64_8 hcardT64_8
    (fun i => conj_mem_of_fixedPoints (reps ⟨8, by decide⟩) (reps rK64) (T64_8 i) (hfix64_8 i) h)

/-! ## Cell (64, 12): |T| = 25 -/

def T64_12list : List Coordinates := [(0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0)]
def T64_12 : Fin 25 → Coordinate 1 := fun i => T64_12list.getD i.val (0,0,0,0,0)

theorem hfix64_12 : ∀ i, ((T64_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK64)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64) :=
  repsFix_of_siftB rK64 ⟨12, by decide⟩ T64_12 (by decide)

theorem hinj64_12 : Function.Injective
    (fun i => ((T64_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK64)) :=
  repsInj_of_reduceAux rK64 T64_12 (by decide)

theorem hcardT64_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK64 ⟨12, by decide⟩ R64 hpxR64 hcardq64 (by decide)).symm

/-- **Cell (64, 12).** -/
theorem cell64_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK64) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK64) (charOfVec rK64 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK64 e (h : Coordinate 1) T64_12 i :=
  species_entry_eq_sum rK64 ⟨12, by decide⟩ e heK h T64_12 hfix64_12 hinj64_12 hcardT64_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK64) (T64_12 i) (hfix64_12 i) h)

/-! ## Cell (64, 26): |T| = 25 -/

def T64_26list : List Coordinates := [(0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0)]
def T64_26 : Fin 25 → Coordinate 1 := fun i => T64_26list.getD i.val (0,0,0,0,0)

theorem hfix64_26 : ∀ i, ((T64_26 i : Coordinate 1) : Coordinate 1 ⧸ reps rK64)
    ∈ fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64) :=
  repsFix_of_siftB rK64 ⟨26, by decide⟩ T64_26 (by decide)

theorem hinj64_26 : Function.Injective
    (fun i => ((T64_26 i : Coordinate 1) : Coordinate 1 ⧸ reps rK64)) :=
  repsInj_of_reduceAux rK64 T64_26 (by decide)

theorem hcardT64_26 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK64 ⟨26, by decide⟩ R64 hpxR64 hcardq64 (by decide)).symm

/-- **Cell (64, 26).** -/
theorem cell64_26 (e : List (ZMod 25)) (heK : charOK (basisAt rK64) e = true)
    (h : ↥(reps (⟨26, by decide⟩ : Fin 148))) :
    species (reps (⟨26, by decide⟩ : Fin 148)) h (basisElt (reps rK64) (charOfVec rK64 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK64 e (h : Coordinate 1) T64_26 i :=
  species_entry_eq_sum rK64 ⟨26, by decide⟩ e heK h T64_26 hfix64_26 hinj64_26 hcardT64_26
    (fun i => conj_mem_of_fixedPoints (reps ⟨26, by decide⟩) (reps rK64) (T64_26 i) (hfix64_26 i) h)

/-! ## Cell (64, 29): |T| = 5 -/

def T64_29list : List Coordinates := [(0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0)]
def T64_29 : Fin 5 → Coordinate 1 := fun i => T64_29list.getD i.val (0,0,0,0,0)

theorem hfix64_29 : ∀ i, ((T64_29 i : Coordinate 1) : Coordinate 1 ⧸ reps rK64)
    ∈ fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64) :=
  repsFix_of_siftB rK64 ⟨29, by decide⟩ T64_29 (by decide)

theorem hinj64_29 : Function.Injective
    (fun i => ((T64_29 i : Coordinate 1) : Coordinate 1 ⧸ reps rK64)) :=
  repsInj_of_reduceAux rK64 T64_29 (by decide)

theorem hcardT64_29 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK64 ⟨29, by decide⟩ R64 hpxR64 hcardq64 (by decide)).symm

/-- **Cell (64, 29).** -/
theorem cell64_29 (e : List (ZMod 25)) (heK : charOK (basisAt rK64) e = true)
    (h : ↥(reps (⟨29, by decide⟩ : Fin 148))) :
    species (reps (⟨29, by decide⟩ : Fin 148)) h (basisElt (reps rK64) (charOfVec rK64 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK64 e (h : Coordinate 1) T64_29 i :=
  species_entry_eq_sum rK64 ⟨29, by decide⟩ e heK h T64_29 hfix64_29 hinj64_29 hcardT64_29
    (fun i => conj_mem_of_fixedPoints (reps ⟨29, by decide⟩) (reps rK64) (T64_29 i) (hfix64_29 i) h)

/-! ## Cell (64, 34): |T| = 5 -/

def T64_34list : List Coordinates := [(0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0)]
def T64_34 : Fin 5 → Coordinate 1 := fun i => T64_34list.getD i.val (0,0,0,0,0)

theorem hfix64_34 : ∀ i, ((T64_34 i : Coordinate 1) : Coordinate 1 ⧸ reps rK64)
    ∈ fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64) :=
  repsFix_of_siftB rK64 ⟨34, by decide⟩ T64_34 (by decide)

theorem hinj64_34 : Function.Injective
    (fun i => ((T64_34 i : Coordinate 1) : Coordinate 1 ⧸ reps rK64)) :=
  repsInj_of_reduceAux rK64 T64_34 (by decide)

theorem hcardT64_34 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK64 ⟨34, by decide⟩ R64 hpxR64 hcardq64 (by decide)).symm

/-- **Cell (64, 34).** -/
theorem cell64_34 (e : List (ZMod 25)) (heK : charOK (basisAt rK64) e = true)
    (h : ↥(reps (⟨34, by decide⟩ : Fin 148))) :
    species (reps (⟨34, by decide⟩ : Fin 148)) h (basisElt (reps rK64) (charOfVec rK64 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK64 e (h : Coordinate 1) T64_34 i :=
  species_entry_eq_sum rK64 ⟨34, by decide⟩ e heK h T64_34 hfix64_34 hinj64_34 hcardT64_34
    (fun i => conj_mem_of_fixedPoints (reps ⟨34, by decide⟩) (reps rK64) (T64_34 i) (hfix64_34 i) h)

/-! ## Cell (64, 39): |T| = 5 -/

def T64_39list : List Coordinates := [(0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0)]
def T64_39 : Fin 5 → Coordinate 1 := fun i => T64_39list.getD i.val (0,0,0,0,0)

theorem hfix64_39 : ∀ i, ((T64_39 i : Coordinate 1) : Coordinate 1 ⧸ reps rK64)
    ∈ fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64) :=
  repsFix_of_siftB rK64 ⟨39, by decide⟩ T64_39 (by decide)

theorem hinj64_39 : Function.Injective
    (fun i => ((T64_39 i : Coordinate 1) : Coordinate 1 ⧸ reps rK64)) :=
  repsInj_of_reduceAux rK64 T64_39 (by decide)

theorem hcardT64_39 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK64 ⟨39, by decide⟩ R64 hpxR64 hcardq64 (by decide)).symm

/-- **Cell (64, 39).** -/
theorem cell64_39 (e : List (ZMod 25)) (heK : charOK (basisAt rK64) e = true)
    (h : ↥(reps (⟨39, by decide⟩ : Fin 148))) :
    species (reps (⟨39, by decide⟩ : Fin 148)) h (basisElt (reps rK64) (charOfVec rK64 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK64 e (h : Coordinate 1) T64_39 i :=
  species_entry_eq_sum rK64 ⟨39, by decide⟩ e heK h T64_39 hfix64_39 hinj64_39 hcardT64_39
    (fun i => conj_mem_of_fixedPoints (reps ⟨39, by decide⟩) (reps rK64) (T64_39 i) (hfix64_39 i) h)

/-! ## Cell (64, 44): |T| = 5 -/

def T64_44list : List Coordinates := [(0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0)]
def T64_44 : Fin 5 → Coordinate 1 := fun i => T64_44list.getD i.val (0,0,0,0,0)

theorem hfix64_44 : ∀ i, ((T64_44 i : Coordinate 1) : Coordinate 1 ⧸ reps rK64)
    ∈ fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64) :=
  repsFix_of_siftB rK64 ⟨44, by decide⟩ T64_44 (by decide)

theorem hinj64_44 : Function.Injective
    (fun i => ((T64_44 i : Coordinate 1) : Coordinate 1 ⧸ reps rK64)) :=
  repsInj_of_reduceAux rK64 T64_44 (by decide)

theorem hcardT64_44 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK64 ⟨44, by decide⟩ R64 hpxR64 hcardq64 (by decide)).symm

/-- **Cell (64, 44).** -/
theorem cell64_44 (e : List (ZMod 25)) (heK : charOK (basisAt rK64) e = true)
    (h : ↥(reps (⟨44, by decide⟩ : Fin 148))) :
    species (reps (⟨44, by decide⟩ : Fin 148)) h (basisElt (reps rK64) (charOfVec rK64 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK64 e (h : Coordinate 1) T64_44 i :=
  species_entry_eq_sum rK64 ⟨44, by decide⟩ e heK h T64_44 hfix64_44 hinj64_44 hcardT64_44
    (fun i => conj_mem_of_fixedPoints (reps ⟨44, by decide⟩) (reps rK64) (T64_44 i) (hfix64_44 i) h)

/-! ## Cell (64, 49): |T| = 5 -/

def T64_49list : List Coordinates := [(0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0)]
def T64_49 : Fin 5 → Coordinate 1 := fun i => T64_49list.getD i.val (0,0,0,0,0)

theorem hfix64_49 : ∀ i, ((T64_49 i : Coordinate 1) : Coordinate 1 ⧸ reps rK64)
    ∈ fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64) :=
  repsFix_of_siftB rK64 ⟨49, by decide⟩ T64_49 (by decide)

theorem hinj64_49 : Function.Injective
    (fun i => ((T64_49 i : Coordinate 1) : Coordinate 1 ⧸ reps rK64)) :=
  repsInj_of_reduceAux rK64 T64_49 (by decide)

theorem hcardT64_49 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK64 ⟨49, by decide⟩ R64 hpxR64 hcardq64 (by decide)).symm

/-- **Cell (64, 49).** -/
theorem cell64_49 (e : List (ZMod 25)) (heK : charOK (basisAt rK64) e = true)
    (h : ↥(reps (⟨49, by decide⟩ : Fin 148))) :
    species (reps (⟨49, by decide⟩ : Fin 148)) h (basisElt (reps rK64) (charOfVec rK64 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK64 e (h : Coordinate 1) T64_49 i :=
  species_entry_eq_sum rK64 ⟨49, by decide⟩ e heK h T64_49 hfix64_49 hinj64_49 hcardT64_49
    (fun i => conj_mem_of_fixedPoints (reps ⟨49, by decide⟩) (reps rK64) (T64_49 i) (hfix64_49 i) h)

/-! ## Cell (64, 64): |T| = 5 -/

def T64_64list : List Coordinates := [(0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0)]
def T64_64 : Fin 5 → Coordinate 1 := fun i => T64_64list.getD i.val (0,0,0,0,0)

theorem hfix64_64 : ∀ i, ((T64_64 i : Coordinate 1) : Coordinate 1 ⧸ reps rK64)
    ∈ fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64) :=
  repsFix_of_siftB rK64 ⟨64, by decide⟩ T64_64 (by decide)

theorem hinj64_64 : Function.Injective
    (fun i => ((T64_64 i : Coordinate 1) : Coordinate 1 ⧸ reps rK64)) :=
  repsInj_of_reduceAux rK64 T64_64 (by decide)

theorem hcardT64_64 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK64 ⟨64, by decide⟩ R64 hpxR64 hcardq64 (by decide)).symm

/-- **Cell (64, 64).** -/
theorem cell64_64 (e : List (ZMod 25)) (heK : charOK (basisAt rK64) e = true)
    (h : ↥(reps (⟨64, by decide⟩ : Fin 148))) :
    species (reps (⟨64, by decide⟩ : Fin 148)) h (basisElt (reps rK64) (charOfVec rK64 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK64 e (h : Coordinate 1) T64_64 i :=
  species_entry_eq_sum rK64 ⟨64, by decide⟩ e heK h T64_64 hfix64_64 hinj64_64 hcardT64_64
    (fun i => conj_mem_of_fixedPoints (reps ⟨64, by decide⟩) (reps rK64) (T64_64 i) (hfix64_64 i) h)

namespace Q2

def R64_2 : Fin 25 → Coordinate 2 := fun i => R64list.getD i.val (0,0,0,0,0)
theorem hpxR64_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK64) (R64_2 i)) := by decide
theorem hcardq64_2 : Nat.card (Coordinate 2 ⧸ reps rK64) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (64, 0) twin -/

def T64_0_2 : Fin 25 → Coordinate 2 := fun i => T64_0list.getD i.val (0,0,0,0,0)

theorem hfix64_0_2 : ∀ i, ((T64_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK64)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK64) :=
  repsFix_of_siftB2 rK64 ⟨0, by decide⟩ T64_0_2 (by decide)

theorem hinj64_0_2 : Function.Injective
    (fun i => ((T64_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK64)) :=
  repsInj_of_reduceAux2 rK64 T64_0_2 (by decide)

theorem hcardT64_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK64)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK64 ⟨0, by decide⟩ R64_2 hpxR64_2 hcardq64_2 (by decide)).symm

/-- **Cell (64, 0) twin (q=2).** -/
theorem cell64_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK64) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK64) (charOfVec2 rK64 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK64 e (h : Coordinate 2) T64_0_2 i :=
  species_entry_eq_sum rK64 ⟨0, by decide⟩ e heK h T64_0_2 hfix64_0_2 hinj64_0_2 hcardT64_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK64) (T64_0_2 i) (hfix64_0_2 i) h)

/-! ### Cell (64, 8) twin -/

def T64_8_2 : Fin 25 → Coordinate 2 := fun i => T64_8list.getD i.val (0,0,0,0,0)

theorem hfix64_8_2 : ∀ i, ((T64_8_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK64)
    ∈ fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK64) :=
  repsFix_of_siftB2 rK64 ⟨8, by decide⟩ T64_8_2 (by decide)

theorem hinj64_8_2 : Function.Injective
    (fun i => ((T64_8_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK64)) :=
  repsInj_of_reduceAux2 rK64 T64_8_2 (by decide)

theorem hcardT64_8_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK64)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK64 ⟨8, by decide⟩ R64_2 hpxR64_2 hcardq64_2 (by decide)).symm

/-- **Cell (64, 8) twin (q=2).** -/
theorem cell64_8_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK64) e = true)
    (h : ↥(reps (⟨8, by decide⟩ : Fin 148))) :
    species (reps (⟨8, by decide⟩ : Fin 148)) h (basisElt (reps rK64) (charOfVec2 rK64 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK64 e (h : Coordinate 2) T64_8_2 i :=
  species_entry_eq_sum rK64 ⟨8, by decide⟩ e heK h T64_8_2 hfix64_8_2 hinj64_8_2 hcardT64_8_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨8, by decide⟩) (reps rK64) (T64_8_2 i) (hfix64_8_2 i) h)

/-! ### Cell (64, 12) twin -/

def T64_12_2 : Fin 25 → Coordinate 2 := fun i => T64_12list.getD i.val (0,0,0,0,0)

theorem hfix64_12_2 : ∀ i, ((T64_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK64)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK64) :=
  repsFix_of_siftB2 rK64 ⟨12, by decide⟩ T64_12_2 (by decide)

theorem hinj64_12_2 : Function.Injective
    (fun i => ((T64_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK64)) :=
  repsInj_of_reduceAux2 rK64 T64_12_2 (by decide)

theorem hcardT64_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK64)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK64 ⟨12, by decide⟩ R64_2 hpxR64_2 hcardq64_2 (by decide)).symm

/-- **Cell (64, 12) twin (q=2).** -/
theorem cell64_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK64) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK64) (charOfVec2 rK64 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK64 e (h : Coordinate 2) T64_12_2 i :=
  species_entry_eq_sum rK64 ⟨12, by decide⟩ e heK h T64_12_2 hfix64_12_2 hinj64_12_2 hcardT64_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK64) (T64_12_2 i) (hfix64_12_2 i) h)

/-! ### Cell (64, 26) twin -/

def T64_26_2 : Fin 25 → Coordinate 2 := fun i => T64_26list.getD i.val (0,0,0,0,0)

theorem hfix64_26_2 : ∀ i, ((T64_26_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK64)
    ∈ fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK64) :=
  repsFix_of_siftB2 rK64 ⟨26, by decide⟩ T64_26_2 (by decide)

theorem hinj64_26_2 : Function.Injective
    (fun i => ((T64_26_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK64)) :=
  repsInj_of_reduceAux2 rK64 T64_26_2 (by decide)

theorem hcardT64_26_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK64)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK64 ⟨26, by decide⟩ R64_2 hpxR64_2 hcardq64_2 (by decide)).symm

/-- **Cell (64, 26) twin (q=2).** -/
theorem cell64_26_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK64) e = true)
    (h : ↥(reps (⟨26, by decide⟩ : Fin 148))) :
    species (reps (⟨26, by decide⟩ : Fin 148)) h (basisElt (reps rK64) (charOfVec2 rK64 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK64 e (h : Coordinate 2) T64_26_2 i :=
  species_entry_eq_sum rK64 ⟨26, by decide⟩ e heK h T64_26_2 hfix64_26_2 hinj64_26_2 hcardT64_26_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨26, by decide⟩) (reps rK64) (T64_26_2 i) (hfix64_26_2 i) h)

/-! ### Cell (64, 29) twin -/

def T64_29_2 : Fin 5 → Coordinate 2 := fun i => T64_29list.getD i.val (0,0,0,0,0)

theorem hfix64_29_2 : ∀ i, ((T64_29_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK64)
    ∈ fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK64) :=
  repsFix_of_siftB2 rK64 ⟨29, by decide⟩ T64_29_2 (by decide)

theorem hinj64_29_2 : Function.Injective
    (fun i => ((T64_29_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK64)) :=
  repsInj_of_reduceAux2 rK64 T64_29_2 (by decide)

theorem hcardT64_29_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK64)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK64 ⟨29, by decide⟩ R64_2 hpxR64_2 hcardq64_2 (by decide)).symm

/-- **Cell (64, 29) twin (q=2).** -/
theorem cell64_29_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK64) e = true)
    (h : ↥(reps (⟨29, by decide⟩ : Fin 148))) :
    species (reps (⟨29, by decide⟩ : Fin 148)) h (basisElt (reps rK64) (charOfVec2 rK64 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK64 e (h : Coordinate 2) T64_29_2 i :=
  species_entry_eq_sum rK64 ⟨29, by decide⟩ e heK h T64_29_2 hfix64_29_2 hinj64_29_2 hcardT64_29_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨29, by decide⟩) (reps rK64) (T64_29_2 i) (hfix64_29_2 i) h)

/-! ### Cell (64, 34) twin -/

def T64_34_2 : Fin 5 → Coordinate 2 := fun i => T64_34list.getD i.val (0,0,0,0,0)

theorem hfix64_34_2 : ∀ i, ((T64_34_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK64)
    ∈ fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK64) :=
  repsFix_of_siftB2 rK64 ⟨34, by decide⟩ T64_34_2 (by decide)

theorem hinj64_34_2 : Function.Injective
    (fun i => ((T64_34_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK64)) :=
  repsInj_of_reduceAux2 rK64 T64_34_2 (by decide)

theorem hcardT64_34_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK64)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK64 ⟨34, by decide⟩ R64_2 hpxR64_2 hcardq64_2 (by decide)).symm

/-- **Cell (64, 34) twin (q=2).** -/
theorem cell64_34_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK64) e = true)
    (h : ↥(reps (⟨34, by decide⟩ : Fin 148))) :
    species (reps (⟨34, by decide⟩ : Fin 148)) h (basisElt (reps rK64) (charOfVec2 rK64 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK64 e (h : Coordinate 2) T64_34_2 i :=
  species_entry_eq_sum rK64 ⟨34, by decide⟩ e heK h T64_34_2 hfix64_34_2 hinj64_34_2 hcardT64_34_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨34, by decide⟩) (reps rK64) (T64_34_2 i) (hfix64_34_2 i) h)

/-! ### Cell (64, 39) twin -/

def T64_39_2 : Fin 5 → Coordinate 2 := fun i => T64_39list.getD i.val (0,0,0,0,0)

theorem hfix64_39_2 : ∀ i, ((T64_39_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK64)
    ∈ fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK64) :=
  repsFix_of_siftB2 rK64 ⟨39, by decide⟩ T64_39_2 (by decide)

theorem hinj64_39_2 : Function.Injective
    (fun i => ((T64_39_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK64)) :=
  repsInj_of_reduceAux2 rK64 T64_39_2 (by decide)

theorem hcardT64_39_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK64)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK64 ⟨39, by decide⟩ R64_2 hpxR64_2 hcardq64_2 (by decide)).symm

/-- **Cell (64, 39) twin (q=2).** -/
theorem cell64_39_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK64) e = true)
    (h : ↥(reps (⟨39, by decide⟩ : Fin 148))) :
    species (reps (⟨39, by decide⟩ : Fin 148)) h (basisElt (reps rK64) (charOfVec2 rK64 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK64 e (h : Coordinate 2) T64_39_2 i :=
  species_entry_eq_sum rK64 ⟨39, by decide⟩ e heK h T64_39_2 hfix64_39_2 hinj64_39_2 hcardT64_39_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨39, by decide⟩) (reps rK64) (T64_39_2 i) (hfix64_39_2 i) h)

/-! ### Cell (64, 44) twin -/

def T64_44_2 : Fin 5 → Coordinate 2 := fun i => T64_44list.getD i.val (0,0,0,0,0)

theorem hfix64_44_2 : ∀ i, ((T64_44_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK64)
    ∈ fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK64) :=
  repsFix_of_siftB2 rK64 ⟨44, by decide⟩ T64_44_2 (by decide)

theorem hinj64_44_2 : Function.Injective
    (fun i => ((T64_44_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK64)) :=
  repsInj_of_reduceAux2 rK64 T64_44_2 (by decide)

theorem hcardT64_44_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK64)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK64 ⟨44, by decide⟩ R64_2 hpxR64_2 hcardq64_2 (by decide)).symm

/-- **Cell (64, 44) twin (q=2).** -/
theorem cell64_44_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK64) e = true)
    (h : ↥(reps (⟨44, by decide⟩ : Fin 148))) :
    species (reps (⟨44, by decide⟩ : Fin 148)) h (basisElt (reps rK64) (charOfVec2 rK64 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK64 e (h : Coordinate 2) T64_44_2 i :=
  species_entry_eq_sum rK64 ⟨44, by decide⟩ e heK h T64_44_2 hfix64_44_2 hinj64_44_2 hcardT64_44_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨44, by decide⟩) (reps rK64) (T64_44_2 i) (hfix64_44_2 i) h)

/-! ### Cell (64, 49) twin -/

def T64_49_2 : Fin 5 → Coordinate 2 := fun i => T64_49list.getD i.val (0,0,0,0,0)

theorem hfix64_49_2 : ∀ i, ((T64_49_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK64)
    ∈ fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK64) :=
  repsFix_of_siftB2 rK64 ⟨49, by decide⟩ T64_49_2 (by decide)

theorem hinj64_49_2 : Function.Injective
    (fun i => ((T64_49_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK64)) :=
  repsInj_of_reduceAux2 rK64 T64_49_2 (by decide)

theorem hcardT64_49_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK64)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK64 ⟨49, by decide⟩ R64_2 hpxR64_2 hcardq64_2 (by decide)).symm

/-- **Cell (64, 49) twin (q=2).** -/
theorem cell64_49_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK64) e = true)
    (h : ↥(reps (⟨49, by decide⟩ : Fin 148))) :
    species (reps (⟨49, by decide⟩ : Fin 148)) h (basisElt (reps rK64) (charOfVec2 rK64 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK64 e (h : Coordinate 2) T64_49_2 i :=
  species_entry_eq_sum rK64 ⟨49, by decide⟩ e heK h T64_49_2 hfix64_49_2 hinj64_49_2 hcardT64_49_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨49, by decide⟩) (reps rK64) (T64_49_2 i) (hfix64_49_2 i) h)

/-! ### Cell (64, 64) twin -/

def T64_64_2 : Fin 5 → Coordinate 2 := fun i => T64_64list.getD i.val (0,0,0,0,0)

theorem hfix64_64_2 : ∀ i, ((T64_64_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK64)
    ∈ fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK64) :=
  repsFix_of_siftB2 rK64 ⟨64, by decide⟩ T64_64_2 (by decide)

theorem hinj64_64_2 : Function.Injective
    (fun i => ((T64_64_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK64)) :=
  repsInj_of_reduceAux2 rK64 T64_64_2 (by decide)

theorem hcardT64_64_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK64)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK64 ⟨64, by decide⟩ R64_2 hpxR64_2 hcardq64_2 (by decide)).symm

/-- **Cell (64, 64) twin (q=2).** -/
theorem cell64_64_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK64) e = true)
    (h : ↥(reps (⟨64, by decide⟩ : Fin 148))) :
    species (reps (⟨64, by decide⟩ : Fin 148)) h (basisElt (reps rK64) (charOfVec2 rK64 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK64 e (h : Coordinate 2) T64_64_2 i :=
  species_entry_eq_sum rK64 ⟨64, by decide⟩ e heK h T64_64_2 hfix64_64_2 hinj64_64_2 hcardT64_64_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨64, by decide⟩) (reps rK64) (T64_64_2 i) (hfix64_64_2 i) h)

end Q2

end LeanDring.P5Presentation
