/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, K-strata data (5^3 stratum, rK 55-59): certified per-cell species-entry instantiations, both
twins.

Covers K-classes 55, 56, 57, 58, 59 (order-5^3 K, |R|=25).  For each nonzero `H`-column
(`(G/K)^H ≠ ∅`), the full coset transversal `R55..` and each `H`-fixed
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

/-! # K-class rK = 55  (|G/K| = 25) -/

def rK55 : Fin 148 := ⟨55, by decide⟩

def R55list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0)]
def R55 : Fin 25 → Coordinate 1 := fun i => R55list.getD i.val (0,0,0,0,0)

theorem hpxR55 : Function.Injective (fun i => reduceAux 1 (basisAt rK55) (R55 i)) := by decide
theorem hcardq55 : Nat.card (Coordinate 1 ⧸ reps rK55) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (55, 0): |T| = 25 -/

def T55_0list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0)]
def T55_0 : Fin 25 → Coordinate 1 := fun i => T55_0list.getD i.val (0,0,0,0,0)

theorem hfix55_0 : ∀ i, ((T55_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK55)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55) :=
  repsFix_of_siftB rK55 ⟨0, by decide⟩ T55_0 (by decide)

theorem hinj55_0 : Function.Injective
    (fun i => ((T55_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK55)) :=
  repsInj_of_reduceAux rK55 T55_0 (by decide)

theorem hcardT55_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK55 ⟨0, by decide⟩ R55 hpxR55 hcardq55 (by decide)).symm

/-- **Cell (55, 0).** -/
theorem cell55_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK55) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK55) (charOfVec rK55 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK55 e (h : Coordinate 1) T55_0 i :=
  species_entry_eq_sum rK55 ⟨0, by decide⟩ e heK h T55_0 hfix55_0 hinj55_0 hcardT55_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK55) (T55_0 i) (hfix55_0 i) h)

/-! ## Cell (55, 9): |T| = 25 -/

def T55_9list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0)]
def T55_9 : Fin 25 → Coordinate 1 := fun i => T55_9list.getD i.val (0,0,0,0,0)

theorem hfix55_9 : ∀ i, ((T55_9 i : Coordinate 1) : Coordinate 1 ⧸ reps rK55)
    ∈ fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55) :=
  repsFix_of_siftB rK55 ⟨9, by decide⟩ T55_9 (by decide)

theorem hinj55_9 : Function.Injective
    (fun i => ((T55_9 i : Coordinate 1) : Coordinate 1 ⧸ reps rK55)) :=
  repsInj_of_reduceAux rK55 T55_9 (by decide)

theorem hcardT55_9 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK55 ⟨9, by decide⟩ R55 hpxR55 hcardq55 (by decide)).symm

/-- **Cell (55, 9).** -/
theorem cell55_9 (e : List (ZMod 25)) (heK : charOK (basisAt rK55) e = true)
    (h : ↥(reps (⟨9, by decide⟩ : Fin 148))) :
    species (reps (⟨9, by decide⟩ : Fin 148)) h (basisElt (reps rK55) (charOfVec rK55 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK55 e (h : Coordinate 1) T55_9 i :=
  species_entry_eq_sum rK55 ⟨9, by decide⟩ e heK h T55_9 hfix55_9 hinj55_9 hcardT55_9
    (fun i => conj_mem_of_fixedPoints (reps ⟨9, by decide⟩) (reps rK55) (T55_9 i) (hfix55_9 i) h)

/-! ## Cell (55, 12): |T| = 25 -/

def T55_12list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0)]
def T55_12 : Fin 25 → Coordinate 1 := fun i => T55_12list.getD i.val (0,0,0,0,0)

theorem hfix55_12 : ∀ i, ((T55_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK55)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55) :=
  repsFix_of_siftB rK55 ⟨12, by decide⟩ T55_12 (by decide)

theorem hinj55_12 : Function.Injective
    (fun i => ((T55_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK55)) :=
  repsInj_of_reduceAux rK55 T55_12 (by decide)

theorem hcardT55_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK55 ⟨12, by decide⟩ R55 hpxR55 hcardq55 (by decide)).symm

/-- **Cell (55, 12).** -/
theorem cell55_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK55) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK55) (charOfVec rK55 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK55 e (h : Coordinate 1) T55_12 i :=
  species_entry_eq_sum rK55 ⟨12, by decide⟩ e heK h T55_12 hfix55_12 hinj55_12 hcardT55_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK55) (T55_12 i) (hfix55_12 i) h)

/-! ## Cell (55, 27): |T| = 25 -/

def T55_27list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0)]
def T55_27 : Fin 25 → Coordinate 1 := fun i => T55_27list.getD i.val (0,0,0,0,0)

theorem hfix55_27 : ∀ i, ((T55_27 i : Coordinate 1) : Coordinate 1 ⧸ reps rK55)
    ∈ fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55) :=
  repsFix_of_siftB rK55 ⟨27, by decide⟩ T55_27 (by decide)

theorem hinj55_27 : Function.Injective
    (fun i => ((T55_27 i : Coordinate 1) : Coordinate 1 ⧸ reps rK55)) :=
  repsInj_of_reduceAux rK55 T55_27 (by decide)

theorem hcardT55_27 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK55 ⟨27, by decide⟩ R55 hpxR55 hcardq55 (by decide)).symm

/-- **Cell (55, 27).** -/
theorem cell55_27 (e : List (ZMod 25)) (heK : charOK (basisAt rK55) e = true)
    (h : ↥(reps (⟨27, by decide⟩ : Fin 148))) :
    species (reps (⟨27, by decide⟩ : Fin 148)) h (basisElt (reps rK55) (charOfVec rK55 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK55 e (h : Coordinate 1) T55_27 i :=
  species_entry_eq_sum rK55 ⟨27, by decide⟩ e heK h T55_27 hfix55_27 hinj55_27 hcardT55_27
    (fun i => conj_mem_of_fixedPoints (reps ⟨27, by decide⟩) (reps rK55) (T55_27 i) (hfix55_27 i) h)

/-! ## Cell (55, 28): |T| = 5 -/

def T55_28list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0)]
def T55_28 : Fin 5 → Coordinate 1 := fun i => T55_28list.getD i.val (0,0,0,0,0)

theorem hfix55_28 : ∀ i, ((T55_28 i : Coordinate 1) : Coordinate 1 ⧸ reps rK55)
    ∈ fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55) :=
  repsFix_of_siftB rK55 ⟨28, by decide⟩ T55_28 (by decide)

theorem hinj55_28 : Function.Injective
    (fun i => ((T55_28 i : Coordinate 1) : Coordinate 1 ⧸ reps rK55)) :=
  repsInj_of_reduceAux rK55 T55_28 (by decide)

theorem hcardT55_28 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK55 ⟨28, by decide⟩ R55 hpxR55 hcardq55 (by decide)).symm

/-- **Cell (55, 28).** -/
theorem cell55_28 (e : List (ZMod 25)) (heK : charOK (basisAt rK55) e = true)
    (h : ↥(reps (⟨28, by decide⟩ : Fin 148))) :
    species (reps (⟨28, by decide⟩ : Fin 148)) h (basisElt (reps rK55) (charOfVec rK55 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK55 e (h : Coordinate 1) T55_28 i :=
  species_entry_eq_sum rK55 ⟨28, by decide⟩ e heK h T55_28 hfix55_28 hinj55_28 hcardT55_28
    (fun i => conj_mem_of_fixedPoints (reps ⟨28, by decide⟩) (reps rK55) (T55_28 i) (hfix55_28 i) h)

/-! ## Cell (55, 33): |T| = 5 -/

def T55_33list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0)]
def T55_33 : Fin 5 → Coordinate 1 := fun i => T55_33list.getD i.val (0,0,0,0,0)

theorem hfix55_33 : ∀ i, ((T55_33 i : Coordinate 1) : Coordinate 1 ⧸ reps rK55)
    ∈ fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55) :=
  repsFix_of_siftB rK55 ⟨33, by decide⟩ T55_33 (by decide)

theorem hinj55_33 : Function.Injective
    (fun i => ((T55_33 i : Coordinate 1) : Coordinate 1 ⧸ reps rK55)) :=
  repsInj_of_reduceAux rK55 T55_33 (by decide)

theorem hcardT55_33 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK55 ⟨33, by decide⟩ R55 hpxR55 hcardq55 (by decide)).symm

/-- **Cell (55, 33).** -/
theorem cell55_33 (e : List (ZMod 25)) (heK : charOK (basisAt rK55) e = true)
    (h : ↥(reps (⟨33, by decide⟩ : Fin 148))) :
    species (reps (⟨33, by decide⟩ : Fin 148)) h (basisElt (reps rK55) (charOfVec rK55 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK55 e (h : Coordinate 1) T55_33 i :=
  species_entry_eq_sum rK55 ⟨33, by decide⟩ e heK h T55_33 hfix55_33 hinj55_33 hcardT55_33
    (fun i => conj_mem_of_fixedPoints (reps ⟨33, by decide⟩) (reps rK55) (T55_33 i) (hfix55_33 i) h)

/-! ## Cell (55, 38): |T| = 5 -/

def T55_38list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0)]
def T55_38 : Fin 5 → Coordinate 1 := fun i => T55_38list.getD i.val (0,0,0,0,0)

theorem hfix55_38 : ∀ i, ((T55_38 i : Coordinate 1) : Coordinate 1 ⧸ reps rK55)
    ∈ fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55) :=
  repsFix_of_siftB rK55 ⟨38, by decide⟩ T55_38 (by decide)

theorem hinj55_38 : Function.Injective
    (fun i => ((T55_38 i : Coordinate 1) : Coordinate 1 ⧸ reps rK55)) :=
  repsInj_of_reduceAux rK55 T55_38 (by decide)

theorem hcardT55_38 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK55 ⟨38, by decide⟩ R55 hpxR55 hcardq55 (by decide)).symm

/-- **Cell (55, 38).** -/
theorem cell55_38 (e : List (ZMod 25)) (heK : charOK (basisAt rK55) e = true)
    (h : ↥(reps (⟨38, by decide⟩ : Fin 148))) :
    species (reps (⟨38, by decide⟩ : Fin 148)) h (basisElt (reps rK55) (charOfVec rK55 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK55 e (h : Coordinate 1) T55_38 i :=
  species_entry_eq_sum rK55 ⟨38, by decide⟩ e heK h T55_38 hfix55_38 hinj55_38 hcardT55_38
    (fun i => conj_mem_of_fixedPoints (reps ⟨38, by decide⟩) (reps rK55) (T55_38 i) (hfix55_38 i) h)

/-! ## Cell (55, 43): |T| = 5 -/

def T55_43list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0)]
def T55_43 : Fin 5 → Coordinate 1 := fun i => T55_43list.getD i.val (0,0,0,0,0)

theorem hfix55_43 : ∀ i, ((T55_43 i : Coordinate 1) : Coordinate 1 ⧸ reps rK55)
    ∈ fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55) :=
  repsFix_of_siftB rK55 ⟨43, by decide⟩ T55_43 (by decide)

theorem hinj55_43 : Function.Injective
    (fun i => ((T55_43 i : Coordinate 1) : Coordinate 1 ⧸ reps rK55)) :=
  repsInj_of_reduceAux rK55 T55_43 (by decide)

theorem hcardT55_43 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK55 ⟨43, by decide⟩ R55 hpxR55 hcardq55 (by decide)).symm

/-- **Cell (55, 43).** -/
theorem cell55_43 (e : List (ZMod 25)) (heK : charOK (basisAt rK55) e = true)
    (h : ↥(reps (⟨43, by decide⟩ : Fin 148))) :
    species (reps (⟨43, by decide⟩ : Fin 148)) h (basisElt (reps rK55) (charOfVec rK55 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK55 e (h : Coordinate 1) T55_43 i :=
  species_entry_eq_sum rK55 ⟨43, by decide⟩ e heK h T55_43 hfix55_43 hinj55_43 hcardT55_43
    (fun i => conj_mem_of_fixedPoints (reps ⟨43, by decide⟩) (reps rK55) (T55_43 i) (hfix55_43 i) h)

/-! ## Cell (55, 48): |T| = 5 -/

def T55_48list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0)]
def T55_48 : Fin 5 → Coordinate 1 := fun i => T55_48list.getD i.val (0,0,0,0,0)

theorem hfix55_48 : ∀ i, ((T55_48 i : Coordinate 1) : Coordinate 1 ⧸ reps rK55)
    ∈ fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55) :=
  repsFix_of_siftB rK55 ⟨48, by decide⟩ T55_48 (by decide)

theorem hinj55_48 : Function.Injective
    (fun i => ((T55_48 i : Coordinate 1) : Coordinate 1 ⧸ reps rK55)) :=
  repsInj_of_reduceAux rK55 T55_48 (by decide)

theorem hcardT55_48 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK55 ⟨48, by decide⟩ R55 hpxR55 hcardq55 (by decide)).symm

/-- **Cell (55, 48).** -/
theorem cell55_48 (e : List (ZMod 25)) (heK : charOK (basisAt rK55) e = true)
    (h : ↥(reps (⟨48, by decide⟩ : Fin 148))) :
    species (reps (⟨48, by decide⟩ : Fin 148)) h (basisElt (reps rK55) (charOfVec rK55 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK55 e (h : Coordinate 1) T55_48 i :=
  species_entry_eq_sum rK55 ⟨48, by decide⟩ e heK h T55_48 hfix55_48 hinj55_48 hcardT55_48
    (fun i => conj_mem_of_fixedPoints (reps ⟨48, by decide⟩) (reps rK55) (T55_48 i) (hfix55_48 i) h)

/-! ## Cell (55, 55): |T| = 5 -/

def T55_55list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0)]
def T55_55 : Fin 5 → Coordinate 1 := fun i => T55_55list.getD i.val (0,0,0,0,0)

theorem hfix55_55 : ∀ i, ((T55_55 i : Coordinate 1) : Coordinate 1 ⧸ reps rK55)
    ∈ fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55) :=
  repsFix_of_siftB rK55 ⟨55, by decide⟩ T55_55 (by decide)

theorem hinj55_55 : Function.Injective
    (fun i => ((T55_55 i : Coordinate 1) : Coordinate 1 ⧸ reps rK55)) :=
  repsInj_of_reduceAux rK55 T55_55 (by decide)

theorem hcardT55_55 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK55 ⟨55, by decide⟩ R55 hpxR55 hcardq55 (by decide)).symm

/-- **Cell (55, 55).** -/
theorem cell55_55 (e : List (ZMod 25)) (heK : charOK (basisAt rK55) e = true)
    (h : ↥(reps (⟨55, by decide⟩ : Fin 148))) :
    species (reps (⟨55, by decide⟩ : Fin 148)) h (basisElt (reps rK55) (charOfVec rK55 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK55 e (h : Coordinate 1) T55_55 i :=
  species_entry_eq_sum rK55 ⟨55, by decide⟩ e heK h T55_55 hfix55_55 hinj55_55 hcardT55_55
    (fun i => conj_mem_of_fixedPoints (reps ⟨55, by decide⟩) (reps rK55) (T55_55 i) (hfix55_55 i) h)

namespace Q2

def R55_2 : Fin 25 → Coordinate 2 := fun i => R55list.getD i.val (0,0,0,0,0)
theorem hpxR55_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK55) (R55_2 i)) := by decide
theorem hcardq55_2 : Nat.card (Coordinate 2 ⧸ reps rK55) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (55, 0) twin -/

def T55_0_2 : Fin 25 → Coordinate 2 := fun i => T55_0list.getD i.val (0,0,0,0,0)

theorem hfix55_0_2 : ∀ i, ((T55_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK55)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK55) :=
  repsFix_of_siftB2 rK55 ⟨0, by decide⟩ T55_0_2 (by decide)

theorem hinj55_0_2 : Function.Injective
    (fun i => ((T55_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK55)) :=
  repsInj_of_reduceAux2 rK55 T55_0_2 (by decide)

theorem hcardT55_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK55)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK55 ⟨0, by decide⟩ R55_2 hpxR55_2 hcardq55_2 (by decide)).symm

/-- **Cell (55, 0) twin (q=2).** -/
theorem cell55_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK55) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK55) (charOfVec2 rK55 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK55 e (h : Coordinate 2) T55_0_2 i :=
  species_entry_eq_sum rK55 ⟨0, by decide⟩ e heK h T55_0_2 hfix55_0_2 hinj55_0_2 hcardT55_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK55) (T55_0_2 i) (hfix55_0_2 i) h)

/-! ### Cell (55, 9) twin -/

def T55_9_2 : Fin 25 → Coordinate 2 := fun i => T55_9list.getD i.val (0,0,0,0,0)

theorem hfix55_9_2 : ∀ i, ((T55_9_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK55)
    ∈ fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK55) :=
  repsFix_of_siftB2 rK55 ⟨9, by decide⟩ T55_9_2 (by decide)

theorem hinj55_9_2 : Function.Injective
    (fun i => ((T55_9_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK55)) :=
  repsInj_of_reduceAux2 rK55 T55_9_2 (by decide)

theorem hcardT55_9_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK55)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK55 ⟨9, by decide⟩ R55_2 hpxR55_2 hcardq55_2 (by decide)).symm

/-- **Cell (55, 9) twin (q=2).** -/
theorem cell55_9_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK55) e = true)
    (h : ↥(reps (⟨9, by decide⟩ : Fin 148))) :
    species (reps (⟨9, by decide⟩ : Fin 148)) h (basisElt (reps rK55) (charOfVec2 rK55 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK55 e (h : Coordinate 2) T55_9_2 i :=
  species_entry_eq_sum rK55 ⟨9, by decide⟩ e heK h T55_9_2 hfix55_9_2 hinj55_9_2 hcardT55_9_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨9, by decide⟩) (reps rK55) (T55_9_2 i) (hfix55_9_2 i) h)

/-! ### Cell (55, 12) twin -/

def T55_12_2 : Fin 25 → Coordinate 2 := fun i => T55_12list.getD i.val (0,0,0,0,0)

theorem hfix55_12_2 : ∀ i, ((T55_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK55)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK55) :=
  repsFix_of_siftB2 rK55 ⟨12, by decide⟩ T55_12_2 (by decide)

theorem hinj55_12_2 : Function.Injective
    (fun i => ((T55_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK55)) :=
  repsInj_of_reduceAux2 rK55 T55_12_2 (by decide)

theorem hcardT55_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK55)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK55 ⟨12, by decide⟩ R55_2 hpxR55_2 hcardq55_2 (by decide)).symm

/-- **Cell (55, 12) twin (q=2).** -/
theorem cell55_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK55) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK55) (charOfVec2 rK55 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK55 e (h : Coordinate 2) T55_12_2 i :=
  species_entry_eq_sum rK55 ⟨12, by decide⟩ e heK h T55_12_2 hfix55_12_2 hinj55_12_2 hcardT55_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK55) (T55_12_2 i) (hfix55_12_2 i) h)

/-! ### Cell (55, 27) twin -/

def T55_27_2 : Fin 25 → Coordinate 2 := fun i => T55_27list.getD i.val (0,0,0,0,0)

theorem hfix55_27_2 : ∀ i, ((T55_27_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK55)
    ∈ fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK55) :=
  repsFix_of_siftB2 rK55 ⟨27, by decide⟩ T55_27_2 (by decide)

theorem hinj55_27_2 : Function.Injective
    (fun i => ((T55_27_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK55)) :=
  repsInj_of_reduceAux2 rK55 T55_27_2 (by decide)

theorem hcardT55_27_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK55)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK55 ⟨27, by decide⟩ R55_2 hpxR55_2 hcardq55_2 (by decide)).symm

/-- **Cell (55, 27) twin (q=2).** -/
theorem cell55_27_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK55) e = true)
    (h : ↥(reps (⟨27, by decide⟩ : Fin 148))) :
    species (reps (⟨27, by decide⟩ : Fin 148)) h (basisElt (reps rK55) (charOfVec2 rK55 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK55 e (h : Coordinate 2) T55_27_2 i :=
  species_entry_eq_sum rK55 ⟨27, by decide⟩ e heK h T55_27_2 hfix55_27_2 hinj55_27_2 hcardT55_27_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨27, by decide⟩) (reps rK55) (T55_27_2 i) (hfix55_27_2 i) h)

/-! ### Cell (55, 28) twin -/

def T55_28_2 : Fin 5 → Coordinate 2 := fun i => T55_28list.getD i.val (0,0,0,0,0)

theorem hfix55_28_2 : ∀ i, ((T55_28_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK55)
    ∈ fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK55) :=
  repsFix_of_siftB2 rK55 ⟨28, by decide⟩ T55_28_2 (by decide)

theorem hinj55_28_2 : Function.Injective
    (fun i => ((T55_28_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK55)) :=
  repsInj_of_reduceAux2 rK55 T55_28_2 (by decide)

theorem hcardT55_28_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK55)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK55 ⟨28, by decide⟩ R55_2 hpxR55_2 hcardq55_2 (by decide)).symm

/-- **Cell (55, 28) twin (q=2).** -/
theorem cell55_28_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK55) e = true)
    (h : ↥(reps (⟨28, by decide⟩ : Fin 148))) :
    species (reps (⟨28, by decide⟩ : Fin 148)) h (basisElt (reps rK55) (charOfVec2 rK55 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK55 e (h : Coordinate 2) T55_28_2 i :=
  species_entry_eq_sum rK55 ⟨28, by decide⟩ e heK h T55_28_2 hfix55_28_2 hinj55_28_2 hcardT55_28_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨28, by decide⟩) (reps rK55) (T55_28_2 i) (hfix55_28_2 i) h)

/-! ### Cell (55, 33) twin -/

def T55_33_2 : Fin 5 → Coordinate 2 := fun i => T55_33list.getD i.val (0,0,0,0,0)

theorem hfix55_33_2 : ∀ i, ((T55_33_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK55)
    ∈ fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK55) :=
  repsFix_of_siftB2 rK55 ⟨33, by decide⟩ T55_33_2 (by decide)

theorem hinj55_33_2 : Function.Injective
    (fun i => ((T55_33_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK55)) :=
  repsInj_of_reduceAux2 rK55 T55_33_2 (by decide)

theorem hcardT55_33_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK55)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK55 ⟨33, by decide⟩ R55_2 hpxR55_2 hcardq55_2 (by decide)).symm

/-- **Cell (55, 33) twin (q=2).** -/
theorem cell55_33_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK55) e = true)
    (h : ↥(reps (⟨33, by decide⟩ : Fin 148))) :
    species (reps (⟨33, by decide⟩ : Fin 148)) h (basisElt (reps rK55) (charOfVec2 rK55 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK55 e (h : Coordinate 2) T55_33_2 i :=
  species_entry_eq_sum rK55 ⟨33, by decide⟩ e heK h T55_33_2 hfix55_33_2 hinj55_33_2 hcardT55_33_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨33, by decide⟩) (reps rK55) (T55_33_2 i) (hfix55_33_2 i) h)

/-! ### Cell (55, 38) twin -/

def T55_38_2 : Fin 5 → Coordinate 2 := fun i => T55_38list.getD i.val (0,0,0,0,0)

theorem hfix55_38_2 : ∀ i, ((T55_38_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK55)
    ∈ fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK55) :=
  repsFix_of_siftB2 rK55 ⟨38, by decide⟩ T55_38_2 (by decide)

theorem hinj55_38_2 : Function.Injective
    (fun i => ((T55_38_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK55)) :=
  repsInj_of_reduceAux2 rK55 T55_38_2 (by decide)

theorem hcardT55_38_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK55)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK55 ⟨38, by decide⟩ R55_2 hpxR55_2 hcardq55_2 (by decide)).symm

/-- **Cell (55, 38) twin (q=2).** -/
theorem cell55_38_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK55) e = true)
    (h : ↥(reps (⟨38, by decide⟩ : Fin 148))) :
    species (reps (⟨38, by decide⟩ : Fin 148)) h (basisElt (reps rK55) (charOfVec2 rK55 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK55 e (h : Coordinate 2) T55_38_2 i :=
  species_entry_eq_sum rK55 ⟨38, by decide⟩ e heK h T55_38_2 hfix55_38_2 hinj55_38_2 hcardT55_38_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨38, by decide⟩) (reps rK55) (T55_38_2 i) (hfix55_38_2 i) h)

/-! ### Cell (55, 43) twin -/

def T55_43_2 : Fin 5 → Coordinate 2 := fun i => T55_43list.getD i.val (0,0,0,0,0)

theorem hfix55_43_2 : ∀ i, ((T55_43_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK55)
    ∈ fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK55) :=
  repsFix_of_siftB2 rK55 ⟨43, by decide⟩ T55_43_2 (by decide)

theorem hinj55_43_2 : Function.Injective
    (fun i => ((T55_43_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK55)) :=
  repsInj_of_reduceAux2 rK55 T55_43_2 (by decide)

theorem hcardT55_43_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK55)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK55 ⟨43, by decide⟩ R55_2 hpxR55_2 hcardq55_2 (by decide)).symm

/-- **Cell (55, 43) twin (q=2).** -/
theorem cell55_43_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK55) e = true)
    (h : ↥(reps (⟨43, by decide⟩ : Fin 148))) :
    species (reps (⟨43, by decide⟩ : Fin 148)) h (basisElt (reps rK55) (charOfVec2 rK55 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK55 e (h : Coordinate 2) T55_43_2 i :=
  species_entry_eq_sum rK55 ⟨43, by decide⟩ e heK h T55_43_2 hfix55_43_2 hinj55_43_2 hcardT55_43_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨43, by decide⟩) (reps rK55) (T55_43_2 i) (hfix55_43_2 i) h)

/-! ### Cell (55, 48) twin -/

def T55_48_2 : Fin 5 → Coordinate 2 := fun i => T55_48list.getD i.val (0,0,0,0,0)

theorem hfix55_48_2 : ∀ i, ((T55_48_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK55)
    ∈ fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK55) :=
  repsFix_of_siftB2 rK55 ⟨48, by decide⟩ T55_48_2 (by decide)

theorem hinj55_48_2 : Function.Injective
    (fun i => ((T55_48_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK55)) :=
  repsInj_of_reduceAux2 rK55 T55_48_2 (by decide)

theorem hcardT55_48_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK55)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK55 ⟨48, by decide⟩ R55_2 hpxR55_2 hcardq55_2 (by decide)).symm

/-- **Cell (55, 48) twin (q=2).** -/
theorem cell55_48_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK55) e = true)
    (h : ↥(reps (⟨48, by decide⟩ : Fin 148))) :
    species (reps (⟨48, by decide⟩ : Fin 148)) h (basisElt (reps rK55) (charOfVec2 rK55 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK55 e (h : Coordinate 2) T55_48_2 i :=
  species_entry_eq_sum rK55 ⟨48, by decide⟩ e heK h T55_48_2 hfix55_48_2 hinj55_48_2 hcardT55_48_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨48, by decide⟩) (reps rK55) (T55_48_2 i) (hfix55_48_2 i) h)

/-! ### Cell (55, 55) twin -/

def T55_55_2 : Fin 5 → Coordinate 2 := fun i => T55_55list.getD i.val (0,0,0,0,0)

theorem hfix55_55_2 : ∀ i, ((T55_55_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK55)
    ∈ fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK55) :=
  repsFix_of_siftB2 rK55 ⟨55, by decide⟩ T55_55_2 (by decide)

theorem hinj55_55_2 : Function.Injective
    (fun i => ((T55_55_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK55)) :=
  repsInj_of_reduceAux2 rK55 T55_55_2 (by decide)

theorem hcardT55_55_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK55)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK55 ⟨55, by decide⟩ R55_2 hpxR55_2 hcardq55_2 (by decide)).symm

/-- **Cell (55, 55) twin (q=2).** -/
theorem cell55_55_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK55) e = true)
    (h : ↥(reps (⟨55, by decide⟩ : Fin 148))) :
    species (reps (⟨55, by decide⟩ : Fin 148)) h (basisElt (reps rK55) (charOfVec2 rK55 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK55 e (h : Coordinate 2) T55_55_2 i :=
  species_entry_eq_sum rK55 ⟨55, by decide⟩ e heK h T55_55_2 hfix55_55_2 hinj55_55_2 hcardT55_55_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨55, by decide⟩) (reps rK55) (T55_55_2 i) (hfix55_55_2 i) h)

end Q2

/-! # K-class rK = 56  (|G/K| = 25) -/

def rK56 : Fin 148 := ⟨56, by decide⟩

def R56list : List Coordinates := [(0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (1,0,0,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (2,0,0,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (3,0,0,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (4,0,0,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0)]
def R56 : Fin 25 → Coordinate 1 := fun i => R56list.getD i.val (0,0,0,0,0)

theorem hpxR56 : Function.Injective (fun i => reduceAux 1 (basisAt rK56) (R56 i)) := by decide
theorem hcardq56 : Nat.card (Coordinate 1 ⧸ reps rK56) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (56, 0): |T| = 25 -/

def T56_0list : List Coordinates := [(0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (1,0,0,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (2,0,0,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (3,0,0,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (4,0,0,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0)]
def T56_0 : Fin 25 → Coordinate 1 := fun i => T56_0list.getD i.val (0,0,0,0,0)

theorem hfix56_0 : ∀ i, ((T56_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK56)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56) :=
  repsFix_of_siftB rK56 ⟨0, by decide⟩ T56_0 (by decide)

theorem hinj56_0 : Function.Injective
    (fun i => ((T56_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK56)) :=
  repsInj_of_reduceAux rK56 T56_0 (by decide)

theorem hcardT56_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK56 ⟨0, by decide⟩ R56 hpxR56 hcardq56 (by decide)).symm

/-- **Cell (56, 0).** -/
theorem cell56_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK56) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK56) (charOfVec rK56 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK56 e (h : Coordinate 1) T56_0 i :=
  species_entry_eq_sum rK56 ⟨0, by decide⟩ e heK h T56_0 hfix56_0 hinj56_0 hcardT56_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK56) (T56_0 i) (hfix56_0 i) h)

/-! ## Cell (56, 1): |T| = 25 -/

def T56_1list : List Coordinates := [(0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (1,0,0,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (2,0,0,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (3,0,0,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (4,0,0,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0)]
def T56_1 : Fin 25 → Coordinate 1 := fun i => T56_1list.getD i.val (0,0,0,0,0)

theorem hfix56_1 : ∀ i, ((T56_1 i : Coordinate 1) : Coordinate 1 ⧸ reps rK56)
    ∈ fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56) :=
  repsFix_of_siftB rK56 ⟨1, by decide⟩ T56_1 (by decide)

theorem hinj56_1 : Function.Injective
    (fun i => ((T56_1 i : Coordinate 1) : Coordinate 1 ⧸ reps rK56)) :=
  repsInj_of_reduceAux rK56 T56_1 (by decide)

theorem hcardT56_1 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK56 ⟨1, by decide⟩ R56 hpxR56 hcardq56 (by decide)).symm

/-- **Cell (56, 1).** -/
theorem cell56_1 (e : List (ZMod 25)) (heK : charOK (basisAt rK56) e = true)
    (h : ↥(reps (⟨1, by decide⟩ : Fin 148))) :
    species (reps (⟨1, by decide⟩ : Fin 148)) h (basisElt (reps rK56) (charOfVec rK56 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK56 e (h : Coordinate 1) T56_1 i :=
  species_entry_eq_sum rK56 ⟨1, by decide⟩ e heK h T56_1 hfix56_1 hinj56_1 hcardT56_1
    (fun i => conj_mem_of_fixedPoints (reps ⟨1, by decide⟩) (reps rK56) (T56_1 i) (hfix56_1 i) h)

/-! ## Cell (56, 12): |T| = 25 -/

def T56_12list : List Coordinates := [(0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (1,0,0,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (2,0,0,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (3,0,0,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (4,0,0,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0)]
def T56_12 : Fin 25 → Coordinate 1 := fun i => T56_12list.getD i.val (0,0,0,0,0)

theorem hfix56_12 : ∀ i, ((T56_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK56)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56) :=
  repsFix_of_siftB rK56 ⟨12, by decide⟩ T56_12 (by decide)

theorem hinj56_12 : Function.Injective
    (fun i => ((T56_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK56)) :=
  repsInj_of_reduceAux rK56 T56_12 (by decide)

theorem hcardT56_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK56 ⟨12, by decide⟩ R56 hpxR56 hcardq56 (by decide)).symm

/-- **Cell (56, 12).** -/
theorem cell56_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK56) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK56) (charOfVec rK56 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK56 e (h : Coordinate 1) T56_12 i :=
  species_entry_eq_sum rK56 ⟨12, by decide⟩ e heK h T56_12 hfix56_12 hinj56_12 hcardT56_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK56) (T56_12 i) (hfix56_12 i) h)

/-! ## Cell (56, 19): |T| = 25 -/

def T56_19list : List Coordinates := [(0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (1,0,0,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (2,0,0,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (3,0,0,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (4,0,0,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0)]
def T56_19 : Fin 25 → Coordinate 1 := fun i => T56_19list.getD i.val (0,0,0,0,0)

theorem hfix56_19 : ∀ i, ((T56_19 i : Coordinate 1) : Coordinate 1 ⧸ reps rK56)
    ∈ fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56) :=
  repsFix_of_siftB rK56 ⟨19, by decide⟩ T56_19 (by decide)

theorem hinj56_19 : Function.Injective
    (fun i => ((T56_19 i : Coordinate 1) : Coordinate 1 ⧸ reps rK56)) :=
  repsInj_of_reduceAux rK56 T56_19 (by decide)

theorem hcardT56_19 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK56 ⟨19, by decide⟩ R56 hpxR56 hcardq56 (by decide)).symm

/-- **Cell (56, 19).** -/
theorem cell56_19 (e : List (ZMod 25)) (heK : charOK (basisAt rK56) e = true)
    (h : ↥(reps (⟨19, by decide⟩ : Fin 148))) :
    species (reps (⟨19, by decide⟩ : Fin 148)) h (basisElt (reps rK56) (charOfVec rK56 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK56 e (h : Coordinate 1) T56_19 i :=
  species_entry_eq_sum rK56 ⟨19, by decide⟩ e heK h T56_19 hfix56_19 hinj56_19 hcardT56_19
    (fun i => conj_mem_of_fixedPoints (reps ⟨19, by decide⟩) (reps rK56) (T56_19 i) (hfix56_19 i) h)

/-! ## Cell (56, 28): |T| = 5 -/

def T56_28list : List Coordinates := [(1,0,0,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0)]
def T56_28 : Fin 5 → Coordinate 1 := fun i => T56_28list.getD i.val (0,0,0,0,0)

theorem hfix56_28 : ∀ i, ((T56_28 i : Coordinate 1) : Coordinate 1 ⧸ reps rK56)
    ∈ fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56) :=
  repsFix_of_siftB rK56 ⟨28, by decide⟩ T56_28 (by decide)

theorem hinj56_28 : Function.Injective
    (fun i => ((T56_28 i : Coordinate 1) : Coordinate 1 ⧸ reps rK56)) :=
  repsInj_of_reduceAux rK56 T56_28 (by decide)

theorem hcardT56_28 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK56 ⟨28, by decide⟩ R56 hpxR56 hcardq56 (by decide)).symm

/-- **Cell (56, 28).** -/
theorem cell56_28 (e : List (ZMod 25)) (heK : charOK (basisAt rK56) e = true)
    (h : ↥(reps (⟨28, by decide⟩ : Fin 148))) :
    species (reps (⟨28, by decide⟩ : Fin 148)) h (basisElt (reps rK56) (charOfVec rK56 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK56 e (h : Coordinate 1) T56_28 i :=
  species_entry_eq_sum rK56 ⟨28, by decide⟩ e heK h T56_28 hfix56_28 hinj56_28 hcardT56_28
    (fun i => conj_mem_of_fixedPoints (reps ⟨28, by decide⟩) (reps rK56) (T56_28 i) (hfix56_28 i) h)

/-! ## Cell (56, 33): |T| = 5 -/

def T56_33list : List Coordinates := [(3,0,0,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0)]
def T56_33 : Fin 5 → Coordinate 1 := fun i => T56_33list.getD i.val (0,0,0,0,0)

theorem hfix56_33 : ∀ i, ((T56_33 i : Coordinate 1) : Coordinate 1 ⧸ reps rK56)
    ∈ fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56) :=
  repsFix_of_siftB rK56 ⟨33, by decide⟩ T56_33 (by decide)

theorem hinj56_33 : Function.Injective
    (fun i => ((T56_33 i : Coordinate 1) : Coordinate 1 ⧸ reps rK56)) :=
  repsInj_of_reduceAux rK56 T56_33 (by decide)

theorem hcardT56_33 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK56 ⟨33, by decide⟩ R56 hpxR56 hcardq56 (by decide)).symm

/-- **Cell (56, 33).** -/
theorem cell56_33 (e : List (ZMod 25)) (heK : charOK (basisAt rK56) e = true)
    (h : ↥(reps (⟨33, by decide⟩ : Fin 148))) :
    species (reps (⟨33, by decide⟩ : Fin 148)) h (basisElt (reps rK56) (charOfVec rK56 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK56 e (h : Coordinate 1) T56_33 i :=
  species_entry_eq_sum rK56 ⟨33, by decide⟩ e heK h T56_33 hfix56_33 hinj56_33 hcardT56_33
    (fun i => conj_mem_of_fixedPoints (reps ⟨33, by decide⟩) (reps rK56) (T56_33 i) (hfix56_33 i) h)

/-! ## Cell (56, 38): |T| = 5 -/

def T56_38list : List Coordinates := [(2,0,0,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0)]
def T56_38 : Fin 5 → Coordinate 1 := fun i => T56_38list.getD i.val (0,0,0,0,0)

theorem hfix56_38 : ∀ i, ((T56_38 i : Coordinate 1) : Coordinate 1 ⧸ reps rK56)
    ∈ fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56) :=
  repsFix_of_siftB rK56 ⟨38, by decide⟩ T56_38 (by decide)

theorem hinj56_38 : Function.Injective
    (fun i => ((T56_38 i : Coordinate 1) : Coordinate 1 ⧸ reps rK56)) :=
  repsInj_of_reduceAux rK56 T56_38 (by decide)

theorem hcardT56_38 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK56 ⟨38, by decide⟩ R56 hpxR56 hcardq56 (by decide)).symm

/-- **Cell (56, 38).** -/
theorem cell56_38 (e : List (ZMod 25)) (heK : charOK (basisAt rK56) e = true)
    (h : ↥(reps (⟨38, by decide⟩ : Fin 148))) :
    species (reps (⟨38, by decide⟩ : Fin 148)) h (basisElt (reps rK56) (charOfVec rK56 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK56 e (h : Coordinate 1) T56_38 i :=
  species_entry_eq_sum rK56 ⟨38, by decide⟩ e heK h T56_38 hfix56_38 hinj56_38 hcardT56_38
    (fun i => conj_mem_of_fixedPoints (reps ⟨38, by decide⟩) (reps rK56) (T56_38 i) (hfix56_38 i) h)

/-! ## Cell (56, 43): |T| = 5 -/

def T56_43list : List Coordinates := [(4,0,0,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0)]
def T56_43 : Fin 5 → Coordinate 1 := fun i => T56_43list.getD i.val (0,0,0,0,0)

theorem hfix56_43 : ∀ i, ((T56_43 i : Coordinate 1) : Coordinate 1 ⧸ reps rK56)
    ∈ fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56) :=
  repsFix_of_siftB rK56 ⟨43, by decide⟩ T56_43 (by decide)

theorem hinj56_43 : Function.Injective
    (fun i => ((T56_43 i : Coordinate 1) : Coordinate 1 ⧸ reps rK56)) :=
  repsInj_of_reduceAux rK56 T56_43 (by decide)

theorem hcardT56_43 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK56 ⟨43, by decide⟩ R56 hpxR56 hcardq56 (by decide)).symm

/-- **Cell (56, 43).** -/
theorem cell56_43 (e : List (ZMod 25)) (heK : charOK (basisAt rK56) e = true)
    (h : ↥(reps (⟨43, by decide⟩ : Fin 148))) :
    species (reps (⟨43, by decide⟩ : Fin 148)) h (basisElt (reps rK56) (charOfVec rK56 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK56 e (h : Coordinate 1) T56_43 i :=
  species_entry_eq_sum rK56 ⟨43, by decide⟩ e heK h T56_43 hfix56_43 hinj56_43 hcardT56_43
    (fun i => conj_mem_of_fixedPoints (reps ⟨43, by decide⟩) (reps rK56) (T56_43 i) (hfix56_43 i) h)

/-! ## Cell (56, 48): |T| = 5 -/

def T56_48list : List Coordinates := [(0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0)]
def T56_48 : Fin 5 → Coordinate 1 := fun i => T56_48list.getD i.val (0,0,0,0,0)

theorem hfix56_48 : ∀ i, ((T56_48 i : Coordinate 1) : Coordinate 1 ⧸ reps rK56)
    ∈ fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56) :=
  repsFix_of_siftB rK56 ⟨48, by decide⟩ T56_48 (by decide)

theorem hinj56_48 : Function.Injective
    (fun i => ((T56_48 i : Coordinate 1) : Coordinate 1 ⧸ reps rK56)) :=
  repsInj_of_reduceAux rK56 T56_48 (by decide)

theorem hcardT56_48 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK56 ⟨48, by decide⟩ R56 hpxR56 hcardq56 (by decide)).symm

/-- **Cell (56, 48).** -/
theorem cell56_48 (e : List (ZMod 25)) (heK : charOK (basisAt rK56) e = true)
    (h : ↥(reps (⟨48, by decide⟩ : Fin 148))) :
    species (reps (⟨48, by decide⟩ : Fin 148)) h (basisElt (reps rK56) (charOfVec rK56 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK56 e (h : Coordinate 1) T56_48 i :=
  species_entry_eq_sum rK56 ⟨48, by decide⟩ e heK h T56_48 hfix56_48 hinj56_48 hcardT56_48
    (fun i => conj_mem_of_fixedPoints (reps ⟨48, by decide⟩) (reps rK56) (T56_48 i) (hfix56_48 i) h)

/-! ## Cell (56, 56): |T| = 5 -/

def T56_56list : List Coordinates := [(0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0)]
def T56_56 : Fin 5 → Coordinate 1 := fun i => T56_56list.getD i.val (0,0,0,0,0)

theorem hfix56_56 : ∀ i, ((T56_56 i : Coordinate 1) : Coordinate 1 ⧸ reps rK56)
    ∈ fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56) :=
  repsFix_of_siftB rK56 ⟨56, by decide⟩ T56_56 (by decide)

theorem hinj56_56 : Function.Injective
    (fun i => ((T56_56 i : Coordinate 1) : Coordinate 1 ⧸ reps rK56)) :=
  repsInj_of_reduceAux rK56 T56_56 (by decide)

theorem hcardT56_56 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK56 ⟨56, by decide⟩ R56 hpxR56 hcardq56 (by decide)).symm

/-- **Cell (56, 56).** -/
theorem cell56_56 (e : List (ZMod 25)) (heK : charOK (basisAt rK56) e = true)
    (h : ↥(reps (⟨56, by decide⟩ : Fin 148))) :
    species (reps (⟨56, by decide⟩ : Fin 148)) h (basisElt (reps rK56) (charOfVec rK56 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK56 e (h : Coordinate 1) T56_56 i :=
  species_entry_eq_sum rK56 ⟨56, by decide⟩ e heK h T56_56 hfix56_56 hinj56_56 hcardT56_56
    (fun i => conj_mem_of_fixedPoints (reps ⟨56, by decide⟩) (reps rK56) (T56_56 i) (hfix56_56 i) h)

namespace Q2

def R56_2 : Fin 25 → Coordinate 2 := fun i => R56list.getD i.val (0,0,0,0,0)
theorem hpxR56_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK56) (R56_2 i)) := by decide
theorem hcardq56_2 : Nat.card (Coordinate 2 ⧸ reps rK56) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (56, 0) twin -/

def T56_0_2 : Fin 25 → Coordinate 2 := fun i => T56_0list.getD i.val (0,0,0,0,0)

theorem hfix56_0_2 : ∀ i, ((T56_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK56)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK56) :=
  repsFix_of_siftB2 rK56 ⟨0, by decide⟩ T56_0_2 (by decide)

theorem hinj56_0_2 : Function.Injective
    (fun i => ((T56_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK56)) :=
  repsInj_of_reduceAux2 rK56 T56_0_2 (by decide)

theorem hcardT56_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK56)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK56 ⟨0, by decide⟩ R56_2 hpxR56_2 hcardq56_2 (by decide)).symm

/-- **Cell (56, 0) twin (q=2).** -/
theorem cell56_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK56) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK56) (charOfVec2 rK56 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK56 e (h : Coordinate 2) T56_0_2 i :=
  species_entry_eq_sum rK56 ⟨0, by decide⟩ e heK h T56_0_2 hfix56_0_2 hinj56_0_2 hcardT56_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK56) (T56_0_2 i) (hfix56_0_2 i) h)

/-! ### Cell (56, 1) twin -/

def T56_1_2 : Fin 25 → Coordinate 2 := fun i => T56_1list.getD i.val (0,0,0,0,0)

theorem hfix56_1_2 : ∀ i, ((T56_1_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK56)
    ∈ fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK56) :=
  repsFix_of_siftB2 rK56 ⟨1, by decide⟩ T56_1_2 (by decide)

theorem hinj56_1_2 : Function.Injective
    (fun i => ((T56_1_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK56)) :=
  repsInj_of_reduceAux2 rK56 T56_1_2 (by decide)

theorem hcardT56_1_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK56)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK56 ⟨1, by decide⟩ R56_2 hpxR56_2 hcardq56_2 (by decide)).symm

/-- **Cell (56, 1) twin (q=2).** -/
theorem cell56_1_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK56) e = true)
    (h : ↥(reps (⟨1, by decide⟩ : Fin 148))) :
    species (reps (⟨1, by decide⟩ : Fin 148)) h (basisElt (reps rK56) (charOfVec2 rK56 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK56 e (h : Coordinate 2) T56_1_2 i :=
  species_entry_eq_sum rK56 ⟨1, by decide⟩ e heK h T56_1_2 hfix56_1_2 hinj56_1_2 hcardT56_1_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨1, by decide⟩) (reps rK56) (T56_1_2 i) (hfix56_1_2 i) h)

/-! ### Cell (56, 12) twin -/

def T56_12_2 : Fin 25 → Coordinate 2 := fun i => T56_12list.getD i.val (0,0,0,0,0)

theorem hfix56_12_2 : ∀ i, ((T56_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK56)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK56) :=
  repsFix_of_siftB2 rK56 ⟨12, by decide⟩ T56_12_2 (by decide)

theorem hinj56_12_2 : Function.Injective
    (fun i => ((T56_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK56)) :=
  repsInj_of_reduceAux2 rK56 T56_12_2 (by decide)

theorem hcardT56_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK56)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK56 ⟨12, by decide⟩ R56_2 hpxR56_2 hcardq56_2 (by decide)).symm

/-- **Cell (56, 12) twin (q=2).** -/
theorem cell56_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK56) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK56) (charOfVec2 rK56 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK56 e (h : Coordinate 2) T56_12_2 i :=
  species_entry_eq_sum rK56 ⟨12, by decide⟩ e heK h T56_12_2 hfix56_12_2 hinj56_12_2 hcardT56_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK56) (T56_12_2 i) (hfix56_12_2 i) h)

/-! ### Cell (56, 19) twin -/

def T56_19_2 : Fin 25 → Coordinate 2 := fun i => T56_19list.getD i.val (0,0,0,0,0)

theorem hfix56_19_2 : ∀ i, ((T56_19_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK56)
    ∈ fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK56) :=
  repsFix_of_siftB2 rK56 ⟨19, by decide⟩ T56_19_2 (by decide)

theorem hinj56_19_2 : Function.Injective
    (fun i => ((T56_19_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK56)) :=
  repsInj_of_reduceAux2 rK56 T56_19_2 (by decide)

theorem hcardT56_19_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK56)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK56 ⟨19, by decide⟩ R56_2 hpxR56_2 hcardq56_2 (by decide)).symm

/-- **Cell (56, 19) twin (q=2).** -/
theorem cell56_19_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK56) e = true)
    (h : ↥(reps (⟨19, by decide⟩ : Fin 148))) :
    species (reps (⟨19, by decide⟩ : Fin 148)) h (basisElt (reps rK56) (charOfVec2 rK56 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK56 e (h : Coordinate 2) T56_19_2 i :=
  species_entry_eq_sum rK56 ⟨19, by decide⟩ e heK h T56_19_2 hfix56_19_2 hinj56_19_2 hcardT56_19_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨19, by decide⟩) (reps rK56) (T56_19_2 i) (hfix56_19_2 i) h)

/-! ### Cell (56, 28) twin -/

def T56_28_2 : Fin 5 → Coordinate 2 := fun i => T56_28list.getD i.val (0,0,0,0,0)

theorem hfix56_28_2 : ∀ i, ((T56_28_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK56)
    ∈ fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK56) :=
  repsFix_of_siftB2 rK56 ⟨28, by decide⟩ T56_28_2 (by decide)

theorem hinj56_28_2 : Function.Injective
    (fun i => ((T56_28_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK56)) :=
  repsInj_of_reduceAux2 rK56 T56_28_2 (by decide)

theorem hcardT56_28_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK56)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK56 ⟨28, by decide⟩ R56_2 hpxR56_2 hcardq56_2 (by decide)).symm

/-- **Cell (56, 28) twin (q=2).** -/
theorem cell56_28_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK56) e = true)
    (h : ↥(reps (⟨28, by decide⟩ : Fin 148))) :
    species (reps (⟨28, by decide⟩ : Fin 148)) h (basisElt (reps rK56) (charOfVec2 rK56 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK56 e (h : Coordinate 2) T56_28_2 i :=
  species_entry_eq_sum rK56 ⟨28, by decide⟩ e heK h T56_28_2 hfix56_28_2 hinj56_28_2 hcardT56_28_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨28, by decide⟩) (reps rK56) (T56_28_2 i) (hfix56_28_2 i) h)

/-! ### Cell (56, 33) twin -/

def T56_33_2 : Fin 5 → Coordinate 2 := fun i => T56_33list.getD i.val (0,0,0,0,0)

theorem hfix56_33_2 : ∀ i, ((T56_33_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK56)
    ∈ fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK56) :=
  repsFix_of_siftB2 rK56 ⟨33, by decide⟩ T56_33_2 (by decide)

theorem hinj56_33_2 : Function.Injective
    (fun i => ((T56_33_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK56)) :=
  repsInj_of_reduceAux2 rK56 T56_33_2 (by decide)

theorem hcardT56_33_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK56)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK56 ⟨33, by decide⟩ R56_2 hpxR56_2 hcardq56_2 (by decide)).symm

/-- **Cell (56, 33) twin (q=2).** -/
theorem cell56_33_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK56) e = true)
    (h : ↥(reps (⟨33, by decide⟩ : Fin 148))) :
    species (reps (⟨33, by decide⟩ : Fin 148)) h (basisElt (reps rK56) (charOfVec2 rK56 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK56 e (h : Coordinate 2) T56_33_2 i :=
  species_entry_eq_sum rK56 ⟨33, by decide⟩ e heK h T56_33_2 hfix56_33_2 hinj56_33_2 hcardT56_33_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨33, by decide⟩) (reps rK56) (T56_33_2 i) (hfix56_33_2 i) h)

/-! ### Cell (56, 38) twin -/

def T56_38_2 : Fin 5 → Coordinate 2 := fun i => T56_38list.getD i.val (0,0,0,0,0)

theorem hfix56_38_2 : ∀ i, ((T56_38_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK56)
    ∈ fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK56) :=
  repsFix_of_siftB2 rK56 ⟨38, by decide⟩ T56_38_2 (by decide)

theorem hinj56_38_2 : Function.Injective
    (fun i => ((T56_38_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK56)) :=
  repsInj_of_reduceAux2 rK56 T56_38_2 (by decide)

theorem hcardT56_38_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK56)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK56 ⟨38, by decide⟩ R56_2 hpxR56_2 hcardq56_2 (by decide)).symm

/-- **Cell (56, 38) twin (q=2).** -/
theorem cell56_38_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK56) e = true)
    (h : ↥(reps (⟨38, by decide⟩ : Fin 148))) :
    species (reps (⟨38, by decide⟩ : Fin 148)) h (basisElt (reps rK56) (charOfVec2 rK56 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK56 e (h : Coordinate 2) T56_38_2 i :=
  species_entry_eq_sum rK56 ⟨38, by decide⟩ e heK h T56_38_2 hfix56_38_2 hinj56_38_2 hcardT56_38_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨38, by decide⟩) (reps rK56) (T56_38_2 i) (hfix56_38_2 i) h)

/-! ### Cell (56, 43) twin -/

def T56_43_2 : Fin 5 → Coordinate 2 := fun i => T56_43list.getD i.val (0,0,0,0,0)

theorem hfix56_43_2 : ∀ i, ((T56_43_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK56)
    ∈ fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK56) :=
  repsFix_of_siftB2 rK56 ⟨43, by decide⟩ T56_43_2 (by decide)

theorem hinj56_43_2 : Function.Injective
    (fun i => ((T56_43_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK56)) :=
  repsInj_of_reduceAux2 rK56 T56_43_2 (by decide)

theorem hcardT56_43_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK56)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK56 ⟨43, by decide⟩ R56_2 hpxR56_2 hcardq56_2 (by decide)).symm

/-- **Cell (56, 43) twin (q=2).** -/
theorem cell56_43_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK56) e = true)
    (h : ↥(reps (⟨43, by decide⟩ : Fin 148))) :
    species (reps (⟨43, by decide⟩ : Fin 148)) h (basisElt (reps rK56) (charOfVec2 rK56 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK56 e (h : Coordinate 2) T56_43_2 i :=
  species_entry_eq_sum rK56 ⟨43, by decide⟩ e heK h T56_43_2 hfix56_43_2 hinj56_43_2 hcardT56_43_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨43, by decide⟩) (reps rK56) (T56_43_2 i) (hfix56_43_2 i) h)

/-! ### Cell (56, 48) twin -/

def T56_48_2 : Fin 5 → Coordinate 2 := fun i => T56_48list.getD i.val (0,0,0,0,0)

theorem hfix56_48_2 : ∀ i, ((T56_48_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK56)
    ∈ fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK56) :=
  repsFix_of_siftB2 rK56 ⟨48, by decide⟩ T56_48_2 (by decide)

theorem hinj56_48_2 : Function.Injective
    (fun i => ((T56_48_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK56)) :=
  repsInj_of_reduceAux2 rK56 T56_48_2 (by decide)

theorem hcardT56_48_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK56)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK56 ⟨48, by decide⟩ R56_2 hpxR56_2 hcardq56_2 (by decide)).symm

/-- **Cell (56, 48) twin (q=2).** -/
theorem cell56_48_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK56) e = true)
    (h : ↥(reps (⟨48, by decide⟩ : Fin 148))) :
    species (reps (⟨48, by decide⟩ : Fin 148)) h (basisElt (reps rK56) (charOfVec2 rK56 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK56 e (h : Coordinate 2) T56_48_2 i :=
  species_entry_eq_sum rK56 ⟨48, by decide⟩ e heK h T56_48_2 hfix56_48_2 hinj56_48_2 hcardT56_48_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨48, by decide⟩) (reps rK56) (T56_48_2 i) (hfix56_48_2 i) h)

/-! ### Cell (56, 56) twin -/

def T56_56_2 : Fin 5 → Coordinate 2 := fun i => T56_56list.getD i.val (0,0,0,0,0)

theorem hfix56_56_2 : ∀ i, ((T56_56_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK56)
    ∈ fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK56) :=
  repsFix_of_siftB2 rK56 ⟨56, by decide⟩ T56_56_2 (by decide)

theorem hinj56_56_2 : Function.Injective
    (fun i => ((T56_56_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK56)) :=
  repsInj_of_reduceAux2 rK56 T56_56_2 (by decide)

theorem hcardT56_56_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK56)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK56 ⟨56, by decide⟩ R56_2 hpxR56_2 hcardq56_2 (by decide)).symm

/-- **Cell (56, 56) twin (q=2).** -/
theorem cell56_56_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK56) e = true)
    (h : ↥(reps (⟨56, by decide⟩ : Fin 148))) :
    species (reps (⟨56, by decide⟩ : Fin 148)) h (basisElt (reps rK56) (charOfVec2 rK56 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK56 e (h : Coordinate 2) T56_56_2 i :=
  species_entry_eq_sum rK56 ⟨56, by decide⟩ e heK h T56_56_2 hfix56_56_2 hinj56_56_2 hcardT56_56_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨56, by decide⟩) (reps rK56) (T56_56_2 i) (hfix56_56_2 i) h)

end Q2

/-! # K-class rK = 57  (|G/K| = 25) -/

def rK57 : Fin 148 := ⟨57, by decide⟩

def R57list : List Coordinates := [(0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0)]
def R57 : Fin 25 → Coordinate 1 := fun i => R57list.getD i.val (0,0,0,0,0)

theorem hpxR57 : Function.Injective (fun i => reduceAux 1 (basisAt rK57) (R57 i)) := by decide
theorem hcardq57 : Nat.card (Coordinate 1 ⧸ reps rK57) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (57, 0): |T| = 25 -/

def T57_0list : List Coordinates := [(0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0)]
def T57_0 : Fin 25 → Coordinate 1 := fun i => T57_0list.getD i.val (0,0,0,0,0)

theorem hfix57_0 : ∀ i, ((T57_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK57)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57) :=
  repsFix_of_siftB rK57 ⟨0, by decide⟩ T57_0 (by decide)

theorem hinj57_0 : Function.Injective
    (fun i => ((T57_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK57)) :=
  repsInj_of_reduceAux rK57 T57_0 (by decide)

theorem hcardT57_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK57 ⟨0, by decide⟩ R57 hpxR57 hcardq57 (by decide)).symm

/-- **Cell (57, 0).** -/
theorem cell57_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK57) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK57) (charOfVec rK57 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK57 e (h : Coordinate 1) T57_0 i :=
  species_entry_eq_sum rK57 ⟨0, by decide⟩ e heK h T57_0 hfix57_0 hinj57_0 hcardT57_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK57) (T57_0 i) (hfix57_0 i) h)

/-! ## Cell (57, 7): |T| = 25 -/

def T57_7list : List Coordinates := [(0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0)]
def T57_7 : Fin 25 → Coordinate 1 := fun i => T57_7list.getD i.val (0,0,0,0,0)

theorem hfix57_7 : ∀ i, ((T57_7 i : Coordinate 1) : Coordinate 1 ⧸ reps rK57)
    ∈ fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57) :=
  repsFix_of_siftB rK57 ⟨7, by decide⟩ T57_7 (by decide)

theorem hinj57_7 : Function.Injective
    (fun i => ((T57_7 i : Coordinate 1) : Coordinate 1 ⧸ reps rK57)) :=
  repsInj_of_reduceAux rK57 T57_7 (by decide)

theorem hcardT57_7 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK57 ⟨7, by decide⟩ R57 hpxR57 hcardq57 (by decide)).symm

/-- **Cell (57, 7).** -/
theorem cell57_7 (e : List (ZMod 25)) (heK : charOK (basisAt rK57) e = true)
    (h : ↥(reps (⟨7, by decide⟩ : Fin 148))) :
    species (reps (⟨7, by decide⟩ : Fin 148)) h (basisElt (reps rK57) (charOfVec rK57 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK57 e (h : Coordinate 1) T57_7 i :=
  species_entry_eq_sum rK57 ⟨7, by decide⟩ e heK h T57_7 hfix57_7 hinj57_7 hcardT57_7
    (fun i => conj_mem_of_fixedPoints (reps ⟨7, by decide⟩) (reps rK57) (T57_7 i) (hfix57_7 i) h)

/-! ## Cell (57, 12): |T| = 25 -/

def T57_12list : List Coordinates := [(0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0)]
def T57_12 : Fin 25 → Coordinate 1 := fun i => T57_12list.getD i.val (0,0,0,0,0)

theorem hfix57_12 : ∀ i, ((T57_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK57)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57) :=
  repsFix_of_siftB rK57 ⟨12, by decide⟩ T57_12 (by decide)

theorem hinj57_12 : Function.Injective
    (fun i => ((T57_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK57)) :=
  repsInj_of_reduceAux rK57 T57_12 (by decide)

theorem hcardT57_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK57 ⟨12, by decide⟩ R57 hpxR57 hcardq57 (by decide)).symm

/-- **Cell (57, 12).** -/
theorem cell57_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK57) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK57) (charOfVec rK57 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK57 e (h : Coordinate 1) T57_12 i :=
  species_entry_eq_sum rK57 ⟨12, by decide⟩ e heK h T57_12 hfix57_12 hinj57_12 hcardT57_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK57) (T57_12 i) (hfix57_12 i) h)

/-! ## Cell (57, 25): |T| = 25 -/

def T57_25list : List Coordinates := [(0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0)]
def T57_25 : Fin 25 → Coordinate 1 := fun i => T57_25list.getD i.val (0,0,0,0,0)

theorem hfix57_25 : ∀ i, ((T57_25 i : Coordinate 1) : Coordinate 1 ⧸ reps rK57)
    ∈ fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57) :=
  repsFix_of_siftB rK57 ⟨25, by decide⟩ T57_25 (by decide)

theorem hinj57_25 : Function.Injective
    (fun i => ((T57_25 i : Coordinate 1) : Coordinate 1 ⧸ reps rK57)) :=
  repsInj_of_reduceAux rK57 T57_25 (by decide)

theorem hcardT57_25 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK57 ⟨25, by decide⟩ R57 hpxR57 hcardq57 (by decide)).symm

/-- **Cell (57, 25).** -/
theorem cell57_25 (e : List (ZMod 25)) (heK : charOK (basisAt rK57) e = true)
    (h : ↥(reps (⟨25, by decide⟩ : Fin 148))) :
    species (reps (⟨25, by decide⟩ : Fin 148)) h (basisElt (reps rK57) (charOfVec rK57 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK57 e (h : Coordinate 1) T57_25 i :=
  species_entry_eq_sum rK57 ⟨25, by decide⟩ e heK h T57_25 hfix57_25 hinj57_25 hcardT57_25
    (fun i => conj_mem_of_fixedPoints (reps ⟨25, by decide⟩) (reps rK57) (T57_25 i) (hfix57_25 i) h)

/-! ## Cell (57, 28): |T| = 5 -/

def T57_28list : List Coordinates := [(2,0,0,2,0), (2,0,0,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0)]
def T57_28 : Fin 5 → Coordinate 1 := fun i => T57_28list.getD i.val (0,0,0,0,0)

theorem hfix57_28 : ∀ i, ((T57_28 i : Coordinate 1) : Coordinate 1 ⧸ reps rK57)
    ∈ fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57) :=
  repsFix_of_siftB rK57 ⟨28, by decide⟩ T57_28 (by decide)

theorem hinj57_28 : Function.Injective
    (fun i => ((T57_28 i : Coordinate 1) : Coordinate 1 ⧸ reps rK57)) :=
  repsInj_of_reduceAux rK57 T57_28 (by decide)

theorem hcardT57_28 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK57 ⟨28, by decide⟩ R57 hpxR57 hcardq57 (by decide)).symm

/-- **Cell (57, 28).** -/
theorem cell57_28 (e : List (ZMod 25)) (heK : charOK (basisAt rK57) e = true)
    (h : ↥(reps (⟨28, by decide⟩ : Fin 148))) :
    species (reps (⟨28, by decide⟩ : Fin 148)) h (basisElt (reps rK57) (charOfVec rK57 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK57 e (h : Coordinate 1) T57_28 i :=
  species_entry_eq_sum rK57 ⟨28, by decide⟩ e heK h T57_28 hfix57_28 hinj57_28 hcardT57_28
    (fun i => conj_mem_of_fixedPoints (reps ⟨28, by decide⟩) (reps rK57) (T57_28 i) (hfix57_28 i) h)

/-! ## Cell (57, 33): |T| = 5 -/

def T57_33list : List Coordinates := [(1,0,0,2,0), (1,0,0,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0)]
def T57_33 : Fin 5 → Coordinate 1 := fun i => T57_33list.getD i.val (0,0,0,0,0)

theorem hfix57_33 : ∀ i, ((T57_33 i : Coordinate 1) : Coordinate 1 ⧸ reps rK57)
    ∈ fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57) :=
  repsFix_of_siftB rK57 ⟨33, by decide⟩ T57_33 (by decide)

theorem hinj57_33 : Function.Injective
    (fun i => ((T57_33 i : Coordinate 1) : Coordinate 1 ⧸ reps rK57)) :=
  repsInj_of_reduceAux rK57 T57_33 (by decide)

theorem hcardT57_33 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK57 ⟨33, by decide⟩ R57 hpxR57 hcardq57 (by decide)).symm

/-- **Cell (57, 33).** -/
theorem cell57_33 (e : List (ZMod 25)) (heK : charOK (basisAt rK57) e = true)
    (h : ↥(reps (⟨33, by decide⟩ : Fin 148))) :
    species (reps (⟨33, by decide⟩ : Fin 148)) h (basisElt (reps rK57) (charOfVec rK57 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK57 e (h : Coordinate 1) T57_33 i :=
  species_entry_eq_sum rK57 ⟨33, by decide⟩ e heK h T57_33 hfix57_33 hinj57_33 hcardT57_33
    (fun i => conj_mem_of_fixedPoints (reps ⟨33, by decide⟩) (reps rK57) (T57_33 i) (hfix57_33 i) h)

/-! ## Cell (57, 38): |T| = 5 -/

def T57_38list : List Coordinates := [(4,0,0,2,0), (4,0,0,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0)]
def T57_38 : Fin 5 → Coordinate 1 := fun i => T57_38list.getD i.val (0,0,0,0,0)

theorem hfix57_38 : ∀ i, ((T57_38 i : Coordinate 1) : Coordinate 1 ⧸ reps rK57)
    ∈ fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57) :=
  repsFix_of_siftB rK57 ⟨38, by decide⟩ T57_38 (by decide)

theorem hinj57_38 : Function.Injective
    (fun i => ((T57_38 i : Coordinate 1) : Coordinate 1 ⧸ reps rK57)) :=
  repsInj_of_reduceAux rK57 T57_38 (by decide)

theorem hcardT57_38 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK57 ⟨38, by decide⟩ R57 hpxR57 hcardq57 (by decide)).symm

/-- **Cell (57, 38).** -/
theorem cell57_38 (e : List (ZMod 25)) (heK : charOK (basisAt rK57) e = true)
    (h : ↥(reps (⟨38, by decide⟩ : Fin 148))) :
    species (reps (⟨38, by decide⟩ : Fin 148)) h (basisElt (reps rK57) (charOfVec rK57 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK57 e (h : Coordinate 1) T57_38 i :=
  species_entry_eq_sum rK57 ⟨38, by decide⟩ e heK h T57_38 hfix57_38 hinj57_38 hcardT57_38
    (fun i => conj_mem_of_fixedPoints (reps ⟨38, by decide⟩) (reps rK57) (T57_38 i) (hfix57_38 i) h)

/-! ## Cell (57, 43): |T| = 5 -/

def T57_43list : List Coordinates := [(3,0,0,2,0), (3,0,0,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0)]
def T57_43 : Fin 5 → Coordinate 1 := fun i => T57_43list.getD i.val (0,0,0,0,0)

theorem hfix57_43 : ∀ i, ((T57_43 i : Coordinate 1) : Coordinate 1 ⧸ reps rK57)
    ∈ fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57) :=
  repsFix_of_siftB rK57 ⟨43, by decide⟩ T57_43 (by decide)

theorem hinj57_43 : Function.Injective
    (fun i => ((T57_43 i : Coordinate 1) : Coordinate 1 ⧸ reps rK57)) :=
  repsInj_of_reduceAux rK57 T57_43 (by decide)

theorem hcardT57_43 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK57 ⟨43, by decide⟩ R57 hpxR57 hcardq57 (by decide)).symm

/-- **Cell (57, 43).** -/
theorem cell57_43 (e : List (ZMod 25)) (heK : charOK (basisAt rK57) e = true)
    (h : ↥(reps (⟨43, by decide⟩ : Fin 148))) :
    species (reps (⟨43, by decide⟩ : Fin 148)) h (basisElt (reps rK57) (charOfVec rK57 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK57 e (h : Coordinate 1) T57_43 i :=
  species_entry_eq_sum rK57 ⟨43, by decide⟩ e heK h T57_43 hfix57_43 hinj57_43 hcardT57_43
    (fun i => conj_mem_of_fixedPoints (reps ⟨43, by decide⟩) (reps rK57) (T57_43 i) (hfix57_43 i) h)

/-! ## Cell (57, 48): |T| = 5 -/

def T57_48list : List Coordinates := [(0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0)]
def T57_48 : Fin 5 → Coordinate 1 := fun i => T57_48list.getD i.val (0,0,0,0,0)

theorem hfix57_48 : ∀ i, ((T57_48 i : Coordinate 1) : Coordinate 1 ⧸ reps rK57)
    ∈ fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57) :=
  repsFix_of_siftB rK57 ⟨48, by decide⟩ T57_48 (by decide)

theorem hinj57_48 : Function.Injective
    (fun i => ((T57_48 i : Coordinate 1) : Coordinate 1 ⧸ reps rK57)) :=
  repsInj_of_reduceAux rK57 T57_48 (by decide)

theorem hcardT57_48 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK57 ⟨48, by decide⟩ R57 hpxR57 hcardq57 (by decide)).symm

/-- **Cell (57, 48).** -/
theorem cell57_48 (e : List (ZMod 25)) (heK : charOK (basisAt rK57) e = true)
    (h : ↥(reps (⟨48, by decide⟩ : Fin 148))) :
    species (reps (⟨48, by decide⟩ : Fin 148)) h (basisElt (reps rK57) (charOfVec rK57 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK57 e (h : Coordinate 1) T57_48 i :=
  species_entry_eq_sum rK57 ⟨48, by decide⟩ e heK h T57_48 hfix57_48 hinj57_48 hcardT57_48
    (fun i => conj_mem_of_fixedPoints (reps ⟨48, by decide⟩) (reps rK57) (T57_48 i) (hfix57_48 i) h)

/-! ## Cell (57, 57): |T| = 5 -/

def T57_57list : List Coordinates := [(0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0)]
def T57_57 : Fin 5 → Coordinate 1 := fun i => T57_57list.getD i.val (0,0,0,0,0)

theorem hfix57_57 : ∀ i, ((T57_57 i : Coordinate 1) : Coordinate 1 ⧸ reps rK57)
    ∈ fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57) :=
  repsFix_of_siftB rK57 ⟨57, by decide⟩ T57_57 (by decide)

theorem hinj57_57 : Function.Injective
    (fun i => ((T57_57 i : Coordinate 1) : Coordinate 1 ⧸ reps rK57)) :=
  repsInj_of_reduceAux rK57 T57_57 (by decide)

theorem hcardT57_57 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK57 ⟨57, by decide⟩ R57 hpxR57 hcardq57 (by decide)).symm

/-- **Cell (57, 57).** -/
theorem cell57_57 (e : List (ZMod 25)) (heK : charOK (basisAt rK57) e = true)
    (h : ↥(reps (⟨57, by decide⟩ : Fin 148))) :
    species (reps (⟨57, by decide⟩ : Fin 148)) h (basisElt (reps rK57) (charOfVec rK57 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK57 e (h : Coordinate 1) T57_57 i :=
  species_entry_eq_sum rK57 ⟨57, by decide⟩ e heK h T57_57 hfix57_57 hinj57_57 hcardT57_57
    (fun i => conj_mem_of_fixedPoints (reps ⟨57, by decide⟩) (reps rK57) (T57_57 i) (hfix57_57 i) h)

namespace Q2

def R57_2 : Fin 25 → Coordinate 2 := fun i => R57list.getD i.val (0,0,0,0,0)
theorem hpxR57_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK57) (R57_2 i)) := by decide
theorem hcardq57_2 : Nat.card (Coordinate 2 ⧸ reps rK57) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (57, 0) twin -/

def T57_0_2 : Fin 25 → Coordinate 2 := fun i => T57_0list.getD i.val (0,0,0,0,0)

theorem hfix57_0_2 : ∀ i, ((T57_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK57)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK57) :=
  repsFix_of_siftB2 rK57 ⟨0, by decide⟩ T57_0_2 (by decide)

theorem hinj57_0_2 : Function.Injective
    (fun i => ((T57_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK57)) :=
  repsInj_of_reduceAux2 rK57 T57_0_2 (by decide)

theorem hcardT57_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK57)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK57 ⟨0, by decide⟩ R57_2 hpxR57_2 hcardq57_2 (by decide)).symm

/-- **Cell (57, 0) twin (q=2).** -/
theorem cell57_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK57) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK57) (charOfVec2 rK57 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK57 e (h : Coordinate 2) T57_0_2 i :=
  species_entry_eq_sum rK57 ⟨0, by decide⟩ e heK h T57_0_2 hfix57_0_2 hinj57_0_2 hcardT57_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK57) (T57_0_2 i) (hfix57_0_2 i) h)

/-! ### Cell (57, 7) twin -/

def T57_7_2 : Fin 25 → Coordinate 2 := fun i => T57_7list.getD i.val (0,0,0,0,0)

theorem hfix57_7_2 : ∀ i, ((T57_7_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK57)
    ∈ fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK57) :=
  repsFix_of_siftB2 rK57 ⟨7, by decide⟩ T57_7_2 (by decide)

theorem hinj57_7_2 : Function.Injective
    (fun i => ((T57_7_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK57)) :=
  repsInj_of_reduceAux2 rK57 T57_7_2 (by decide)

theorem hcardT57_7_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK57)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK57 ⟨7, by decide⟩ R57_2 hpxR57_2 hcardq57_2 (by decide)).symm

/-- **Cell (57, 7) twin (q=2).** -/
theorem cell57_7_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK57) e = true)
    (h : ↥(reps (⟨7, by decide⟩ : Fin 148))) :
    species (reps (⟨7, by decide⟩ : Fin 148)) h (basisElt (reps rK57) (charOfVec2 rK57 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK57 e (h : Coordinate 2) T57_7_2 i :=
  species_entry_eq_sum rK57 ⟨7, by decide⟩ e heK h T57_7_2 hfix57_7_2 hinj57_7_2 hcardT57_7_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨7, by decide⟩) (reps rK57) (T57_7_2 i) (hfix57_7_2 i) h)

/-! ### Cell (57, 12) twin -/

def T57_12_2 : Fin 25 → Coordinate 2 := fun i => T57_12list.getD i.val (0,0,0,0,0)

theorem hfix57_12_2 : ∀ i, ((T57_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK57)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK57) :=
  repsFix_of_siftB2 rK57 ⟨12, by decide⟩ T57_12_2 (by decide)

theorem hinj57_12_2 : Function.Injective
    (fun i => ((T57_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK57)) :=
  repsInj_of_reduceAux2 rK57 T57_12_2 (by decide)

theorem hcardT57_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK57)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK57 ⟨12, by decide⟩ R57_2 hpxR57_2 hcardq57_2 (by decide)).symm

/-- **Cell (57, 12) twin (q=2).** -/
theorem cell57_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK57) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK57) (charOfVec2 rK57 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK57 e (h : Coordinate 2) T57_12_2 i :=
  species_entry_eq_sum rK57 ⟨12, by decide⟩ e heK h T57_12_2 hfix57_12_2 hinj57_12_2 hcardT57_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK57) (T57_12_2 i) (hfix57_12_2 i) h)

/-! ### Cell (57, 25) twin -/

def T57_25_2 : Fin 25 → Coordinate 2 := fun i => T57_25list.getD i.val (0,0,0,0,0)

theorem hfix57_25_2 : ∀ i, ((T57_25_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK57)
    ∈ fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK57) :=
  repsFix_of_siftB2 rK57 ⟨25, by decide⟩ T57_25_2 (by decide)

theorem hinj57_25_2 : Function.Injective
    (fun i => ((T57_25_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK57)) :=
  repsInj_of_reduceAux2 rK57 T57_25_2 (by decide)

theorem hcardT57_25_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK57)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK57 ⟨25, by decide⟩ R57_2 hpxR57_2 hcardq57_2 (by decide)).symm

/-- **Cell (57, 25) twin (q=2).** -/
theorem cell57_25_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK57) e = true)
    (h : ↥(reps (⟨25, by decide⟩ : Fin 148))) :
    species (reps (⟨25, by decide⟩ : Fin 148)) h (basisElt (reps rK57) (charOfVec2 rK57 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK57 e (h : Coordinate 2) T57_25_2 i :=
  species_entry_eq_sum rK57 ⟨25, by decide⟩ e heK h T57_25_2 hfix57_25_2 hinj57_25_2 hcardT57_25_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨25, by decide⟩) (reps rK57) (T57_25_2 i) (hfix57_25_2 i) h)

/-! ### Cell (57, 28) twin -/

def T57_28_2 : Fin 5 → Coordinate 2 := fun i => T57_28list.getD i.val (0,0,0,0,0)

theorem hfix57_28_2 : ∀ i, ((T57_28_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK57)
    ∈ fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK57) :=
  repsFix_of_siftB2 rK57 ⟨28, by decide⟩ T57_28_2 (by decide)

theorem hinj57_28_2 : Function.Injective
    (fun i => ((T57_28_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK57)) :=
  repsInj_of_reduceAux2 rK57 T57_28_2 (by decide)

theorem hcardT57_28_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK57)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK57 ⟨28, by decide⟩ R57_2 hpxR57_2 hcardq57_2 (by decide)).symm

/-- **Cell (57, 28) twin (q=2).** -/
theorem cell57_28_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK57) e = true)
    (h : ↥(reps (⟨28, by decide⟩ : Fin 148))) :
    species (reps (⟨28, by decide⟩ : Fin 148)) h (basisElt (reps rK57) (charOfVec2 rK57 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK57 e (h : Coordinate 2) T57_28_2 i :=
  species_entry_eq_sum rK57 ⟨28, by decide⟩ e heK h T57_28_2 hfix57_28_2 hinj57_28_2 hcardT57_28_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨28, by decide⟩) (reps rK57) (T57_28_2 i) (hfix57_28_2 i) h)

/-! ### Cell (57, 33) twin -/

def T57_33_2 : Fin 5 → Coordinate 2 := fun i => T57_33list.getD i.val (0,0,0,0,0)

theorem hfix57_33_2 : ∀ i, ((T57_33_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK57)
    ∈ fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK57) :=
  repsFix_of_siftB2 rK57 ⟨33, by decide⟩ T57_33_2 (by decide)

theorem hinj57_33_2 : Function.Injective
    (fun i => ((T57_33_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK57)) :=
  repsInj_of_reduceAux2 rK57 T57_33_2 (by decide)

theorem hcardT57_33_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK57)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK57 ⟨33, by decide⟩ R57_2 hpxR57_2 hcardq57_2 (by decide)).symm

/-- **Cell (57, 33) twin (q=2).** -/
theorem cell57_33_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK57) e = true)
    (h : ↥(reps (⟨33, by decide⟩ : Fin 148))) :
    species (reps (⟨33, by decide⟩ : Fin 148)) h (basisElt (reps rK57) (charOfVec2 rK57 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK57 e (h : Coordinate 2) T57_33_2 i :=
  species_entry_eq_sum rK57 ⟨33, by decide⟩ e heK h T57_33_2 hfix57_33_2 hinj57_33_2 hcardT57_33_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨33, by decide⟩) (reps rK57) (T57_33_2 i) (hfix57_33_2 i) h)

/-! ### Cell (57, 38) twin -/

def T57_38_2 : Fin 5 → Coordinate 2 := fun i => T57_38list.getD i.val (0,0,0,0,0)

theorem hfix57_38_2 : ∀ i, ((T57_38_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK57)
    ∈ fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK57) :=
  repsFix_of_siftB2 rK57 ⟨38, by decide⟩ T57_38_2 (by decide)

theorem hinj57_38_2 : Function.Injective
    (fun i => ((T57_38_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK57)) :=
  repsInj_of_reduceAux2 rK57 T57_38_2 (by decide)

theorem hcardT57_38_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK57)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK57 ⟨38, by decide⟩ R57_2 hpxR57_2 hcardq57_2 (by decide)).symm

/-- **Cell (57, 38) twin (q=2).** -/
theorem cell57_38_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK57) e = true)
    (h : ↥(reps (⟨38, by decide⟩ : Fin 148))) :
    species (reps (⟨38, by decide⟩ : Fin 148)) h (basisElt (reps rK57) (charOfVec2 rK57 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK57 e (h : Coordinate 2) T57_38_2 i :=
  species_entry_eq_sum rK57 ⟨38, by decide⟩ e heK h T57_38_2 hfix57_38_2 hinj57_38_2 hcardT57_38_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨38, by decide⟩) (reps rK57) (T57_38_2 i) (hfix57_38_2 i) h)

/-! ### Cell (57, 43) twin -/

def T57_43_2 : Fin 5 → Coordinate 2 := fun i => T57_43list.getD i.val (0,0,0,0,0)

theorem hfix57_43_2 : ∀ i, ((T57_43_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK57)
    ∈ fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK57) :=
  repsFix_of_siftB2 rK57 ⟨43, by decide⟩ T57_43_2 (by decide)

theorem hinj57_43_2 : Function.Injective
    (fun i => ((T57_43_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK57)) :=
  repsInj_of_reduceAux2 rK57 T57_43_2 (by decide)

theorem hcardT57_43_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK57)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK57 ⟨43, by decide⟩ R57_2 hpxR57_2 hcardq57_2 (by decide)).symm

/-- **Cell (57, 43) twin (q=2).** -/
theorem cell57_43_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK57) e = true)
    (h : ↥(reps (⟨43, by decide⟩ : Fin 148))) :
    species (reps (⟨43, by decide⟩ : Fin 148)) h (basisElt (reps rK57) (charOfVec2 rK57 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK57 e (h : Coordinate 2) T57_43_2 i :=
  species_entry_eq_sum rK57 ⟨43, by decide⟩ e heK h T57_43_2 hfix57_43_2 hinj57_43_2 hcardT57_43_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨43, by decide⟩) (reps rK57) (T57_43_2 i) (hfix57_43_2 i) h)

/-! ### Cell (57, 48) twin -/

def T57_48_2 : Fin 5 → Coordinate 2 := fun i => T57_48list.getD i.val (0,0,0,0,0)

theorem hfix57_48_2 : ∀ i, ((T57_48_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK57)
    ∈ fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK57) :=
  repsFix_of_siftB2 rK57 ⟨48, by decide⟩ T57_48_2 (by decide)

theorem hinj57_48_2 : Function.Injective
    (fun i => ((T57_48_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK57)) :=
  repsInj_of_reduceAux2 rK57 T57_48_2 (by decide)

theorem hcardT57_48_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK57)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK57 ⟨48, by decide⟩ R57_2 hpxR57_2 hcardq57_2 (by decide)).symm

/-- **Cell (57, 48) twin (q=2).** -/
theorem cell57_48_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK57) e = true)
    (h : ↥(reps (⟨48, by decide⟩ : Fin 148))) :
    species (reps (⟨48, by decide⟩ : Fin 148)) h (basisElt (reps rK57) (charOfVec2 rK57 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK57 e (h : Coordinate 2) T57_48_2 i :=
  species_entry_eq_sum rK57 ⟨48, by decide⟩ e heK h T57_48_2 hfix57_48_2 hinj57_48_2 hcardT57_48_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨48, by decide⟩) (reps rK57) (T57_48_2 i) (hfix57_48_2 i) h)

/-! ### Cell (57, 57) twin -/

def T57_57_2 : Fin 5 → Coordinate 2 := fun i => T57_57list.getD i.val (0,0,0,0,0)

theorem hfix57_57_2 : ∀ i, ((T57_57_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK57)
    ∈ fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK57) :=
  repsFix_of_siftB2 rK57 ⟨57, by decide⟩ T57_57_2 (by decide)

theorem hinj57_57_2 : Function.Injective
    (fun i => ((T57_57_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK57)) :=
  repsInj_of_reduceAux2 rK57 T57_57_2 (by decide)

theorem hcardT57_57_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK57)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK57 ⟨57, by decide⟩ R57_2 hpxR57_2 hcardq57_2 (by decide)).symm

/-- **Cell (57, 57) twin (q=2).** -/
theorem cell57_57_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK57) e = true)
    (h : ↥(reps (⟨57, by decide⟩ : Fin 148))) :
    species (reps (⟨57, by decide⟩ : Fin 148)) h (basisElt (reps rK57) (charOfVec2 rK57 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK57 e (h : Coordinate 2) T57_57_2 i :=
  species_entry_eq_sum rK57 ⟨57, by decide⟩ e heK h T57_57_2 hfix57_57_2 hinj57_57_2 hcardT57_57_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨57, by decide⟩) (reps rK57) (T57_57_2 i) (hfix57_57_2 i) h)

end Q2

/-! # K-class rK = 58  (|G/K| = 25) -/

def rK58 : Fin 148 := ⟨58, by decide⟩

def R58list : List Coordinates := [(0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,0,0,4,0), (1,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,0,0,4,0), (2,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,0,0,4,0), (3,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,0,0,4,0), (4,0,0,0,0)]
def R58 : Fin 25 → Coordinate 1 := fun i => R58list.getD i.val (0,0,0,0,0)

theorem hpxR58 : Function.Injective (fun i => reduceAux 1 (basisAt rK58) (R58 i)) := by decide
theorem hcardq58 : Nat.card (Coordinate 1 ⧸ reps rK58) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (58, 0): |T| = 25 -/

def T58_0list : List Coordinates := [(0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,0,0,4,0), (1,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,0,0,4,0), (2,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,0,0,4,0), (3,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,0,0,4,0), (4,0,0,0,0)]
def T58_0 : Fin 25 → Coordinate 1 := fun i => T58_0list.getD i.val (0,0,0,0,0)

theorem hfix58_0 : ∀ i, ((T58_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK58)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58) :=
  repsFix_of_siftB rK58 ⟨0, by decide⟩ T58_0 (by decide)

theorem hinj58_0 : Function.Injective
    (fun i => ((T58_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK58)) :=
  repsInj_of_reduceAux rK58 T58_0 (by decide)

theorem hcardT58_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK58 ⟨0, by decide⟩ R58 hpxR58 hcardq58 (by decide)).symm

/-- **Cell (58, 0).** -/
theorem cell58_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK58) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK58) (charOfVec rK58 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK58 e (h : Coordinate 1) T58_0 i :=
  species_entry_eq_sum rK58 ⟨0, by decide⟩ e heK h T58_0 hfix58_0 hinj58_0 hcardT58_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK58) (T58_0 i) (hfix58_0 i) h)

/-! ## Cell (58, 6): |T| = 25 -/

def T58_6list : List Coordinates := [(0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,0,0,4,0), (1,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,0,0,4,0), (2,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,0,0,4,0), (3,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,0,0,4,0), (4,0,0,0,0)]
def T58_6 : Fin 25 → Coordinate 1 := fun i => T58_6list.getD i.val (0,0,0,0,0)

theorem hfix58_6 : ∀ i, ((T58_6 i : Coordinate 1) : Coordinate 1 ⧸ reps rK58)
    ∈ fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58) :=
  repsFix_of_siftB rK58 ⟨6, by decide⟩ T58_6 (by decide)

theorem hinj58_6 : Function.Injective
    (fun i => ((T58_6 i : Coordinate 1) : Coordinate 1 ⧸ reps rK58)) :=
  repsInj_of_reduceAux rK58 T58_6 (by decide)

theorem hcardT58_6 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK58 ⟨6, by decide⟩ R58 hpxR58 hcardq58 (by decide)).symm

/-- **Cell (58, 6).** -/
theorem cell58_6 (e : List (ZMod 25)) (heK : charOK (basisAt rK58) e = true)
    (h : ↥(reps (⟨6, by decide⟩ : Fin 148))) :
    species (reps (⟨6, by decide⟩ : Fin 148)) h (basisElt (reps rK58) (charOfVec rK58 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK58 e (h : Coordinate 1) T58_6 i :=
  species_entry_eq_sum rK58 ⟨6, by decide⟩ e heK h T58_6 hfix58_6 hinj58_6 hcardT58_6
    (fun i => conj_mem_of_fixedPoints (reps ⟨6, by decide⟩) (reps rK58) (T58_6 i) (hfix58_6 i) h)

/-! ## Cell (58, 12): |T| = 25 -/

def T58_12list : List Coordinates := [(0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,0,0,4,0), (1,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,0,0,4,0), (2,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,0,0,4,0), (3,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,0,0,4,0), (4,0,0,0,0)]
def T58_12 : Fin 25 → Coordinate 1 := fun i => T58_12list.getD i.val (0,0,0,0,0)

theorem hfix58_12 : ∀ i, ((T58_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK58)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58) :=
  repsFix_of_siftB rK58 ⟨12, by decide⟩ T58_12 (by decide)

theorem hinj58_12 : Function.Injective
    (fun i => ((T58_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK58)) :=
  repsInj_of_reduceAux rK58 T58_12 (by decide)

theorem hcardT58_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK58 ⟨12, by decide⟩ R58 hpxR58 hcardq58 (by decide)).symm

/-- **Cell (58, 12).** -/
theorem cell58_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK58) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK58) (charOfVec rK58 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK58 e (h : Coordinate 1) T58_12 i :=
  species_entry_eq_sum rK58 ⟨12, by decide⟩ e heK h T58_12 hfix58_12 hinj58_12 hcardT58_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK58) (T58_12 i) (hfix58_12 i) h)

/-! ## Cell (58, 24): |T| = 25 -/

def T58_24list : List Coordinates := [(0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,0,0,4,0), (1,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,0,0,4,0), (2,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,0,0,4,0), (3,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,0,0,4,0), (4,0,0,0,0)]
def T58_24 : Fin 25 → Coordinate 1 := fun i => T58_24list.getD i.val (0,0,0,0,0)

theorem hfix58_24 : ∀ i, ((T58_24 i : Coordinate 1) : Coordinate 1 ⧸ reps rK58)
    ∈ fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58) :=
  repsFix_of_siftB rK58 ⟨24, by decide⟩ T58_24 (by decide)

theorem hinj58_24 : Function.Injective
    (fun i => ((T58_24 i : Coordinate 1) : Coordinate 1 ⧸ reps rK58)) :=
  repsInj_of_reduceAux rK58 T58_24 (by decide)

theorem hcardT58_24 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK58 ⟨24, by decide⟩ R58 hpxR58 hcardq58 (by decide)).symm

/-- **Cell (58, 24).** -/
theorem cell58_24 (e : List (ZMod 25)) (heK : charOK (basisAt rK58) e = true)
    (h : ↥(reps (⟨24, by decide⟩ : Fin 148))) :
    species (reps (⟨24, by decide⟩ : Fin 148)) h (basisElt (reps rK58) (charOfVec rK58 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK58 e (h : Coordinate 1) T58_24 i :=
  species_entry_eq_sum rK58 ⟨24, by decide⟩ e heK h T58_24 hfix58_24 hinj58_24 hcardT58_24
    (fun i => conj_mem_of_fixedPoints (reps ⟨24, by decide⟩) (reps rK58) (T58_24 i) (hfix58_24 i) h)

/-! ## Cell (58, 28): |T| = 5 -/

def T58_28list : List Coordinates := [(3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,0,0,4,0), (3,0,0,0,0)]
def T58_28 : Fin 5 → Coordinate 1 := fun i => T58_28list.getD i.val (0,0,0,0,0)

theorem hfix58_28 : ∀ i, ((T58_28 i : Coordinate 1) : Coordinate 1 ⧸ reps rK58)
    ∈ fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58) :=
  repsFix_of_siftB rK58 ⟨28, by decide⟩ T58_28 (by decide)

theorem hinj58_28 : Function.Injective
    (fun i => ((T58_28 i : Coordinate 1) : Coordinate 1 ⧸ reps rK58)) :=
  repsInj_of_reduceAux rK58 T58_28 (by decide)

theorem hcardT58_28 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK58 ⟨28, by decide⟩ R58 hpxR58 hcardq58 (by decide)).symm

/-- **Cell (58, 28).** -/
theorem cell58_28 (e : List (ZMod 25)) (heK : charOK (basisAt rK58) e = true)
    (h : ↥(reps (⟨28, by decide⟩ : Fin 148))) :
    species (reps (⟨28, by decide⟩ : Fin 148)) h (basisElt (reps rK58) (charOfVec rK58 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK58 e (h : Coordinate 1) T58_28 i :=
  species_entry_eq_sum rK58 ⟨28, by decide⟩ e heK h T58_28 hfix58_28 hinj58_28 hcardT58_28
    (fun i => conj_mem_of_fixedPoints (reps ⟨28, by decide⟩) (reps rK58) (T58_28 i) (hfix58_28 i) h)

/-! ## Cell (58, 33): |T| = 5 -/

def T58_33list : List Coordinates := [(4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,0,0,4,0), (4,0,0,0,0)]
def T58_33 : Fin 5 → Coordinate 1 := fun i => T58_33list.getD i.val (0,0,0,0,0)

theorem hfix58_33 : ∀ i, ((T58_33 i : Coordinate 1) : Coordinate 1 ⧸ reps rK58)
    ∈ fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58) :=
  repsFix_of_siftB rK58 ⟨33, by decide⟩ T58_33 (by decide)

theorem hinj58_33 : Function.Injective
    (fun i => ((T58_33 i : Coordinate 1) : Coordinate 1 ⧸ reps rK58)) :=
  repsInj_of_reduceAux rK58 T58_33 (by decide)

theorem hcardT58_33 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK58 ⟨33, by decide⟩ R58 hpxR58 hcardq58 (by decide)).symm

/-- **Cell (58, 33).** -/
theorem cell58_33 (e : List (ZMod 25)) (heK : charOK (basisAt rK58) e = true)
    (h : ↥(reps (⟨33, by decide⟩ : Fin 148))) :
    species (reps (⟨33, by decide⟩ : Fin 148)) h (basisElt (reps rK58) (charOfVec rK58 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK58 e (h : Coordinate 1) T58_33 i :=
  species_entry_eq_sum rK58 ⟨33, by decide⟩ e heK h T58_33 hfix58_33 hinj58_33 hcardT58_33
    (fun i => conj_mem_of_fixedPoints (reps ⟨33, by decide⟩) (reps rK58) (T58_33 i) (hfix58_33 i) h)

/-! ## Cell (58, 38): |T| = 5 -/

def T58_38list : List Coordinates := [(1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,0,0,4,0), (1,0,0,0,0)]
def T58_38 : Fin 5 → Coordinate 1 := fun i => T58_38list.getD i.val (0,0,0,0,0)

theorem hfix58_38 : ∀ i, ((T58_38 i : Coordinate 1) : Coordinate 1 ⧸ reps rK58)
    ∈ fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58) :=
  repsFix_of_siftB rK58 ⟨38, by decide⟩ T58_38 (by decide)

theorem hinj58_38 : Function.Injective
    (fun i => ((T58_38 i : Coordinate 1) : Coordinate 1 ⧸ reps rK58)) :=
  repsInj_of_reduceAux rK58 T58_38 (by decide)

theorem hcardT58_38 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK58 ⟨38, by decide⟩ R58 hpxR58 hcardq58 (by decide)).symm

/-- **Cell (58, 38).** -/
theorem cell58_38 (e : List (ZMod 25)) (heK : charOK (basisAt rK58) e = true)
    (h : ↥(reps (⟨38, by decide⟩ : Fin 148))) :
    species (reps (⟨38, by decide⟩ : Fin 148)) h (basisElt (reps rK58) (charOfVec rK58 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK58 e (h : Coordinate 1) T58_38 i :=
  species_entry_eq_sum rK58 ⟨38, by decide⟩ e heK h T58_38 hfix58_38 hinj58_38 hcardT58_38
    (fun i => conj_mem_of_fixedPoints (reps ⟨38, by decide⟩) (reps rK58) (T58_38 i) (hfix58_38 i) h)

/-! ## Cell (58, 43): |T| = 5 -/

def T58_43list : List Coordinates := [(2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,0,0,4,0), (2,0,0,0,0)]
def T58_43 : Fin 5 → Coordinate 1 := fun i => T58_43list.getD i.val (0,0,0,0,0)

theorem hfix58_43 : ∀ i, ((T58_43 i : Coordinate 1) : Coordinate 1 ⧸ reps rK58)
    ∈ fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58) :=
  repsFix_of_siftB rK58 ⟨43, by decide⟩ T58_43 (by decide)

theorem hinj58_43 : Function.Injective
    (fun i => ((T58_43 i : Coordinate 1) : Coordinate 1 ⧸ reps rK58)) :=
  repsInj_of_reduceAux rK58 T58_43 (by decide)

theorem hcardT58_43 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK58 ⟨43, by decide⟩ R58 hpxR58 hcardq58 (by decide)).symm

/-- **Cell (58, 43).** -/
theorem cell58_43 (e : List (ZMod 25)) (heK : charOK (basisAt rK58) e = true)
    (h : ↥(reps (⟨43, by decide⟩ : Fin 148))) :
    species (reps (⟨43, by decide⟩ : Fin 148)) h (basisElt (reps rK58) (charOfVec rK58 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK58 e (h : Coordinate 1) T58_43 i :=
  species_entry_eq_sum rK58 ⟨43, by decide⟩ e heK h T58_43 hfix58_43 hinj58_43 hcardT58_43
    (fun i => conj_mem_of_fixedPoints (reps ⟨43, by decide⟩) (reps rK58) (T58_43 i) (hfix58_43 i) h)

/-! ## Cell (58, 48): |T| = 5 -/

def T58_48list : List Coordinates := [(0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0)]
def T58_48 : Fin 5 → Coordinate 1 := fun i => T58_48list.getD i.val (0,0,0,0,0)

theorem hfix58_48 : ∀ i, ((T58_48 i : Coordinate 1) : Coordinate 1 ⧸ reps rK58)
    ∈ fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58) :=
  repsFix_of_siftB rK58 ⟨48, by decide⟩ T58_48 (by decide)

theorem hinj58_48 : Function.Injective
    (fun i => ((T58_48 i : Coordinate 1) : Coordinate 1 ⧸ reps rK58)) :=
  repsInj_of_reduceAux rK58 T58_48 (by decide)

theorem hcardT58_48 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK58 ⟨48, by decide⟩ R58 hpxR58 hcardq58 (by decide)).symm

/-- **Cell (58, 48).** -/
theorem cell58_48 (e : List (ZMod 25)) (heK : charOK (basisAt rK58) e = true)
    (h : ↥(reps (⟨48, by decide⟩ : Fin 148))) :
    species (reps (⟨48, by decide⟩ : Fin 148)) h (basisElt (reps rK58) (charOfVec rK58 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK58 e (h : Coordinate 1) T58_48 i :=
  species_entry_eq_sum rK58 ⟨48, by decide⟩ e heK h T58_48 hfix58_48 hinj58_48 hcardT58_48
    (fun i => conj_mem_of_fixedPoints (reps ⟨48, by decide⟩) (reps rK58) (T58_48 i) (hfix58_48 i) h)

/-! ## Cell (58, 58): |T| = 5 -/

def T58_58list : List Coordinates := [(0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0)]
def T58_58 : Fin 5 → Coordinate 1 := fun i => T58_58list.getD i.val (0,0,0,0,0)

theorem hfix58_58 : ∀ i, ((T58_58 i : Coordinate 1) : Coordinate 1 ⧸ reps rK58)
    ∈ fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58) :=
  repsFix_of_siftB rK58 ⟨58, by decide⟩ T58_58 (by decide)

theorem hinj58_58 : Function.Injective
    (fun i => ((T58_58 i : Coordinate 1) : Coordinate 1 ⧸ reps rK58)) :=
  repsInj_of_reduceAux rK58 T58_58 (by decide)

theorem hcardT58_58 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK58 ⟨58, by decide⟩ R58 hpxR58 hcardq58 (by decide)).symm

/-- **Cell (58, 58).** -/
theorem cell58_58 (e : List (ZMod 25)) (heK : charOK (basisAt rK58) e = true)
    (h : ↥(reps (⟨58, by decide⟩ : Fin 148))) :
    species (reps (⟨58, by decide⟩ : Fin 148)) h (basisElt (reps rK58) (charOfVec rK58 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK58 e (h : Coordinate 1) T58_58 i :=
  species_entry_eq_sum rK58 ⟨58, by decide⟩ e heK h T58_58 hfix58_58 hinj58_58 hcardT58_58
    (fun i => conj_mem_of_fixedPoints (reps ⟨58, by decide⟩) (reps rK58) (T58_58 i) (hfix58_58 i) h)

namespace Q2

def R58_2 : Fin 25 → Coordinate 2 := fun i => R58list.getD i.val (0,0,0,0,0)
theorem hpxR58_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK58) (R58_2 i)) := by decide
theorem hcardq58_2 : Nat.card (Coordinate 2 ⧸ reps rK58) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (58, 0) twin -/

def T58_0_2 : Fin 25 → Coordinate 2 := fun i => T58_0list.getD i.val (0,0,0,0,0)

theorem hfix58_0_2 : ∀ i, ((T58_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK58)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK58) :=
  repsFix_of_siftB2 rK58 ⟨0, by decide⟩ T58_0_2 (by decide)

theorem hinj58_0_2 : Function.Injective
    (fun i => ((T58_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK58)) :=
  repsInj_of_reduceAux2 rK58 T58_0_2 (by decide)

theorem hcardT58_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK58)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK58 ⟨0, by decide⟩ R58_2 hpxR58_2 hcardq58_2 (by decide)).symm

/-- **Cell (58, 0) twin (q=2).** -/
theorem cell58_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK58) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK58) (charOfVec2 rK58 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK58 e (h : Coordinate 2) T58_0_2 i :=
  species_entry_eq_sum rK58 ⟨0, by decide⟩ e heK h T58_0_2 hfix58_0_2 hinj58_0_2 hcardT58_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK58) (T58_0_2 i) (hfix58_0_2 i) h)

/-! ### Cell (58, 6) twin -/

def T58_6_2 : Fin 25 → Coordinate 2 := fun i => T58_6list.getD i.val (0,0,0,0,0)

theorem hfix58_6_2 : ∀ i, ((T58_6_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK58)
    ∈ fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK58) :=
  repsFix_of_siftB2 rK58 ⟨6, by decide⟩ T58_6_2 (by decide)

theorem hinj58_6_2 : Function.Injective
    (fun i => ((T58_6_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK58)) :=
  repsInj_of_reduceAux2 rK58 T58_6_2 (by decide)

theorem hcardT58_6_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK58)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK58 ⟨6, by decide⟩ R58_2 hpxR58_2 hcardq58_2 (by decide)).symm

/-- **Cell (58, 6) twin (q=2).** -/
theorem cell58_6_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK58) e = true)
    (h : ↥(reps (⟨6, by decide⟩ : Fin 148))) :
    species (reps (⟨6, by decide⟩ : Fin 148)) h (basisElt (reps rK58) (charOfVec2 rK58 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK58 e (h : Coordinate 2) T58_6_2 i :=
  species_entry_eq_sum rK58 ⟨6, by decide⟩ e heK h T58_6_2 hfix58_6_2 hinj58_6_2 hcardT58_6_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨6, by decide⟩) (reps rK58) (T58_6_2 i) (hfix58_6_2 i) h)

/-! ### Cell (58, 12) twin -/

def T58_12_2 : Fin 25 → Coordinate 2 := fun i => T58_12list.getD i.val (0,0,0,0,0)

theorem hfix58_12_2 : ∀ i, ((T58_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK58)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK58) :=
  repsFix_of_siftB2 rK58 ⟨12, by decide⟩ T58_12_2 (by decide)

theorem hinj58_12_2 : Function.Injective
    (fun i => ((T58_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK58)) :=
  repsInj_of_reduceAux2 rK58 T58_12_2 (by decide)

theorem hcardT58_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK58)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK58 ⟨12, by decide⟩ R58_2 hpxR58_2 hcardq58_2 (by decide)).symm

/-- **Cell (58, 12) twin (q=2).** -/
theorem cell58_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK58) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK58) (charOfVec2 rK58 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK58 e (h : Coordinate 2) T58_12_2 i :=
  species_entry_eq_sum rK58 ⟨12, by decide⟩ e heK h T58_12_2 hfix58_12_2 hinj58_12_2 hcardT58_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK58) (T58_12_2 i) (hfix58_12_2 i) h)

/-! ### Cell (58, 24) twin -/

def T58_24_2 : Fin 25 → Coordinate 2 := fun i => T58_24list.getD i.val (0,0,0,0,0)

theorem hfix58_24_2 : ∀ i, ((T58_24_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK58)
    ∈ fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK58) :=
  repsFix_of_siftB2 rK58 ⟨24, by decide⟩ T58_24_2 (by decide)

theorem hinj58_24_2 : Function.Injective
    (fun i => ((T58_24_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK58)) :=
  repsInj_of_reduceAux2 rK58 T58_24_2 (by decide)

theorem hcardT58_24_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK58)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK58 ⟨24, by decide⟩ R58_2 hpxR58_2 hcardq58_2 (by decide)).symm

/-- **Cell (58, 24) twin (q=2).** -/
theorem cell58_24_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK58) e = true)
    (h : ↥(reps (⟨24, by decide⟩ : Fin 148))) :
    species (reps (⟨24, by decide⟩ : Fin 148)) h (basisElt (reps rK58) (charOfVec2 rK58 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK58 e (h : Coordinate 2) T58_24_2 i :=
  species_entry_eq_sum rK58 ⟨24, by decide⟩ e heK h T58_24_2 hfix58_24_2 hinj58_24_2 hcardT58_24_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨24, by decide⟩) (reps rK58) (T58_24_2 i) (hfix58_24_2 i) h)

/-! ### Cell (58, 28) twin -/

def T58_28_2 : Fin 5 → Coordinate 2 := fun i => T58_28list.getD i.val (0,0,0,0,0)

theorem hfix58_28_2 : ∀ i, ((T58_28_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK58)
    ∈ fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK58) :=
  repsFix_of_siftB2 rK58 ⟨28, by decide⟩ T58_28_2 (by decide)

theorem hinj58_28_2 : Function.Injective
    (fun i => ((T58_28_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK58)) :=
  repsInj_of_reduceAux2 rK58 T58_28_2 (by decide)

theorem hcardT58_28_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK58)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK58 ⟨28, by decide⟩ R58_2 hpxR58_2 hcardq58_2 (by decide)).symm

/-- **Cell (58, 28) twin (q=2).** -/
theorem cell58_28_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK58) e = true)
    (h : ↥(reps (⟨28, by decide⟩ : Fin 148))) :
    species (reps (⟨28, by decide⟩ : Fin 148)) h (basisElt (reps rK58) (charOfVec2 rK58 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK58 e (h : Coordinate 2) T58_28_2 i :=
  species_entry_eq_sum rK58 ⟨28, by decide⟩ e heK h T58_28_2 hfix58_28_2 hinj58_28_2 hcardT58_28_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨28, by decide⟩) (reps rK58) (T58_28_2 i) (hfix58_28_2 i) h)

/-! ### Cell (58, 33) twin -/

def T58_33_2 : Fin 5 → Coordinate 2 := fun i => T58_33list.getD i.val (0,0,0,0,0)

theorem hfix58_33_2 : ∀ i, ((T58_33_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK58)
    ∈ fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK58) :=
  repsFix_of_siftB2 rK58 ⟨33, by decide⟩ T58_33_2 (by decide)

theorem hinj58_33_2 : Function.Injective
    (fun i => ((T58_33_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK58)) :=
  repsInj_of_reduceAux2 rK58 T58_33_2 (by decide)

theorem hcardT58_33_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK58)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK58 ⟨33, by decide⟩ R58_2 hpxR58_2 hcardq58_2 (by decide)).symm

/-- **Cell (58, 33) twin (q=2).** -/
theorem cell58_33_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK58) e = true)
    (h : ↥(reps (⟨33, by decide⟩ : Fin 148))) :
    species (reps (⟨33, by decide⟩ : Fin 148)) h (basisElt (reps rK58) (charOfVec2 rK58 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK58 e (h : Coordinate 2) T58_33_2 i :=
  species_entry_eq_sum rK58 ⟨33, by decide⟩ e heK h T58_33_2 hfix58_33_2 hinj58_33_2 hcardT58_33_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨33, by decide⟩) (reps rK58) (T58_33_2 i) (hfix58_33_2 i) h)

/-! ### Cell (58, 38) twin -/

def T58_38_2 : Fin 5 → Coordinate 2 := fun i => T58_38list.getD i.val (0,0,0,0,0)

theorem hfix58_38_2 : ∀ i, ((T58_38_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK58)
    ∈ fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK58) :=
  repsFix_of_siftB2 rK58 ⟨38, by decide⟩ T58_38_2 (by decide)

theorem hinj58_38_2 : Function.Injective
    (fun i => ((T58_38_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK58)) :=
  repsInj_of_reduceAux2 rK58 T58_38_2 (by decide)

theorem hcardT58_38_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK58)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK58 ⟨38, by decide⟩ R58_2 hpxR58_2 hcardq58_2 (by decide)).symm

/-- **Cell (58, 38) twin (q=2).** -/
theorem cell58_38_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK58) e = true)
    (h : ↥(reps (⟨38, by decide⟩ : Fin 148))) :
    species (reps (⟨38, by decide⟩ : Fin 148)) h (basisElt (reps rK58) (charOfVec2 rK58 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK58 e (h : Coordinate 2) T58_38_2 i :=
  species_entry_eq_sum rK58 ⟨38, by decide⟩ e heK h T58_38_2 hfix58_38_2 hinj58_38_2 hcardT58_38_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨38, by decide⟩) (reps rK58) (T58_38_2 i) (hfix58_38_2 i) h)

/-! ### Cell (58, 43) twin -/

def T58_43_2 : Fin 5 → Coordinate 2 := fun i => T58_43list.getD i.val (0,0,0,0,0)

theorem hfix58_43_2 : ∀ i, ((T58_43_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK58)
    ∈ fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK58) :=
  repsFix_of_siftB2 rK58 ⟨43, by decide⟩ T58_43_2 (by decide)

theorem hinj58_43_2 : Function.Injective
    (fun i => ((T58_43_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK58)) :=
  repsInj_of_reduceAux2 rK58 T58_43_2 (by decide)

theorem hcardT58_43_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK58)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK58 ⟨43, by decide⟩ R58_2 hpxR58_2 hcardq58_2 (by decide)).symm

/-- **Cell (58, 43) twin (q=2).** -/
theorem cell58_43_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK58) e = true)
    (h : ↥(reps (⟨43, by decide⟩ : Fin 148))) :
    species (reps (⟨43, by decide⟩ : Fin 148)) h (basisElt (reps rK58) (charOfVec2 rK58 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK58 e (h : Coordinate 2) T58_43_2 i :=
  species_entry_eq_sum rK58 ⟨43, by decide⟩ e heK h T58_43_2 hfix58_43_2 hinj58_43_2 hcardT58_43_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨43, by decide⟩) (reps rK58) (T58_43_2 i) (hfix58_43_2 i) h)

/-! ### Cell (58, 48) twin -/

def T58_48_2 : Fin 5 → Coordinate 2 := fun i => T58_48list.getD i.val (0,0,0,0,0)

theorem hfix58_48_2 : ∀ i, ((T58_48_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK58)
    ∈ fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK58) :=
  repsFix_of_siftB2 rK58 ⟨48, by decide⟩ T58_48_2 (by decide)

theorem hinj58_48_2 : Function.Injective
    (fun i => ((T58_48_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK58)) :=
  repsInj_of_reduceAux2 rK58 T58_48_2 (by decide)

theorem hcardT58_48_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK58)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK58 ⟨48, by decide⟩ R58_2 hpxR58_2 hcardq58_2 (by decide)).symm

/-- **Cell (58, 48) twin (q=2).** -/
theorem cell58_48_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK58) e = true)
    (h : ↥(reps (⟨48, by decide⟩ : Fin 148))) :
    species (reps (⟨48, by decide⟩ : Fin 148)) h (basisElt (reps rK58) (charOfVec2 rK58 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK58 e (h : Coordinate 2) T58_48_2 i :=
  species_entry_eq_sum rK58 ⟨48, by decide⟩ e heK h T58_48_2 hfix58_48_2 hinj58_48_2 hcardT58_48_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨48, by decide⟩) (reps rK58) (T58_48_2 i) (hfix58_48_2 i) h)

/-! ### Cell (58, 58) twin -/

def T58_58_2 : Fin 5 → Coordinate 2 := fun i => T58_58list.getD i.val (0,0,0,0,0)

theorem hfix58_58_2 : ∀ i, ((T58_58_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK58)
    ∈ fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK58) :=
  repsFix_of_siftB2 rK58 ⟨58, by decide⟩ T58_58_2 (by decide)

theorem hinj58_58_2 : Function.Injective
    (fun i => ((T58_58_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK58)) :=
  repsInj_of_reduceAux2 rK58 T58_58_2 (by decide)

theorem hcardT58_58_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK58)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK58 ⟨58, by decide⟩ R58_2 hpxR58_2 hcardq58_2 (by decide)).symm

/-- **Cell (58, 58) twin (q=2).** -/
theorem cell58_58_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK58) e = true)
    (h : ↥(reps (⟨58, by decide⟩ : Fin 148))) :
    species (reps (⟨58, by decide⟩ : Fin 148)) h (basisElt (reps rK58) (charOfVec2 rK58 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK58 e (h : Coordinate 2) T58_58_2 i :=
  species_entry_eq_sum rK58 ⟨58, by decide⟩ e heK h T58_58_2 hfix58_58_2 hinj58_58_2 hcardT58_58_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨58, by decide⟩) (reps rK58) (T58_58_2 i) (hfix58_58_2 i) h)

end Q2

/-! # K-class rK = 59  (|G/K| = 25) -/

def rK59 : Fin 148 := ⟨59, by decide⟩

def R59list : List Coordinates := [(0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,0,0,4,0)]
def R59 : Fin 25 → Coordinate 1 := fun i => R59list.getD i.val (0,0,0,0,0)

theorem hpxR59 : Function.Injective (fun i => reduceAux 1 (basisAt rK59) (R59 i)) := by decide
theorem hcardq59 : Nat.card (Coordinate 1 ⧸ reps rK59) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (59, 0): |T| = 25 -/

def T59_0list : List Coordinates := [(0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,0,0,4,0)]
def T59_0 : Fin 25 → Coordinate 1 := fun i => T59_0list.getD i.val (0,0,0,0,0)

theorem hfix59_0 : ∀ i, ((T59_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK59)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59) :=
  repsFix_of_siftB rK59 ⟨0, by decide⟩ T59_0 (by decide)

theorem hinj59_0 : Function.Injective
    (fun i => ((T59_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK59)) :=
  repsInj_of_reduceAux rK59 T59_0 (by decide)

theorem hcardT59_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK59 ⟨0, by decide⟩ R59 hpxR59 hcardq59 (by decide)).symm

/-- **Cell (59, 0).** -/
theorem cell59_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK59) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK59) (charOfVec rK59 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK59 e (h : Coordinate 1) T59_0 i :=
  species_entry_eq_sum rK59 ⟨0, by decide⟩ e heK h T59_0 hfix59_0 hinj59_0 hcardT59_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK59) (T59_0 i) (hfix59_0 i) h)

/-! ## Cell (59, 8): |T| = 25 -/

def T59_8list : List Coordinates := [(0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,0,0,4,0)]
def T59_8 : Fin 25 → Coordinate 1 := fun i => T59_8list.getD i.val (0,0,0,0,0)

theorem hfix59_8 : ∀ i, ((T59_8 i : Coordinate 1) : Coordinate 1 ⧸ reps rK59)
    ∈ fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59) :=
  repsFix_of_siftB rK59 ⟨8, by decide⟩ T59_8 (by decide)

theorem hinj59_8 : Function.Injective
    (fun i => ((T59_8 i : Coordinate 1) : Coordinate 1 ⧸ reps rK59)) :=
  repsInj_of_reduceAux rK59 T59_8 (by decide)

theorem hcardT59_8 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK59 ⟨8, by decide⟩ R59 hpxR59 hcardq59 (by decide)).symm

/-- **Cell (59, 8).** -/
theorem cell59_8 (e : List (ZMod 25)) (heK : charOK (basisAt rK59) e = true)
    (h : ↥(reps (⟨8, by decide⟩ : Fin 148))) :
    species (reps (⟨8, by decide⟩ : Fin 148)) h (basisElt (reps rK59) (charOfVec rK59 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK59 e (h : Coordinate 1) T59_8 i :=
  species_entry_eq_sum rK59 ⟨8, by decide⟩ e heK h T59_8 hfix59_8 hinj59_8 hcardT59_8
    (fun i => conj_mem_of_fixedPoints (reps ⟨8, by decide⟩) (reps rK59) (T59_8 i) (hfix59_8 i) h)

/-! ## Cell (59, 12): |T| = 25 -/

def T59_12list : List Coordinates := [(0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,0,0,4,0)]
def T59_12 : Fin 25 → Coordinate 1 := fun i => T59_12list.getD i.val (0,0,0,0,0)

theorem hfix59_12 : ∀ i, ((T59_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK59)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59) :=
  repsFix_of_siftB rK59 ⟨12, by decide⟩ T59_12 (by decide)

theorem hinj59_12 : Function.Injective
    (fun i => ((T59_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK59)) :=
  repsInj_of_reduceAux rK59 T59_12 (by decide)

theorem hcardT59_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK59 ⟨12, by decide⟩ R59 hpxR59 hcardq59 (by decide)).symm

/-- **Cell (59, 12).** -/
theorem cell59_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK59) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK59) (charOfVec rK59 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK59 e (h : Coordinate 1) T59_12 i :=
  species_entry_eq_sum rK59 ⟨12, by decide⟩ e heK h T59_12 hfix59_12 hinj59_12 hcardT59_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK59) (T59_12 i) (hfix59_12 i) h)

/-! ## Cell (59, 26): |T| = 25 -/

def T59_26list : List Coordinates := [(0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,0,0,4,0)]
def T59_26 : Fin 25 → Coordinate 1 := fun i => T59_26list.getD i.val (0,0,0,0,0)

theorem hfix59_26 : ∀ i, ((T59_26 i : Coordinate 1) : Coordinate 1 ⧸ reps rK59)
    ∈ fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59) :=
  repsFix_of_siftB rK59 ⟨26, by decide⟩ T59_26 (by decide)

theorem hinj59_26 : Function.Injective
    (fun i => ((T59_26 i : Coordinate 1) : Coordinate 1 ⧸ reps rK59)) :=
  repsInj_of_reduceAux rK59 T59_26 (by decide)

theorem hcardT59_26 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK59 ⟨26, by decide⟩ R59 hpxR59 hcardq59 (by decide)).symm

/-- **Cell (59, 26).** -/
theorem cell59_26 (e : List (ZMod 25)) (heK : charOK (basisAt rK59) e = true)
    (h : ↥(reps (⟨26, by decide⟩ : Fin 148))) :
    species (reps (⟨26, by decide⟩ : Fin 148)) h (basisElt (reps rK59) (charOfVec rK59 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK59 e (h : Coordinate 1) T59_26 i :=
  species_entry_eq_sum rK59 ⟨26, by decide⟩ e heK h T59_26 hfix59_26 hinj59_26 hcardT59_26
    (fun i => conj_mem_of_fixedPoints (reps ⟨26, by decide⟩) (reps rK59) (T59_26 i) (hfix59_26 i) h)

/-! ## Cell (59, 28): |T| = 5 -/

def T59_28list : List Coordinates := [(4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,0,0,4,0)]
def T59_28 : Fin 5 → Coordinate 1 := fun i => T59_28list.getD i.val (0,0,0,0,0)

theorem hfix59_28 : ∀ i, ((T59_28 i : Coordinate 1) : Coordinate 1 ⧸ reps rK59)
    ∈ fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59) :=
  repsFix_of_siftB rK59 ⟨28, by decide⟩ T59_28 (by decide)

theorem hinj59_28 : Function.Injective
    (fun i => ((T59_28 i : Coordinate 1) : Coordinate 1 ⧸ reps rK59)) :=
  repsInj_of_reduceAux rK59 T59_28 (by decide)

theorem hcardT59_28 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK59 ⟨28, by decide⟩ R59 hpxR59 hcardq59 (by decide)).symm

/-- **Cell (59, 28).** -/
theorem cell59_28 (e : List (ZMod 25)) (heK : charOK (basisAt rK59) e = true)
    (h : ↥(reps (⟨28, by decide⟩ : Fin 148))) :
    species (reps (⟨28, by decide⟩ : Fin 148)) h (basisElt (reps rK59) (charOfVec rK59 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK59 e (h : Coordinate 1) T59_28 i :=
  species_entry_eq_sum rK59 ⟨28, by decide⟩ e heK h T59_28 hfix59_28 hinj59_28 hcardT59_28
    (fun i => conj_mem_of_fixedPoints (reps ⟨28, by decide⟩) (reps rK59) (T59_28 i) (hfix59_28 i) h)

/-! ## Cell (59, 33): |T| = 5 -/

def T59_33list : List Coordinates := [(2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,0,0,4,0)]
def T59_33 : Fin 5 → Coordinate 1 := fun i => T59_33list.getD i.val (0,0,0,0,0)

theorem hfix59_33 : ∀ i, ((T59_33 i : Coordinate 1) : Coordinate 1 ⧸ reps rK59)
    ∈ fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59) :=
  repsFix_of_siftB rK59 ⟨33, by decide⟩ T59_33 (by decide)

theorem hinj59_33 : Function.Injective
    (fun i => ((T59_33 i : Coordinate 1) : Coordinate 1 ⧸ reps rK59)) :=
  repsInj_of_reduceAux rK59 T59_33 (by decide)

theorem hcardT59_33 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK59 ⟨33, by decide⟩ R59 hpxR59 hcardq59 (by decide)).symm

/-- **Cell (59, 33).** -/
theorem cell59_33 (e : List (ZMod 25)) (heK : charOK (basisAt rK59) e = true)
    (h : ↥(reps (⟨33, by decide⟩ : Fin 148))) :
    species (reps (⟨33, by decide⟩ : Fin 148)) h (basisElt (reps rK59) (charOfVec rK59 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK59 e (h : Coordinate 1) T59_33 i :=
  species_entry_eq_sum rK59 ⟨33, by decide⟩ e heK h T59_33 hfix59_33 hinj59_33 hcardT59_33
    (fun i => conj_mem_of_fixedPoints (reps ⟨33, by decide⟩) (reps rK59) (T59_33 i) (hfix59_33 i) h)

/-! ## Cell (59, 38): |T| = 5 -/

def T59_38list : List Coordinates := [(3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,0,0,4,0)]
def T59_38 : Fin 5 → Coordinate 1 := fun i => T59_38list.getD i.val (0,0,0,0,0)

theorem hfix59_38 : ∀ i, ((T59_38 i : Coordinate 1) : Coordinate 1 ⧸ reps rK59)
    ∈ fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59) :=
  repsFix_of_siftB rK59 ⟨38, by decide⟩ T59_38 (by decide)

theorem hinj59_38 : Function.Injective
    (fun i => ((T59_38 i : Coordinate 1) : Coordinate 1 ⧸ reps rK59)) :=
  repsInj_of_reduceAux rK59 T59_38 (by decide)

theorem hcardT59_38 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK59 ⟨38, by decide⟩ R59 hpxR59 hcardq59 (by decide)).symm

/-- **Cell (59, 38).** -/
theorem cell59_38 (e : List (ZMod 25)) (heK : charOK (basisAt rK59) e = true)
    (h : ↥(reps (⟨38, by decide⟩ : Fin 148))) :
    species (reps (⟨38, by decide⟩ : Fin 148)) h (basisElt (reps rK59) (charOfVec rK59 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK59 e (h : Coordinate 1) T59_38 i :=
  species_entry_eq_sum rK59 ⟨38, by decide⟩ e heK h T59_38 hfix59_38 hinj59_38 hcardT59_38
    (fun i => conj_mem_of_fixedPoints (reps ⟨38, by decide⟩) (reps rK59) (T59_38 i) (hfix59_38 i) h)

/-! ## Cell (59, 43): |T| = 5 -/

def T59_43list : List Coordinates := [(1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,0,0,4,0)]
def T59_43 : Fin 5 → Coordinate 1 := fun i => T59_43list.getD i.val (0,0,0,0,0)

theorem hfix59_43 : ∀ i, ((T59_43 i : Coordinate 1) : Coordinate 1 ⧸ reps rK59)
    ∈ fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59) :=
  repsFix_of_siftB rK59 ⟨43, by decide⟩ T59_43 (by decide)

theorem hinj59_43 : Function.Injective
    (fun i => ((T59_43 i : Coordinate 1) : Coordinate 1 ⧸ reps rK59)) :=
  repsInj_of_reduceAux rK59 T59_43 (by decide)

theorem hcardT59_43 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK59 ⟨43, by decide⟩ R59 hpxR59 hcardq59 (by decide)).symm

/-- **Cell (59, 43).** -/
theorem cell59_43 (e : List (ZMod 25)) (heK : charOK (basisAt rK59) e = true)
    (h : ↥(reps (⟨43, by decide⟩ : Fin 148))) :
    species (reps (⟨43, by decide⟩ : Fin 148)) h (basisElt (reps rK59) (charOfVec rK59 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK59 e (h : Coordinate 1) T59_43 i :=
  species_entry_eq_sum rK59 ⟨43, by decide⟩ e heK h T59_43 hfix59_43 hinj59_43 hcardT59_43
    (fun i => conj_mem_of_fixedPoints (reps ⟨43, by decide⟩) (reps rK59) (T59_43 i) (hfix59_43 i) h)

/-! ## Cell (59, 48): |T| = 5 -/

def T59_48list : List Coordinates := [(0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0)]
def T59_48 : Fin 5 → Coordinate 1 := fun i => T59_48list.getD i.val (0,0,0,0,0)

theorem hfix59_48 : ∀ i, ((T59_48 i : Coordinate 1) : Coordinate 1 ⧸ reps rK59)
    ∈ fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59) :=
  repsFix_of_siftB rK59 ⟨48, by decide⟩ T59_48 (by decide)

theorem hinj59_48 : Function.Injective
    (fun i => ((T59_48 i : Coordinate 1) : Coordinate 1 ⧸ reps rK59)) :=
  repsInj_of_reduceAux rK59 T59_48 (by decide)

theorem hcardT59_48 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK59 ⟨48, by decide⟩ R59 hpxR59 hcardq59 (by decide)).symm

/-- **Cell (59, 48).** -/
theorem cell59_48 (e : List (ZMod 25)) (heK : charOK (basisAt rK59) e = true)
    (h : ↥(reps (⟨48, by decide⟩ : Fin 148))) :
    species (reps (⟨48, by decide⟩ : Fin 148)) h (basisElt (reps rK59) (charOfVec rK59 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK59 e (h : Coordinate 1) T59_48 i :=
  species_entry_eq_sum rK59 ⟨48, by decide⟩ e heK h T59_48 hfix59_48 hinj59_48 hcardT59_48
    (fun i => conj_mem_of_fixedPoints (reps ⟨48, by decide⟩) (reps rK59) (T59_48 i) (hfix59_48 i) h)

/-! ## Cell (59, 59): |T| = 5 -/

def T59_59list : List Coordinates := [(0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0)]
def T59_59 : Fin 5 → Coordinate 1 := fun i => T59_59list.getD i.val (0,0,0,0,0)

theorem hfix59_59 : ∀ i, ((T59_59 i : Coordinate 1) : Coordinate 1 ⧸ reps rK59)
    ∈ fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59) :=
  repsFix_of_siftB rK59 ⟨59, by decide⟩ T59_59 (by decide)

theorem hinj59_59 : Function.Injective
    (fun i => ((T59_59 i : Coordinate 1) : Coordinate 1 ⧸ reps rK59)) :=
  repsInj_of_reduceAux rK59 T59_59 (by decide)

theorem hcardT59_59 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK59 ⟨59, by decide⟩ R59 hpxR59 hcardq59 (by decide)).symm

/-- **Cell (59, 59).** -/
theorem cell59_59 (e : List (ZMod 25)) (heK : charOK (basisAt rK59) e = true)
    (h : ↥(reps (⟨59, by decide⟩ : Fin 148))) :
    species (reps (⟨59, by decide⟩ : Fin 148)) h (basisElt (reps rK59) (charOfVec rK59 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK59 e (h : Coordinate 1) T59_59 i :=
  species_entry_eq_sum rK59 ⟨59, by decide⟩ e heK h T59_59 hfix59_59 hinj59_59 hcardT59_59
    (fun i => conj_mem_of_fixedPoints (reps ⟨59, by decide⟩) (reps rK59) (T59_59 i) (hfix59_59 i) h)

namespace Q2

def R59_2 : Fin 25 → Coordinate 2 := fun i => R59list.getD i.val (0,0,0,0,0)
theorem hpxR59_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK59) (R59_2 i)) := by decide
theorem hcardq59_2 : Nat.card (Coordinate 2 ⧸ reps rK59) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (59, 0) twin -/

def T59_0_2 : Fin 25 → Coordinate 2 := fun i => T59_0list.getD i.val (0,0,0,0,0)

theorem hfix59_0_2 : ∀ i, ((T59_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK59)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK59) :=
  repsFix_of_siftB2 rK59 ⟨0, by decide⟩ T59_0_2 (by decide)

theorem hinj59_0_2 : Function.Injective
    (fun i => ((T59_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK59)) :=
  repsInj_of_reduceAux2 rK59 T59_0_2 (by decide)

theorem hcardT59_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK59)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK59 ⟨0, by decide⟩ R59_2 hpxR59_2 hcardq59_2 (by decide)).symm

/-- **Cell (59, 0) twin (q=2).** -/
theorem cell59_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK59) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK59) (charOfVec2 rK59 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK59 e (h : Coordinate 2) T59_0_2 i :=
  species_entry_eq_sum rK59 ⟨0, by decide⟩ e heK h T59_0_2 hfix59_0_2 hinj59_0_2 hcardT59_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK59) (T59_0_2 i) (hfix59_0_2 i) h)

/-! ### Cell (59, 8) twin -/

def T59_8_2 : Fin 25 → Coordinate 2 := fun i => T59_8list.getD i.val (0,0,0,0,0)

theorem hfix59_8_2 : ∀ i, ((T59_8_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK59)
    ∈ fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK59) :=
  repsFix_of_siftB2 rK59 ⟨8, by decide⟩ T59_8_2 (by decide)

theorem hinj59_8_2 : Function.Injective
    (fun i => ((T59_8_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK59)) :=
  repsInj_of_reduceAux2 rK59 T59_8_2 (by decide)

theorem hcardT59_8_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK59)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK59 ⟨8, by decide⟩ R59_2 hpxR59_2 hcardq59_2 (by decide)).symm

/-- **Cell (59, 8) twin (q=2).** -/
theorem cell59_8_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK59) e = true)
    (h : ↥(reps (⟨8, by decide⟩ : Fin 148))) :
    species (reps (⟨8, by decide⟩ : Fin 148)) h (basisElt (reps rK59) (charOfVec2 rK59 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK59 e (h : Coordinate 2) T59_8_2 i :=
  species_entry_eq_sum rK59 ⟨8, by decide⟩ e heK h T59_8_2 hfix59_8_2 hinj59_8_2 hcardT59_8_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨8, by decide⟩) (reps rK59) (T59_8_2 i) (hfix59_8_2 i) h)

/-! ### Cell (59, 12) twin -/

def T59_12_2 : Fin 25 → Coordinate 2 := fun i => T59_12list.getD i.val (0,0,0,0,0)

theorem hfix59_12_2 : ∀ i, ((T59_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK59)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK59) :=
  repsFix_of_siftB2 rK59 ⟨12, by decide⟩ T59_12_2 (by decide)

theorem hinj59_12_2 : Function.Injective
    (fun i => ((T59_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK59)) :=
  repsInj_of_reduceAux2 rK59 T59_12_2 (by decide)

theorem hcardT59_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK59)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK59 ⟨12, by decide⟩ R59_2 hpxR59_2 hcardq59_2 (by decide)).symm

/-- **Cell (59, 12) twin (q=2).** -/
theorem cell59_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK59) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK59) (charOfVec2 rK59 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK59 e (h : Coordinate 2) T59_12_2 i :=
  species_entry_eq_sum rK59 ⟨12, by decide⟩ e heK h T59_12_2 hfix59_12_2 hinj59_12_2 hcardT59_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK59) (T59_12_2 i) (hfix59_12_2 i) h)

/-! ### Cell (59, 26) twin -/

def T59_26_2 : Fin 25 → Coordinate 2 := fun i => T59_26list.getD i.val (0,0,0,0,0)

theorem hfix59_26_2 : ∀ i, ((T59_26_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK59)
    ∈ fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK59) :=
  repsFix_of_siftB2 rK59 ⟨26, by decide⟩ T59_26_2 (by decide)

theorem hinj59_26_2 : Function.Injective
    (fun i => ((T59_26_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK59)) :=
  repsInj_of_reduceAux2 rK59 T59_26_2 (by decide)

theorem hcardT59_26_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK59)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK59 ⟨26, by decide⟩ R59_2 hpxR59_2 hcardq59_2 (by decide)).symm

/-- **Cell (59, 26) twin (q=2).** -/
theorem cell59_26_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK59) e = true)
    (h : ↥(reps (⟨26, by decide⟩ : Fin 148))) :
    species (reps (⟨26, by decide⟩ : Fin 148)) h (basisElt (reps rK59) (charOfVec2 rK59 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK59 e (h : Coordinate 2) T59_26_2 i :=
  species_entry_eq_sum rK59 ⟨26, by decide⟩ e heK h T59_26_2 hfix59_26_2 hinj59_26_2 hcardT59_26_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨26, by decide⟩) (reps rK59) (T59_26_2 i) (hfix59_26_2 i) h)

/-! ### Cell (59, 28) twin -/

def T59_28_2 : Fin 5 → Coordinate 2 := fun i => T59_28list.getD i.val (0,0,0,0,0)

theorem hfix59_28_2 : ∀ i, ((T59_28_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK59)
    ∈ fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK59) :=
  repsFix_of_siftB2 rK59 ⟨28, by decide⟩ T59_28_2 (by decide)

theorem hinj59_28_2 : Function.Injective
    (fun i => ((T59_28_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK59)) :=
  repsInj_of_reduceAux2 rK59 T59_28_2 (by decide)

theorem hcardT59_28_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK59)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK59 ⟨28, by decide⟩ R59_2 hpxR59_2 hcardq59_2 (by decide)).symm

/-- **Cell (59, 28) twin (q=2).** -/
theorem cell59_28_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK59) e = true)
    (h : ↥(reps (⟨28, by decide⟩ : Fin 148))) :
    species (reps (⟨28, by decide⟩ : Fin 148)) h (basisElt (reps rK59) (charOfVec2 rK59 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK59 e (h : Coordinate 2) T59_28_2 i :=
  species_entry_eq_sum rK59 ⟨28, by decide⟩ e heK h T59_28_2 hfix59_28_2 hinj59_28_2 hcardT59_28_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨28, by decide⟩) (reps rK59) (T59_28_2 i) (hfix59_28_2 i) h)

/-! ### Cell (59, 33) twin -/

def T59_33_2 : Fin 5 → Coordinate 2 := fun i => T59_33list.getD i.val (0,0,0,0,0)

theorem hfix59_33_2 : ∀ i, ((T59_33_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK59)
    ∈ fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK59) :=
  repsFix_of_siftB2 rK59 ⟨33, by decide⟩ T59_33_2 (by decide)

theorem hinj59_33_2 : Function.Injective
    (fun i => ((T59_33_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK59)) :=
  repsInj_of_reduceAux2 rK59 T59_33_2 (by decide)

theorem hcardT59_33_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK59)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK59 ⟨33, by decide⟩ R59_2 hpxR59_2 hcardq59_2 (by decide)).symm

/-- **Cell (59, 33) twin (q=2).** -/
theorem cell59_33_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK59) e = true)
    (h : ↥(reps (⟨33, by decide⟩ : Fin 148))) :
    species (reps (⟨33, by decide⟩ : Fin 148)) h (basisElt (reps rK59) (charOfVec2 rK59 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK59 e (h : Coordinate 2) T59_33_2 i :=
  species_entry_eq_sum rK59 ⟨33, by decide⟩ e heK h T59_33_2 hfix59_33_2 hinj59_33_2 hcardT59_33_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨33, by decide⟩) (reps rK59) (T59_33_2 i) (hfix59_33_2 i) h)

/-! ### Cell (59, 38) twin -/

def T59_38_2 : Fin 5 → Coordinate 2 := fun i => T59_38list.getD i.val (0,0,0,0,0)

theorem hfix59_38_2 : ∀ i, ((T59_38_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK59)
    ∈ fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK59) :=
  repsFix_of_siftB2 rK59 ⟨38, by decide⟩ T59_38_2 (by decide)

theorem hinj59_38_2 : Function.Injective
    (fun i => ((T59_38_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK59)) :=
  repsInj_of_reduceAux2 rK59 T59_38_2 (by decide)

theorem hcardT59_38_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK59)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK59 ⟨38, by decide⟩ R59_2 hpxR59_2 hcardq59_2 (by decide)).symm

/-- **Cell (59, 38) twin (q=2).** -/
theorem cell59_38_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK59) e = true)
    (h : ↥(reps (⟨38, by decide⟩ : Fin 148))) :
    species (reps (⟨38, by decide⟩ : Fin 148)) h (basisElt (reps rK59) (charOfVec2 rK59 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK59 e (h : Coordinate 2) T59_38_2 i :=
  species_entry_eq_sum rK59 ⟨38, by decide⟩ e heK h T59_38_2 hfix59_38_2 hinj59_38_2 hcardT59_38_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨38, by decide⟩) (reps rK59) (T59_38_2 i) (hfix59_38_2 i) h)

/-! ### Cell (59, 43) twin -/

def T59_43_2 : Fin 5 → Coordinate 2 := fun i => T59_43list.getD i.val (0,0,0,0,0)

theorem hfix59_43_2 : ∀ i, ((T59_43_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK59)
    ∈ fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK59) :=
  repsFix_of_siftB2 rK59 ⟨43, by decide⟩ T59_43_2 (by decide)

theorem hinj59_43_2 : Function.Injective
    (fun i => ((T59_43_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK59)) :=
  repsInj_of_reduceAux2 rK59 T59_43_2 (by decide)

theorem hcardT59_43_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK59)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK59 ⟨43, by decide⟩ R59_2 hpxR59_2 hcardq59_2 (by decide)).symm

/-- **Cell (59, 43) twin (q=2).** -/
theorem cell59_43_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK59) e = true)
    (h : ↥(reps (⟨43, by decide⟩ : Fin 148))) :
    species (reps (⟨43, by decide⟩ : Fin 148)) h (basisElt (reps rK59) (charOfVec2 rK59 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK59 e (h : Coordinate 2) T59_43_2 i :=
  species_entry_eq_sum rK59 ⟨43, by decide⟩ e heK h T59_43_2 hfix59_43_2 hinj59_43_2 hcardT59_43_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨43, by decide⟩) (reps rK59) (T59_43_2 i) (hfix59_43_2 i) h)

/-! ### Cell (59, 48) twin -/

def T59_48_2 : Fin 5 → Coordinate 2 := fun i => T59_48list.getD i.val (0,0,0,0,0)

theorem hfix59_48_2 : ∀ i, ((T59_48_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK59)
    ∈ fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK59) :=
  repsFix_of_siftB2 rK59 ⟨48, by decide⟩ T59_48_2 (by decide)

theorem hinj59_48_2 : Function.Injective
    (fun i => ((T59_48_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK59)) :=
  repsInj_of_reduceAux2 rK59 T59_48_2 (by decide)

theorem hcardT59_48_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK59)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK59 ⟨48, by decide⟩ R59_2 hpxR59_2 hcardq59_2 (by decide)).symm

/-- **Cell (59, 48) twin (q=2).** -/
theorem cell59_48_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK59) e = true)
    (h : ↥(reps (⟨48, by decide⟩ : Fin 148))) :
    species (reps (⟨48, by decide⟩ : Fin 148)) h (basisElt (reps rK59) (charOfVec2 rK59 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK59 e (h : Coordinate 2) T59_48_2 i :=
  species_entry_eq_sum rK59 ⟨48, by decide⟩ e heK h T59_48_2 hfix59_48_2 hinj59_48_2 hcardT59_48_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨48, by decide⟩) (reps rK59) (T59_48_2 i) (hfix59_48_2 i) h)

/-! ### Cell (59, 59) twin -/

def T59_59_2 : Fin 5 → Coordinate 2 := fun i => T59_59list.getD i.val (0,0,0,0,0)

theorem hfix59_59_2 : ∀ i, ((T59_59_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK59)
    ∈ fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK59) :=
  repsFix_of_siftB2 rK59 ⟨59, by decide⟩ T59_59_2 (by decide)

theorem hinj59_59_2 : Function.Injective
    (fun i => ((T59_59_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK59)) :=
  repsInj_of_reduceAux2 rK59 T59_59_2 (by decide)

theorem hcardT59_59_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK59)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK59 ⟨59, by decide⟩ R59_2 hpxR59_2 hcardq59_2 (by decide)).symm

/-- **Cell (59, 59) twin (q=2).** -/
theorem cell59_59_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK59) e = true)
    (h : ↥(reps (⟨59, by decide⟩ : Fin 148))) :
    species (reps (⟨59, by decide⟩ : Fin 148)) h (basisElt (reps rK59) (charOfVec2 rK59 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK59 e (h : Coordinate 2) T59_59_2 i :=
  species_entry_eq_sum rK59 ⟨59, by decide⟩ e heK h T59_59_2 hfix59_59_2 hinj59_59_2 hcardT59_59_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨59, by decide⟩) (reps rK59) (T59_59_2 i) (hfix59_59_2 i) h)

end Q2

end LeanDring.P5Presentation
