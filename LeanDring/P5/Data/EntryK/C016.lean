/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, K-strata data (5^3 stratum, rK 65-69): certified per-cell species-entry instantiations, both
twins.

Covers K-classes 65, 66, 67, 68, 69 (order-5^3 K, |R|=25).  For each nonzero `H`-column
(`(G/K)^H ≠ ∅`), the full coset transversal `R65..` and each `H`-fixed
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

/-! # K-class rK = 65  (|G/K| = 25) -/

def rK65 : Fin 148 := ⟨65, by decide⟩

def R65list : List Coordinates := [(0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0)]
def R65 : Fin 25 → Coordinate 1 := fun i => R65list.getD i.val (0,0,0,0,0)

theorem hpxR65 : Function.Injective (fun i => reduceAux 1 (basisAt rK65) (R65 i)) := by decide
theorem hcardq65 : Nat.card (Coordinate 1 ⧸ reps rK65) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (65, 0): |T| = 25 -/

def T65_0list : List Coordinates := [(0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0)]
def T65_0 : Fin 25 → Coordinate 1 := fun i => T65_0list.getD i.val (0,0,0,0,0)

theorem hfix65_0 : ∀ i, ((T65_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK65)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65) :=
  repsFix_of_siftB rK65 ⟨0, by decide⟩ T65_0 (by decide)

theorem hinj65_0 : Function.Injective
    (fun i => ((T65_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK65)) :=
  repsInj_of_reduceAux rK65 T65_0 (by decide)

theorem hcardT65_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK65 ⟨0, by decide⟩ R65 hpxR65 hcardq65 (by decide)).symm

/-- **Cell (65, 0).** -/
theorem cell65_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK65) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK65) (charOfVec rK65 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK65 e (h : Coordinate 1) T65_0 i :=
  species_entry_eq_sum rK65 ⟨0, by decide⟩ e heK h T65_0 hfix65_0 hinj65_0 hcardT65_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK65) (T65_0 i) (hfix65_0 i) h)

/-! ## Cell (65, 9): |T| = 25 -/

def T65_9list : List Coordinates := [(0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0)]
def T65_9 : Fin 25 → Coordinate 1 := fun i => T65_9list.getD i.val (0,0,0,0,0)

theorem hfix65_9 : ∀ i, ((T65_9 i : Coordinate 1) : Coordinate 1 ⧸ reps rK65)
    ∈ fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65) :=
  repsFix_of_siftB rK65 ⟨9, by decide⟩ T65_9 (by decide)

theorem hinj65_9 : Function.Injective
    (fun i => ((T65_9 i : Coordinate 1) : Coordinate 1 ⧸ reps rK65)) :=
  repsInj_of_reduceAux rK65 T65_9 (by decide)

theorem hcardT65_9 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK65 ⟨9, by decide⟩ R65 hpxR65 hcardq65 (by decide)).symm

/-- **Cell (65, 9).** -/
theorem cell65_9 (e : List (ZMod 25)) (heK : charOK (basisAt rK65) e = true)
    (h : ↥(reps (⟨9, by decide⟩ : Fin 148))) :
    species (reps (⟨9, by decide⟩ : Fin 148)) h (basisElt (reps rK65) (charOfVec rK65 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK65 e (h : Coordinate 1) T65_9 i :=
  species_entry_eq_sum rK65 ⟨9, by decide⟩ e heK h T65_9 hfix65_9 hinj65_9 hcardT65_9
    (fun i => conj_mem_of_fixedPoints (reps ⟨9, by decide⟩) (reps rK65) (T65_9 i) (hfix65_9 i) h)

/-! ## Cell (65, 12): |T| = 25 -/

def T65_12list : List Coordinates := [(0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0)]
def T65_12 : Fin 25 → Coordinate 1 := fun i => T65_12list.getD i.val (0,0,0,0,0)

theorem hfix65_12 : ∀ i, ((T65_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK65)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65) :=
  repsFix_of_siftB rK65 ⟨12, by decide⟩ T65_12 (by decide)

theorem hinj65_12 : Function.Injective
    (fun i => ((T65_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK65)) :=
  repsInj_of_reduceAux rK65 T65_12 (by decide)

theorem hcardT65_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK65 ⟨12, by decide⟩ R65 hpxR65 hcardq65 (by decide)).symm

/-- **Cell (65, 12).** -/
theorem cell65_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK65) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK65) (charOfVec rK65 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK65 e (h : Coordinate 1) T65_12 i :=
  species_entry_eq_sum rK65 ⟨12, by decide⟩ e heK h T65_12 hfix65_12 hinj65_12 hcardT65_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK65) (T65_12 i) (hfix65_12 i) h)

/-! ## Cell (65, 27): |T| = 25 -/

def T65_27list : List Coordinates := [(0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0)]
def T65_27 : Fin 25 → Coordinate 1 := fun i => T65_27list.getD i.val (0,0,0,0,0)

theorem hfix65_27 : ∀ i, ((T65_27 i : Coordinate 1) : Coordinate 1 ⧸ reps rK65)
    ∈ fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65) :=
  repsFix_of_siftB rK65 ⟨27, by decide⟩ T65_27 (by decide)

theorem hinj65_27 : Function.Injective
    (fun i => ((T65_27 i : Coordinate 1) : Coordinate 1 ⧸ reps rK65)) :=
  repsInj_of_reduceAux rK65 T65_27 (by decide)

theorem hcardT65_27 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK65 ⟨27, by decide⟩ R65 hpxR65 hcardq65 (by decide)).symm

/-- **Cell (65, 27).** -/
theorem cell65_27 (e : List (ZMod 25)) (heK : charOK (basisAt rK65) e = true)
    (h : ↥(reps (⟨27, by decide⟩ : Fin 148))) :
    species (reps (⟨27, by decide⟩ : Fin 148)) h (basisElt (reps rK65) (charOfVec rK65 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK65 e (h : Coordinate 1) T65_27 i :=
  species_entry_eq_sum rK65 ⟨27, by decide⟩ e heK h T65_27 hfix65_27 hinj65_27 hcardT65_27
    (fun i => conj_mem_of_fixedPoints (reps ⟨27, by decide⟩) (reps rK65) (T65_27 i) (hfix65_27 i) h)

/-! ## Cell (65, 30): |T| = 5 -/

def T65_30list : List Coordinates := [(0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0)]
def T65_30 : Fin 5 → Coordinate 1 := fun i => T65_30list.getD i.val (0,0,0,0,0)

theorem hfix65_30 : ∀ i, ((T65_30 i : Coordinate 1) : Coordinate 1 ⧸ reps rK65)
    ∈ fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65) :=
  repsFix_of_siftB rK65 ⟨30, by decide⟩ T65_30 (by decide)

theorem hinj65_30 : Function.Injective
    (fun i => ((T65_30 i : Coordinate 1) : Coordinate 1 ⧸ reps rK65)) :=
  repsInj_of_reduceAux rK65 T65_30 (by decide)

theorem hcardT65_30 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK65 ⟨30, by decide⟩ R65 hpxR65 hcardq65 (by decide)).symm

/-- **Cell (65, 30).** -/
theorem cell65_30 (e : List (ZMod 25)) (heK : charOK (basisAt rK65) e = true)
    (h : ↥(reps (⟨30, by decide⟩ : Fin 148))) :
    species (reps (⟨30, by decide⟩ : Fin 148)) h (basisElt (reps rK65) (charOfVec rK65 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK65 e (h : Coordinate 1) T65_30 i :=
  species_entry_eq_sum rK65 ⟨30, by decide⟩ e heK h T65_30 hfix65_30 hinj65_30 hcardT65_30
    (fun i => conj_mem_of_fixedPoints (reps ⟨30, by decide⟩) (reps rK65) (T65_30 i) (hfix65_30 i) h)

/-! ## Cell (65, 35): |T| = 5 -/

def T65_35list : List Coordinates := [(0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0)]
def T65_35 : Fin 5 → Coordinate 1 := fun i => T65_35list.getD i.val (0,0,0,0,0)

theorem hfix65_35 : ∀ i, ((T65_35 i : Coordinate 1) : Coordinate 1 ⧸ reps rK65)
    ∈ fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65) :=
  repsFix_of_siftB rK65 ⟨35, by decide⟩ T65_35 (by decide)

theorem hinj65_35 : Function.Injective
    (fun i => ((T65_35 i : Coordinate 1) : Coordinate 1 ⧸ reps rK65)) :=
  repsInj_of_reduceAux rK65 T65_35 (by decide)

theorem hcardT65_35 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK65 ⟨35, by decide⟩ R65 hpxR65 hcardq65 (by decide)).symm

/-- **Cell (65, 35).** -/
theorem cell65_35 (e : List (ZMod 25)) (heK : charOK (basisAt rK65) e = true)
    (h : ↥(reps (⟨35, by decide⟩ : Fin 148))) :
    species (reps (⟨35, by decide⟩ : Fin 148)) h (basisElt (reps rK65) (charOfVec rK65 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK65 e (h : Coordinate 1) T65_35 i :=
  species_entry_eq_sum rK65 ⟨35, by decide⟩ e heK h T65_35 hfix65_35 hinj65_35 hcardT65_35
    (fun i => conj_mem_of_fixedPoints (reps ⟨35, by decide⟩) (reps rK65) (T65_35 i) (hfix65_35 i) h)

/-! ## Cell (65, 40): |T| = 5 -/

def T65_40list : List Coordinates := [(0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0)]
def T65_40 : Fin 5 → Coordinate 1 := fun i => T65_40list.getD i.val (0,0,0,0,0)

theorem hfix65_40 : ∀ i, ((T65_40 i : Coordinate 1) : Coordinate 1 ⧸ reps rK65)
    ∈ fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65) :=
  repsFix_of_siftB rK65 ⟨40, by decide⟩ T65_40 (by decide)

theorem hinj65_40 : Function.Injective
    (fun i => ((T65_40 i : Coordinate 1) : Coordinate 1 ⧸ reps rK65)) :=
  repsInj_of_reduceAux rK65 T65_40 (by decide)

theorem hcardT65_40 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK65 ⟨40, by decide⟩ R65 hpxR65 hcardq65 (by decide)).symm

/-- **Cell (65, 40).** -/
theorem cell65_40 (e : List (ZMod 25)) (heK : charOK (basisAt rK65) e = true)
    (h : ↥(reps (⟨40, by decide⟩ : Fin 148))) :
    species (reps (⟨40, by decide⟩ : Fin 148)) h (basisElt (reps rK65) (charOfVec rK65 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK65 e (h : Coordinate 1) T65_40 i :=
  species_entry_eq_sum rK65 ⟨40, by decide⟩ e heK h T65_40 hfix65_40 hinj65_40 hcardT65_40
    (fun i => conj_mem_of_fixedPoints (reps ⟨40, by decide⟩) (reps rK65) (T65_40 i) (hfix65_40 i) h)

/-! ## Cell (65, 45): |T| = 5 -/

def T65_45list : List Coordinates := [(0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0)]
def T65_45 : Fin 5 → Coordinate 1 := fun i => T65_45list.getD i.val (0,0,0,0,0)

theorem hfix65_45 : ∀ i, ((T65_45 i : Coordinate 1) : Coordinate 1 ⧸ reps rK65)
    ∈ fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65) :=
  repsFix_of_siftB rK65 ⟨45, by decide⟩ T65_45 (by decide)

theorem hinj65_45 : Function.Injective
    (fun i => ((T65_45 i : Coordinate 1) : Coordinate 1 ⧸ reps rK65)) :=
  repsInj_of_reduceAux rK65 T65_45 (by decide)

theorem hcardT65_45 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK65 ⟨45, by decide⟩ R65 hpxR65 hcardq65 (by decide)).symm

/-- **Cell (65, 45).** -/
theorem cell65_45 (e : List (ZMod 25)) (heK : charOK (basisAt rK65) e = true)
    (h : ↥(reps (⟨45, by decide⟩ : Fin 148))) :
    species (reps (⟨45, by decide⟩ : Fin 148)) h (basisElt (reps rK65) (charOfVec rK65 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK65 e (h : Coordinate 1) T65_45 i :=
  species_entry_eq_sum rK65 ⟨45, by decide⟩ e heK h T65_45 hfix65_45 hinj65_45 hcardT65_45
    (fun i => conj_mem_of_fixedPoints (reps ⟨45, by decide⟩) (reps rK65) (T65_45 i) (hfix65_45 i) h)

/-! ## Cell (65, 50): |T| = 5 -/

def T65_50list : List Coordinates := [(0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0)]
def T65_50 : Fin 5 → Coordinate 1 := fun i => T65_50list.getD i.val (0,0,0,0,0)

theorem hfix65_50 : ∀ i, ((T65_50 i : Coordinate 1) : Coordinate 1 ⧸ reps rK65)
    ∈ fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65) :=
  repsFix_of_siftB rK65 ⟨50, by decide⟩ T65_50 (by decide)

theorem hinj65_50 : Function.Injective
    (fun i => ((T65_50 i : Coordinate 1) : Coordinate 1 ⧸ reps rK65)) :=
  repsInj_of_reduceAux rK65 T65_50 (by decide)

theorem hcardT65_50 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK65 ⟨50, by decide⟩ R65 hpxR65 hcardq65 (by decide)).symm

/-- **Cell (65, 50).** -/
theorem cell65_50 (e : List (ZMod 25)) (heK : charOK (basisAt rK65) e = true)
    (h : ↥(reps (⟨50, by decide⟩ : Fin 148))) :
    species (reps (⟨50, by decide⟩ : Fin 148)) h (basisElt (reps rK65) (charOfVec rK65 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK65 e (h : Coordinate 1) T65_50 i :=
  species_entry_eq_sum rK65 ⟨50, by decide⟩ e heK h T65_50 hfix65_50 hinj65_50 hcardT65_50
    (fun i => conj_mem_of_fixedPoints (reps ⟨50, by decide⟩) (reps rK65) (T65_50 i) (hfix65_50 i) h)

/-! ## Cell (65, 65): |T| = 5 -/

def T65_65list : List Coordinates := [(0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0)]
def T65_65 : Fin 5 → Coordinate 1 := fun i => T65_65list.getD i.val (0,0,0,0,0)

theorem hfix65_65 : ∀ i, ((T65_65 i : Coordinate 1) : Coordinate 1 ⧸ reps rK65)
    ∈ fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65) :=
  repsFix_of_siftB rK65 ⟨65, by decide⟩ T65_65 (by decide)

theorem hinj65_65 : Function.Injective
    (fun i => ((T65_65 i : Coordinate 1) : Coordinate 1 ⧸ reps rK65)) :=
  repsInj_of_reduceAux rK65 T65_65 (by decide)

theorem hcardT65_65 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK65 ⟨65, by decide⟩ R65 hpxR65 hcardq65 (by decide)).symm

/-- **Cell (65, 65).** -/
theorem cell65_65 (e : List (ZMod 25)) (heK : charOK (basisAt rK65) e = true)
    (h : ↥(reps (⟨65, by decide⟩ : Fin 148))) :
    species (reps (⟨65, by decide⟩ : Fin 148)) h (basisElt (reps rK65) (charOfVec rK65 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK65 e (h : Coordinate 1) T65_65 i :=
  species_entry_eq_sum rK65 ⟨65, by decide⟩ e heK h T65_65 hfix65_65 hinj65_65 hcardT65_65
    (fun i => conj_mem_of_fixedPoints (reps ⟨65, by decide⟩) (reps rK65) (T65_65 i) (hfix65_65 i) h)

namespace Q2

def R65_2 : Fin 25 → Coordinate 2 := fun i => R65list.getD i.val (0,0,0,0,0)
theorem hpxR65_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK65) (R65_2 i)) := by decide
theorem hcardq65_2 : Nat.card (Coordinate 2 ⧸ reps rK65) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (65, 0) twin -/

def T65_0_2 : Fin 25 → Coordinate 2 := fun i => T65_0list.getD i.val (0,0,0,0,0)

theorem hfix65_0_2 : ∀ i, ((T65_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK65)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK65) :=
  repsFix_of_siftB2 rK65 ⟨0, by decide⟩ T65_0_2 (by decide)

theorem hinj65_0_2 : Function.Injective
    (fun i => ((T65_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK65)) :=
  repsInj_of_reduceAux2 rK65 T65_0_2 (by decide)

theorem hcardT65_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK65)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK65 ⟨0, by decide⟩ R65_2 hpxR65_2 hcardq65_2 (by decide)).symm

/-- **Cell (65, 0) twin (q=2).** -/
theorem cell65_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK65) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK65) (charOfVec2 rK65 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK65 e (h : Coordinate 2) T65_0_2 i :=
  species_entry_eq_sum rK65 ⟨0, by decide⟩ e heK h T65_0_2 hfix65_0_2 hinj65_0_2 hcardT65_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK65) (T65_0_2 i) (hfix65_0_2 i) h)

/-! ### Cell (65, 9) twin -/

def T65_9_2 : Fin 25 → Coordinate 2 := fun i => T65_9list.getD i.val (0,0,0,0,0)

theorem hfix65_9_2 : ∀ i, ((T65_9_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK65)
    ∈ fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK65) :=
  repsFix_of_siftB2 rK65 ⟨9, by decide⟩ T65_9_2 (by decide)

theorem hinj65_9_2 : Function.Injective
    (fun i => ((T65_9_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK65)) :=
  repsInj_of_reduceAux2 rK65 T65_9_2 (by decide)

theorem hcardT65_9_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK65)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK65 ⟨9, by decide⟩ R65_2 hpxR65_2 hcardq65_2 (by decide)).symm

/-- **Cell (65, 9) twin (q=2).** -/
theorem cell65_9_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK65) e = true)
    (h : ↥(reps (⟨9, by decide⟩ : Fin 148))) :
    species (reps (⟨9, by decide⟩ : Fin 148)) h (basisElt (reps rK65) (charOfVec2 rK65 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK65 e (h : Coordinate 2) T65_9_2 i :=
  species_entry_eq_sum rK65 ⟨9, by decide⟩ e heK h T65_9_2 hfix65_9_2 hinj65_9_2 hcardT65_9_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨9, by decide⟩) (reps rK65) (T65_9_2 i) (hfix65_9_2 i) h)

/-! ### Cell (65, 12) twin -/

def T65_12_2 : Fin 25 → Coordinate 2 := fun i => T65_12list.getD i.val (0,0,0,0,0)

theorem hfix65_12_2 : ∀ i, ((T65_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK65)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK65) :=
  repsFix_of_siftB2 rK65 ⟨12, by decide⟩ T65_12_2 (by decide)

theorem hinj65_12_2 : Function.Injective
    (fun i => ((T65_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK65)) :=
  repsInj_of_reduceAux2 rK65 T65_12_2 (by decide)

theorem hcardT65_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK65)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK65 ⟨12, by decide⟩ R65_2 hpxR65_2 hcardq65_2 (by decide)).symm

/-- **Cell (65, 12) twin (q=2).** -/
theorem cell65_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK65) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK65) (charOfVec2 rK65 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK65 e (h : Coordinate 2) T65_12_2 i :=
  species_entry_eq_sum rK65 ⟨12, by decide⟩ e heK h T65_12_2 hfix65_12_2 hinj65_12_2 hcardT65_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK65) (T65_12_2 i) (hfix65_12_2 i) h)

/-! ### Cell (65, 27) twin -/

def T65_27_2 : Fin 25 → Coordinate 2 := fun i => T65_27list.getD i.val (0,0,0,0,0)

theorem hfix65_27_2 : ∀ i, ((T65_27_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK65)
    ∈ fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK65) :=
  repsFix_of_siftB2 rK65 ⟨27, by decide⟩ T65_27_2 (by decide)

theorem hinj65_27_2 : Function.Injective
    (fun i => ((T65_27_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK65)) :=
  repsInj_of_reduceAux2 rK65 T65_27_2 (by decide)

theorem hcardT65_27_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK65)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK65 ⟨27, by decide⟩ R65_2 hpxR65_2 hcardq65_2 (by decide)).symm

/-- **Cell (65, 27) twin (q=2).** -/
theorem cell65_27_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK65) e = true)
    (h : ↥(reps (⟨27, by decide⟩ : Fin 148))) :
    species (reps (⟨27, by decide⟩ : Fin 148)) h (basisElt (reps rK65) (charOfVec2 rK65 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK65 e (h : Coordinate 2) T65_27_2 i :=
  species_entry_eq_sum rK65 ⟨27, by decide⟩ e heK h T65_27_2 hfix65_27_2 hinj65_27_2 hcardT65_27_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨27, by decide⟩) (reps rK65) (T65_27_2 i) (hfix65_27_2 i) h)

/-! ### Cell (65, 30) twin -/

def T65_30_2 : Fin 5 → Coordinate 2 := fun i => T65_30list.getD i.val (0,0,0,0,0)

theorem hfix65_30_2 : ∀ i, ((T65_30_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK65)
    ∈ fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK65) :=
  repsFix_of_siftB2 rK65 ⟨30, by decide⟩ T65_30_2 (by decide)

theorem hinj65_30_2 : Function.Injective
    (fun i => ((T65_30_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK65)) :=
  repsInj_of_reduceAux2 rK65 T65_30_2 (by decide)

theorem hcardT65_30_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK65)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK65 ⟨30, by decide⟩ R65_2 hpxR65_2 hcardq65_2 (by decide)).symm

/-- **Cell (65, 30) twin (q=2).** -/
theorem cell65_30_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK65) e = true)
    (h : ↥(reps (⟨30, by decide⟩ : Fin 148))) :
    species (reps (⟨30, by decide⟩ : Fin 148)) h (basisElt (reps rK65) (charOfVec2 rK65 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK65 e (h : Coordinate 2) T65_30_2 i :=
  species_entry_eq_sum rK65 ⟨30, by decide⟩ e heK h T65_30_2 hfix65_30_2 hinj65_30_2 hcardT65_30_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨30, by decide⟩) (reps rK65) (T65_30_2 i) (hfix65_30_2 i) h)

/-! ### Cell (65, 35) twin -/

def T65_35_2 : Fin 5 → Coordinate 2 := fun i => T65_35list.getD i.val (0,0,0,0,0)

theorem hfix65_35_2 : ∀ i, ((T65_35_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK65)
    ∈ fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK65) :=
  repsFix_of_siftB2 rK65 ⟨35, by decide⟩ T65_35_2 (by decide)

theorem hinj65_35_2 : Function.Injective
    (fun i => ((T65_35_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK65)) :=
  repsInj_of_reduceAux2 rK65 T65_35_2 (by decide)

theorem hcardT65_35_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK65)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK65 ⟨35, by decide⟩ R65_2 hpxR65_2 hcardq65_2 (by decide)).symm

/-- **Cell (65, 35) twin (q=2).** -/
theorem cell65_35_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK65) e = true)
    (h : ↥(reps (⟨35, by decide⟩ : Fin 148))) :
    species (reps (⟨35, by decide⟩ : Fin 148)) h (basisElt (reps rK65) (charOfVec2 rK65 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK65 e (h : Coordinate 2) T65_35_2 i :=
  species_entry_eq_sum rK65 ⟨35, by decide⟩ e heK h T65_35_2 hfix65_35_2 hinj65_35_2 hcardT65_35_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨35, by decide⟩) (reps rK65) (T65_35_2 i) (hfix65_35_2 i) h)

/-! ### Cell (65, 40) twin -/

def T65_40_2 : Fin 5 → Coordinate 2 := fun i => T65_40list.getD i.val (0,0,0,0,0)

theorem hfix65_40_2 : ∀ i, ((T65_40_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK65)
    ∈ fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK65) :=
  repsFix_of_siftB2 rK65 ⟨40, by decide⟩ T65_40_2 (by decide)

theorem hinj65_40_2 : Function.Injective
    (fun i => ((T65_40_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK65)) :=
  repsInj_of_reduceAux2 rK65 T65_40_2 (by decide)

theorem hcardT65_40_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK65)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK65 ⟨40, by decide⟩ R65_2 hpxR65_2 hcardq65_2 (by decide)).symm

/-- **Cell (65, 40) twin (q=2).** -/
theorem cell65_40_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK65) e = true)
    (h : ↥(reps (⟨40, by decide⟩ : Fin 148))) :
    species (reps (⟨40, by decide⟩ : Fin 148)) h (basisElt (reps rK65) (charOfVec2 rK65 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK65 e (h : Coordinate 2) T65_40_2 i :=
  species_entry_eq_sum rK65 ⟨40, by decide⟩ e heK h T65_40_2 hfix65_40_2 hinj65_40_2 hcardT65_40_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨40, by decide⟩) (reps rK65) (T65_40_2 i) (hfix65_40_2 i) h)

/-! ### Cell (65, 45) twin -/

def T65_45_2 : Fin 5 → Coordinate 2 := fun i => T65_45list.getD i.val (0,0,0,0,0)

theorem hfix65_45_2 : ∀ i, ((T65_45_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK65)
    ∈ fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK65) :=
  repsFix_of_siftB2 rK65 ⟨45, by decide⟩ T65_45_2 (by decide)

theorem hinj65_45_2 : Function.Injective
    (fun i => ((T65_45_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK65)) :=
  repsInj_of_reduceAux2 rK65 T65_45_2 (by decide)

theorem hcardT65_45_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK65)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK65 ⟨45, by decide⟩ R65_2 hpxR65_2 hcardq65_2 (by decide)).symm

/-- **Cell (65, 45) twin (q=2).** -/
theorem cell65_45_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK65) e = true)
    (h : ↥(reps (⟨45, by decide⟩ : Fin 148))) :
    species (reps (⟨45, by decide⟩ : Fin 148)) h (basisElt (reps rK65) (charOfVec2 rK65 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK65 e (h : Coordinate 2) T65_45_2 i :=
  species_entry_eq_sum rK65 ⟨45, by decide⟩ e heK h T65_45_2 hfix65_45_2 hinj65_45_2 hcardT65_45_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨45, by decide⟩) (reps rK65) (T65_45_2 i) (hfix65_45_2 i) h)

/-! ### Cell (65, 50) twin -/

def T65_50_2 : Fin 5 → Coordinate 2 := fun i => T65_50list.getD i.val (0,0,0,0,0)

theorem hfix65_50_2 : ∀ i, ((T65_50_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK65)
    ∈ fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK65) :=
  repsFix_of_siftB2 rK65 ⟨50, by decide⟩ T65_50_2 (by decide)

theorem hinj65_50_2 : Function.Injective
    (fun i => ((T65_50_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK65)) :=
  repsInj_of_reduceAux2 rK65 T65_50_2 (by decide)

theorem hcardT65_50_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK65)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK65 ⟨50, by decide⟩ R65_2 hpxR65_2 hcardq65_2 (by decide)).symm

/-- **Cell (65, 50) twin (q=2).** -/
theorem cell65_50_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK65) e = true)
    (h : ↥(reps (⟨50, by decide⟩ : Fin 148))) :
    species (reps (⟨50, by decide⟩ : Fin 148)) h (basisElt (reps rK65) (charOfVec2 rK65 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK65 e (h : Coordinate 2) T65_50_2 i :=
  species_entry_eq_sum rK65 ⟨50, by decide⟩ e heK h T65_50_2 hfix65_50_2 hinj65_50_2 hcardT65_50_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨50, by decide⟩) (reps rK65) (T65_50_2 i) (hfix65_50_2 i) h)

/-! ### Cell (65, 65) twin -/

def T65_65_2 : Fin 5 → Coordinate 2 := fun i => T65_65list.getD i.val (0,0,0,0,0)

theorem hfix65_65_2 : ∀ i, ((T65_65_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK65)
    ∈ fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK65) :=
  repsFix_of_siftB2 rK65 ⟨65, by decide⟩ T65_65_2 (by decide)

theorem hinj65_65_2 : Function.Injective
    (fun i => ((T65_65_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK65)) :=
  repsInj_of_reduceAux2 rK65 T65_65_2 (by decide)

theorem hcardT65_65_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK65)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK65 ⟨65, by decide⟩ R65_2 hpxR65_2 hcardq65_2 (by decide)).symm

/-- **Cell (65, 65) twin (q=2).** -/
theorem cell65_65_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK65) e = true)
    (h : ↥(reps (⟨65, by decide⟩ : Fin 148))) :
    species (reps (⟨65, by decide⟩ : Fin 148)) h (basisElt (reps rK65) (charOfVec2 rK65 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK65 e (h : Coordinate 2) T65_65_2 i :=
  species_entry_eq_sum rK65 ⟨65, by decide⟩ e heK h T65_65_2 hfix65_65_2 hinj65_65_2 hcardT65_65_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨65, by decide⟩) (reps rK65) (T65_65_2 i) (hfix65_65_2 i) h)

end Q2

/-! # K-class rK = 66  (|G/K| = 25) -/

def rK66 : Fin 148 := ⟨66, by decide⟩

def R66list : List Coordinates := [(0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0)]
def R66 : Fin 25 → Coordinate 1 := fun i => R66list.getD i.val (0,0,0,0,0)

theorem hpxR66 : Function.Injective (fun i => reduceAux 1 (basisAt rK66) (R66 i)) := by decide
theorem hcardq66 : Nat.card (Coordinate 1 ⧸ reps rK66) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (66, 0): |T| = 25 -/

def T66_0list : List Coordinates := [(0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0)]
def T66_0 : Fin 25 → Coordinate 1 := fun i => T66_0list.getD i.val (0,0,0,0,0)

theorem hfix66_0 : ∀ i, ((T66_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK66)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66) :=
  repsFix_of_siftB rK66 ⟨0, by decide⟩ T66_0 (by decide)

theorem hinj66_0 : Function.Injective
    (fun i => ((T66_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK66)) :=
  repsInj_of_reduceAux rK66 T66_0 (by decide)

theorem hcardT66_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK66 ⟨0, by decide⟩ R66 hpxR66 hcardq66 (by decide)).symm

/-- **Cell (66, 0).** -/
theorem cell66_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK66) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK66) (charOfVec rK66 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK66 e (h : Coordinate 1) T66_0 i :=
  species_entry_eq_sum rK66 ⟨0, by decide⟩ e heK h T66_0 hfix66_0 hinj66_0 hcardT66_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK66) (T66_0 i) (hfix66_0 i) h)

/-! ## Cell (66, 1): |T| = 25 -/

def T66_1list : List Coordinates := [(0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0)]
def T66_1 : Fin 25 → Coordinate 1 := fun i => T66_1list.getD i.val (0,0,0,0,0)

theorem hfix66_1 : ∀ i, ((T66_1 i : Coordinate 1) : Coordinate 1 ⧸ reps rK66)
    ∈ fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66) :=
  repsFix_of_siftB rK66 ⟨1, by decide⟩ T66_1 (by decide)

theorem hinj66_1 : Function.Injective
    (fun i => ((T66_1 i : Coordinate 1) : Coordinate 1 ⧸ reps rK66)) :=
  repsInj_of_reduceAux rK66 T66_1 (by decide)

theorem hcardT66_1 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK66 ⟨1, by decide⟩ R66 hpxR66 hcardq66 (by decide)).symm

/-- **Cell (66, 1).** -/
theorem cell66_1 (e : List (ZMod 25)) (heK : charOK (basisAt rK66) e = true)
    (h : ↥(reps (⟨1, by decide⟩ : Fin 148))) :
    species (reps (⟨1, by decide⟩ : Fin 148)) h (basisElt (reps rK66) (charOfVec rK66 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK66 e (h : Coordinate 1) T66_1 i :=
  species_entry_eq_sum rK66 ⟨1, by decide⟩ e heK h T66_1 hfix66_1 hinj66_1 hcardT66_1
    (fun i => conj_mem_of_fixedPoints (reps ⟨1, by decide⟩) (reps rK66) (T66_1 i) (hfix66_1 i) h)

/-! ## Cell (66, 12): |T| = 25 -/

def T66_12list : List Coordinates := [(0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0)]
def T66_12 : Fin 25 → Coordinate 1 := fun i => T66_12list.getD i.val (0,0,0,0,0)

theorem hfix66_12 : ∀ i, ((T66_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK66)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66) :=
  repsFix_of_siftB rK66 ⟨12, by decide⟩ T66_12 (by decide)

theorem hinj66_12 : Function.Injective
    (fun i => ((T66_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK66)) :=
  repsInj_of_reduceAux rK66 T66_12 (by decide)

theorem hcardT66_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK66 ⟨12, by decide⟩ R66 hpxR66 hcardq66 (by decide)).symm

/-- **Cell (66, 12).** -/
theorem cell66_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK66) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK66) (charOfVec rK66 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK66 e (h : Coordinate 1) T66_12 i :=
  species_entry_eq_sum rK66 ⟨12, by decide⟩ e heK h T66_12 hfix66_12 hinj66_12 hcardT66_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK66) (T66_12 i) (hfix66_12 i) h)

/-! ## Cell (66, 19): |T| = 25 -/

def T66_19list : List Coordinates := [(0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0)]
def T66_19 : Fin 25 → Coordinate 1 := fun i => T66_19list.getD i.val (0,0,0,0,0)

theorem hfix66_19 : ∀ i, ((T66_19 i : Coordinate 1) : Coordinate 1 ⧸ reps rK66)
    ∈ fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66) :=
  repsFix_of_siftB rK66 ⟨19, by decide⟩ T66_19 (by decide)

theorem hinj66_19 : Function.Injective
    (fun i => ((T66_19 i : Coordinate 1) : Coordinate 1 ⧸ reps rK66)) :=
  repsInj_of_reduceAux rK66 T66_19 (by decide)

theorem hcardT66_19 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK66 ⟨19, by decide⟩ R66 hpxR66 hcardq66 (by decide)).symm

/-- **Cell (66, 19).** -/
theorem cell66_19 (e : List (ZMod 25)) (heK : charOK (basisAt rK66) e = true)
    (h : ↥(reps (⟨19, by decide⟩ : Fin 148))) :
    species (reps (⟨19, by decide⟩ : Fin 148)) h (basisElt (reps rK66) (charOfVec rK66 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK66 e (h : Coordinate 1) T66_19 i :=
  species_entry_eq_sum rK66 ⟨19, by decide⟩ e heK h T66_19 hfix66_19 hinj66_19 hcardT66_19
    (fun i => conj_mem_of_fixedPoints (reps ⟨19, by decide⟩) (reps rK66) (T66_19 i) (hfix66_19 i) h)

/-! ## Cell (66, 30): |T| = 5 -/

def T66_30list : List Coordinates := [(0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0)]
def T66_30 : Fin 5 → Coordinate 1 := fun i => T66_30list.getD i.val (0,0,0,0,0)

theorem hfix66_30 : ∀ i, ((T66_30 i : Coordinate 1) : Coordinate 1 ⧸ reps rK66)
    ∈ fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66) :=
  repsFix_of_siftB rK66 ⟨30, by decide⟩ T66_30 (by decide)

theorem hinj66_30 : Function.Injective
    (fun i => ((T66_30 i : Coordinate 1) : Coordinate 1 ⧸ reps rK66)) :=
  repsInj_of_reduceAux rK66 T66_30 (by decide)

theorem hcardT66_30 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK66 ⟨30, by decide⟩ R66 hpxR66 hcardq66 (by decide)).symm

/-- **Cell (66, 30).** -/
theorem cell66_30 (e : List (ZMod 25)) (heK : charOK (basisAt rK66) e = true)
    (h : ↥(reps (⟨30, by decide⟩ : Fin 148))) :
    species (reps (⟨30, by decide⟩ : Fin 148)) h (basisElt (reps rK66) (charOfVec rK66 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK66 e (h : Coordinate 1) T66_30 i :=
  species_entry_eq_sum rK66 ⟨30, by decide⟩ e heK h T66_30 hfix66_30 hinj66_30 hcardT66_30
    (fun i => conj_mem_of_fixedPoints (reps ⟨30, by decide⟩) (reps rK66) (T66_30 i) (hfix66_30 i) h)

/-! ## Cell (66, 35): |T| = 5 -/

def T66_35list : List Coordinates := [(0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0)]
def T66_35 : Fin 5 → Coordinate 1 := fun i => T66_35list.getD i.val (0,0,0,0,0)

theorem hfix66_35 : ∀ i, ((T66_35 i : Coordinate 1) : Coordinate 1 ⧸ reps rK66)
    ∈ fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66) :=
  repsFix_of_siftB rK66 ⟨35, by decide⟩ T66_35 (by decide)

theorem hinj66_35 : Function.Injective
    (fun i => ((T66_35 i : Coordinate 1) : Coordinate 1 ⧸ reps rK66)) :=
  repsInj_of_reduceAux rK66 T66_35 (by decide)

theorem hcardT66_35 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK66 ⟨35, by decide⟩ R66 hpxR66 hcardq66 (by decide)).symm

/-- **Cell (66, 35).** -/
theorem cell66_35 (e : List (ZMod 25)) (heK : charOK (basisAt rK66) e = true)
    (h : ↥(reps (⟨35, by decide⟩ : Fin 148))) :
    species (reps (⟨35, by decide⟩ : Fin 148)) h (basisElt (reps rK66) (charOfVec rK66 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK66 e (h : Coordinate 1) T66_35 i :=
  species_entry_eq_sum rK66 ⟨35, by decide⟩ e heK h T66_35 hfix66_35 hinj66_35 hcardT66_35
    (fun i => conj_mem_of_fixedPoints (reps ⟨35, by decide⟩) (reps rK66) (T66_35 i) (hfix66_35 i) h)

/-! ## Cell (66, 40): |T| = 5 -/

def T66_40list : List Coordinates := [(0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0)]
def T66_40 : Fin 5 → Coordinate 1 := fun i => T66_40list.getD i.val (0,0,0,0,0)

theorem hfix66_40 : ∀ i, ((T66_40 i : Coordinate 1) : Coordinate 1 ⧸ reps rK66)
    ∈ fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66) :=
  repsFix_of_siftB rK66 ⟨40, by decide⟩ T66_40 (by decide)

theorem hinj66_40 : Function.Injective
    (fun i => ((T66_40 i : Coordinate 1) : Coordinate 1 ⧸ reps rK66)) :=
  repsInj_of_reduceAux rK66 T66_40 (by decide)

theorem hcardT66_40 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK66 ⟨40, by decide⟩ R66 hpxR66 hcardq66 (by decide)).symm

/-- **Cell (66, 40).** -/
theorem cell66_40 (e : List (ZMod 25)) (heK : charOK (basisAt rK66) e = true)
    (h : ↥(reps (⟨40, by decide⟩ : Fin 148))) :
    species (reps (⟨40, by decide⟩ : Fin 148)) h (basisElt (reps rK66) (charOfVec rK66 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK66 e (h : Coordinate 1) T66_40 i :=
  species_entry_eq_sum rK66 ⟨40, by decide⟩ e heK h T66_40 hfix66_40 hinj66_40 hcardT66_40
    (fun i => conj_mem_of_fixedPoints (reps ⟨40, by decide⟩) (reps rK66) (T66_40 i) (hfix66_40 i) h)

/-! ## Cell (66, 45): |T| = 5 -/

def T66_45list : List Coordinates := [(0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0)]
def T66_45 : Fin 5 → Coordinate 1 := fun i => T66_45list.getD i.val (0,0,0,0,0)

theorem hfix66_45 : ∀ i, ((T66_45 i : Coordinate 1) : Coordinate 1 ⧸ reps rK66)
    ∈ fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66) :=
  repsFix_of_siftB rK66 ⟨45, by decide⟩ T66_45 (by decide)

theorem hinj66_45 : Function.Injective
    (fun i => ((T66_45 i : Coordinate 1) : Coordinate 1 ⧸ reps rK66)) :=
  repsInj_of_reduceAux rK66 T66_45 (by decide)

theorem hcardT66_45 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK66 ⟨45, by decide⟩ R66 hpxR66 hcardq66 (by decide)).symm

/-- **Cell (66, 45).** -/
theorem cell66_45 (e : List (ZMod 25)) (heK : charOK (basisAt rK66) e = true)
    (h : ↥(reps (⟨45, by decide⟩ : Fin 148))) :
    species (reps (⟨45, by decide⟩ : Fin 148)) h (basisElt (reps rK66) (charOfVec rK66 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK66 e (h : Coordinate 1) T66_45 i :=
  species_entry_eq_sum rK66 ⟨45, by decide⟩ e heK h T66_45 hfix66_45 hinj66_45 hcardT66_45
    (fun i => conj_mem_of_fixedPoints (reps ⟨45, by decide⟩) (reps rK66) (T66_45 i) (hfix66_45 i) h)

/-! ## Cell (66, 50): |T| = 5 -/

def T66_50list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0)]
def T66_50 : Fin 5 → Coordinate 1 := fun i => T66_50list.getD i.val (0,0,0,0,0)

theorem hfix66_50 : ∀ i, ((T66_50 i : Coordinate 1) : Coordinate 1 ⧸ reps rK66)
    ∈ fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66) :=
  repsFix_of_siftB rK66 ⟨50, by decide⟩ T66_50 (by decide)

theorem hinj66_50 : Function.Injective
    (fun i => ((T66_50 i : Coordinate 1) : Coordinate 1 ⧸ reps rK66)) :=
  repsInj_of_reduceAux rK66 T66_50 (by decide)

theorem hcardT66_50 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK66 ⟨50, by decide⟩ R66 hpxR66 hcardq66 (by decide)).symm

/-- **Cell (66, 50).** -/
theorem cell66_50 (e : List (ZMod 25)) (heK : charOK (basisAt rK66) e = true)
    (h : ↥(reps (⟨50, by decide⟩ : Fin 148))) :
    species (reps (⟨50, by decide⟩ : Fin 148)) h (basisElt (reps rK66) (charOfVec rK66 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK66 e (h : Coordinate 1) T66_50 i :=
  species_entry_eq_sum rK66 ⟨50, by decide⟩ e heK h T66_50 hfix66_50 hinj66_50 hcardT66_50
    (fun i => conj_mem_of_fixedPoints (reps ⟨50, by decide⟩) (reps rK66) (T66_50 i) (hfix66_50 i) h)

/-! ## Cell (66, 66): |T| = 5 -/

def T66_66list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0)]
def T66_66 : Fin 5 → Coordinate 1 := fun i => T66_66list.getD i.val (0,0,0,0,0)

theorem hfix66_66 : ∀ i, ((T66_66 i : Coordinate 1) : Coordinate 1 ⧸ reps rK66)
    ∈ fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66) :=
  repsFix_of_siftB rK66 ⟨66, by decide⟩ T66_66 (by decide)

theorem hinj66_66 : Function.Injective
    (fun i => ((T66_66 i : Coordinate 1) : Coordinate 1 ⧸ reps rK66)) :=
  repsInj_of_reduceAux rK66 T66_66 (by decide)

theorem hcardT66_66 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK66 ⟨66, by decide⟩ R66 hpxR66 hcardq66 (by decide)).symm

/-- **Cell (66, 66).** -/
theorem cell66_66 (e : List (ZMod 25)) (heK : charOK (basisAt rK66) e = true)
    (h : ↥(reps (⟨66, by decide⟩ : Fin 148))) :
    species (reps (⟨66, by decide⟩ : Fin 148)) h (basisElt (reps rK66) (charOfVec rK66 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK66 e (h : Coordinate 1) T66_66 i :=
  species_entry_eq_sum rK66 ⟨66, by decide⟩ e heK h T66_66 hfix66_66 hinj66_66 hcardT66_66
    (fun i => conj_mem_of_fixedPoints (reps ⟨66, by decide⟩) (reps rK66) (T66_66 i) (hfix66_66 i) h)

namespace Q2

def R66_2 : Fin 25 → Coordinate 2 := fun i => R66list.getD i.val (0,0,0,0,0)
theorem hpxR66_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK66) (R66_2 i)) := by decide
theorem hcardq66_2 : Nat.card (Coordinate 2 ⧸ reps rK66) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (66, 0) twin -/

def T66_0_2 : Fin 25 → Coordinate 2 := fun i => T66_0list.getD i.val (0,0,0,0,0)

theorem hfix66_0_2 : ∀ i, ((T66_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK66)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK66) :=
  repsFix_of_siftB2 rK66 ⟨0, by decide⟩ T66_0_2 (by decide)

theorem hinj66_0_2 : Function.Injective
    (fun i => ((T66_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK66)) :=
  repsInj_of_reduceAux2 rK66 T66_0_2 (by decide)

theorem hcardT66_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK66)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK66 ⟨0, by decide⟩ R66_2 hpxR66_2 hcardq66_2 (by decide)).symm

/-- **Cell (66, 0) twin (q=2).** -/
theorem cell66_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK66) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK66) (charOfVec2 rK66 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK66 e (h : Coordinate 2) T66_0_2 i :=
  species_entry_eq_sum rK66 ⟨0, by decide⟩ e heK h T66_0_2 hfix66_0_2 hinj66_0_2 hcardT66_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK66) (T66_0_2 i) (hfix66_0_2 i) h)

/-! ### Cell (66, 1) twin -/

def T66_1_2 : Fin 25 → Coordinate 2 := fun i => T66_1list.getD i.val (0,0,0,0,0)

theorem hfix66_1_2 : ∀ i, ((T66_1_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK66)
    ∈ fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK66) :=
  repsFix_of_siftB2 rK66 ⟨1, by decide⟩ T66_1_2 (by decide)

theorem hinj66_1_2 : Function.Injective
    (fun i => ((T66_1_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK66)) :=
  repsInj_of_reduceAux2 rK66 T66_1_2 (by decide)

theorem hcardT66_1_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK66)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK66 ⟨1, by decide⟩ R66_2 hpxR66_2 hcardq66_2 (by decide)).symm

/-- **Cell (66, 1) twin (q=2).** -/
theorem cell66_1_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK66) e = true)
    (h : ↥(reps (⟨1, by decide⟩ : Fin 148))) :
    species (reps (⟨1, by decide⟩ : Fin 148)) h (basisElt (reps rK66) (charOfVec2 rK66 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK66 e (h : Coordinate 2) T66_1_2 i :=
  species_entry_eq_sum rK66 ⟨1, by decide⟩ e heK h T66_1_2 hfix66_1_2 hinj66_1_2 hcardT66_1_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨1, by decide⟩) (reps rK66) (T66_1_2 i) (hfix66_1_2 i) h)

/-! ### Cell (66, 12) twin -/

def T66_12_2 : Fin 25 → Coordinate 2 := fun i => T66_12list.getD i.val (0,0,0,0,0)

theorem hfix66_12_2 : ∀ i, ((T66_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK66)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK66) :=
  repsFix_of_siftB2 rK66 ⟨12, by decide⟩ T66_12_2 (by decide)

theorem hinj66_12_2 : Function.Injective
    (fun i => ((T66_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK66)) :=
  repsInj_of_reduceAux2 rK66 T66_12_2 (by decide)

theorem hcardT66_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK66)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK66 ⟨12, by decide⟩ R66_2 hpxR66_2 hcardq66_2 (by decide)).symm

/-- **Cell (66, 12) twin (q=2).** -/
theorem cell66_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK66) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK66) (charOfVec2 rK66 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK66 e (h : Coordinate 2) T66_12_2 i :=
  species_entry_eq_sum rK66 ⟨12, by decide⟩ e heK h T66_12_2 hfix66_12_2 hinj66_12_2 hcardT66_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK66) (T66_12_2 i) (hfix66_12_2 i) h)

/-! ### Cell (66, 19) twin -/

def T66_19_2 : Fin 25 → Coordinate 2 := fun i => T66_19list.getD i.val (0,0,0,0,0)

theorem hfix66_19_2 : ∀ i, ((T66_19_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK66)
    ∈ fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK66) :=
  repsFix_of_siftB2 rK66 ⟨19, by decide⟩ T66_19_2 (by decide)

theorem hinj66_19_2 : Function.Injective
    (fun i => ((T66_19_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK66)) :=
  repsInj_of_reduceAux2 rK66 T66_19_2 (by decide)

theorem hcardT66_19_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK66)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK66 ⟨19, by decide⟩ R66_2 hpxR66_2 hcardq66_2 (by decide)).symm

/-- **Cell (66, 19) twin (q=2).** -/
theorem cell66_19_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK66) e = true)
    (h : ↥(reps (⟨19, by decide⟩ : Fin 148))) :
    species (reps (⟨19, by decide⟩ : Fin 148)) h (basisElt (reps rK66) (charOfVec2 rK66 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK66 e (h : Coordinate 2) T66_19_2 i :=
  species_entry_eq_sum rK66 ⟨19, by decide⟩ e heK h T66_19_2 hfix66_19_2 hinj66_19_2 hcardT66_19_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨19, by decide⟩) (reps rK66) (T66_19_2 i) (hfix66_19_2 i) h)

/-! ### Cell (66, 30) twin -/

def T66_30_2 : Fin 5 → Coordinate 2 := fun i => T66_30list.getD i.val (0,0,0,0,0)

theorem hfix66_30_2 : ∀ i, ((T66_30_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK66)
    ∈ fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK66) :=
  repsFix_of_siftB2 rK66 ⟨30, by decide⟩ T66_30_2 (by decide)

theorem hinj66_30_2 : Function.Injective
    (fun i => ((T66_30_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK66)) :=
  repsInj_of_reduceAux2 rK66 T66_30_2 (by decide)

theorem hcardT66_30_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK66)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK66 ⟨30, by decide⟩ R66_2 hpxR66_2 hcardq66_2 (by decide)).symm

/-- **Cell (66, 30) twin (q=2).** -/
theorem cell66_30_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK66) e = true)
    (h : ↥(reps (⟨30, by decide⟩ : Fin 148))) :
    species (reps (⟨30, by decide⟩ : Fin 148)) h (basisElt (reps rK66) (charOfVec2 rK66 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK66 e (h : Coordinate 2) T66_30_2 i :=
  species_entry_eq_sum rK66 ⟨30, by decide⟩ e heK h T66_30_2 hfix66_30_2 hinj66_30_2 hcardT66_30_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨30, by decide⟩) (reps rK66) (T66_30_2 i) (hfix66_30_2 i) h)

/-! ### Cell (66, 35) twin -/

def T66_35_2 : Fin 5 → Coordinate 2 := fun i => T66_35list.getD i.val (0,0,0,0,0)

theorem hfix66_35_2 : ∀ i, ((T66_35_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK66)
    ∈ fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK66) :=
  repsFix_of_siftB2 rK66 ⟨35, by decide⟩ T66_35_2 (by decide)

theorem hinj66_35_2 : Function.Injective
    (fun i => ((T66_35_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK66)) :=
  repsInj_of_reduceAux2 rK66 T66_35_2 (by decide)

theorem hcardT66_35_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK66)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK66 ⟨35, by decide⟩ R66_2 hpxR66_2 hcardq66_2 (by decide)).symm

/-- **Cell (66, 35) twin (q=2).** -/
theorem cell66_35_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK66) e = true)
    (h : ↥(reps (⟨35, by decide⟩ : Fin 148))) :
    species (reps (⟨35, by decide⟩ : Fin 148)) h (basisElt (reps rK66) (charOfVec2 rK66 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK66 e (h : Coordinate 2) T66_35_2 i :=
  species_entry_eq_sum rK66 ⟨35, by decide⟩ e heK h T66_35_2 hfix66_35_2 hinj66_35_2 hcardT66_35_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨35, by decide⟩) (reps rK66) (T66_35_2 i) (hfix66_35_2 i) h)

/-! ### Cell (66, 40) twin -/

def T66_40_2 : Fin 5 → Coordinate 2 := fun i => T66_40list.getD i.val (0,0,0,0,0)

theorem hfix66_40_2 : ∀ i, ((T66_40_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK66)
    ∈ fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK66) :=
  repsFix_of_siftB2 rK66 ⟨40, by decide⟩ T66_40_2 (by decide)

theorem hinj66_40_2 : Function.Injective
    (fun i => ((T66_40_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK66)) :=
  repsInj_of_reduceAux2 rK66 T66_40_2 (by decide)

theorem hcardT66_40_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK66)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK66 ⟨40, by decide⟩ R66_2 hpxR66_2 hcardq66_2 (by decide)).symm

/-- **Cell (66, 40) twin (q=2).** -/
theorem cell66_40_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK66) e = true)
    (h : ↥(reps (⟨40, by decide⟩ : Fin 148))) :
    species (reps (⟨40, by decide⟩ : Fin 148)) h (basisElt (reps rK66) (charOfVec2 rK66 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK66 e (h : Coordinate 2) T66_40_2 i :=
  species_entry_eq_sum rK66 ⟨40, by decide⟩ e heK h T66_40_2 hfix66_40_2 hinj66_40_2 hcardT66_40_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨40, by decide⟩) (reps rK66) (T66_40_2 i) (hfix66_40_2 i) h)

/-! ### Cell (66, 45) twin -/

def T66_45_2 : Fin 5 → Coordinate 2 := fun i => T66_45list.getD i.val (0,0,0,0,0)

theorem hfix66_45_2 : ∀ i, ((T66_45_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK66)
    ∈ fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK66) :=
  repsFix_of_siftB2 rK66 ⟨45, by decide⟩ T66_45_2 (by decide)

theorem hinj66_45_2 : Function.Injective
    (fun i => ((T66_45_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK66)) :=
  repsInj_of_reduceAux2 rK66 T66_45_2 (by decide)

theorem hcardT66_45_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK66)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK66 ⟨45, by decide⟩ R66_2 hpxR66_2 hcardq66_2 (by decide)).symm

/-- **Cell (66, 45) twin (q=2).** -/
theorem cell66_45_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK66) e = true)
    (h : ↥(reps (⟨45, by decide⟩ : Fin 148))) :
    species (reps (⟨45, by decide⟩ : Fin 148)) h (basisElt (reps rK66) (charOfVec2 rK66 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK66 e (h : Coordinate 2) T66_45_2 i :=
  species_entry_eq_sum rK66 ⟨45, by decide⟩ e heK h T66_45_2 hfix66_45_2 hinj66_45_2 hcardT66_45_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨45, by decide⟩) (reps rK66) (T66_45_2 i) (hfix66_45_2 i) h)

/-! ### Cell (66, 50) twin -/

def T66_50_2 : Fin 5 → Coordinate 2 := fun i => T66_50list.getD i.val (0,0,0,0,0)

theorem hfix66_50_2 : ∀ i, ((T66_50_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK66)
    ∈ fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK66) :=
  repsFix_of_siftB2 rK66 ⟨50, by decide⟩ T66_50_2 (by decide)

theorem hinj66_50_2 : Function.Injective
    (fun i => ((T66_50_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK66)) :=
  repsInj_of_reduceAux2 rK66 T66_50_2 (by decide)

theorem hcardT66_50_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK66)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK66 ⟨50, by decide⟩ R66_2 hpxR66_2 hcardq66_2 (by decide)).symm

/-- **Cell (66, 50) twin (q=2).** -/
theorem cell66_50_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK66) e = true)
    (h : ↥(reps (⟨50, by decide⟩ : Fin 148))) :
    species (reps (⟨50, by decide⟩ : Fin 148)) h (basisElt (reps rK66) (charOfVec2 rK66 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK66 e (h : Coordinate 2) T66_50_2 i :=
  species_entry_eq_sum rK66 ⟨50, by decide⟩ e heK h T66_50_2 hfix66_50_2 hinj66_50_2 hcardT66_50_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨50, by decide⟩) (reps rK66) (T66_50_2 i) (hfix66_50_2 i) h)

/-! ### Cell (66, 66) twin -/

def T66_66_2 : Fin 5 → Coordinate 2 := fun i => T66_66list.getD i.val (0,0,0,0,0)

theorem hfix66_66_2 : ∀ i, ((T66_66_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK66)
    ∈ fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK66) :=
  repsFix_of_siftB2 rK66 ⟨66, by decide⟩ T66_66_2 (by decide)

theorem hinj66_66_2 : Function.Injective
    (fun i => ((T66_66_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK66)) :=
  repsInj_of_reduceAux2 rK66 T66_66_2 (by decide)

theorem hcardT66_66_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK66)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK66 ⟨66, by decide⟩ R66_2 hpxR66_2 hcardq66_2 (by decide)).symm

/-- **Cell (66, 66) twin (q=2).** -/
theorem cell66_66_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK66) e = true)
    (h : ↥(reps (⟨66, by decide⟩ : Fin 148))) :
    species (reps (⟨66, by decide⟩ : Fin 148)) h (basisElt (reps rK66) (charOfVec2 rK66 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK66 e (h : Coordinate 2) T66_66_2 i :=
  species_entry_eq_sum rK66 ⟨66, by decide⟩ e heK h T66_66_2 hfix66_66_2 hinj66_66_2 hcardT66_66_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨66, by decide⟩) (reps rK66) (T66_66_2 i) (hfix66_66_2 i) h)

end Q2

/-! # K-class rK = 67  (|G/K| = 25) -/

def rK67 : Fin 148 := ⟨67, by decide⟩

def R67list : List Coordinates := [(0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0)]
def R67 : Fin 25 → Coordinate 1 := fun i => R67list.getD i.val (0,0,0,0,0)

theorem hpxR67 : Function.Injective (fun i => reduceAux 1 (basisAt rK67) (R67 i)) := by decide
theorem hcardq67 : Nat.card (Coordinate 1 ⧸ reps rK67) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (67, 0): |T| = 25 -/

def T67_0list : List Coordinates := [(0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0)]
def T67_0 : Fin 25 → Coordinate 1 := fun i => T67_0list.getD i.val (0,0,0,0,0)

theorem hfix67_0 : ∀ i, ((T67_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK67)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67) :=
  repsFix_of_siftB rK67 ⟨0, by decide⟩ T67_0 (by decide)

theorem hinj67_0 : Function.Injective
    (fun i => ((T67_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK67)) :=
  repsInj_of_reduceAux rK67 T67_0 (by decide)

theorem hcardT67_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK67 ⟨0, by decide⟩ R67 hpxR67 hcardq67 (by decide)).symm

/-- **Cell (67, 0).** -/
theorem cell67_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK67) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK67) (charOfVec rK67 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK67 e (h : Coordinate 1) T67_0 i :=
  species_entry_eq_sum rK67 ⟨0, by decide⟩ e heK h T67_0 hfix67_0 hinj67_0 hcardT67_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK67) (T67_0 i) (hfix67_0 i) h)

/-! ## Cell (67, 7): |T| = 25 -/

def T67_7list : List Coordinates := [(0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0)]
def T67_7 : Fin 25 → Coordinate 1 := fun i => T67_7list.getD i.val (0,0,0,0,0)

theorem hfix67_7 : ∀ i, ((T67_7 i : Coordinate 1) : Coordinate 1 ⧸ reps rK67)
    ∈ fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67) :=
  repsFix_of_siftB rK67 ⟨7, by decide⟩ T67_7 (by decide)

theorem hinj67_7 : Function.Injective
    (fun i => ((T67_7 i : Coordinate 1) : Coordinate 1 ⧸ reps rK67)) :=
  repsInj_of_reduceAux rK67 T67_7 (by decide)

theorem hcardT67_7 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK67 ⟨7, by decide⟩ R67 hpxR67 hcardq67 (by decide)).symm

/-- **Cell (67, 7).** -/
theorem cell67_7 (e : List (ZMod 25)) (heK : charOK (basisAt rK67) e = true)
    (h : ↥(reps (⟨7, by decide⟩ : Fin 148))) :
    species (reps (⟨7, by decide⟩ : Fin 148)) h (basisElt (reps rK67) (charOfVec rK67 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK67 e (h : Coordinate 1) T67_7 i :=
  species_entry_eq_sum rK67 ⟨7, by decide⟩ e heK h T67_7 hfix67_7 hinj67_7 hcardT67_7
    (fun i => conj_mem_of_fixedPoints (reps ⟨7, by decide⟩) (reps rK67) (T67_7 i) (hfix67_7 i) h)

/-! ## Cell (67, 12): |T| = 25 -/

def T67_12list : List Coordinates := [(0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0)]
def T67_12 : Fin 25 → Coordinate 1 := fun i => T67_12list.getD i.val (0,0,0,0,0)

theorem hfix67_12 : ∀ i, ((T67_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK67)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67) :=
  repsFix_of_siftB rK67 ⟨12, by decide⟩ T67_12 (by decide)

theorem hinj67_12 : Function.Injective
    (fun i => ((T67_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK67)) :=
  repsInj_of_reduceAux rK67 T67_12 (by decide)

theorem hcardT67_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK67 ⟨12, by decide⟩ R67 hpxR67 hcardq67 (by decide)).symm

/-- **Cell (67, 12).** -/
theorem cell67_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK67) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK67) (charOfVec rK67 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK67 e (h : Coordinate 1) T67_12 i :=
  species_entry_eq_sum rK67 ⟨12, by decide⟩ e heK h T67_12 hfix67_12 hinj67_12 hcardT67_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK67) (T67_12 i) (hfix67_12 i) h)

/-! ## Cell (67, 25): |T| = 25 -/

def T67_25list : List Coordinates := [(0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0)]
def T67_25 : Fin 25 → Coordinate 1 := fun i => T67_25list.getD i.val (0,0,0,0,0)

theorem hfix67_25 : ∀ i, ((T67_25 i : Coordinate 1) : Coordinate 1 ⧸ reps rK67)
    ∈ fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67) :=
  repsFix_of_siftB rK67 ⟨25, by decide⟩ T67_25 (by decide)

theorem hinj67_25 : Function.Injective
    (fun i => ((T67_25 i : Coordinate 1) : Coordinate 1 ⧸ reps rK67)) :=
  repsInj_of_reduceAux rK67 T67_25 (by decide)

theorem hcardT67_25 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK67 ⟨25, by decide⟩ R67 hpxR67 hcardq67 (by decide)).symm

/-- **Cell (67, 25).** -/
theorem cell67_25 (e : List (ZMod 25)) (heK : charOK (basisAt rK67) e = true)
    (h : ↥(reps (⟨25, by decide⟩ : Fin 148))) :
    species (reps (⟨25, by decide⟩ : Fin 148)) h (basisElt (reps rK67) (charOfVec rK67 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK67 e (h : Coordinate 1) T67_25 i :=
  species_entry_eq_sum rK67 ⟨25, by decide⟩ e heK h T67_25 hfix67_25 hinj67_25 hcardT67_25
    (fun i => conj_mem_of_fixedPoints (reps ⟨25, by decide⟩) (reps rK67) (T67_25 i) (hfix67_25 i) h)

/-! ## Cell (67, 30): |T| = 5 -/

def T67_30list : List Coordinates := [(0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0)]
def T67_30 : Fin 5 → Coordinate 1 := fun i => T67_30list.getD i.val (0,0,0,0,0)

theorem hfix67_30 : ∀ i, ((T67_30 i : Coordinate 1) : Coordinate 1 ⧸ reps rK67)
    ∈ fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67) :=
  repsFix_of_siftB rK67 ⟨30, by decide⟩ T67_30 (by decide)

theorem hinj67_30 : Function.Injective
    (fun i => ((T67_30 i : Coordinate 1) : Coordinate 1 ⧸ reps rK67)) :=
  repsInj_of_reduceAux rK67 T67_30 (by decide)

theorem hcardT67_30 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK67 ⟨30, by decide⟩ R67 hpxR67 hcardq67 (by decide)).symm

/-- **Cell (67, 30).** -/
theorem cell67_30 (e : List (ZMod 25)) (heK : charOK (basisAt rK67) e = true)
    (h : ↥(reps (⟨30, by decide⟩ : Fin 148))) :
    species (reps (⟨30, by decide⟩ : Fin 148)) h (basisElt (reps rK67) (charOfVec rK67 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK67 e (h : Coordinate 1) T67_30 i :=
  species_entry_eq_sum rK67 ⟨30, by decide⟩ e heK h T67_30 hfix67_30 hinj67_30 hcardT67_30
    (fun i => conj_mem_of_fixedPoints (reps ⟨30, by decide⟩) (reps rK67) (T67_30 i) (hfix67_30 i) h)

/-! ## Cell (67, 35): |T| = 5 -/

def T67_35list : List Coordinates := [(0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0)]
def T67_35 : Fin 5 → Coordinate 1 := fun i => T67_35list.getD i.val (0,0,0,0,0)

theorem hfix67_35 : ∀ i, ((T67_35 i : Coordinate 1) : Coordinate 1 ⧸ reps rK67)
    ∈ fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67) :=
  repsFix_of_siftB rK67 ⟨35, by decide⟩ T67_35 (by decide)

theorem hinj67_35 : Function.Injective
    (fun i => ((T67_35 i : Coordinate 1) : Coordinate 1 ⧸ reps rK67)) :=
  repsInj_of_reduceAux rK67 T67_35 (by decide)

theorem hcardT67_35 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK67 ⟨35, by decide⟩ R67 hpxR67 hcardq67 (by decide)).symm

/-- **Cell (67, 35).** -/
theorem cell67_35 (e : List (ZMod 25)) (heK : charOK (basisAt rK67) e = true)
    (h : ↥(reps (⟨35, by decide⟩ : Fin 148))) :
    species (reps (⟨35, by decide⟩ : Fin 148)) h (basisElt (reps rK67) (charOfVec rK67 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK67 e (h : Coordinate 1) T67_35 i :=
  species_entry_eq_sum rK67 ⟨35, by decide⟩ e heK h T67_35 hfix67_35 hinj67_35 hcardT67_35
    (fun i => conj_mem_of_fixedPoints (reps ⟨35, by decide⟩) (reps rK67) (T67_35 i) (hfix67_35 i) h)

/-! ## Cell (67, 40): |T| = 5 -/

def T67_40list : List Coordinates := [(0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0)]
def T67_40 : Fin 5 → Coordinate 1 := fun i => T67_40list.getD i.val (0,0,0,0,0)

theorem hfix67_40 : ∀ i, ((T67_40 i : Coordinate 1) : Coordinate 1 ⧸ reps rK67)
    ∈ fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67) :=
  repsFix_of_siftB rK67 ⟨40, by decide⟩ T67_40 (by decide)

theorem hinj67_40 : Function.Injective
    (fun i => ((T67_40 i : Coordinate 1) : Coordinate 1 ⧸ reps rK67)) :=
  repsInj_of_reduceAux rK67 T67_40 (by decide)

theorem hcardT67_40 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK67 ⟨40, by decide⟩ R67 hpxR67 hcardq67 (by decide)).symm

/-- **Cell (67, 40).** -/
theorem cell67_40 (e : List (ZMod 25)) (heK : charOK (basisAt rK67) e = true)
    (h : ↥(reps (⟨40, by decide⟩ : Fin 148))) :
    species (reps (⟨40, by decide⟩ : Fin 148)) h (basisElt (reps rK67) (charOfVec rK67 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK67 e (h : Coordinate 1) T67_40 i :=
  species_entry_eq_sum rK67 ⟨40, by decide⟩ e heK h T67_40 hfix67_40 hinj67_40 hcardT67_40
    (fun i => conj_mem_of_fixedPoints (reps ⟨40, by decide⟩) (reps rK67) (T67_40 i) (hfix67_40 i) h)

/-! ## Cell (67, 45): |T| = 5 -/

def T67_45list : List Coordinates := [(0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0)]
def T67_45 : Fin 5 → Coordinate 1 := fun i => T67_45list.getD i.val (0,0,0,0,0)

theorem hfix67_45 : ∀ i, ((T67_45 i : Coordinate 1) : Coordinate 1 ⧸ reps rK67)
    ∈ fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67) :=
  repsFix_of_siftB rK67 ⟨45, by decide⟩ T67_45 (by decide)

theorem hinj67_45 : Function.Injective
    (fun i => ((T67_45 i : Coordinate 1) : Coordinate 1 ⧸ reps rK67)) :=
  repsInj_of_reduceAux rK67 T67_45 (by decide)

theorem hcardT67_45 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK67 ⟨45, by decide⟩ R67 hpxR67 hcardq67 (by decide)).symm

/-- **Cell (67, 45).** -/
theorem cell67_45 (e : List (ZMod 25)) (heK : charOK (basisAt rK67) e = true)
    (h : ↥(reps (⟨45, by decide⟩ : Fin 148))) :
    species (reps (⟨45, by decide⟩ : Fin 148)) h (basisElt (reps rK67) (charOfVec rK67 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK67 e (h : Coordinate 1) T67_45 i :=
  species_entry_eq_sum rK67 ⟨45, by decide⟩ e heK h T67_45 hfix67_45 hinj67_45 hcardT67_45
    (fun i => conj_mem_of_fixedPoints (reps ⟨45, by decide⟩) (reps rK67) (T67_45 i) (hfix67_45 i) h)

/-! ## Cell (67, 50): |T| = 5 -/

def T67_50list : List Coordinates := [(0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0)]
def T67_50 : Fin 5 → Coordinate 1 := fun i => T67_50list.getD i.val (0,0,0,0,0)

theorem hfix67_50 : ∀ i, ((T67_50 i : Coordinate 1) : Coordinate 1 ⧸ reps rK67)
    ∈ fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67) :=
  repsFix_of_siftB rK67 ⟨50, by decide⟩ T67_50 (by decide)

theorem hinj67_50 : Function.Injective
    (fun i => ((T67_50 i : Coordinate 1) : Coordinate 1 ⧸ reps rK67)) :=
  repsInj_of_reduceAux rK67 T67_50 (by decide)

theorem hcardT67_50 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK67 ⟨50, by decide⟩ R67 hpxR67 hcardq67 (by decide)).symm

/-- **Cell (67, 50).** -/
theorem cell67_50 (e : List (ZMod 25)) (heK : charOK (basisAt rK67) e = true)
    (h : ↥(reps (⟨50, by decide⟩ : Fin 148))) :
    species (reps (⟨50, by decide⟩ : Fin 148)) h (basisElt (reps rK67) (charOfVec rK67 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK67 e (h : Coordinate 1) T67_50 i :=
  species_entry_eq_sum rK67 ⟨50, by decide⟩ e heK h T67_50 hfix67_50 hinj67_50 hcardT67_50
    (fun i => conj_mem_of_fixedPoints (reps ⟨50, by decide⟩) (reps rK67) (T67_50 i) (hfix67_50 i) h)

/-! ## Cell (67, 67): |T| = 5 -/

def T67_67list : List Coordinates := [(0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0)]
def T67_67 : Fin 5 → Coordinate 1 := fun i => T67_67list.getD i.val (0,0,0,0,0)

theorem hfix67_67 : ∀ i, ((T67_67 i : Coordinate 1) : Coordinate 1 ⧸ reps rK67)
    ∈ fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67) :=
  repsFix_of_siftB rK67 ⟨67, by decide⟩ T67_67 (by decide)

theorem hinj67_67 : Function.Injective
    (fun i => ((T67_67 i : Coordinate 1) : Coordinate 1 ⧸ reps rK67)) :=
  repsInj_of_reduceAux rK67 T67_67 (by decide)

theorem hcardT67_67 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK67 ⟨67, by decide⟩ R67 hpxR67 hcardq67 (by decide)).symm

/-- **Cell (67, 67).** -/
theorem cell67_67 (e : List (ZMod 25)) (heK : charOK (basisAt rK67) e = true)
    (h : ↥(reps (⟨67, by decide⟩ : Fin 148))) :
    species (reps (⟨67, by decide⟩ : Fin 148)) h (basisElt (reps rK67) (charOfVec rK67 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK67 e (h : Coordinate 1) T67_67 i :=
  species_entry_eq_sum rK67 ⟨67, by decide⟩ e heK h T67_67 hfix67_67 hinj67_67 hcardT67_67
    (fun i => conj_mem_of_fixedPoints (reps ⟨67, by decide⟩) (reps rK67) (T67_67 i) (hfix67_67 i) h)

namespace Q2

def R67_2 : Fin 25 → Coordinate 2 := fun i => R67list.getD i.val (0,0,0,0,0)
theorem hpxR67_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK67) (R67_2 i)) := by decide
theorem hcardq67_2 : Nat.card (Coordinate 2 ⧸ reps rK67) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (67, 0) twin -/

def T67_0_2 : Fin 25 → Coordinate 2 := fun i => T67_0list.getD i.val (0,0,0,0,0)

theorem hfix67_0_2 : ∀ i, ((T67_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK67)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK67) :=
  repsFix_of_siftB2 rK67 ⟨0, by decide⟩ T67_0_2 (by decide)

theorem hinj67_0_2 : Function.Injective
    (fun i => ((T67_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK67)) :=
  repsInj_of_reduceAux2 rK67 T67_0_2 (by decide)

theorem hcardT67_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK67)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK67 ⟨0, by decide⟩ R67_2 hpxR67_2 hcardq67_2 (by decide)).symm

/-- **Cell (67, 0) twin (q=2).** -/
theorem cell67_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK67) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK67) (charOfVec2 rK67 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK67 e (h : Coordinate 2) T67_0_2 i :=
  species_entry_eq_sum rK67 ⟨0, by decide⟩ e heK h T67_0_2 hfix67_0_2 hinj67_0_2 hcardT67_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK67) (T67_0_2 i) (hfix67_0_2 i) h)

/-! ### Cell (67, 7) twin -/

def T67_7_2 : Fin 25 → Coordinate 2 := fun i => T67_7list.getD i.val (0,0,0,0,0)

theorem hfix67_7_2 : ∀ i, ((T67_7_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK67)
    ∈ fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK67) :=
  repsFix_of_siftB2 rK67 ⟨7, by decide⟩ T67_7_2 (by decide)

theorem hinj67_7_2 : Function.Injective
    (fun i => ((T67_7_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK67)) :=
  repsInj_of_reduceAux2 rK67 T67_7_2 (by decide)

theorem hcardT67_7_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK67)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK67 ⟨7, by decide⟩ R67_2 hpxR67_2 hcardq67_2 (by decide)).symm

/-- **Cell (67, 7) twin (q=2).** -/
theorem cell67_7_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK67) e = true)
    (h : ↥(reps (⟨7, by decide⟩ : Fin 148))) :
    species (reps (⟨7, by decide⟩ : Fin 148)) h (basisElt (reps rK67) (charOfVec2 rK67 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK67 e (h : Coordinate 2) T67_7_2 i :=
  species_entry_eq_sum rK67 ⟨7, by decide⟩ e heK h T67_7_2 hfix67_7_2 hinj67_7_2 hcardT67_7_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨7, by decide⟩) (reps rK67) (T67_7_2 i) (hfix67_7_2 i) h)

/-! ### Cell (67, 12) twin -/

def T67_12_2 : Fin 25 → Coordinate 2 := fun i => T67_12list.getD i.val (0,0,0,0,0)

theorem hfix67_12_2 : ∀ i, ((T67_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK67)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK67) :=
  repsFix_of_siftB2 rK67 ⟨12, by decide⟩ T67_12_2 (by decide)

theorem hinj67_12_2 : Function.Injective
    (fun i => ((T67_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK67)) :=
  repsInj_of_reduceAux2 rK67 T67_12_2 (by decide)

theorem hcardT67_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK67)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK67 ⟨12, by decide⟩ R67_2 hpxR67_2 hcardq67_2 (by decide)).symm

/-- **Cell (67, 12) twin (q=2).** -/
theorem cell67_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK67) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK67) (charOfVec2 rK67 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK67 e (h : Coordinate 2) T67_12_2 i :=
  species_entry_eq_sum rK67 ⟨12, by decide⟩ e heK h T67_12_2 hfix67_12_2 hinj67_12_2 hcardT67_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK67) (T67_12_2 i) (hfix67_12_2 i) h)

/-! ### Cell (67, 25) twin -/

def T67_25_2 : Fin 25 → Coordinate 2 := fun i => T67_25list.getD i.val (0,0,0,0,0)

theorem hfix67_25_2 : ∀ i, ((T67_25_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK67)
    ∈ fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK67) :=
  repsFix_of_siftB2 rK67 ⟨25, by decide⟩ T67_25_2 (by decide)

theorem hinj67_25_2 : Function.Injective
    (fun i => ((T67_25_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK67)) :=
  repsInj_of_reduceAux2 rK67 T67_25_2 (by decide)

theorem hcardT67_25_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK67)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK67 ⟨25, by decide⟩ R67_2 hpxR67_2 hcardq67_2 (by decide)).symm

/-- **Cell (67, 25) twin (q=2).** -/
theorem cell67_25_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK67) e = true)
    (h : ↥(reps (⟨25, by decide⟩ : Fin 148))) :
    species (reps (⟨25, by decide⟩ : Fin 148)) h (basisElt (reps rK67) (charOfVec2 rK67 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK67 e (h : Coordinate 2) T67_25_2 i :=
  species_entry_eq_sum rK67 ⟨25, by decide⟩ e heK h T67_25_2 hfix67_25_2 hinj67_25_2 hcardT67_25_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨25, by decide⟩) (reps rK67) (T67_25_2 i) (hfix67_25_2 i) h)

/-! ### Cell (67, 30) twin -/

def T67_30_2 : Fin 5 → Coordinate 2 := fun i => T67_30list.getD i.val (0,0,0,0,0)

theorem hfix67_30_2 : ∀ i, ((T67_30_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK67)
    ∈ fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK67) :=
  repsFix_of_siftB2 rK67 ⟨30, by decide⟩ T67_30_2 (by decide)

theorem hinj67_30_2 : Function.Injective
    (fun i => ((T67_30_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK67)) :=
  repsInj_of_reduceAux2 rK67 T67_30_2 (by decide)

theorem hcardT67_30_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK67)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK67 ⟨30, by decide⟩ R67_2 hpxR67_2 hcardq67_2 (by decide)).symm

/-- **Cell (67, 30) twin (q=2).** -/
theorem cell67_30_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK67) e = true)
    (h : ↥(reps (⟨30, by decide⟩ : Fin 148))) :
    species (reps (⟨30, by decide⟩ : Fin 148)) h (basisElt (reps rK67) (charOfVec2 rK67 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK67 e (h : Coordinate 2) T67_30_2 i :=
  species_entry_eq_sum rK67 ⟨30, by decide⟩ e heK h T67_30_2 hfix67_30_2 hinj67_30_2 hcardT67_30_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨30, by decide⟩) (reps rK67) (T67_30_2 i) (hfix67_30_2 i) h)

/-! ### Cell (67, 35) twin -/

def T67_35_2 : Fin 5 → Coordinate 2 := fun i => T67_35list.getD i.val (0,0,0,0,0)

theorem hfix67_35_2 : ∀ i, ((T67_35_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK67)
    ∈ fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK67) :=
  repsFix_of_siftB2 rK67 ⟨35, by decide⟩ T67_35_2 (by decide)

theorem hinj67_35_2 : Function.Injective
    (fun i => ((T67_35_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK67)) :=
  repsInj_of_reduceAux2 rK67 T67_35_2 (by decide)

theorem hcardT67_35_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK67)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK67 ⟨35, by decide⟩ R67_2 hpxR67_2 hcardq67_2 (by decide)).symm

/-- **Cell (67, 35) twin (q=2).** -/
theorem cell67_35_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK67) e = true)
    (h : ↥(reps (⟨35, by decide⟩ : Fin 148))) :
    species (reps (⟨35, by decide⟩ : Fin 148)) h (basisElt (reps rK67) (charOfVec2 rK67 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK67 e (h : Coordinate 2) T67_35_2 i :=
  species_entry_eq_sum rK67 ⟨35, by decide⟩ e heK h T67_35_2 hfix67_35_2 hinj67_35_2 hcardT67_35_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨35, by decide⟩) (reps rK67) (T67_35_2 i) (hfix67_35_2 i) h)

/-! ### Cell (67, 40) twin -/

def T67_40_2 : Fin 5 → Coordinate 2 := fun i => T67_40list.getD i.val (0,0,0,0,0)

theorem hfix67_40_2 : ∀ i, ((T67_40_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK67)
    ∈ fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK67) :=
  repsFix_of_siftB2 rK67 ⟨40, by decide⟩ T67_40_2 (by decide)

theorem hinj67_40_2 : Function.Injective
    (fun i => ((T67_40_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK67)) :=
  repsInj_of_reduceAux2 rK67 T67_40_2 (by decide)

theorem hcardT67_40_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK67)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK67 ⟨40, by decide⟩ R67_2 hpxR67_2 hcardq67_2 (by decide)).symm

/-- **Cell (67, 40) twin (q=2).** -/
theorem cell67_40_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK67) e = true)
    (h : ↥(reps (⟨40, by decide⟩ : Fin 148))) :
    species (reps (⟨40, by decide⟩ : Fin 148)) h (basisElt (reps rK67) (charOfVec2 rK67 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK67 e (h : Coordinate 2) T67_40_2 i :=
  species_entry_eq_sum rK67 ⟨40, by decide⟩ e heK h T67_40_2 hfix67_40_2 hinj67_40_2 hcardT67_40_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨40, by decide⟩) (reps rK67) (T67_40_2 i) (hfix67_40_2 i) h)

/-! ### Cell (67, 45) twin -/

def T67_45_2 : Fin 5 → Coordinate 2 := fun i => T67_45list.getD i.val (0,0,0,0,0)

theorem hfix67_45_2 : ∀ i, ((T67_45_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK67)
    ∈ fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK67) :=
  repsFix_of_siftB2 rK67 ⟨45, by decide⟩ T67_45_2 (by decide)

theorem hinj67_45_2 : Function.Injective
    (fun i => ((T67_45_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK67)) :=
  repsInj_of_reduceAux2 rK67 T67_45_2 (by decide)

theorem hcardT67_45_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK67)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK67 ⟨45, by decide⟩ R67_2 hpxR67_2 hcardq67_2 (by decide)).symm

/-- **Cell (67, 45) twin (q=2).** -/
theorem cell67_45_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK67) e = true)
    (h : ↥(reps (⟨45, by decide⟩ : Fin 148))) :
    species (reps (⟨45, by decide⟩ : Fin 148)) h (basisElt (reps rK67) (charOfVec2 rK67 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK67 e (h : Coordinate 2) T67_45_2 i :=
  species_entry_eq_sum rK67 ⟨45, by decide⟩ e heK h T67_45_2 hfix67_45_2 hinj67_45_2 hcardT67_45_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨45, by decide⟩) (reps rK67) (T67_45_2 i) (hfix67_45_2 i) h)

/-! ### Cell (67, 50) twin -/

def T67_50_2 : Fin 5 → Coordinate 2 := fun i => T67_50list.getD i.val (0,0,0,0,0)

theorem hfix67_50_2 : ∀ i, ((T67_50_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK67)
    ∈ fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK67) :=
  repsFix_of_siftB2 rK67 ⟨50, by decide⟩ T67_50_2 (by decide)

theorem hinj67_50_2 : Function.Injective
    (fun i => ((T67_50_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK67)) :=
  repsInj_of_reduceAux2 rK67 T67_50_2 (by decide)

theorem hcardT67_50_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK67)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK67 ⟨50, by decide⟩ R67_2 hpxR67_2 hcardq67_2 (by decide)).symm

/-- **Cell (67, 50) twin (q=2).** -/
theorem cell67_50_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK67) e = true)
    (h : ↥(reps (⟨50, by decide⟩ : Fin 148))) :
    species (reps (⟨50, by decide⟩ : Fin 148)) h (basisElt (reps rK67) (charOfVec2 rK67 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK67 e (h : Coordinate 2) T67_50_2 i :=
  species_entry_eq_sum rK67 ⟨50, by decide⟩ e heK h T67_50_2 hfix67_50_2 hinj67_50_2 hcardT67_50_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨50, by decide⟩) (reps rK67) (T67_50_2 i) (hfix67_50_2 i) h)

/-! ### Cell (67, 67) twin -/

def T67_67_2 : Fin 5 → Coordinate 2 := fun i => T67_67list.getD i.val (0,0,0,0,0)

theorem hfix67_67_2 : ∀ i, ((T67_67_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK67)
    ∈ fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK67) :=
  repsFix_of_siftB2 rK67 ⟨67, by decide⟩ T67_67_2 (by decide)

theorem hinj67_67_2 : Function.Injective
    (fun i => ((T67_67_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK67)) :=
  repsInj_of_reduceAux2 rK67 T67_67_2 (by decide)

theorem hcardT67_67_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK67)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK67 ⟨67, by decide⟩ R67_2 hpxR67_2 hcardq67_2 (by decide)).symm

/-- **Cell (67, 67) twin (q=2).** -/
theorem cell67_67_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK67) e = true)
    (h : ↥(reps (⟨67, by decide⟩ : Fin 148))) :
    species (reps (⟨67, by decide⟩ : Fin 148)) h (basisElt (reps rK67) (charOfVec2 rK67 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK67 e (h : Coordinate 2) T67_67_2 i :=
  species_entry_eq_sum rK67 ⟨67, by decide⟩ e heK h T67_67_2 hfix67_67_2 hinj67_67_2 hcardT67_67_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨67, by decide⟩) (reps rK67) (T67_67_2 i) (hfix67_67_2 i) h)

end Q2

/-! # K-class rK = 68  (|G/K| = 25) -/

def rK68 : Fin 148 := ⟨68, by decide⟩

def R68list : List Coordinates := [(0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0)]
def R68 : Fin 25 → Coordinate 1 := fun i => R68list.getD i.val (0,0,0,0,0)

theorem hpxR68 : Function.Injective (fun i => reduceAux 1 (basisAt rK68) (R68 i)) := by decide
theorem hcardq68 : Nat.card (Coordinate 1 ⧸ reps rK68) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (68, 0): |T| = 25 -/

def T68_0list : List Coordinates := [(0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0)]
def T68_0 : Fin 25 → Coordinate 1 := fun i => T68_0list.getD i.val (0,0,0,0,0)

theorem hfix68_0 : ∀ i, ((T68_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK68)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68) :=
  repsFix_of_siftB rK68 ⟨0, by decide⟩ T68_0 (by decide)

theorem hinj68_0 : Function.Injective
    (fun i => ((T68_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK68)) :=
  repsInj_of_reduceAux rK68 T68_0 (by decide)

theorem hcardT68_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK68 ⟨0, by decide⟩ R68 hpxR68 hcardq68 (by decide)).symm

/-- **Cell (68, 0).** -/
theorem cell68_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK68) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK68) (charOfVec rK68 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK68 e (h : Coordinate 1) T68_0 i :=
  species_entry_eq_sum rK68 ⟨0, by decide⟩ e heK h T68_0 hfix68_0 hinj68_0 hcardT68_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK68) (T68_0 i) (hfix68_0 i) h)

/-! ## Cell (68, 6): |T| = 25 -/

def T68_6list : List Coordinates := [(0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0)]
def T68_6 : Fin 25 → Coordinate 1 := fun i => T68_6list.getD i.val (0,0,0,0,0)

theorem hfix68_6 : ∀ i, ((T68_6 i : Coordinate 1) : Coordinate 1 ⧸ reps rK68)
    ∈ fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68) :=
  repsFix_of_siftB rK68 ⟨6, by decide⟩ T68_6 (by decide)

theorem hinj68_6 : Function.Injective
    (fun i => ((T68_6 i : Coordinate 1) : Coordinate 1 ⧸ reps rK68)) :=
  repsInj_of_reduceAux rK68 T68_6 (by decide)

theorem hcardT68_6 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK68 ⟨6, by decide⟩ R68 hpxR68 hcardq68 (by decide)).symm

/-- **Cell (68, 6).** -/
theorem cell68_6 (e : List (ZMod 25)) (heK : charOK (basisAt rK68) e = true)
    (h : ↥(reps (⟨6, by decide⟩ : Fin 148))) :
    species (reps (⟨6, by decide⟩ : Fin 148)) h (basisElt (reps rK68) (charOfVec rK68 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK68 e (h : Coordinate 1) T68_6 i :=
  species_entry_eq_sum rK68 ⟨6, by decide⟩ e heK h T68_6 hfix68_6 hinj68_6 hcardT68_6
    (fun i => conj_mem_of_fixedPoints (reps ⟨6, by decide⟩) (reps rK68) (T68_6 i) (hfix68_6 i) h)

/-! ## Cell (68, 12): |T| = 25 -/

def T68_12list : List Coordinates := [(0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0)]
def T68_12 : Fin 25 → Coordinate 1 := fun i => T68_12list.getD i.val (0,0,0,0,0)

theorem hfix68_12 : ∀ i, ((T68_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK68)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68) :=
  repsFix_of_siftB rK68 ⟨12, by decide⟩ T68_12 (by decide)

theorem hinj68_12 : Function.Injective
    (fun i => ((T68_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK68)) :=
  repsInj_of_reduceAux rK68 T68_12 (by decide)

theorem hcardT68_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK68 ⟨12, by decide⟩ R68 hpxR68 hcardq68 (by decide)).symm

/-- **Cell (68, 12).** -/
theorem cell68_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK68) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK68) (charOfVec rK68 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK68 e (h : Coordinate 1) T68_12 i :=
  species_entry_eq_sum rK68 ⟨12, by decide⟩ e heK h T68_12 hfix68_12 hinj68_12 hcardT68_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK68) (T68_12 i) (hfix68_12 i) h)

/-! ## Cell (68, 24): |T| = 25 -/

def T68_24list : List Coordinates := [(0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0)]
def T68_24 : Fin 25 → Coordinate 1 := fun i => T68_24list.getD i.val (0,0,0,0,0)

theorem hfix68_24 : ∀ i, ((T68_24 i : Coordinate 1) : Coordinate 1 ⧸ reps rK68)
    ∈ fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68) :=
  repsFix_of_siftB rK68 ⟨24, by decide⟩ T68_24 (by decide)

theorem hinj68_24 : Function.Injective
    (fun i => ((T68_24 i : Coordinate 1) : Coordinate 1 ⧸ reps rK68)) :=
  repsInj_of_reduceAux rK68 T68_24 (by decide)

theorem hcardT68_24 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK68 ⟨24, by decide⟩ R68 hpxR68 hcardq68 (by decide)).symm

/-- **Cell (68, 24).** -/
theorem cell68_24 (e : List (ZMod 25)) (heK : charOK (basisAt rK68) e = true)
    (h : ↥(reps (⟨24, by decide⟩ : Fin 148))) :
    species (reps (⟨24, by decide⟩ : Fin 148)) h (basisElt (reps rK68) (charOfVec rK68 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK68 e (h : Coordinate 1) T68_24 i :=
  species_entry_eq_sum rK68 ⟨24, by decide⟩ e heK h T68_24 hfix68_24 hinj68_24 hcardT68_24
    (fun i => conj_mem_of_fixedPoints (reps ⟨24, by decide⟩) (reps rK68) (T68_24 i) (hfix68_24 i) h)

/-! ## Cell (68, 30): |T| = 5 -/

def T68_30list : List Coordinates := [(0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0)]
def T68_30 : Fin 5 → Coordinate 1 := fun i => T68_30list.getD i.val (0,0,0,0,0)

theorem hfix68_30 : ∀ i, ((T68_30 i : Coordinate 1) : Coordinate 1 ⧸ reps rK68)
    ∈ fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68) :=
  repsFix_of_siftB rK68 ⟨30, by decide⟩ T68_30 (by decide)

theorem hinj68_30 : Function.Injective
    (fun i => ((T68_30 i : Coordinate 1) : Coordinate 1 ⧸ reps rK68)) :=
  repsInj_of_reduceAux rK68 T68_30 (by decide)

theorem hcardT68_30 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK68 ⟨30, by decide⟩ R68 hpxR68 hcardq68 (by decide)).symm

/-- **Cell (68, 30).** -/
theorem cell68_30 (e : List (ZMod 25)) (heK : charOK (basisAt rK68) e = true)
    (h : ↥(reps (⟨30, by decide⟩ : Fin 148))) :
    species (reps (⟨30, by decide⟩ : Fin 148)) h (basisElt (reps rK68) (charOfVec rK68 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK68 e (h : Coordinate 1) T68_30 i :=
  species_entry_eq_sum rK68 ⟨30, by decide⟩ e heK h T68_30 hfix68_30 hinj68_30 hcardT68_30
    (fun i => conj_mem_of_fixedPoints (reps ⟨30, by decide⟩) (reps rK68) (T68_30 i) (hfix68_30 i) h)

/-! ## Cell (68, 35): |T| = 5 -/

def T68_35list : List Coordinates := [(0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0)]
def T68_35 : Fin 5 → Coordinate 1 := fun i => T68_35list.getD i.val (0,0,0,0,0)

theorem hfix68_35 : ∀ i, ((T68_35 i : Coordinate 1) : Coordinate 1 ⧸ reps rK68)
    ∈ fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68) :=
  repsFix_of_siftB rK68 ⟨35, by decide⟩ T68_35 (by decide)

theorem hinj68_35 : Function.Injective
    (fun i => ((T68_35 i : Coordinate 1) : Coordinate 1 ⧸ reps rK68)) :=
  repsInj_of_reduceAux rK68 T68_35 (by decide)

theorem hcardT68_35 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK68 ⟨35, by decide⟩ R68 hpxR68 hcardq68 (by decide)).symm

/-- **Cell (68, 35).** -/
theorem cell68_35 (e : List (ZMod 25)) (heK : charOK (basisAt rK68) e = true)
    (h : ↥(reps (⟨35, by decide⟩ : Fin 148))) :
    species (reps (⟨35, by decide⟩ : Fin 148)) h (basisElt (reps rK68) (charOfVec rK68 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK68 e (h : Coordinate 1) T68_35 i :=
  species_entry_eq_sum rK68 ⟨35, by decide⟩ e heK h T68_35 hfix68_35 hinj68_35 hcardT68_35
    (fun i => conj_mem_of_fixedPoints (reps ⟨35, by decide⟩) (reps rK68) (T68_35 i) (hfix68_35 i) h)

/-! ## Cell (68, 40): |T| = 5 -/

def T68_40list : List Coordinates := [(0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0)]
def T68_40 : Fin 5 → Coordinate 1 := fun i => T68_40list.getD i.val (0,0,0,0,0)

theorem hfix68_40 : ∀ i, ((T68_40 i : Coordinate 1) : Coordinate 1 ⧸ reps rK68)
    ∈ fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68) :=
  repsFix_of_siftB rK68 ⟨40, by decide⟩ T68_40 (by decide)

theorem hinj68_40 : Function.Injective
    (fun i => ((T68_40 i : Coordinate 1) : Coordinate 1 ⧸ reps rK68)) :=
  repsInj_of_reduceAux rK68 T68_40 (by decide)

theorem hcardT68_40 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK68 ⟨40, by decide⟩ R68 hpxR68 hcardq68 (by decide)).symm

/-- **Cell (68, 40).** -/
theorem cell68_40 (e : List (ZMod 25)) (heK : charOK (basisAt rK68) e = true)
    (h : ↥(reps (⟨40, by decide⟩ : Fin 148))) :
    species (reps (⟨40, by decide⟩ : Fin 148)) h (basisElt (reps rK68) (charOfVec rK68 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK68 e (h : Coordinate 1) T68_40 i :=
  species_entry_eq_sum rK68 ⟨40, by decide⟩ e heK h T68_40 hfix68_40 hinj68_40 hcardT68_40
    (fun i => conj_mem_of_fixedPoints (reps ⟨40, by decide⟩) (reps rK68) (T68_40 i) (hfix68_40 i) h)

/-! ## Cell (68, 45): |T| = 5 -/

def T68_45list : List Coordinates := [(0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0)]
def T68_45 : Fin 5 → Coordinate 1 := fun i => T68_45list.getD i.val (0,0,0,0,0)

theorem hfix68_45 : ∀ i, ((T68_45 i : Coordinate 1) : Coordinate 1 ⧸ reps rK68)
    ∈ fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68) :=
  repsFix_of_siftB rK68 ⟨45, by decide⟩ T68_45 (by decide)

theorem hinj68_45 : Function.Injective
    (fun i => ((T68_45 i : Coordinate 1) : Coordinate 1 ⧸ reps rK68)) :=
  repsInj_of_reduceAux rK68 T68_45 (by decide)

theorem hcardT68_45 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK68 ⟨45, by decide⟩ R68 hpxR68 hcardq68 (by decide)).symm

/-- **Cell (68, 45).** -/
theorem cell68_45 (e : List (ZMod 25)) (heK : charOK (basisAt rK68) e = true)
    (h : ↥(reps (⟨45, by decide⟩ : Fin 148))) :
    species (reps (⟨45, by decide⟩ : Fin 148)) h (basisElt (reps rK68) (charOfVec rK68 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK68 e (h : Coordinate 1) T68_45 i :=
  species_entry_eq_sum rK68 ⟨45, by decide⟩ e heK h T68_45 hfix68_45 hinj68_45 hcardT68_45
    (fun i => conj_mem_of_fixedPoints (reps ⟨45, by decide⟩) (reps rK68) (T68_45 i) (hfix68_45 i) h)

/-! ## Cell (68, 50): |T| = 5 -/

def T68_50list : List Coordinates := [(0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0)]
def T68_50 : Fin 5 → Coordinate 1 := fun i => T68_50list.getD i.val (0,0,0,0,0)

theorem hfix68_50 : ∀ i, ((T68_50 i : Coordinate 1) : Coordinate 1 ⧸ reps rK68)
    ∈ fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68) :=
  repsFix_of_siftB rK68 ⟨50, by decide⟩ T68_50 (by decide)

theorem hinj68_50 : Function.Injective
    (fun i => ((T68_50 i : Coordinate 1) : Coordinate 1 ⧸ reps rK68)) :=
  repsInj_of_reduceAux rK68 T68_50 (by decide)

theorem hcardT68_50 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK68 ⟨50, by decide⟩ R68 hpxR68 hcardq68 (by decide)).symm

/-- **Cell (68, 50).** -/
theorem cell68_50 (e : List (ZMod 25)) (heK : charOK (basisAt rK68) e = true)
    (h : ↥(reps (⟨50, by decide⟩ : Fin 148))) :
    species (reps (⟨50, by decide⟩ : Fin 148)) h (basisElt (reps rK68) (charOfVec rK68 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK68 e (h : Coordinate 1) T68_50 i :=
  species_entry_eq_sum rK68 ⟨50, by decide⟩ e heK h T68_50 hfix68_50 hinj68_50 hcardT68_50
    (fun i => conj_mem_of_fixedPoints (reps ⟨50, by decide⟩) (reps rK68) (T68_50 i) (hfix68_50 i) h)

/-! ## Cell (68, 68): |T| = 5 -/

def T68_68list : List Coordinates := [(0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0)]
def T68_68 : Fin 5 → Coordinate 1 := fun i => T68_68list.getD i.val (0,0,0,0,0)

theorem hfix68_68 : ∀ i, ((T68_68 i : Coordinate 1) : Coordinate 1 ⧸ reps rK68)
    ∈ fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68) :=
  repsFix_of_siftB rK68 ⟨68, by decide⟩ T68_68 (by decide)

theorem hinj68_68 : Function.Injective
    (fun i => ((T68_68 i : Coordinate 1) : Coordinate 1 ⧸ reps rK68)) :=
  repsInj_of_reduceAux rK68 T68_68 (by decide)

theorem hcardT68_68 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK68 ⟨68, by decide⟩ R68 hpxR68 hcardq68 (by decide)).symm

/-- **Cell (68, 68).** -/
theorem cell68_68 (e : List (ZMod 25)) (heK : charOK (basisAt rK68) e = true)
    (h : ↥(reps (⟨68, by decide⟩ : Fin 148))) :
    species (reps (⟨68, by decide⟩ : Fin 148)) h (basisElt (reps rK68) (charOfVec rK68 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK68 e (h : Coordinate 1) T68_68 i :=
  species_entry_eq_sum rK68 ⟨68, by decide⟩ e heK h T68_68 hfix68_68 hinj68_68 hcardT68_68
    (fun i => conj_mem_of_fixedPoints (reps ⟨68, by decide⟩) (reps rK68) (T68_68 i) (hfix68_68 i) h)

namespace Q2

def R68_2 : Fin 25 → Coordinate 2 := fun i => R68list.getD i.val (0,0,0,0,0)
theorem hpxR68_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK68) (R68_2 i)) := by decide
theorem hcardq68_2 : Nat.card (Coordinate 2 ⧸ reps rK68) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (68, 0) twin -/

def T68_0_2 : Fin 25 → Coordinate 2 := fun i => T68_0list.getD i.val (0,0,0,0,0)

theorem hfix68_0_2 : ∀ i, ((T68_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK68)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK68) :=
  repsFix_of_siftB2 rK68 ⟨0, by decide⟩ T68_0_2 (by decide)

theorem hinj68_0_2 : Function.Injective
    (fun i => ((T68_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK68)) :=
  repsInj_of_reduceAux2 rK68 T68_0_2 (by decide)

theorem hcardT68_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK68)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK68 ⟨0, by decide⟩ R68_2 hpxR68_2 hcardq68_2 (by decide)).symm

/-- **Cell (68, 0) twin (q=2).** -/
theorem cell68_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK68) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK68) (charOfVec2 rK68 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK68 e (h : Coordinate 2) T68_0_2 i :=
  species_entry_eq_sum rK68 ⟨0, by decide⟩ e heK h T68_0_2 hfix68_0_2 hinj68_0_2 hcardT68_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK68) (T68_0_2 i) (hfix68_0_2 i) h)

/-! ### Cell (68, 6) twin -/

def T68_6_2 : Fin 25 → Coordinate 2 := fun i => T68_6list.getD i.val (0,0,0,0,0)

theorem hfix68_6_2 : ∀ i, ((T68_6_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK68)
    ∈ fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK68) :=
  repsFix_of_siftB2 rK68 ⟨6, by decide⟩ T68_6_2 (by decide)

theorem hinj68_6_2 : Function.Injective
    (fun i => ((T68_6_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK68)) :=
  repsInj_of_reduceAux2 rK68 T68_6_2 (by decide)

theorem hcardT68_6_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK68)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK68 ⟨6, by decide⟩ R68_2 hpxR68_2 hcardq68_2 (by decide)).symm

/-- **Cell (68, 6) twin (q=2).** -/
theorem cell68_6_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK68) e = true)
    (h : ↥(reps (⟨6, by decide⟩ : Fin 148))) :
    species (reps (⟨6, by decide⟩ : Fin 148)) h (basisElt (reps rK68) (charOfVec2 rK68 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK68 e (h : Coordinate 2) T68_6_2 i :=
  species_entry_eq_sum rK68 ⟨6, by decide⟩ e heK h T68_6_2 hfix68_6_2 hinj68_6_2 hcardT68_6_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨6, by decide⟩) (reps rK68) (T68_6_2 i) (hfix68_6_2 i) h)

/-! ### Cell (68, 12) twin -/

def T68_12_2 : Fin 25 → Coordinate 2 := fun i => T68_12list.getD i.val (0,0,0,0,0)

theorem hfix68_12_2 : ∀ i, ((T68_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK68)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK68) :=
  repsFix_of_siftB2 rK68 ⟨12, by decide⟩ T68_12_2 (by decide)

theorem hinj68_12_2 : Function.Injective
    (fun i => ((T68_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK68)) :=
  repsInj_of_reduceAux2 rK68 T68_12_2 (by decide)

theorem hcardT68_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK68)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK68 ⟨12, by decide⟩ R68_2 hpxR68_2 hcardq68_2 (by decide)).symm

/-- **Cell (68, 12) twin (q=2).** -/
theorem cell68_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK68) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK68) (charOfVec2 rK68 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK68 e (h : Coordinate 2) T68_12_2 i :=
  species_entry_eq_sum rK68 ⟨12, by decide⟩ e heK h T68_12_2 hfix68_12_2 hinj68_12_2 hcardT68_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK68) (T68_12_2 i) (hfix68_12_2 i) h)

/-! ### Cell (68, 24) twin -/

def T68_24_2 : Fin 25 → Coordinate 2 := fun i => T68_24list.getD i.val (0,0,0,0,0)

theorem hfix68_24_2 : ∀ i, ((T68_24_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK68)
    ∈ fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK68) :=
  repsFix_of_siftB2 rK68 ⟨24, by decide⟩ T68_24_2 (by decide)

theorem hinj68_24_2 : Function.Injective
    (fun i => ((T68_24_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK68)) :=
  repsInj_of_reduceAux2 rK68 T68_24_2 (by decide)

theorem hcardT68_24_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK68)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK68 ⟨24, by decide⟩ R68_2 hpxR68_2 hcardq68_2 (by decide)).symm

/-- **Cell (68, 24) twin (q=2).** -/
theorem cell68_24_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK68) e = true)
    (h : ↥(reps (⟨24, by decide⟩ : Fin 148))) :
    species (reps (⟨24, by decide⟩ : Fin 148)) h (basisElt (reps rK68) (charOfVec2 rK68 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK68 e (h : Coordinate 2) T68_24_2 i :=
  species_entry_eq_sum rK68 ⟨24, by decide⟩ e heK h T68_24_2 hfix68_24_2 hinj68_24_2 hcardT68_24_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨24, by decide⟩) (reps rK68) (T68_24_2 i) (hfix68_24_2 i) h)

/-! ### Cell (68, 30) twin -/

def T68_30_2 : Fin 5 → Coordinate 2 := fun i => T68_30list.getD i.val (0,0,0,0,0)

theorem hfix68_30_2 : ∀ i, ((T68_30_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK68)
    ∈ fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK68) :=
  repsFix_of_siftB2 rK68 ⟨30, by decide⟩ T68_30_2 (by decide)

theorem hinj68_30_2 : Function.Injective
    (fun i => ((T68_30_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK68)) :=
  repsInj_of_reduceAux2 rK68 T68_30_2 (by decide)

theorem hcardT68_30_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK68)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK68 ⟨30, by decide⟩ R68_2 hpxR68_2 hcardq68_2 (by decide)).symm

/-- **Cell (68, 30) twin (q=2).** -/
theorem cell68_30_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK68) e = true)
    (h : ↥(reps (⟨30, by decide⟩ : Fin 148))) :
    species (reps (⟨30, by decide⟩ : Fin 148)) h (basisElt (reps rK68) (charOfVec2 rK68 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK68 e (h : Coordinate 2) T68_30_2 i :=
  species_entry_eq_sum rK68 ⟨30, by decide⟩ e heK h T68_30_2 hfix68_30_2 hinj68_30_2 hcardT68_30_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨30, by decide⟩) (reps rK68) (T68_30_2 i) (hfix68_30_2 i) h)

/-! ### Cell (68, 35) twin -/

def T68_35_2 : Fin 5 → Coordinate 2 := fun i => T68_35list.getD i.val (0,0,0,0,0)

theorem hfix68_35_2 : ∀ i, ((T68_35_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK68)
    ∈ fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK68) :=
  repsFix_of_siftB2 rK68 ⟨35, by decide⟩ T68_35_2 (by decide)

theorem hinj68_35_2 : Function.Injective
    (fun i => ((T68_35_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK68)) :=
  repsInj_of_reduceAux2 rK68 T68_35_2 (by decide)

theorem hcardT68_35_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK68)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK68 ⟨35, by decide⟩ R68_2 hpxR68_2 hcardq68_2 (by decide)).symm

/-- **Cell (68, 35) twin (q=2).** -/
theorem cell68_35_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK68) e = true)
    (h : ↥(reps (⟨35, by decide⟩ : Fin 148))) :
    species (reps (⟨35, by decide⟩ : Fin 148)) h (basisElt (reps rK68) (charOfVec2 rK68 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK68 e (h : Coordinate 2) T68_35_2 i :=
  species_entry_eq_sum rK68 ⟨35, by decide⟩ e heK h T68_35_2 hfix68_35_2 hinj68_35_2 hcardT68_35_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨35, by decide⟩) (reps rK68) (T68_35_2 i) (hfix68_35_2 i) h)

/-! ### Cell (68, 40) twin -/

def T68_40_2 : Fin 5 → Coordinate 2 := fun i => T68_40list.getD i.val (0,0,0,0,0)

theorem hfix68_40_2 : ∀ i, ((T68_40_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK68)
    ∈ fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK68) :=
  repsFix_of_siftB2 rK68 ⟨40, by decide⟩ T68_40_2 (by decide)

theorem hinj68_40_2 : Function.Injective
    (fun i => ((T68_40_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK68)) :=
  repsInj_of_reduceAux2 rK68 T68_40_2 (by decide)

theorem hcardT68_40_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK68)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK68 ⟨40, by decide⟩ R68_2 hpxR68_2 hcardq68_2 (by decide)).symm

/-- **Cell (68, 40) twin (q=2).** -/
theorem cell68_40_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK68) e = true)
    (h : ↥(reps (⟨40, by decide⟩ : Fin 148))) :
    species (reps (⟨40, by decide⟩ : Fin 148)) h (basisElt (reps rK68) (charOfVec2 rK68 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK68 e (h : Coordinate 2) T68_40_2 i :=
  species_entry_eq_sum rK68 ⟨40, by decide⟩ e heK h T68_40_2 hfix68_40_2 hinj68_40_2 hcardT68_40_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨40, by decide⟩) (reps rK68) (T68_40_2 i) (hfix68_40_2 i) h)

/-! ### Cell (68, 45) twin -/

def T68_45_2 : Fin 5 → Coordinate 2 := fun i => T68_45list.getD i.val (0,0,0,0,0)

theorem hfix68_45_2 : ∀ i, ((T68_45_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK68)
    ∈ fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK68) :=
  repsFix_of_siftB2 rK68 ⟨45, by decide⟩ T68_45_2 (by decide)

theorem hinj68_45_2 : Function.Injective
    (fun i => ((T68_45_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK68)) :=
  repsInj_of_reduceAux2 rK68 T68_45_2 (by decide)

theorem hcardT68_45_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK68)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK68 ⟨45, by decide⟩ R68_2 hpxR68_2 hcardq68_2 (by decide)).symm

/-- **Cell (68, 45) twin (q=2).** -/
theorem cell68_45_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK68) e = true)
    (h : ↥(reps (⟨45, by decide⟩ : Fin 148))) :
    species (reps (⟨45, by decide⟩ : Fin 148)) h (basisElt (reps rK68) (charOfVec2 rK68 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK68 e (h : Coordinate 2) T68_45_2 i :=
  species_entry_eq_sum rK68 ⟨45, by decide⟩ e heK h T68_45_2 hfix68_45_2 hinj68_45_2 hcardT68_45_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨45, by decide⟩) (reps rK68) (T68_45_2 i) (hfix68_45_2 i) h)

/-! ### Cell (68, 50) twin -/

def T68_50_2 : Fin 5 → Coordinate 2 := fun i => T68_50list.getD i.val (0,0,0,0,0)

theorem hfix68_50_2 : ∀ i, ((T68_50_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK68)
    ∈ fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK68) :=
  repsFix_of_siftB2 rK68 ⟨50, by decide⟩ T68_50_2 (by decide)

theorem hinj68_50_2 : Function.Injective
    (fun i => ((T68_50_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK68)) :=
  repsInj_of_reduceAux2 rK68 T68_50_2 (by decide)

theorem hcardT68_50_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK68)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK68 ⟨50, by decide⟩ R68_2 hpxR68_2 hcardq68_2 (by decide)).symm

/-- **Cell (68, 50) twin (q=2).** -/
theorem cell68_50_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK68) e = true)
    (h : ↥(reps (⟨50, by decide⟩ : Fin 148))) :
    species (reps (⟨50, by decide⟩ : Fin 148)) h (basisElt (reps rK68) (charOfVec2 rK68 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK68 e (h : Coordinate 2) T68_50_2 i :=
  species_entry_eq_sum rK68 ⟨50, by decide⟩ e heK h T68_50_2 hfix68_50_2 hinj68_50_2 hcardT68_50_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨50, by decide⟩) (reps rK68) (T68_50_2 i) (hfix68_50_2 i) h)

/-! ### Cell (68, 68) twin -/

def T68_68_2 : Fin 5 → Coordinate 2 := fun i => T68_68list.getD i.val (0,0,0,0,0)

theorem hfix68_68_2 : ∀ i, ((T68_68_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK68)
    ∈ fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK68) :=
  repsFix_of_siftB2 rK68 ⟨68, by decide⟩ T68_68_2 (by decide)

theorem hinj68_68_2 : Function.Injective
    (fun i => ((T68_68_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK68)) :=
  repsInj_of_reduceAux2 rK68 T68_68_2 (by decide)

theorem hcardT68_68_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK68)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK68 ⟨68, by decide⟩ R68_2 hpxR68_2 hcardq68_2 (by decide)).symm

/-- **Cell (68, 68) twin (q=2).** -/
theorem cell68_68_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK68) e = true)
    (h : ↥(reps (⟨68, by decide⟩ : Fin 148))) :
    species (reps (⟨68, by decide⟩ : Fin 148)) h (basisElt (reps rK68) (charOfVec2 rK68 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK68 e (h : Coordinate 2) T68_68_2 i :=
  species_entry_eq_sum rK68 ⟨68, by decide⟩ e heK h T68_68_2 hfix68_68_2 hinj68_68_2 hcardT68_68_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨68, by decide⟩) (reps rK68) (T68_68_2 i) (hfix68_68_2 i) h)

end Q2

/-! # K-class rK = 69  (|G/K| = 25) -/

def rK69 : Fin 148 := ⟨69, by decide⟩

def R69list : List Coordinates := [(0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0)]
def R69 : Fin 25 → Coordinate 1 := fun i => R69list.getD i.val (0,0,0,0,0)

theorem hpxR69 : Function.Injective (fun i => reduceAux 1 (basisAt rK69) (R69 i)) := by decide
theorem hcardq69 : Nat.card (Coordinate 1 ⧸ reps rK69) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (69, 0): |T| = 25 -/

def T69_0list : List Coordinates := [(0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0)]
def T69_0 : Fin 25 → Coordinate 1 := fun i => T69_0list.getD i.val (0,0,0,0,0)

theorem hfix69_0 : ∀ i, ((T69_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK69)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69) :=
  repsFix_of_siftB rK69 ⟨0, by decide⟩ T69_0 (by decide)

theorem hinj69_0 : Function.Injective
    (fun i => ((T69_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK69)) :=
  repsInj_of_reduceAux rK69 T69_0 (by decide)

theorem hcardT69_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK69 ⟨0, by decide⟩ R69 hpxR69 hcardq69 (by decide)).symm

/-- **Cell (69, 0).** -/
theorem cell69_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK69) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK69) (charOfVec rK69 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK69 e (h : Coordinate 1) T69_0 i :=
  species_entry_eq_sum rK69 ⟨0, by decide⟩ e heK h T69_0 hfix69_0 hinj69_0 hcardT69_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK69) (T69_0 i) (hfix69_0 i) h)

/-! ## Cell (69, 8): |T| = 25 -/

def T69_8list : List Coordinates := [(0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0)]
def T69_8 : Fin 25 → Coordinate 1 := fun i => T69_8list.getD i.val (0,0,0,0,0)

theorem hfix69_8 : ∀ i, ((T69_8 i : Coordinate 1) : Coordinate 1 ⧸ reps rK69)
    ∈ fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69) :=
  repsFix_of_siftB rK69 ⟨8, by decide⟩ T69_8 (by decide)

theorem hinj69_8 : Function.Injective
    (fun i => ((T69_8 i : Coordinate 1) : Coordinate 1 ⧸ reps rK69)) :=
  repsInj_of_reduceAux rK69 T69_8 (by decide)

theorem hcardT69_8 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK69 ⟨8, by decide⟩ R69 hpxR69 hcardq69 (by decide)).symm

/-- **Cell (69, 8).** -/
theorem cell69_8 (e : List (ZMod 25)) (heK : charOK (basisAt rK69) e = true)
    (h : ↥(reps (⟨8, by decide⟩ : Fin 148))) :
    species (reps (⟨8, by decide⟩ : Fin 148)) h (basisElt (reps rK69) (charOfVec rK69 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK69 e (h : Coordinate 1) T69_8 i :=
  species_entry_eq_sum rK69 ⟨8, by decide⟩ e heK h T69_8 hfix69_8 hinj69_8 hcardT69_8
    (fun i => conj_mem_of_fixedPoints (reps ⟨8, by decide⟩) (reps rK69) (T69_8 i) (hfix69_8 i) h)

/-! ## Cell (69, 12): |T| = 25 -/

def T69_12list : List Coordinates := [(0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0)]
def T69_12 : Fin 25 → Coordinate 1 := fun i => T69_12list.getD i.val (0,0,0,0,0)

theorem hfix69_12 : ∀ i, ((T69_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK69)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69) :=
  repsFix_of_siftB rK69 ⟨12, by decide⟩ T69_12 (by decide)

theorem hinj69_12 : Function.Injective
    (fun i => ((T69_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK69)) :=
  repsInj_of_reduceAux rK69 T69_12 (by decide)

theorem hcardT69_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK69 ⟨12, by decide⟩ R69 hpxR69 hcardq69 (by decide)).symm

/-- **Cell (69, 12).** -/
theorem cell69_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK69) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK69) (charOfVec rK69 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK69 e (h : Coordinate 1) T69_12 i :=
  species_entry_eq_sum rK69 ⟨12, by decide⟩ e heK h T69_12 hfix69_12 hinj69_12 hcardT69_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK69) (T69_12 i) (hfix69_12 i) h)

/-! ## Cell (69, 26): |T| = 25 -/

def T69_26list : List Coordinates := [(0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0)]
def T69_26 : Fin 25 → Coordinate 1 := fun i => T69_26list.getD i.val (0,0,0,0,0)

theorem hfix69_26 : ∀ i, ((T69_26 i : Coordinate 1) : Coordinate 1 ⧸ reps rK69)
    ∈ fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69) :=
  repsFix_of_siftB rK69 ⟨26, by decide⟩ T69_26 (by decide)

theorem hinj69_26 : Function.Injective
    (fun i => ((T69_26 i : Coordinate 1) : Coordinate 1 ⧸ reps rK69)) :=
  repsInj_of_reduceAux rK69 T69_26 (by decide)

theorem hcardT69_26 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK69 ⟨26, by decide⟩ R69 hpxR69 hcardq69 (by decide)).symm

/-- **Cell (69, 26).** -/
theorem cell69_26 (e : List (ZMod 25)) (heK : charOK (basisAt rK69) e = true)
    (h : ↥(reps (⟨26, by decide⟩ : Fin 148))) :
    species (reps (⟨26, by decide⟩ : Fin 148)) h (basisElt (reps rK69) (charOfVec rK69 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK69 e (h : Coordinate 1) T69_26 i :=
  species_entry_eq_sum rK69 ⟨26, by decide⟩ e heK h T69_26 hfix69_26 hinj69_26 hcardT69_26
    (fun i => conj_mem_of_fixedPoints (reps ⟨26, by decide⟩) (reps rK69) (T69_26 i) (hfix69_26 i) h)

/-! ## Cell (69, 30): |T| = 5 -/

def T69_30list : List Coordinates := [(0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0)]
def T69_30 : Fin 5 → Coordinate 1 := fun i => T69_30list.getD i.val (0,0,0,0,0)

theorem hfix69_30 : ∀ i, ((T69_30 i : Coordinate 1) : Coordinate 1 ⧸ reps rK69)
    ∈ fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69) :=
  repsFix_of_siftB rK69 ⟨30, by decide⟩ T69_30 (by decide)

theorem hinj69_30 : Function.Injective
    (fun i => ((T69_30 i : Coordinate 1) : Coordinate 1 ⧸ reps rK69)) :=
  repsInj_of_reduceAux rK69 T69_30 (by decide)

theorem hcardT69_30 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK69 ⟨30, by decide⟩ R69 hpxR69 hcardq69 (by decide)).symm

/-- **Cell (69, 30).** -/
theorem cell69_30 (e : List (ZMod 25)) (heK : charOK (basisAt rK69) e = true)
    (h : ↥(reps (⟨30, by decide⟩ : Fin 148))) :
    species (reps (⟨30, by decide⟩ : Fin 148)) h (basisElt (reps rK69) (charOfVec rK69 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK69 e (h : Coordinate 1) T69_30 i :=
  species_entry_eq_sum rK69 ⟨30, by decide⟩ e heK h T69_30 hfix69_30 hinj69_30 hcardT69_30
    (fun i => conj_mem_of_fixedPoints (reps ⟨30, by decide⟩) (reps rK69) (T69_30 i) (hfix69_30 i) h)

/-! ## Cell (69, 35): |T| = 5 -/

def T69_35list : List Coordinates := [(0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0)]
def T69_35 : Fin 5 → Coordinate 1 := fun i => T69_35list.getD i.val (0,0,0,0,0)

theorem hfix69_35 : ∀ i, ((T69_35 i : Coordinate 1) : Coordinate 1 ⧸ reps rK69)
    ∈ fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69) :=
  repsFix_of_siftB rK69 ⟨35, by decide⟩ T69_35 (by decide)

theorem hinj69_35 : Function.Injective
    (fun i => ((T69_35 i : Coordinate 1) : Coordinate 1 ⧸ reps rK69)) :=
  repsInj_of_reduceAux rK69 T69_35 (by decide)

theorem hcardT69_35 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK69 ⟨35, by decide⟩ R69 hpxR69 hcardq69 (by decide)).symm

/-- **Cell (69, 35).** -/
theorem cell69_35 (e : List (ZMod 25)) (heK : charOK (basisAt rK69) e = true)
    (h : ↥(reps (⟨35, by decide⟩ : Fin 148))) :
    species (reps (⟨35, by decide⟩ : Fin 148)) h (basisElt (reps rK69) (charOfVec rK69 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK69 e (h : Coordinate 1) T69_35 i :=
  species_entry_eq_sum rK69 ⟨35, by decide⟩ e heK h T69_35 hfix69_35 hinj69_35 hcardT69_35
    (fun i => conj_mem_of_fixedPoints (reps ⟨35, by decide⟩) (reps rK69) (T69_35 i) (hfix69_35 i) h)

/-! ## Cell (69, 40): |T| = 5 -/

def T69_40list : List Coordinates := [(0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0)]
def T69_40 : Fin 5 → Coordinate 1 := fun i => T69_40list.getD i.val (0,0,0,0,0)

theorem hfix69_40 : ∀ i, ((T69_40 i : Coordinate 1) : Coordinate 1 ⧸ reps rK69)
    ∈ fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69) :=
  repsFix_of_siftB rK69 ⟨40, by decide⟩ T69_40 (by decide)

theorem hinj69_40 : Function.Injective
    (fun i => ((T69_40 i : Coordinate 1) : Coordinate 1 ⧸ reps rK69)) :=
  repsInj_of_reduceAux rK69 T69_40 (by decide)

theorem hcardT69_40 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK69 ⟨40, by decide⟩ R69 hpxR69 hcardq69 (by decide)).symm

/-- **Cell (69, 40).** -/
theorem cell69_40 (e : List (ZMod 25)) (heK : charOK (basisAt rK69) e = true)
    (h : ↥(reps (⟨40, by decide⟩ : Fin 148))) :
    species (reps (⟨40, by decide⟩ : Fin 148)) h (basisElt (reps rK69) (charOfVec rK69 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK69 e (h : Coordinate 1) T69_40 i :=
  species_entry_eq_sum rK69 ⟨40, by decide⟩ e heK h T69_40 hfix69_40 hinj69_40 hcardT69_40
    (fun i => conj_mem_of_fixedPoints (reps ⟨40, by decide⟩) (reps rK69) (T69_40 i) (hfix69_40 i) h)

/-! ## Cell (69, 45): |T| = 5 -/

def T69_45list : List Coordinates := [(0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0)]
def T69_45 : Fin 5 → Coordinate 1 := fun i => T69_45list.getD i.val (0,0,0,0,0)

theorem hfix69_45 : ∀ i, ((T69_45 i : Coordinate 1) : Coordinate 1 ⧸ reps rK69)
    ∈ fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69) :=
  repsFix_of_siftB rK69 ⟨45, by decide⟩ T69_45 (by decide)

theorem hinj69_45 : Function.Injective
    (fun i => ((T69_45 i : Coordinate 1) : Coordinate 1 ⧸ reps rK69)) :=
  repsInj_of_reduceAux rK69 T69_45 (by decide)

theorem hcardT69_45 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK69 ⟨45, by decide⟩ R69 hpxR69 hcardq69 (by decide)).symm

/-- **Cell (69, 45).** -/
theorem cell69_45 (e : List (ZMod 25)) (heK : charOK (basisAt rK69) e = true)
    (h : ↥(reps (⟨45, by decide⟩ : Fin 148))) :
    species (reps (⟨45, by decide⟩ : Fin 148)) h (basisElt (reps rK69) (charOfVec rK69 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK69 e (h : Coordinate 1) T69_45 i :=
  species_entry_eq_sum rK69 ⟨45, by decide⟩ e heK h T69_45 hfix69_45 hinj69_45 hcardT69_45
    (fun i => conj_mem_of_fixedPoints (reps ⟨45, by decide⟩) (reps rK69) (T69_45 i) (hfix69_45 i) h)

/-! ## Cell (69, 50): |T| = 5 -/

def T69_50list : List Coordinates := [(0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0)]
def T69_50 : Fin 5 → Coordinate 1 := fun i => T69_50list.getD i.val (0,0,0,0,0)

theorem hfix69_50 : ∀ i, ((T69_50 i : Coordinate 1) : Coordinate 1 ⧸ reps rK69)
    ∈ fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69) :=
  repsFix_of_siftB rK69 ⟨50, by decide⟩ T69_50 (by decide)

theorem hinj69_50 : Function.Injective
    (fun i => ((T69_50 i : Coordinate 1) : Coordinate 1 ⧸ reps rK69)) :=
  repsInj_of_reduceAux rK69 T69_50 (by decide)

theorem hcardT69_50 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK69 ⟨50, by decide⟩ R69 hpxR69 hcardq69 (by decide)).symm

/-- **Cell (69, 50).** -/
theorem cell69_50 (e : List (ZMod 25)) (heK : charOK (basisAt rK69) e = true)
    (h : ↥(reps (⟨50, by decide⟩ : Fin 148))) :
    species (reps (⟨50, by decide⟩ : Fin 148)) h (basisElt (reps rK69) (charOfVec rK69 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK69 e (h : Coordinate 1) T69_50 i :=
  species_entry_eq_sum rK69 ⟨50, by decide⟩ e heK h T69_50 hfix69_50 hinj69_50 hcardT69_50
    (fun i => conj_mem_of_fixedPoints (reps ⟨50, by decide⟩) (reps rK69) (T69_50 i) (hfix69_50 i) h)

/-! ## Cell (69, 69): |T| = 5 -/

def T69_69list : List Coordinates := [(0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0)]
def T69_69 : Fin 5 → Coordinate 1 := fun i => T69_69list.getD i.val (0,0,0,0,0)

theorem hfix69_69 : ∀ i, ((T69_69 i : Coordinate 1) : Coordinate 1 ⧸ reps rK69)
    ∈ fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69) :=
  repsFix_of_siftB rK69 ⟨69, by decide⟩ T69_69 (by decide)

theorem hinj69_69 : Function.Injective
    (fun i => ((T69_69 i : Coordinate 1) : Coordinate 1 ⧸ reps rK69)) :=
  repsInj_of_reduceAux rK69 T69_69 (by decide)

theorem hcardT69_69 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK69 ⟨69, by decide⟩ R69 hpxR69 hcardq69 (by decide)).symm

/-- **Cell (69, 69).** -/
theorem cell69_69 (e : List (ZMod 25)) (heK : charOK (basisAt rK69) e = true)
    (h : ↥(reps (⟨69, by decide⟩ : Fin 148))) :
    species (reps (⟨69, by decide⟩ : Fin 148)) h (basisElt (reps rK69) (charOfVec rK69 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK69 e (h : Coordinate 1) T69_69 i :=
  species_entry_eq_sum rK69 ⟨69, by decide⟩ e heK h T69_69 hfix69_69 hinj69_69 hcardT69_69
    (fun i => conj_mem_of_fixedPoints (reps ⟨69, by decide⟩) (reps rK69) (T69_69 i) (hfix69_69 i) h)

namespace Q2

def R69_2 : Fin 25 → Coordinate 2 := fun i => R69list.getD i.val (0,0,0,0,0)
theorem hpxR69_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK69) (R69_2 i)) := by decide
theorem hcardq69_2 : Nat.card (Coordinate 2 ⧸ reps rK69) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (69, 0) twin -/

def T69_0_2 : Fin 25 → Coordinate 2 := fun i => T69_0list.getD i.val (0,0,0,0,0)

theorem hfix69_0_2 : ∀ i, ((T69_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK69)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK69) :=
  repsFix_of_siftB2 rK69 ⟨0, by decide⟩ T69_0_2 (by decide)

theorem hinj69_0_2 : Function.Injective
    (fun i => ((T69_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK69)) :=
  repsInj_of_reduceAux2 rK69 T69_0_2 (by decide)

theorem hcardT69_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK69)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK69 ⟨0, by decide⟩ R69_2 hpxR69_2 hcardq69_2 (by decide)).symm

/-- **Cell (69, 0) twin (q=2).** -/
theorem cell69_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK69) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK69) (charOfVec2 rK69 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK69 e (h : Coordinate 2) T69_0_2 i :=
  species_entry_eq_sum rK69 ⟨0, by decide⟩ e heK h T69_0_2 hfix69_0_2 hinj69_0_2 hcardT69_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK69) (T69_0_2 i) (hfix69_0_2 i) h)

/-! ### Cell (69, 8) twin -/

def T69_8_2 : Fin 25 → Coordinate 2 := fun i => T69_8list.getD i.val (0,0,0,0,0)

theorem hfix69_8_2 : ∀ i, ((T69_8_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK69)
    ∈ fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK69) :=
  repsFix_of_siftB2 rK69 ⟨8, by decide⟩ T69_8_2 (by decide)

theorem hinj69_8_2 : Function.Injective
    (fun i => ((T69_8_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK69)) :=
  repsInj_of_reduceAux2 rK69 T69_8_2 (by decide)

theorem hcardT69_8_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK69)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK69 ⟨8, by decide⟩ R69_2 hpxR69_2 hcardq69_2 (by decide)).symm

/-- **Cell (69, 8) twin (q=2).** -/
theorem cell69_8_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK69) e = true)
    (h : ↥(reps (⟨8, by decide⟩ : Fin 148))) :
    species (reps (⟨8, by decide⟩ : Fin 148)) h (basisElt (reps rK69) (charOfVec2 rK69 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK69 e (h : Coordinate 2) T69_8_2 i :=
  species_entry_eq_sum rK69 ⟨8, by decide⟩ e heK h T69_8_2 hfix69_8_2 hinj69_8_2 hcardT69_8_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨8, by decide⟩) (reps rK69) (T69_8_2 i) (hfix69_8_2 i) h)

/-! ### Cell (69, 12) twin -/

def T69_12_2 : Fin 25 → Coordinate 2 := fun i => T69_12list.getD i.val (0,0,0,0,0)

theorem hfix69_12_2 : ∀ i, ((T69_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK69)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK69) :=
  repsFix_of_siftB2 rK69 ⟨12, by decide⟩ T69_12_2 (by decide)

theorem hinj69_12_2 : Function.Injective
    (fun i => ((T69_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK69)) :=
  repsInj_of_reduceAux2 rK69 T69_12_2 (by decide)

theorem hcardT69_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK69)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK69 ⟨12, by decide⟩ R69_2 hpxR69_2 hcardq69_2 (by decide)).symm

/-- **Cell (69, 12) twin (q=2).** -/
theorem cell69_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK69) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK69) (charOfVec2 rK69 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK69 e (h : Coordinate 2) T69_12_2 i :=
  species_entry_eq_sum rK69 ⟨12, by decide⟩ e heK h T69_12_2 hfix69_12_2 hinj69_12_2 hcardT69_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK69) (T69_12_2 i) (hfix69_12_2 i) h)

/-! ### Cell (69, 26) twin -/

def T69_26_2 : Fin 25 → Coordinate 2 := fun i => T69_26list.getD i.val (0,0,0,0,0)

theorem hfix69_26_2 : ∀ i, ((T69_26_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK69)
    ∈ fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK69) :=
  repsFix_of_siftB2 rK69 ⟨26, by decide⟩ T69_26_2 (by decide)

theorem hinj69_26_2 : Function.Injective
    (fun i => ((T69_26_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK69)) :=
  repsInj_of_reduceAux2 rK69 T69_26_2 (by decide)

theorem hcardT69_26_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK69)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK69 ⟨26, by decide⟩ R69_2 hpxR69_2 hcardq69_2 (by decide)).symm

/-- **Cell (69, 26) twin (q=2).** -/
theorem cell69_26_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK69) e = true)
    (h : ↥(reps (⟨26, by decide⟩ : Fin 148))) :
    species (reps (⟨26, by decide⟩ : Fin 148)) h (basisElt (reps rK69) (charOfVec2 rK69 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK69 e (h : Coordinate 2) T69_26_2 i :=
  species_entry_eq_sum rK69 ⟨26, by decide⟩ e heK h T69_26_2 hfix69_26_2 hinj69_26_2 hcardT69_26_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨26, by decide⟩) (reps rK69) (T69_26_2 i) (hfix69_26_2 i) h)

/-! ### Cell (69, 30) twin -/

def T69_30_2 : Fin 5 → Coordinate 2 := fun i => T69_30list.getD i.val (0,0,0,0,0)

theorem hfix69_30_2 : ∀ i, ((T69_30_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK69)
    ∈ fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK69) :=
  repsFix_of_siftB2 rK69 ⟨30, by decide⟩ T69_30_2 (by decide)

theorem hinj69_30_2 : Function.Injective
    (fun i => ((T69_30_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK69)) :=
  repsInj_of_reduceAux2 rK69 T69_30_2 (by decide)

theorem hcardT69_30_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK69)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK69 ⟨30, by decide⟩ R69_2 hpxR69_2 hcardq69_2 (by decide)).symm

/-- **Cell (69, 30) twin (q=2).** -/
theorem cell69_30_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK69) e = true)
    (h : ↥(reps (⟨30, by decide⟩ : Fin 148))) :
    species (reps (⟨30, by decide⟩ : Fin 148)) h (basisElt (reps rK69) (charOfVec2 rK69 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK69 e (h : Coordinate 2) T69_30_2 i :=
  species_entry_eq_sum rK69 ⟨30, by decide⟩ e heK h T69_30_2 hfix69_30_2 hinj69_30_2 hcardT69_30_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨30, by decide⟩) (reps rK69) (T69_30_2 i) (hfix69_30_2 i) h)

/-! ### Cell (69, 35) twin -/

def T69_35_2 : Fin 5 → Coordinate 2 := fun i => T69_35list.getD i.val (0,0,0,0,0)

theorem hfix69_35_2 : ∀ i, ((T69_35_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK69)
    ∈ fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK69) :=
  repsFix_of_siftB2 rK69 ⟨35, by decide⟩ T69_35_2 (by decide)

theorem hinj69_35_2 : Function.Injective
    (fun i => ((T69_35_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK69)) :=
  repsInj_of_reduceAux2 rK69 T69_35_2 (by decide)

theorem hcardT69_35_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK69)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK69 ⟨35, by decide⟩ R69_2 hpxR69_2 hcardq69_2 (by decide)).symm

/-- **Cell (69, 35) twin (q=2).** -/
theorem cell69_35_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK69) e = true)
    (h : ↥(reps (⟨35, by decide⟩ : Fin 148))) :
    species (reps (⟨35, by decide⟩ : Fin 148)) h (basisElt (reps rK69) (charOfVec2 rK69 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK69 e (h : Coordinate 2) T69_35_2 i :=
  species_entry_eq_sum rK69 ⟨35, by decide⟩ e heK h T69_35_2 hfix69_35_2 hinj69_35_2 hcardT69_35_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨35, by decide⟩) (reps rK69) (T69_35_2 i) (hfix69_35_2 i) h)

/-! ### Cell (69, 40) twin -/

def T69_40_2 : Fin 5 → Coordinate 2 := fun i => T69_40list.getD i.val (0,0,0,0,0)

theorem hfix69_40_2 : ∀ i, ((T69_40_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK69)
    ∈ fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK69) :=
  repsFix_of_siftB2 rK69 ⟨40, by decide⟩ T69_40_2 (by decide)

theorem hinj69_40_2 : Function.Injective
    (fun i => ((T69_40_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK69)) :=
  repsInj_of_reduceAux2 rK69 T69_40_2 (by decide)

theorem hcardT69_40_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK69)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK69 ⟨40, by decide⟩ R69_2 hpxR69_2 hcardq69_2 (by decide)).symm

/-- **Cell (69, 40) twin (q=2).** -/
theorem cell69_40_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK69) e = true)
    (h : ↥(reps (⟨40, by decide⟩ : Fin 148))) :
    species (reps (⟨40, by decide⟩ : Fin 148)) h (basisElt (reps rK69) (charOfVec2 rK69 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK69 e (h : Coordinate 2) T69_40_2 i :=
  species_entry_eq_sum rK69 ⟨40, by decide⟩ e heK h T69_40_2 hfix69_40_2 hinj69_40_2 hcardT69_40_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨40, by decide⟩) (reps rK69) (T69_40_2 i) (hfix69_40_2 i) h)

/-! ### Cell (69, 45) twin -/

def T69_45_2 : Fin 5 → Coordinate 2 := fun i => T69_45list.getD i.val (0,0,0,0,0)

theorem hfix69_45_2 : ∀ i, ((T69_45_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK69)
    ∈ fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK69) :=
  repsFix_of_siftB2 rK69 ⟨45, by decide⟩ T69_45_2 (by decide)

theorem hinj69_45_2 : Function.Injective
    (fun i => ((T69_45_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK69)) :=
  repsInj_of_reduceAux2 rK69 T69_45_2 (by decide)

theorem hcardT69_45_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK69)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK69 ⟨45, by decide⟩ R69_2 hpxR69_2 hcardq69_2 (by decide)).symm

/-- **Cell (69, 45) twin (q=2).** -/
theorem cell69_45_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK69) e = true)
    (h : ↥(reps (⟨45, by decide⟩ : Fin 148))) :
    species (reps (⟨45, by decide⟩ : Fin 148)) h (basisElt (reps rK69) (charOfVec2 rK69 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK69 e (h : Coordinate 2) T69_45_2 i :=
  species_entry_eq_sum rK69 ⟨45, by decide⟩ e heK h T69_45_2 hfix69_45_2 hinj69_45_2 hcardT69_45_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨45, by decide⟩) (reps rK69) (T69_45_2 i) (hfix69_45_2 i) h)

/-! ### Cell (69, 50) twin -/

def T69_50_2 : Fin 5 → Coordinate 2 := fun i => T69_50list.getD i.val (0,0,0,0,0)

theorem hfix69_50_2 : ∀ i, ((T69_50_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK69)
    ∈ fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK69) :=
  repsFix_of_siftB2 rK69 ⟨50, by decide⟩ T69_50_2 (by decide)

theorem hinj69_50_2 : Function.Injective
    (fun i => ((T69_50_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK69)) :=
  repsInj_of_reduceAux2 rK69 T69_50_2 (by decide)

theorem hcardT69_50_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK69)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK69 ⟨50, by decide⟩ R69_2 hpxR69_2 hcardq69_2 (by decide)).symm

/-- **Cell (69, 50) twin (q=2).** -/
theorem cell69_50_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK69) e = true)
    (h : ↥(reps (⟨50, by decide⟩ : Fin 148))) :
    species (reps (⟨50, by decide⟩ : Fin 148)) h (basisElt (reps rK69) (charOfVec2 rK69 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK69 e (h : Coordinate 2) T69_50_2 i :=
  species_entry_eq_sum rK69 ⟨50, by decide⟩ e heK h T69_50_2 hfix69_50_2 hinj69_50_2 hcardT69_50_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨50, by decide⟩) (reps rK69) (T69_50_2 i) (hfix69_50_2 i) h)

/-! ### Cell (69, 69) twin -/

def T69_69_2 : Fin 5 → Coordinate 2 := fun i => T69_69list.getD i.val (0,0,0,0,0)

theorem hfix69_69_2 : ∀ i, ((T69_69_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK69)
    ∈ fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK69) :=
  repsFix_of_siftB2 rK69 ⟨69, by decide⟩ T69_69_2 (by decide)

theorem hinj69_69_2 : Function.Injective
    (fun i => ((T69_69_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK69)) :=
  repsInj_of_reduceAux2 rK69 T69_69_2 (by decide)

theorem hcardT69_69_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK69)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK69 ⟨69, by decide⟩ R69_2 hpxR69_2 hcardq69_2 (by decide)).symm

/-- **Cell (69, 69) twin (q=2).** -/
theorem cell69_69_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK69) e = true)
    (h : ↥(reps (⟨69, by decide⟩ : Fin 148))) :
    species (reps (⟨69, by decide⟩ : Fin 148)) h (basisElt (reps rK69) (charOfVec2 rK69 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK69 e (h : Coordinate 2) T69_69_2 i :=
  species_entry_eq_sum rK69 ⟨69, by decide⟩ e heK h T69_69_2 hfix69_69_2 hinj69_69_2 hcardT69_69_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨69, by decide⟩) (reps rK69) (T69_69_2 i) (hfix69_69_2 i) h)

end Q2

end LeanDring.P5Presentation
