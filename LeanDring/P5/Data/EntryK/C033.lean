/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, K-strata data (5^4 stratum, rK 128-129): certified per-cell species-entry instantiations, both
twins.

Covers K-classes 128, 129 (order-5^4 K, |R|=5).  For each nonzero `H`-column
(`(G/K)^H ≠ ∅`), the full coset transversal `R128..` and each `H`-fixed
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

/-! # K-class rK = 128  (|G/K| = 5) -/

def rK128 : Fin 148 := ⟨128, by decide⟩

def R128list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def R128 : Fin 5 → Coordinate 1 := fun i => R128list.getD i.val (0,0,0,0,0)

theorem hpxR128 : Function.Injective (fun i => reduceAux 1 (basisAt rK128) (R128 i)) := by decide
theorem hcardq128 : Nat.card (Coordinate 1 ⧸ reps rK128) = 5 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (128, 0): |T| = 5 -/

def T128_0list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T128_0 : Fin 5 → Coordinate 1 := fun i => T128_0list.getD i.val (0,0,0,0,0)

theorem hfix128_0 : ∀ i, ((T128_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK128)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128) :=
  repsFix_of_siftB rK128 ⟨0, by decide⟩ T128_0 (by decide)

theorem hinj128_0 : Function.Injective
    (fun i => ((T128_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK128)) :=
  repsInj_of_reduceAux rK128 T128_0 (by decide)

theorem hcardT128_0 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK128 ⟨0, by decide⟩ R128 hpxR128 hcardq128 (by decide)).symm

/-- **Cell (128, 0).** -/
theorem cell128_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK128) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK128) (charOfVec rK128 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK128 e (h : Coordinate 1) T128_0 i :=
  species_entry_eq_sum rK128 ⟨0, by decide⟩ e heK h T128_0 hfix128_0 hinj128_0 hcardT128_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK128) (T128_0 i) (hfix128_0 i) h)

/-! ## Cell (128, 3): |T| = 5 -/

def T128_3list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T128_3 : Fin 5 → Coordinate 1 := fun i => T128_3list.getD i.val (0,0,0,0,0)

theorem hfix128_3 : ∀ i, ((T128_3 i : Coordinate 1) : Coordinate 1 ⧸ reps rK128)
    ∈ fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128) :=
  repsFix_of_siftB rK128 ⟨3, by decide⟩ T128_3 (by decide)

theorem hinj128_3 : Function.Injective
    (fun i => ((T128_3 i : Coordinate 1) : Coordinate 1 ⧸ reps rK128)) :=
  repsInj_of_reduceAux rK128 T128_3 (by decide)

theorem hcardT128_3 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK128 ⟨3, by decide⟩ R128 hpxR128 hcardq128 (by decide)).symm

/-- **Cell (128, 3).** -/
theorem cell128_3 (e : List (ZMod 25)) (heK : charOK (basisAt rK128) e = true)
    (h : ↥(reps (⟨3, by decide⟩ : Fin 148))) :
    species (reps (⟨3, by decide⟩ : Fin 148)) h (basisElt (reps rK128) (charOfVec rK128 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK128 e (h : Coordinate 1) T128_3 i :=
  species_entry_eq_sum rK128 ⟨3, by decide⟩ e heK h T128_3 hfix128_3 hinj128_3 hcardT128_3
    (fun i => conj_mem_of_fixedPoints (reps ⟨3, by decide⟩) (reps rK128) (T128_3 i) (hfix128_3 i) h)

/-! ## Cell (128, 10): |T| = 5 -/

def T128_10list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T128_10 : Fin 5 → Coordinate 1 := fun i => T128_10list.getD i.val (0,0,0,0,0)

theorem hfix128_10 : ∀ i, ((T128_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK128)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128) :=
  repsFix_of_siftB rK128 ⟨10, by decide⟩ T128_10 (by decide)

theorem hinj128_10 : Function.Injective
    (fun i => ((T128_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK128)) :=
  repsInj_of_reduceAux rK128 T128_10 (by decide)

theorem hcardT128_10 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK128 ⟨10, by decide⟩ R128 hpxR128 hcardq128 (by decide)).symm

/-- **Cell (128, 10).** -/
theorem cell128_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK128) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK128) (charOfVec rK128 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK128 e (h : Coordinate 1) T128_10 i :=
  species_entry_eq_sum rK128 ⟨10, by decide⟩ e heK h T128_10 hfix128_10 hinj128_10 hcardT128_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK128) (T128_10 i) (hfix128_10 i) h)

/-! ## Cell (128, 12): |T| = 5 -/

def T128_12list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T128_12 : Fin 5 → Coordinate 1 := fun i => T128_12list.getD i.val (0,0,0,0,0)

theorem hfix128_12 : ∀ i, ((T128_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK128)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128) :=
  repsFix_of_siftB rK128 ⟨12, by decide⟩ T128_12 (by decide)

theorem hinj128_12 : Function.Injective
    (fun i => ((T128_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK128)) :=
  repsInj_of_reduceAux rK128 T128_12 (by decide)

theorem hcardT128_12 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK128 ⟨12, by decide⟩ R128 hpxR128 hcardq128 (by decide)).symm

/-- **Cell (128, 12).** -/
theorem cell128_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK128) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK128) (charOfVec rK128 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK128 e (h : Coordinate 1) T128_12 i :=
  species_entry_eq_sum rK128 ⟨12, by decide⟩ e heK h T128_12 hfix128_12 hinj128_12 hcardT128_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK128) (T128_12 i) (hfix128_12 i) h)

/-! ## Cell (128, 21): |T| = 5 -/

def T128_21list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T128_21 : Fin 5 → Coordinate 1 := fun i => T128_21list.getD i.val (0,0,0,0,0)

theorem hfix128_21 : ∀ i, ((T128_21 i : Coordinate 1) : Coordinate 1 ⧸ reps rK128)
    ∈ fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128) :=
  repsFix_of_siftB rK128 ⟨21, by decide⟩ T128_21 (by decide)

theorem hinj128_21 : Function.Injective
    (fun i => ((T128_21 i : Coordinate 1) : Coordinate 1 ⧸ reps rK128)) :=
  repsInj_of_reduceAux rK128 T128_21 (by decide)

theorem hcardT128_21 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK128 ⟨21, by decide⟩ R128 hpxR128 hcardq128 (by decide)).symm

/-- **Cell (128, 21).** -/
theorem cell128_21 (e : List (ZMod 25)) (heK : charOK (basisAt rK128) e = true)
    (h : ↥(reps (⟨21, by decide⟩ : Fin 148))) :
    species (reps (⟨21, by decide⟩ : Fin 148)) h (basisElt (reps rK128) (charOfVec rK128 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK128 e (h : Coordinate 1) T128_21 i :=
  species_entry_eq_sum rK128 ⟨21, by decide⟩ e heK h T128_21 hfix128_21 hinj128_21 hcardT128_21
    (fun i => conj_mem_of_fixedPoints (reps ⟨21, by decide⟩) (reps rK128) (T128_21 i) (hfix128_21 i) h)

/-! ## Cell (128, 28): |T| = 5 -/

def T128_28list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T128_28 : Fin 5 → Coordinate 1 := fun i => T128_28list.getD i.val (0,0,0,0,0)

theorem hfix128_28 : ∀ i, ((T128_28 i : Coordinate 1) : Coordinate 1 ⧸ reps rK128)
    ∈ fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128) :=
  repsFix_of_siftB rK128 ⟨28, by decide⟩ T128_28 (by decide)

theorem hinj128_28 : Function.Injective
    (fun i => ((T128_28 i : Coordinate 1) : Coordinate 1 ⧸ reps rK128)) :=
  repsInj_of_reduceAux rK128 T128_28 (by decide)

theorem hcardT128_28 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK128 ⟨28, by decide⟩ R128 hpxR128 hcardq128 (by decide)).symm

/-- **Cell (128, 28).** -/
theorem cell128_28 (e : List (ZMod 25)) (heK : charOK (basisAt rK128) e = true)
    (h : ↥(reps (⟨28, by decide⟩ : Fin 148))) :
    species (reps (⟨28, by decide⟩ : Fin 148)) h (basisElt (reps rK128) (charOfVec rK128 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK128 e (h : Coordinate 1) T128_28 i :=
  species_entry_eq_sum rK128 ⟨28, by decide⟩ e heK h T128_28 hfix128_28 hinj128_28 hcardT128_28
    (fun i => conj_mem_of_fixedPoints (reps ⟨28, by decide⟩) (reps rK128) (T128_28 i) (hfix128_28 i) h)

/-! ## Cell (128, 34): |T| = 5 -/

def T128_34list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T128_34 : Fin 5 → Coordinate 1 := fun i => T128_34list.getD i.val (0,0,0,0,0)

theorem hfix128_34 : ∀ i, ((T128_34 i : Coordinate 1) : Coordinate 1 ⧸ reps rK128)
    ∈ fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128) :=
  repsFix_of_siftB rK128 ⟨34, by decide⟩ T128_34 (by decide)

theorem hinj128_34 : Function.Injective
    (fun i => ((T128_34 i : Coordinate 1) : Coordinate 1 ⧸ reps rK128)) :=
  repsInj_of_reduceAux rK128 T128_34 (by decide)

theorem hcardT128_34 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK128 ⟨34, by decide⟩ R128 hpxR128 hcardq128 (by decide)).symm

/-- **Cell (128, 34).** -/
theorem cell128_34 (e : List (ZMod 25)) (heK : charOK (basisAt rK128) e = true)
    (h : ↥(reps (⟨34, by decide⟩ : Fin 148))) :
    species (reps (⟨34, by decide⟩ : Fin 148)) h (basisElt (reps rK128) (charOfVec rK128 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK128 e (h : Coordinate 1) T128_34 i :=
  species_entry_eq_sum rK128 ⟨34, by decide⟩ e heK h T128_34 hfix128_34 hinj128_34 hcardT128_34
    (fun i => conj_mem_of_fixedPoints (reps ⟨34, by decide⟩) (reps rK128) (T128_34 i) (hfix128_34 i) h)

/-! ## Cell (128, 41): |T| = 5 -/

def T128_41list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T128_41 : Fin 5 → Coordinate 1 := fun i => T128_41list.getD i.val (0,0,0,0,0)

theorem hfix128_41 : ∀ i, ((T128_41 i : Coordinate 1) : Coordinate 1 ⧸ reps rK128)
    ∈ fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128) :=
  repsFix_of_siftB rK128 ⟨41, by decide⟩ T128_41 (by decide)

theorem hinj128_41 : Function.Injective
    (fun i => ((T128_41 i : Coordinate 1) : Coordinate 1 ⧸ reps rK128)) :=
  repsInj_of_reduceAux rK128 T128_41 (by decide)

theorem hcardT128_41 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK128 ⟨41, by decide⟩ R128 hpxR128 hcardq128 (by decide)).symm

/-- **Cell (128, 41).** -/
theorem cell128_41 (e : List (ZMod 25)) (heK : charOK (basisAt rK128) e = true)
    (h : ↥(reps (⟨41, by decide⟩ : Fin 148))) :
    species (reps (⟨41, by decide⟩ : Fin 148)) h (basisElt (reps rK128) (charOfVec rK128 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK128 e (h : Coordinate 1) T128_41 i :=
  species_entry_eq_sum rK128 ⟨41, by decide⟩ e heK h T128_41 hfix128_41 hinj128_41 hcardT128_41
    (fun i => conj_mem_of_fixedPoints (reps ⟨41, by decide⟩) (reps rK128) (T128_41 i) (hfix128_41 i) h)

/-! ## Cell (128, 47): |T| = 5 -/

def T128_47list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T128_47 : Fin 5 → Coordinate 1 := fun i => T128_47list.getD i.val (0,0,0,0,0)

theorem hfix128_47 : ∀ i, ((T128_47 i : Coordinate 1) : Coordinate 1 ⧸ reps rK128)
    ∈ fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128) :=
  repsFix_of_siftB rK128 ⟨47, by decide⟩ T128_47 (by decide)

theorem hinj128_47 : Function.Injective
    (fun i => ((T128_47 i : Coordinate 1) : Coordinate 1 ⧸ reps rK128)) :=
  repsInj_of_reduceAux rK128 T128_47 (by decide)

theorem hcardT128_47 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK128 ⟨47, by decide⟩ R128 hpxR128 hcardq128 (by decide)).symm

/-- **Cell (128, 47).** -/
theorem cell128_47 (e : List (ZMod 25)) (heK : charOK (basisAt rK128) e = true)
    (h : ↥(reps (⟨47, by decide⟩ : Fin 148))) :
    species (reps (⟨47, by decide⟩ : Fin 148)) h (basisElt (reps rK128) (charOfVec rK128 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK128 e (h : Coordinate 1) T128_47 i :=
  species_entry_eq_sum rK128 ⟨47, by decide⟩ e heK h T128_47 hfix128_47 hinj128_47 hcardT128_47
    (fun i => conj_mem_of_fixedPoints (reps ⟨47, by decide⟩) (reps rK128) (T128_47 i) (hfix128_47 i) h)

/-! ## Cell (128, 50): |T| = 5 -/

def T128_50list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T128_50 : Fin 5 → Coordinate 1 := fun i => T128_50list.getD i.val (0,0,0,0,0)

theorem hfix128_50 : ∀ i, ((T128_50 i : Coordinate 1) : Coordinate 1 ⧸ reps rK128)
    ∈ fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128) :=
  repsFix_of_siftB rK128 ⟨50, by decide⟩ T128_50 (by decide)

theorem hinj128_50 : Function.Injective
    (fun i => ((T128_50 i : Coordinate 1) : Coordinate 1 ⧸ reps rK128)) :=
  repsInj_of_reduceAux rK128 T128_50 (by decide)

theorem hcardT128_50 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK128 ⟨50, by decide⟩ R128 hpxR128 hcardq128 (by decide)).symm

/-- **Cell (128, 50).** -/
theorem cell128_50 (e : List (ZMod 25)) (heK : charOK (basisAt rK128) e = true)
    (h : ↥(reps (⟨50, by decide⟩ : Fin 148))) :
    species (reps (⟨50, by decide⟩ : Fin 148)) h (basisElt (reps rK128) (charOfVec rK128 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK128 e (h : Coordinate 1) T128_50 i :=
  species_entry_eq_sum rK128 ⟨50, by decide⟩ e heK h T128_50 hfix128_50 hinj128_50 hcardT128_50
    (fun i => conj_mem_of_fixedPoints (reps ⟨50, by decide⟩) (reps rK128) (T128_50 i) (hfix128_50 i) h)

/-! ## Cell (128, 53): |T| = 5 -/

def T128_53list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T128_53 : Fin 5 → Coordinate 1 := fun i => T128_53list.getD i.val (0,0,0,0,0)

theorem hfix128_53 : ∀ i, ((T128_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK128)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128) :=
  repsFix_of_siftB rK128 ⟨53, by decide⟩ T128_53 (by decide)

theorem hinj128_53 : Function.Injective
    (fun i => ((T128_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK128)) :=
  repsInj_of_reduceAux rK128 T128_53 (by decide)

theorem hcardT128_53 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK128 ⟨53, by decide⟩ R128 hpxR128 hcardq128 (by decide)).symm

/-- **Cell (128, 53).** -/
theorem cell128_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK128) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK128) (charOfVec rK128 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK128 e (h : Coordinate 1) T128_53 i :=
  species_entry_eq_sum rK128 ⟨53, by decide⟩ e heK h T128_53 hfix128_53 hinj128_53 hcardT128_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK128) (T128_53 i) (hfix128_53 i) h)

/-! ## Cell (128, 82): |T| = 5 -/

def T128_82list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T128_82 : Fin 5 → Coordinate 1 := fun i => T128_82list.getD i.val (0,0,0,0,0)

theorem hfix128_82 : ∀ i, ((T128_82 i : Coordinate 1) : Coordinate 1 ⧸ reps rK128)
    ∈ fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128) :=
  repsFix_of_siftB rK128 ⟨82, by decide⟩ T128_82 (by decide)

theorem hinj128_82 : Function.Injective
    (fun i => ((T128_82 i : Coordinate 1) : Coordinate 1 ⧸ reps rK128)) :=
  repsInj_of_reduceAux rK128 T128_82 (by decide)

theorem hcardT128_82 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK128 ⟨82, by decide⟩ R128 hpxR128 hcardq128 (by decide)).symm

/-- **Cell (128, 82).** -/
theorem cell128_82 (e : List (ZMod 25)) (heK : charOK (basisAt rK128) e = true)
    (h : ↥(reps (⟨82, by decide⟩ : Fin 148))) :
    species (reps (⟨82, by decide⟩ : Fin 148)) h (basisElt (reps rK128) (charOfVec rK128 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK128 e (h : Coordinate 1) T128_82 i :=
  species_entry_eq_sum rK128 ⟨82, by decide⟩ e heK h T128_82 hfix128_82 hinj128_82 hcardT128_82
    (fun i => conj_mem_of_fixedPoints (reps ⟨82, by decide⟩) (reps rK128) (T128_82 i) (hfix128_82 i) h)

/-! ## Cell (128, 90): |T| = 5 -/

def T128_90list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T128_90 : Fin 5 → Coordinate 1 := fun i => T128_90list.getD i.val (0,0,0,0,0)

theorem hfix128_90 : ∀ i, ((T128_90 i : Coordinate 1) : Coordinate 1 ⧸ reps rK128)
    ∈ fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128) :=
  repsFix_of_siftB rK128 ⟨90, by decide⟩ T128_90 (by decide)

theorem hinj128_90 : Function.Injective
    (fun i => ((T128_90 i : Coordinate 1) : Coordinate 1 ⧸ reps rK128)) :=
  repsInj_of_reduceAux rK128 T128_90 (by decide)

theorem hcardT128_90 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK128 ⟨90, by decide⟩ R128 hpxR128 hcardq128 (by decide)).symm

/-- **Cell (128, 90).** -/
theorem cell128_90 (e : List (ZMod 25)) (heK : charOK (basisAt rK128) e = true)
    (h : ↥(reps (⟨90, by decide⟩ : Fin 148))) :
    species (reps (⟨90, by decide⟩ : Fin 148)) h (basisElt (reps rK128) (charOfVec rK128 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK128 e (h : Coordinate 1) T128_90 i :=
  species_entry_eq_sum rK128 ⟨90, by decide⟩ e heK h T128_90 hfix128_90 hinj128_90 hcardT128_90
    (fun i => conj_mem_of_fixedPoints (reps ⟨90, by decide⟩) (reps rK128) (T128_90 i) (hfix128_90 i) h)

/-! ## Cell (128, 96): |T| = 5 -/

def T128_96list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T128_96 : Fin 5 → Coordinate 1 := fun i => T128_96list.getD i.val (0,0,0,0,0)

theorem hfix128_96 : ∀ i, ((T128_96 i : Coordinate 1) : Coordinate 1 ⧸ reps rK128)
    ∈ fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128) :=
  repsFix_of_siftB rK128 ⟨96, by decide⟩ T128_96 (by decide)

theorem hinj128_96 : Function.Injective
    (fun i => ((T128_96 i : Coordinate 1) : Coordinate 1 ⧸ reps rK128)) :=
  repsInj_of_reduceAux rK128 T128_96 (by decide)

theorem hcardT128_96 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK128 ⟨96, by decide⟩ R128 hpxR128 hcardq128 (by decide)).symm

/-- **Cell (128, 96).** -/
theorem cell128_96 (e : List (ZMod 25)) (heK : charOK (basisAt rK128) e = true)
    (h : ↥(reps (⟨96, by decide⟩ : Fin 148))) :
    species (reps (⟨96, by decide⟩ : Fin 148)) h (basisElt (reps rK128) (charOfVec rK128 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK128 e (h : Coordinate 1) T128_96 i :=
  species_entry_eq_sum rK128 ⟨96, by decide⟩ e heK h T128_96 hfix128_96 hinj128_96 hcardT128_96
    (fun i => conj_mem_of_fixedPoints (reps ⟨96, by decide⟩) (reps rK128) (T128_96 i) (hfix128_96 i) h)

/-! ## Cell (128, 103): |T| = 5 -/

def T128_103list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T128_103 : Fin 5 → Coordinate 1 := fun i => T128_103list.getD i.val (0,0,0,0,0)

theorem hfix128_103 : ∀ i, ((T128_103 i : Coordinate 1) : Coordinate 1 ⧸ reps rK128)
    ∈ fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128) :=
  repsFix_of_siftB rK128 ⟨103, by decide⟩ T128_103 (by decide)

theorem hinj128_103 : Function.Injective
    (fun i => ((T128_103 i : Coordinate 1) : Coordinate 1 ⧸ reps rK128)) :=
  repsInj_of_reduceAux rK128 T128_103 (by decide)

theorem hcardT128_103 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK128 ⟨103, by decide⟩ R128 hpxR128 hcardq128 (by decide)).symm

/-- **Cell (128, 103).** -/
theorem cell128_103 (e : List (ZMod 25)) (heK : charOK (basisAt rK128) e = true)
    (h : ↥(reps (⟨103, by decide⟩ : Fin 148))) :
    species (reps (⟨103, by decide⟩ : Fin 148)) h (basisElt (reps rK128) (charOfVec rK128 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK128 e (h : Coordinate 1) T128_103 i :=
  species_entry_eq_sum rK128 ⟨103, by decide⟩ e heK h T128_103 hfix128_103 hinj128_103 hcardT128_103
    (fun i => conj_mem_of_fixedPoints (reps ⟨103, by decide⟩) (reps rK128) (T128_103 i) (hfix128_103 i) h)

/-! ## Cell (128, 109): |T| = 5 -/

def T128_109list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T128_109 : Fin 5 → Coordinate 1 := fun i => T128_109list.getD i.val (0,0,0,0,0)

theorem hfix128_109 : ∀ i, ((T128_109 i : Coordinate 1) : Coordinate 1 ⧸ reps rK128)
    ∈ fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128) :=
  repsFix_of_siftB rK128 ⟨109, by decide⟩ T128_109 (by decide)

theorem hinj128_109 : Function.Injective
    (fun i => ((T128_109 i : Coordinate 1) : Coordinate 1 ⧸ reps rK128)) :=
  repsInj_of_reduceAux rK128 T128_109 (by decide)

theorem hcardT128_109 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK128 ⟨109, by decide⟩ R128 hpxR128 hcardq128 (by decide)).symm

/-- **Cell (128, 109).** -/
theorem cell128_109 (e : List (ZMod 25)) (heK : charOK (basisAt rK128) e = true)
    (h : ↥(reps (⟨109, by decide⟩ : Fin 148))) :
    species (reps (⟨109, by decide⟩ : Fin 148)) h (basisElt (reps rK128) (charOfVec rK128 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK128 e (h : Coordinate 1) T128_109 i :=
  species_entry_eq_sum rK128 ⟨109, by decide⟩ e heK h T128_109 hfix128_109 hinj128_109 hcardT128_109
    (fun i => conj_mem_of_fixedPoints (reps ⟨109, by decide⟩) (reps rK128) (T128_109 i) (hfix128_109 i) h)

/-! ## Cell (128, 112): |T| = 5 -/

def T128_112list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T128_112 : Fin 5 → Coordinate 1 := fun i => T128_112list.getD i.val (0,0,0,0,0)

theorem hfix128_112 : ∀ i, ((T128_112 i : Coordinate 1) : Coordinate 1 ⧸ reps rK128)
    ∈ fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128) :=
  repsFix_of_siftB rK128 ⟨112, by decide⟩ T128_112 (by decide)

theorem hinj128_112 : Function.Injective
    (fun i => ((T128_112 i : Coordinate 1) : Coordinate 1 ⧸ reps rK128)) :=
  repsInj_of_reduceAux rK128 T128_112 (by decide)

theorem hcardT128_112 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK128 ⟨112, by decide⟩ R128 hpxR128 hcardq128 (by decide)).symm

/-- **Cell (128, 112).** -/
theorem cell128_112 (e : List (ZMod 25)) (heK : charOK (basisAt rK128) e = true)
    (h : ↥(reps (⟨112, by decide⟩ : Fin 148))) :
    species (reps (⟨112, by decide⟩ : Fin 148)) h (basisElt (reps rK128) (charOfVec rK128 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK128 e (h : Coordinate 1) T128_112 i :=
  species_entry_eq_sum rK128 ⟨112, by decide⟩ e heK h T128_112 hfix128_112 hinj128_112 hcardT128_112
    (fun i => conj_mem_of_fixedPoints (reps ⟨112, by decide⟩) (reps rK128) (T128_112 i) (hfix128_112 i) h)

/-! ## Cell (128, 128): |T| = 5 -/

def T128_128list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T128_128 : Fin 5 → Coordinate 1 := fun i => T128_128list.getD i.val (0,0,0,0,0)

theorem hfix128_128 : ∀ i, ((T128_128 i : Coordinate 1) : Coordinate 1 ⧸ reps rK128)
    ∈ fixedPoints (reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128) :=
  repsFix_of_siftB rK128 ⟨128, by decide⟩ T128_128 (by decide)

theorem hinj128_128 : Function.Injective
    (fun i => ((T128_128 i : Coordinate 1) : Coordinate 1 ⧸ reps rK128)) :=
  repsInj_of_reduceAux rK128 T128_128 (by decide)

theorem hcardT128_128 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK128 ⟨128, by decide⟩ R128 hpxR128 hcardq128 (by decide)).symm

/-- **Cell (128, 128).** -/
theorem cell128_128 (e : List (ZMod 25)) (heK : charOK (basisAt rK128) e = true)
    (h : ↥(reps (⟨128, by decide⟩ : Fin 148))) :
    species (reps (⟨128, by decide⟩ : Fin 148)) h (basisElt (reps rK128) (charOfVec rK128 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK128 e (h : Coordinate 1) T128_128 i :=
  species_entry_eq_sum rK128 ⟨128, by decide⟩ e heK h T128_128 hfix128_128 hinj128_128 hcardT128_128
    (fun i => conj_mem_of_fixedPoints (reps ⟨128, by decide⟩) (reps rK128) (T128_128 i) (hfix128_128 i) h)

namespace Q2

def R128_2 : Fin 5 → Coordinate 2 := fun i => R128list.getD i.val (0,0,0,0,0)
theorem hpxR128_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK128) (R128_2 i)) := by decide
theorem hcardq128_2 : Nat.card (Coordinate 2 ⧸ reps rK128) = 5 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (128, 0) twin -/

def T128_0_2 : Fin 5 → Coordinate 2 := fun i => T128_0list.getD i.val (0,0,0,0,0)

theorem hfix128_0_2 : ∀ i, ((T128_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK128)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK128) :=
  repsFix_of_siftB2 rK128 ⟨0, by decide⟩ T128_0_2 (by decide)

theorem hinj128_0_2 : Function.Injective
    (fun i => ((T128_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK128)) :=
  repsInj_of_reduceAux2 rK128 T128_0_2 (by decide)

theorem hcardT128_0_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK128)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK128 ⟨0, by decide⟩ R128_2 hpxR128_2 hcardq128_2 (by decide)).symm

/-- **Cell (128, 0) twin (q=2).** -/
theorem cell128_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK128) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK128) (charOfVec2 rK128 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK128 e (h : Coordinate 2) T128_0_2 i :=
  species_entry_eq_sum rK128 ⟨0, by decide⟩ e heK h T128_0_2 hfix128_0_2 hinj128_0_2 hcardT128_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK128) (T128_0_2 i) (hfix128_0_2 i) h)

/-! ### Cell (128, 3) twin -/

def T128_3_2 : Fin 5 → Coordinate 2 := fun i => T128_3list.getD i.val (0,0,0,0,0)

theorem hfix128_3_2 : ∀ i, ((T128_3_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK128)
    ∈ fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK128) :=
  repsFix_of_siftB2 rK128 ⟨3, by decide⟩ T128_3_2 (by decide)

theorem hinj128_3_2 : Function.Injective
    (fun i => ((T128_3_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK128)) :=
  repsInj_of_reduceAux2 rK128 T128_3_2 (by decide)

theorem hcardT128_3_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK128)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK128 ⟨3, by decide⟩ R128_2 hpxR128_2 hcardq128_2 (by decide)).symm

/-- **Cell (128, 3) twin (q=2).** -/
theorem cell128_3_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK128) e = true)
    (h : ↥(reps (⟨3, by decide⟩ : Fin 148))) :
    species (reps (⟨3, by decide⟩ : Fin 148)) h (basisElt (reps rK128) (charOfVec2 rK128 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK128 e (h : Coordinate 2) T128_3_2 i :=
  species_entry_eq_sum rK128 ⟨3, by decide⟩ e heK h T128_3_2 hfix128_3_2 hinj128_3_2 hcardT128_3_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨3, by decide⟩) (reps rK128) (T128_3_2 i) (hfix128_3_2 i) h)

/-! ### Cell (128, 10) twin -/

def T128_10_2 : Fin 5 → Coordinate 2 := fun i => T128_10list.getD i.val (0,0,0,0,0)

theorem hfix128_10_2 : ∀ i, ((T128_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK128)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK128) :=
  repsFix_of_siftB2 rK128 ⟨10, by decide⟩ T128_10_2 (by decide)

theorem hinj128_10_2 : Function.Injective
    (fun i => ((T128_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK128)) :=
  repsInj_of_reduceAux2 rK128 T128_10_2 (by decide)

theorem hcardT128_10_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK128)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK128 ⟨10, by decide⟩ R128_2 hpxR128_2 hcardq128_2 (by decide)).symm

/-- **Cell (128, 10) twin (q=2).** -/
theorem cell128_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK128) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK128) (charOfVec2 rK128 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK128 e (h : Coordinate 2) T128_10_2 i :=
  species_entry_eq_sum rK128 ⟨10, by decide⟩ e heK h T128_10_2 hfix128_10_2 hinj128_10_2 hcardT128_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK128) (T128_10_2 i) (hfix128_10_2 i) h)

/-! ### Cell (128, 12) twin -/

def T128_12_2 : Fin 5 → Coordinate 2 := fun i => T128_12list.getD i.val (0,0,0,0,0)

theorem hfix128_12_2 : ∀ i, ((T128_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK128)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK128) :=
  repsFix_of_siftB2 rK128 ⟨12, by decide⟩ T128_12_2 (by decide)

theorem hinj128_12_2 : Function.Injective
    (fun i => ((T128_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK128)) :=
  repsInj_of_reduceAux2 rK128 T128_12_2 (by decide)

theorem hcardT128_12_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK128)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK128 ⟨12, by decide⟩ R128_2 hpxR128_2 hcardq128_2 (by decide)).symm

/-- **Cell (128, 12) twin (q=2).** -/
theorem cell128_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK128) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK128) (charOfVec2 rK128 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK128 e (h : Coordinate 2) T128_12_2 i :=
  species_entry_eq_sum rK128 ⟨12, by decide⟩ e heK h T128_12_2 hfix128_12_2 hinj128_12_2 hcardT128_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK128) (T128_12_2 i) (hfix128_12_2 i) h)

/-! ### Cell (128, 21) twin -/

def T128_21_2 : Fin 5 → Coordinate 2 := fun i => T128_21list.getD i.val (0,0,0,0,0)

theorem hfix128_21_2 : ∀ i, ((T128_21_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK128)
    ∈ fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK128) :=
  repsFix_of_siftB2 rK128 ⟨21, by decide⟩ T128_21_2 (by decide)

theorem hinj128_21_2 : Function.Injective
    (fun i => ((T128_21_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK128)) :=
  repsInj_of_reduceAux2 rK128 T128_21_2 (by decide)

theorem hcardT128_21_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK128)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK128 ⟨21, by decide⟩ R128_2 hpxR128_2 hcardq128_2 (by decide)).symm

/-- **Cell (128, 21) twin (q=2).** -/
theorem cell128_21_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK128) e = true)
    (h : ↥(reps (⟨21, by decide⟩ : Fin 148))) :
    species (reps (⟨21, by decide⟩ : Fin 148)) h (basisElt (reps rK128) (charOfVec2 rK128 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK128 e (h : Coordinate 2) T128_21_2 i :=
  species_entry_eq_sum rK128 ⟨21, by decide⟩ e heK h T128_21_2 hfix128_21_2 hinj128_21_2 hcardT128_21_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨21, by decide⟩) (reps rK128) (T128_21_2 i) (hfix128_21_2 i) h)

/-! ### Cell (128, 28) twin -/

def T128_28_2 : Fin 5 → Coordinate 2 := fun i => T128_28list.getD i.val (0,0,0,0,0)

theorem hfix128_28_2 : ∀ i, ((T128_28_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK128)
    ∈ fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK128) :=
  repsFix_of_siftB2 rK128 ⟨28, by decide⟩ T128_28_2 (by decide)

theorem hinj128_28_2 : Function.Injective
    (fun i => ((T128_28_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK128)) :=
  repsInj_of_reduceAux2 rK128 T128_28_2 (by decide)

theorem hcardT128_28_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK128)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK128 ⟨28, by decide⟩ R128_2 hpxR128_2 hcardq128_2 (by decide)).symm

/-- **Cell (128, 28) twin (q=2).** -/
theorem cell128_28_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK128) e = true)
    (h : ↥(reps (⟨28, by decide⟩ : Fin 148))) :
    species (reps (⟨28, by decide⟩ : Fin 148)) h (basisElt (reps rK128) (charOfVec2 rK128 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK128 e (h : Coordinate 2) T128_28_2 i :=
  species_entry_eq_sum rK128 ⟨28, by decide⟩ e heK h T128_28_2 hfix128_28_2 hinj128_28_2 hcardT128_28_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨28, by decide⟩) (reps rK128) (T128_28_2 i) (hfix128_28_2 i) h)

/-! ### Cell (128, 34) twin -/

def T128_34_2 : Fin 5 → Coordinate 2 := fun i => T128_34list.getD i.val (0,0,0,0,0)

theorem hfix128_34_2 : ∀ i, ((T128_34_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK128)
    ∈ fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK128) :=
  repsFix_of_siftB2 rK128 ⟨34, by decide⟩ T128_34_2 (by decide)

theorem hinj128_34_2 : Function.Injective
    (fun i => ((T128_34_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK128)) :=
  repsInj_of_reduceAux2 rK128 T128_34_2 (by decide)

theorem hcardT128_34_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK128)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK128 ⟨34, by decide⟩ R128_2 hpxR128_2 hcardq128_2 (by decide)).symm

/-- **Cell (128, 34) twin (q=2).** -/
theorem cell128_34_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK128) e = true)
    (h : ↥(reps (⟨34, by decide⟩ : Fin 148))) :
    species (reps (⟨34, by decide⟩ : Fin 148)) h (basisElt (reps rK128) (charOfVec2 rK128 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK128 e (h : Coordinate 2) T128_34_2 i :=
  species_entry_eq_sum rK128 ⟨34, by decide⟩ e heK h T128_34_2 hfix128_34_2 hinj128_34_2 hcardT128_34_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨34, by decide⟩) (reps rK128) (T128_34_2 i) (hfix128_34_2 i) h)

/-! ### Cell (128, 41) twin -/

def T128_41_2 : Fin 5 → Coordinate 2 := fun i => T128_41list.getD i.val (0,0,0,0,0)

theorem hfix128_41_2 : ∀ i, ((T128_41_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK128)
    ∈ fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK128) :=
  repsFix_of_siftB2 rK128 ⟨41, by decide⟩ T128_41_2 (by decide)

theorem hinj128_41_2 : Function.Injective
    (fun i => ((T128_41_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK128)) :=
  repsInj_of_reduceAux2 rK128 T128_41_2 (by decide)

theorem hcardT128_41_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK128)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK128 ⟨41, by decide⟩ R128_2 hpxR128_2 hcardq128_2 (by decide)).symm

/-- **Cell (128, 41) twin (q=2).** -/
theorem cell128_41_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK128) e = true)
    (h : ↥(reps (⟨41, by decide⟩ : Fin 148))) :
    species (reps (⟨41, by decide⟩ : Fin 148)) h (basisElt (reps rK128) (charOfVec2 rK128 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK128 e (h : Coordinate 2) T128_41_2 i :=
  species_entry_eq_sum rK128 ⟨41, by decide⟩ e heK h T128_41_2 hfix128_41_2 hinj128_41_2 hcardT128_41_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨41, by decide⟩) (reps rK128) (T128_41_2 i) (hfix128_41_2 i) h)

/-! ### Cell (128, 47) twin -/

def T128_47_2 : Fin 5 → Coordinate 2 := fun i => T128_47list.getD i.val (0,0,0,0,0)

theorem hfix128_47_2 : ∀ i, ((T128_47_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK128)
    ∈ fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK128) :=
  repsFix_of_siftB2 rK128 ⟨47, by decide⟩ T128_47_2 (by decide)

theorem hinj128_47_2 : Function.Injective
    (fun i => ((T128_47_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK128)) :=
  repsInj_of_reduceAux2 rK128 T128_47_2 (by decide)

theorem hcardT128_47_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK128)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK128 ⟨47, by decide⟩ R128_2 hpxR128_2 hcardq128_2 (by decide)).symm

/-- **Cell (128, 47) twin (q=2).** -/
theorem cell128_47_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK128) e = true)
    (h : ↥(reps (⟨47, by decide⟩ : Fin 148))) :
    species (reps (⟨47, by decide⟩ : Fin 148)) h (basisElt (reps rK128) (charOfVec2 rK128 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK128 e (h : Coordinate 2) T128_47_2 i :=
  species_entry_eq_sum rK128 ⟨47, by decide⟩ e heK h T128_47_2 hfix128_47_2 hinj128_47_2 hcardT128_47_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨47, by decide⟩) (reps rK128) (T128_47_2 i) (hfix128_47_2 i) h)

/-! ### Cell (128, 50) twin -/

def T128_50_2 : Fin 5 → Coordinate 2 := fun i => T128_50list.getD i.val (0,0,0,0,0)

theorem hfix128_50_2 : ∀ i, ((T128_50_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK128)
    ∈ fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK128) :=
  repsFix_of_siftB2 rK128 ⟨50, by decide⟩ T128_50_2 (by decide)

theorem hinj128_50_2 : Function.Injective
    (fun i => ((T128_50_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK128)) :=
  repsInj_of_reduceAux2 rK128 T128_50_2 (by decide)

theorem hcardT128_50_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK128)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK128 ⟨50, by decide⟩ R128_2 hpxR128_2 hcardq128_2 (by decide)).symm

/-- **Cell (128, 50) twin (q=2).** -/
theorem cell128_50_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK128) e = true)
    (h : ↥(reps (⟨50, by decide⟩ : Fin 148))) :
    species (reps (⟨50, by decide⟩ : Fin 148)) h (basisElt (reps rK128) (charOfVec2 rK128 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK128 e (h : Coordinate 2) T128_50_2 i :=
  species_entry_eq_sum rK128 ⟨50, by decide⟩ e heK h T128_50_2 hfix128_50_2 hinj128_50_2 hcardT128_50_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨50, by decide⟩) (reps rK128) (T128_50_2 i) (hfix128_50_2 i) h)

/-! ### Cell (128, 53) twin -/

def T128_53_2 : Fin 5 → Coordinate 2 := fun i => T128_53list.getD i.val (0,0,0,0,0)

theorem hfix128_53_2 : ∀ i, ((T128_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK128)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK128) :=
  repsFix_of_siftB2 rK128 ⟨53, by decide⟩ T128_53_2 (by decide)

theorem hinj128_53_2 : Function.Injective
    (fun i => ((T128_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK128)) :=
  repsInj_of_reduceAux2 rK128 T128_53_2 (by decide)

theorem hcardT128_53_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK128)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK128 ⟨53, by decide⟩ R128_2 hpxR128_2 hcardq128_2 (by decide)).symm

/-- **Cell (128, 53) twin (q=2).** -/
theorem cell128_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK128) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK128) (charOfVec2 rK128 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK128 e (h : Coordinate 2) T128_53_2 i :=
  species_entry_eq_sum rK128 ⟨53, by decide⟩ e heK h T128_53_2 hfix128_53_2 hinj128_53_2 hcardT128_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK128) (T128_53_2 i) (hfix128_53_2 i) h)

/-! ### Cell (128, 82) twin -/

def T128_82_2 : Fin 5 → Coordinate 2 := fun i => T128_82list.getD i.val (0,0,0,0,0)

theorem hfix128_82_2 : ∀ i, ((T128_82_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK128)
    ∈ fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK128) :=
  repsFix_of_siftB2 rK128 ⟨82, by decide⟩ T128_82_2 (by decide)

theorem hinj128_82_2 : Function.Injective
    (fun i => ((T128_82_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK128)) :=
  repsInj_of_reduceAux2 rK128 T128_82_2 (by decide)

theorem hcardT128_82_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK128)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK128 ⟨82, by decide⟩ R128_2 hpxR128_2 hcardq128_2 (by decide)).symm

/-- **Cell (128, 82) twin (q=2).** -/
theorem cell128_82_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK128) e = true)
    (h : ↥(reps (⟨82, by decide⟩ : Fin 148))) :
    species (reps (⟨82, by decide⟩ : Fin 148)) h (basisElt (reps rK128) (charOfVec2 rK128 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK128 e (h : Coordinate 2) T128_82_2 i :=
  species_entry_eq_sum rK128 ⟨82, by decide⟩ e heK h T128_82_2 hfix128_82_2 hinj128_82_2 hcardT128_82_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨82, by decide⟩) (reps rK128) (T128_82_2 i) (hfix128_82_2 i) h)

/-! ### Cell (128, 90) twin -/

def T128_90_2 : Fin 5 → Coordinate 2 := fun i => T128_90list.getD i.val (0,0,0,0,0)

theorem hfix128_90_2 : ∀ i, ((T128_90_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK128)
    ∈ fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK128) :=
  repsFix_of_siftB2 rK128 ⟨90, by decide⟩ T128_90_2 (by decide)

theorem hinj128_90_2 : Function.Injective
    (fun i => ((T128_90_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK128)) :=
  repsInj_of_reduceAux2 rK128 T128_90_2 (by decide)

theorem hcardT128_90_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK128)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK128 ⟨90, by decide⟩ R128_2 hpxR128_2 hcardq128_2 (by decide)).symm

/-- **Cell (128, 90) twin (q=2).** -/
theorem cell128_90_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK128) e = true)
    (h : ↥(reps (⟨90, by decide⟩ : Fin 148))) :
    species (reps (⟨90, by decide⟩ : Fin 148)) h (basisElt (reps rK128) (charOfVec2 rK128 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK128 e (h : Coordinate 2) T128_90_2 i :=
  species_entry_eq_sum rK128 ⟨90, by decide⟩ e heK h T128_90_2 hfix128_90_2 hinj128_90_2 hcardT128_90_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨90, by decide⟩) (reps rK128) (T128_90_2 i) (hfix128_90_2 i) h)

/-! ### Cell (128, 96) twin -/

def T128_96_2 : Fin 5 → Coordinate 2 := fun i => T128_96list.getD i.val (0,0,0,0,0)

theorem hfix128_96_2 : ∀ i, ((T128_96_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK128)
    ∈ fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK128) :=
  repsFix_of_siftB2 rK128 ⟨96, by decide⟩ T128_96_2 (by decide)

theorem hinj128_96_2 : Function.Injective
    (fun i => ((T128_96_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK128)) :=
  repsInj_of_reduceAux2 rK128 T128_96_2 (by decide)

theorem hcardT128_96_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK128)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK128 ⟨96, by decide⟩ R128_2 hpxR128_2 hcardq128_2 (by decide)).symm

/-- **Cell (128, 96) twin (q=2).** -/
theorem cell128_96_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK128) e = true)
    (h : ↥(reps (⟨96, by decide⟩ : Fin 148))) :
    species (reps (⟨96, by decide⟩ : Fin 148)) h (basisElt (reps rK128) (charOfVec2 rK128 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK128 e (h : Coordinate 2) T128_96_2 i :=
  species_entry_eq_sum rK128 ⟨96, by decide⟩ e heK h T128_96_2 hfix128_96_2 hinj128_96_2 hcardT128_96_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨96, by decide⟩) (reps rK128) (T128_96_2 i) (hfix128_96_2 i) h)

/-! ### Cell (128, 103) twin -/

def T128_103_2 : Fin 5 → Coordinate 2 := fun i => T128_103list.getD i.val (0,0,0,0,0)

theorem hfix128_103_2 : ∀ i, ((T128_103_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK128)
    ∈ fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK128) :=
  repsFix_of_siftB2 rK128 ⟨103, by decide⟩ T128_103_2 (by decide)

theorem hinj128_103_2 : Function.Injective
    (fun i => ((T128_103_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK128)) :=
  repsInj_of_reduceAux2 rK128 T128_103_2 (by decide)

theorem hcardT128_103_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK128)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK128 ⟨103, by decide⟩ R128_2 hpxR128_2 hcardq128_2 (by decide)).symm

/-- **Cell (128, 103) twin (q=2).** -/
theorem cell128_103_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK128) e = true)
    (h : ↥(reps (⟨103, by decide⟩ : Fin 148))) :
    species (reps (⟨103, by decide⟩ : Fin 148)) h (basisElt (reps rK128) (charOfVec2 rK128 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK128 e (h : Coordinate 2) T128_103_2 i :=
  species_entry_eq_sum rK128 ⟨103, by decide⟩ e heK h T128_103_2 hfix128_103_2 hinj128_103_2 hcardT128_103_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨103, by decide⟩) (reps rK128) (T128_103_2 i) (hfix128_103_2 i) h)

/-! ### Cell (128, 109) twin -/

def T128_109_2 : Fin 5 → Coordinate 2 := fun i => T128_109list.getD i.val (0,0,0,0,0)

theorem hfix128_109_2 : ∀ i, ((T128_109_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK128)
    ∈ fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK128) :=
  repsFix_of_siftB2 rK128 ⟨109, by decide⟩ T128_109_2 (by decide)

theorem hinj128_109_2 : Function.Injective
    (fun i => ((T128_109_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK128)) :=
  repsInj_of_reduceAux2 rK128 T128_109_2 (by decide)

theorem hcardT128_109_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK128)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK128 ⟨109, by decide⟩ R128_2 hpxR128_2 hcardq128_2 (by decide)).symm

/-- **Cell (128, 109) twin (q=2).** -/
theorem cell128_109_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK128) e = true)
    (h : ↥(reps (⟨109, by decide⟩ : Fin 148))) :
    species (reps (⟨109, by decide⟩ : Fin 148)) h (basisElt (reps rK128) (charOfVec2 rK128 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK128 e (h : Coordinate 2) T128_109_2 i :=
  species_entry_eq_sum rK128 ⟨109, by decide⟩ e heK h T128_109_2 hfix128_109_2 hinj128_109_2 hcardT128_109_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨109, by decide⟩) (reps rK128) (T128_109_2 i) (hfix128_109_2 i) h)

/-! ### Cell (128, 112) twin -/

def T128_112_2 : Fin 5 → Coordinate 2 := fun i => T128_112list.getD i.val (0,0,0,0,0)

theorem hfix128_112_2 : ∀ i, ((T128_112_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK128)
    ∈ fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK128) :=
  repsFix_of_siftB2 rK128 ⟨112, by decide⟩ T128_112_2 (by decide)

theorem hinj128_112_2 : Function.Injective
    (fun i => ((T128_112_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK128)) :=
  repsInj_of_reduceAux2 rK128 T128_112_2 (by decide)

theorem hcardT128_112_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK128)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK128 ⟨112, by decide⟩ R128_2 hpxR128_2 hcardq128_2 (by decide)).symm

/-- **Cell (128, 112) twin (q=2).** -/
theorem cell128_112_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK128) e = true)
    (h : ↥(reps (⟨112, by decide⟩ : Fin 148))) :
    species (reps (⟨112, by decide⟩ : Fin 148)) h (basisElt (reps rK128) (charOfVec2 rK128 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK128 e (h : Coordinate 2) T128_112_2 i :=
  species_entry_eq_sum rK128 ⟨112, by decide⟩ e heK h T128_112_2 hfix128_112_2 hinj128_112_2 hcardT128_112_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨112, by decide⟩) (reps rK128) (T128_112_2 i) (hfix128_112_2 i) h)

/-! ### Cell (128, 128) twin -/

def T128_128_2 : Fin 5 → Coordinate 2 := fun i => T128_128list.getD i.val (0,0,0,0,0)

theorem hfix128_128_2 : ∀ i, ((T128_128_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK128)
    ∈ fixedPoints (reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK128) :=
  repsFix_of_siftB2 rK128 ⟨128, by decide⟩ T128_128_2 (by decide)

theorem hinj128_128_2 : Function.Injective
    (fun i => ((T128_128_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK128)) :=
  repsInj_of_reduceAux2 rK128 T128_128_2 (by decide)

theorem hcardT128_128_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK128)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK128 ⟨128, by decide⟩ R128_2 hpxR128_2 hcardq128_2 (by decide)).symm

/-- **Cell (128, 128) twin (q=2).** -/
theorem cell128_128_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK128) e = true)
    (h : ↥(reps (⟨128, by decide⟩ : Fin 148))) :
    species (reps (⟨128, by decide⟩ : Fin 148)) h (basisElt (reps rK128) (charOfVec2 rK128 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK128 e (h : Coordinate 2) T128_128_2 i :=
  species_entry_eq_sum rK128 ⟨128, by decide⟩ e heK h T128_128_2 hfix128_128_2 hinj128_128_2 hcardT128_128_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨128, by decide⟩) (reps rK128) (T128_128_2 i) (hfix128_128_2 i) h)

end Q2

/-! # K-class rK = 129  (|G/K| = 5) -/

def rK129 : Fin 148 := ⟨129, by decide⟩

def R129list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def R129 : Fin 5 → Coordinate 1 := fun i => R129list.getD i.val (0,0,0,0,0)

theorem hpxR129 : Function.Injective (fun i => reduceAux 1 (basisAt rK129) (R129 i)) := by decide
theorem hcardq129 : Nat.card (Coordinate 1 ⧸ reps rK129) = 5 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (129, 0): |T| = 5 -/

def T129_0list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T129_0 : Fin 5 → Coordinate 1 := fun i => T129_0list.getD i.val (0,0,0,0,0)

theorem hfix129_0 : ∀ i, ((T129_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK129)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129) :=
  repsFix_of_siftB rK129 ⟨0, by decide⟩ T129_0 (by decide)

theorem hinj129_0 : Function.Injective
    (fun i => ((T129_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK129)) :=
  repsInj_of_reduceAux rK129 T129_0 (by decide)

theorem hcardT129_0 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK129 ⟨0, by decide⟩ R129 hpxR129 hcardq129 (by decide)).symm

/-- **Cell (129, 0).** -/
theorem cell129_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK129) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK129) (charOfVec rK129 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK129 e (h : Coordinate 1) T129_0 i :=
  species_entry_eq_sum rK129 ⟨0, by decide⟩ e heK h T129_0 hfix129_0 hinj129_0 hcardT129_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK129) (T129_0 i) (hfix129_0 i) h)

/-! ## Cell (129, 3): |T| = 5 -/

def T129_3list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T129_3 : Fin 5 → Coordinate 1 := fun i => T129_3list.getD i.val (0,0,0,0,0)

theorem hfix129_3 : ∀ i, ((T129_3 i : Coordinate 1) : Coordinate 1 ⧸ reps rK129)
    ∈ fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129) :=
  repsFix_of_siftB rK129 ⟨3, by decide⟩ T129_3 (by decide)

theorem hinj129_3 : Function.Injective
    (fun i => ((T129_3 i : Coordinate 1) : Coordinate 1 ⧸ reps rK129)) :=
  repsInj_of_reduceAux rK129 T129_3 (by decide)

theorem hcardT129_3 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK129 ⟨3, by decide⟩ R129 hpxR129 hcardq129 (by decide)).symm

/-- **Cell (129, 3).** -/
theorem cell129_3 (e : List (ZMod 25)) (heK : charOK (basisAt rK129) e = true)
    (h : ↥(reps (⟨3, by decide⟩ : Fin 148))) :
    species (reps (⟨3, by decide⟩ : Fin 148)) h (basisElt (reps rK129) (charOfVec rK129 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK129 e (h : Coordinate 1) T129_3 i :=
  species_entry_eq_sum rK129 ⟨3, by decide⟩ e heK h T129_3 hfix129_3 hinj129_3 hcardT129_3
    (fun i => conj_mem_of_fixedPoints (reps ⟨3, by decide⟩) (reps rK129) (T129_3 i) (hfix129_3 i) h)

/-! ## Cell (129, 10): |T| = 5 -/

def T129_10list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T129_10 : Fin 5 → Coordinate 1 := fun i => T129_10list.getD i.val (0,0,0,0,0)

theorem hfix129_10 : ∀ i, ((T129_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK129)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129) :=
  repsFix_of_siftB rK129 ⟨10, by decide⟩ T129_10 (by decide)

theorem hinj129_10 : Function.Injective
    (fun i => ((T129_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK129)) :=
  repsInj_of_reduceAux rK129 T129_10 (by decide)

theorem hcardT129_10 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK129 ⟨10, by decide⟩ R129 hpxR129 hcardq129 (by decide)).symm

/-- **Cell (129, 10).** -/
theorem cell129_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK129) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK129) (charOfVec rK129 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK129 e (h : Coordinate 1) T129_10 i :=
  species_entry_eq_sum rK129 ⟨10, by decide⟩ e heK h T129_10 hfix129_10 hinj129_10 hcardT129_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK129) (T129_10 i) (hfix129_10 i) h)

/-! ## Cell (129, 12): |T| = 5 -/

def T129_12list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T129_12 : Fin 5 → Coordinate 1 := fun i => T129_12list.getD i.val (0,0,0,0,0)

theorem hfix129_12 : ∀ i, ((T129_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK129)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129) :=
  repsFix_of_siftB rK129 ⟨12, by decide⟩ T129_12 (by decide)

theorem hinj129_12 : Function.Injective
    (fun i => ((T129_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK129)) :=
  repsInj_of_reduceAux rK129 T129_12 (by decide)

theorem hcardT129_12 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK129 ⟨12, by decide⟩ R129 hpxR129 hcardq129 (by decide)).symm

/-- **Cell (129, 12).** -/
theorem cell129_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK129) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK129) (charOfVec rK129 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK129 e (h : Coordinate 1) T129_12 i :=
  species_entry_eq_sum rK129 ⟨12, by decide⟩ e heK h T129_12 hfix129_12 hinj129_12 hcardT129_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK129) (T129_12 i) (hfix129_12 i) h)

/-! ## Cell (129, 21): |T| = 5 -/

def T129_21list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T129_21 : Fin 5 → Coordinate 1 := fun i => T129_21list.getD i.val (0,0,0,0,0)

theorem hfix129_21 : ∀ i, ((T129_21 i : Coordinate 1) : Coordinate 1 ⧸ reps rK129)
    ∈ fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129) :=
  repsFix_of_siftB rK129 ⟨21, by decide⟩ T129_21 (by decide)

theorem hinj129_21 : Function.Injective
    (fun i => ((T129_21 i : Coordinate 1) : Coordinate 1 ⧸ reps rK129)) :=
  repsInj_of_reduceAux rK129 T129_21 (by decide)

theorem hcardT129_21 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK129 ⟨21, by decide⟩ R129 hpxR129 hcardq129 (by decide)).symm

/-- **Cell (129, 21).** -/
theorem cell129_21 (e : List (ZMod 25)) (heK : charOK (basisAt rK129) e = true)
    (h : ↥(reps (⟨21, by decide⟩ : Fin 148))) :
    species (reps (⟨21, by decide⟩ : Fin 148)) h (basisElt (reps rK129) (charOfVec rK129 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK129 e (h : Coordinate 1) T129_21 i :=
  species_entry_eq_sum rK129 ⟨21, by decide⟩ e heK h T129_21 hfix129_21 hinj129_21 hcardT129_21
    (fun i => conj_mem_of_fixedPoints (reps ⟨21, by decide⟩) (reps rK129) (T129_21 i) (hfix129_21 i) h)

/-! ## Cell (129, 29): |T| = 5 -/

def T129_29list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T129_29 : Fin 5 → Coordinate 1 := fun i => T129_29list.getD i.val (0,0,0,0,0)

theorem hfix129_29 : ∀ i, ((T129_29 i : Coordinate 1) : Coordinate 1 ⧸ reps rK129)
    ∈ fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129) :=
  repsFix_of_siftB rK129 ⟨29, by decide⟩ T129_29 (by decide)

theorem hinj129_29 : Function.Injective
    (fun i => ((T129_29 i : Coordinate 1) : Coordinate 1 ⧸ reps rK129)) :=
  repsInj_of_reduceAux rK129 T129_29 (by decide)

theorem hcardT129_29 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK129 ⟨29, by decide⟩ R129 hpxR129 hcardq129 (by decide)).symm

/-- **Cell (129, 29).** -/
theorem cell129_29 (e : List (ZMod 25)) (heK : charOK (basisAt rK129) e = true)
    (h : ↥(reps (⟨29, by decide⟩ : Fin 148))) :
    species (reps (⟨29, by decide⟩ : Fin 148)) h (basisElt (reps rK129) (charOfVec rK129 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK129 e (h : Coordinate 1) T129_29 i :=
  species_entry_eq_sum rK129 ⟨29, by decide⟩ e heK h T129_29 hfix129_29 hinj129_29 hcardT129_29
    (fun i => conj_mem_of_fixedPoints (reps ⟨29, by decide⟩) (reps rK129) (T129_29 i) (hfix129_29 i) h)

/-! ## Cell (129, 35): |T| = 5 -/

def T129_35list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T129_35 : Fin 5 → Coordinate 1 := fun i => T129_35list.getD i.val (0,0,0,0,0)

theorem hfix129_35 : ∀ i, ((T129_35 i : Coordinate 1) : Coordinate 1 ⧸ reps rK129)
    ∈ fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129) :=
  repsFix_of_siftB rK129 ⟨35, by decide⟩ T129_35 (by decide)

theorem hinj129_35 : Function.Injective
    (fun i => ((T129_35 i : Coordinate 1) : Coordinate 1 ⧸ reps rK129)) :=
  repsInj_of_reduceAux rK129 T129_35 (by decide)

theorem hcardT129_35 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK129 ⟨35, by decide⟩ R129 hpxR129 hcardq129 (by decide)).symm

/-- **Cell (129, 35).** -/
theorem cell129_35 (e : List (ZMod 25)) (heK : charOK (basisAt rK129) e = true)
    (h : ↥(reps (⟨35, by decide⟩ : Fin 148))) :
    species (reps (⟨35, by decide⟩ : Fin 148)) h (basisElt (reps rK129) (charOfVec rK129 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK129 e (h : Coordinate 1) T129_35 i :=
  species_entry_eq_sum rK129 ⟨35, by decide⟩ e heK h T129_35 hfix129_35 hinj129_35 hcardT129_35
    (fun i => conj_mem_of_fixedPoints (reps ⟨35, by decide⟩) (reps rK129) (T129_35 i) (hfix129_35 i) h)

/-! ## Cell (129, 42): |T| = 5 -/

def T129_42list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T129_42 : Fin 5 → Coordinate 1 := fun i => T129_42list.getD i.val (0,0,0,0,0)

theorem hfix129_42 : ∀ i, ((T129_42 i : Coordinate 1) : Coordinate 1 ⧸ reps rK129)
    ∈ fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129) :=
  repsFix_of_siftB rK129 ⟨42, by decide⟩ T129_42 (by decide)

theorem hinj129_42 : Function.Injective
    (fun i => ((T129_42 i : Coordinate 1) : Coordinate 1 ⧸ reps rK129)) :=
  repsInj_of_reduceAux rK129 T129_42 (by decide)

theorem hcardT129_42 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK129 ⟨42, by decide⟩ R129 hpxR129 hcardq129 (by decide)).symm

/-- **Cell (129, 42).** -/
theorem cell129_42 (e : List (ZMod 25)) (heK : charOK (basisAt rK129) e = true)
    (h : ↥(reps (⟨42, by decide⟩ : Fin 148))) :
    species (reps (⟨42, by decide⟩ : Fin 148)) h (basisElt (reps rK129) (charOfVec rK129 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK129 e (h : Coordinate 1) T129_42 i :=
  species_entry_eq_sum rK129 ⟨42, by decide⟩ e heK h T129_42 hfix129_42 hinj129_42 hcardT129_42
    (fun i => conj_mem_of_fixedPoints (reps ⟨42, by decide⟩) (reps rK129) (T129_42 i) (hfix129_42 i) h)

/-! ## Cell (129, 43): |T| = 5 -/

def T129_43list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T129_43 : Fin 5 → Coordinate 1 := fun i => T129_43list.getD i.val (0,0,0,0,0)

theorem hfix129_43 : ∀ i, ((T129_43 i : Coordinate 1) : Coordinate 1 ⧸ reps rK129)
    ∈ fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129) :=
  repsFix_of_siftB rK129 ⟨43, by decide⟩ T129_43 (by decide)

theorem hinj129_43 : Function.Injective
    (fun i => ((T129_43 i : Coordinate 1) : Coordinate 1 ⧸ reps rK129)) :=
  repsInj_of_reduceAux rK129 T129_43 (by decide)

theorem hcardT129_43 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK129 ⟨43, by decide⟩ R129 hpxR129 hcardq129 (by decide)).symm

/-- **Cell (129, 43).** -/
theorem cell129_43 (e : List (ZMod 25)) (heK : charOK (basisAt rK129) e = true)
    (h : ↥(reps (⟨43, by decide⟩ : Fin 148))) :
    species (reps (⟨43, by decide⟩ : Fin 148)) h (basisElt (reps rK129) (charOfVec rK129 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK129 e (h : Coordinate 1) T129_43 i :=
  species_entry_eq_sum rK129 ⟨43, by decide⟩ e heK h T129_43 hfix129_43 hinj129_43 hcardT129_43
    (fun i => conj_mem_of_fixedPoints (reps ⟨43, by decide⟩) (reps rK129) (T129_43 i) (hfix129_43 i) h)

/-! ## Cell (129, 51): |T| = 5 -/

def T129_51list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T129_51 : Fin 5 → Coordinate 1 := fun i => T129_51list.getD i.val (0,0,0,0,0)

theorem hfix129_51 : ∀ i, ((T129_51 i : Coordinate 1) : Coordinate 1 ⧸ reps rK129)
    ∈ fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129) :=
  repsFix_of_siftB rK129 ⟨51, by decide⟩ T129_51 (by decide)

theorem hinj129_51 : Function.Injective
    (fun i => ((T129_51 i : Coordinate 1) : Coordinate 1 ⧸ reps rK129)) :=
  repsInj_of_reduceAux rK129 T129_51 (by decide)

theorem hcardT129_51 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK129 ⟨51, by decide⟩ R129 hpxR129 hcardq129 (by decide)).symm

/-- **Cell (129, 51).** -/
theorem cell129_51 (e : List (ZMod 25)) (heK : charOK (basisAt rK129) e = true)
    (h : ↥(reps (⟨51, by decide⟩ : Fin 148))) :
    species (reps (⟨51, by decide⟩ : Fin 148)) h (basisElt (reps rK129) (charOfVec rK129 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK129 e (h : Coordinate 1) T129_51 i :=
  species_entry_eq_sum rK129 ⟨51, by decide⟩ e heK h T129_51 hfix129_51 hinj129_51 hcardT129_51
    (fun i => conj_mem_of_fixedPoints (reps ⟨51, by decide⟩) (reps rK129) (T129_51 i) (hfix129_51 i) h)

/-! ## Cell (129, 53): |T| = 5 -/

def T129_53list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T129_53 : Fin 5 → Coordinate 1 := fun i => T129_53list.getD i.val (0,0,0,0,0)

theorem hfix129_53 : ∀ i, ((T129_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK129)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129) :=
  repsFix_of_siftB rK129 ⟨53, by decide⟩ T129_53 (by decide)

theorem hinj129_53 : Function.Injective
    (fun i => ((T129_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK129)) :=
  repsInj_of_reduceAux rK129 T129_53 (by decide)

theorem hcardT129_53 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK129 ⟨53, by decide⟩ R129 hpxR129 hcardq129 (by decide)).symm

/-- **Cell (129, 53).** -/
theorem cell129_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK129) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK129) (charOfVec rK129 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK129 e (h : Coordinate 1) T129_53 i :=
  species_entry_eq_sum rK129 ⟨53, by decide⟩ e heK h T129_53 hfix129_53 hinj129_53 hcardT129_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK129) (T129_53 i) (hfix129_53 i) h)

/-! ## Cell (129, 82): |T| = 5 -/

def T129_82list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T129_82 : Fin 5 → Coordinate 1 := fun i => T129_82list.getD i.val (0,0,0,0,0)

theorem hfix129_82 : ∀ i, ((T129_82 i : Coordinate 1) : Coordinate 1 ⧸ reps rK129)
    ∈ fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129) :=
  repsFix_of_siftB rK129 ⟨82, by decide⟩ T129_82 (by decide)

theorem hinj129_82 : Function.Injective
    (fun i => ((T129_82 i : Coordinate 1) : Coordinate 1 ⧸ reps rK129)) :=
  repsInj_of_reduceAux rK129 T129_82 (by decide)

theorem hcardT129_82 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK129 ⟨82, by decide⟩ R129 hpxR129 hcardq129 (by decide)).symm

/-- **Cell (129, 82).** -/
theorem cell129_82 (e : List (ZMod 25)) (heK : charOK (basisAt rK129) e = true)
    (h : ↥(reps (⟨82, by decide⟩ : Fin 148))) :
    species (reps (⟨82, by decide⟩ : Fin 148)) h (basisElt (reps rK129) (charOfVec rK129 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK129 e (h : Coordinate 1) T129_82 i :=
  species_entry_eq_sum rK129 ⟨82, by decide⟩ e heK h T129_82 hfix129_82 hinj129_82 hcardT129_82
    (fun i => conj_mem_of_fixedPoints (reps ⟨82, by decide⟩) (reps rK129) (T129_82 i) (hfix129_82 i) h)

/-! ## Cell (129, 91): |T| = 5 -/

def T129_91list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T129_91 : Fin 5 → Coordinate 1 := fun i => T129_91list.getD i.val (0,0,0,0,0)

theorem hfix129_91 : ∀ i, ((T129_91 i : Coordinate 1) : Coordinate 1 ⧸ reps rK129)
    ∈ fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129) :=
  repsFix_of_siftB rK129 ⟨91, by decide⟩ T129_91 (by decide)

theorem hinj129_91 : Function.Injective
    (fun i => ((T129_91 i : Coordinate 1) : Coordinate 1 ⧸ reps rK129)) :=
  repsInj_of_reduceAux rK129 T129_91 (by decide)

theorem hcardT129_91 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK129 ⟨91, by decide⟩ R129 hpxR129 hcardq129 (by decide)).symm

/-- **Cell (129, 91).** -/
theorem cell129_91 (e : List (ZMod 25)) (heK : charOK (basisAt rK129) e = true)
    (h : ↥(reps (⟨91, by decide⟩ : Fin 148))) :
    species (reps (⟨91, by decide⟩ : Fin 148)) h (basisElt (reps rK129) (charOfVec rK129 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK129 e (h : Coordinate 1) T129_91 i :=
  species_entry_eq_sum rK129 ⟨91, by decide⟩ e heK h T129_91 hfix129_91 hinj129_91 hcardT129_91
    (fun i => conj_mem_of_fixedPoints (reps ⟨91, by decide⟩) (reps rK129) (T129_91 i) (hfix129_91 i) h)

/-! ## Cell (129, 97): |T| = 5 -/

def T129_97list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T129_97 : Fin 5 → Coordinate 1 := fun i => T129_97list.getD i.val (0,0,0,0,0)

theorem hfix129_97 : ∀ i, ((T129_97 i : Coordinate 1) : Coordinate 1 ⧸ reps rK129)
    ∈ fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129) :=
  repsFix_of_siftB rK129 ⟨97, by decide⟩ T129_97 (by decide)

theorem hinj129_97 : Function.Injective
    (fun i => ((T129_97 i : Coordinate 1) : Coordinate 1 ⧸ reps rK129)) :=
  repsInj_of_reduceAux rK129 T129_97 (by decide)

theorem hcardT129_97 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK129 ⟨97, by decide⟩ R129 hpxR129 hcardq129 (by decide)).symm

/-- **Cell (129, 97).** -/
theorem cell129_97 (e : List (ZMod 25)) (heK : charOK (basisAt rK129) e = true)
    (h : ↥(reps (⟨97, by decide⟩ : Fin 148))) :
    species (reps (⟨97, by decide⟩ : Fin 148)) h (basisElt (reps rK129) (charOfVec rK129 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK129 e (h : Coordinate 1) T129_97 i :=
  species_entry_eq_sum rK129 ⟨97, by decide⟩ e heK h T129_97 hfix129_97 hinj129_97 hcardT129_97
    (fun i => conj_mem_of_fixedPoints (reps ⟨97, by decide⟩) (reps rK129) (T129_97 i) (hfix129_97 i) h)

/-! ## Cell (129, 104): |T| = 5 -/

def T129_104list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T129_104 : Fin 5 → Coordinate 1 := fun i => T129_104list.getD i.val (0,0,0,0,0)

theorem hfix129_104 : ∀ i, ((T129_104 i : Coordinate 1) : Coordinate 1 ⧸ reps rK129)
    ∈ fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129) :=
  repsFix_of_siftB rK129 ⟨104, by decide⟩ T129_104 (by decide)

theorem hinj129_104 : Function.Injective
    (fun i => ((T129_104 i : Coordinate 1) : Coordinate 1 ⧸ reps rK129)) :=
  repsInj_of_reduceAux rK129 T129_104 (by decide)

theorem hcardT129_104 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK129 ⟨104, by decide⟩ R129 hpxR129 hcardq129 (by decide)).symm

/-- **Cell (129, 104).** -/
theorem cell129_104 (e : List (ZMod 25)) (heK : charOK (basisAt rK129) e = true)
    (h : ↥(reps (⟨104, by decide⟩ : Fin 148))) :
    species (reps (⟨104, by decide⟩ : Fin 148)) h (basisElt (reps rK129) (charOfVec rK129 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK129 e (h : Coordinate 1) T129_104 i :=
  species_entry_eq_sum rK129 ⟨104, by decide⟩ e heK h T129_104 hfix129_104 hinj129_104 hcardT129_104
    (fun i => conj_mem_of_fixedPoints (reps ⟨104, by decide⟩) (reps rK129) (T129_104 i) (hfix129_104 i) h)

/-! ## Cell (129, 105): |T| = 5 -/

def T129_105list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T129_105 : Fin 5 → Coordinate 1 := fun i => T129_105list.getD i.val (0,0,0,0,0)

theorem hfix129_105 : ∀ i, ((T129_105 i : Coordinate 1) : Coordinate 1 ⧸ reps rK129)
    ∈ fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129) :=
  repsFix_of_siftB rK129 ⟨105, by decide⟩ T129_105 (by decide)

theorem hinj129_105 : Function.Injective
    (fun i => ((T129_105 i : Coordinate 1) : Coordinate 1 ⧸ reps rK129)) :=
  repsInj_of_reduceAux rK129 T129_105 (by decide)

theorem hcardT129_105 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK129 ⟨105, by decide⟩ R129 hpxR129 hcardq129 (by decide)).symm

/-- **Cell (129, 105).** -/
theorem cell129_105 (e : List (ZMod 25)) (heK : charOK (basisAt rK129) e = true)
    (h : ↥(reps (⟨105, by decide⟩ : Fin 148))) :
    species (reps (⟨105, by decide⟩ : Fin 148)) h (basisElt (reps rK129) (charOfVec rK129 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK129 e (h : Coordinate 1) T129_105 i :=
  species_entry_eq_sum rK129 ⟨105, by decide⟩ e heK h T129_105 hfix129_105 hinj129_105 hcardT129_105
    (fun i => conj_mem_of_fixedPoints (reps ⟨105, by decide⟩) (reps rK129) (T129_105 i) (hfix129_105 i) h)

/-! ## Cell (129, 113): |T| = 5 -/

def T129_113list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T129_113 : Fin 5 → Coordinate 1 := fun i => T129_113list.getD i.val (0,0,0,0,0)

theorem hfix129_113 : ∀ i, ((T129_113 i : Coordinate 1) : Coordinate 1 ⧸ reps rK129)
    ∈ fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129) :=
  repsFix_of_siftB rK129 ⟨113, by decide⟩ T129_113 (by decide)

theorem hinj129_113 : Function.Injective
    (fun i => ((T129_113 i : Coordinate 1) : Coordinate 1 ⧸ reps rK129)) :=
  repsInj_of_reduceAux rK129 T129_113 (by decide)

theorem hcardT129_113 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK129 ⟨113, by decide⟩ R129 hpxR129 hcardq129 (by decide)).symm

/-- **Cell (129, 113).** -/
theorem cell129_113 (e : List (ZMod 25)) (heK : charOK (basisAt rK129) e = true)
    (h : ↥(reps (⟨113, by decide⟩ : Fin 148))) :
    species (reps (⟨113, by decide⟩ : Fin 148)) h (basisElt (reps rK129) (charOfVec rK129 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK129 e (h : Coordinate 1) T129_113 i :=
  species_entry_eq_sum rK129 ⟨113, by decide⟩ e heK h T129_113 hfix129_113 hinj129_113 hcardT129_113
    (fun i => conj_mem_of_fixedPoints (reps ⟨113, by decide⟩) (reps rK129) (T129_113 i) (hfix129_113 i) h)

/-! ## Cell (129, 129): |T| = 5 -/

def T129_129list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T129_129 : Fin 5 → Coordinate 1 := fun i => T129_129list.getD i.val (0,0,0,0,0)

theorem hfix129_129 : ∀ i, ((T129_129 i : Coordinate 1) : Coordinate 1 ⧸ reps rK129)
    ∈ fixedPoints (reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129) :=
  repsFix_of_siftB rK129 ⟨129, by decide⟩ T129_129 (by decide)

theorem hinj129_129 : Function.Injective
    (fun i => ((T129_129 i : Coordinate 1) : Coordinate 1 ⧸ reps rK129)) :=
  repsInj_of_reduceAux rK129 T129_129 (by decide)

theorem hcardT129_129 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK129 ⟨129, by decide⟩ R129 hpxR129 hcardq129 (by decide)).symm

/-- **Cell (129, 129).** -/
theorem cell129_129 (e : List (ZMod 25)) (heK : charOK (basisAt rK129) e = true)
    (h : ↥(reps (⟨129, by decide⟩ : Fin 148))) :
    species (reps (⟨129, by decide⟩ : Fin 148)) h (basisElt (reps rK129) (charOfVec rK129 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK129 e (h : Coordinate 1) T129_129 i :=
  species_entry_eq_sum rK129 ⟨129, by decide⟩ e heK h T129_129 hfix129_129 hinj129_129 hcardT129_129
    (fun i => conj_mem_of_fixedPoints (reps ⟨129, by decide⟩) (reps rK129) (T129_129 i) (hfix129_129 i) h)

namespace Q2

def R129_2 : Fin 5 → Coordinate 2 := fun i => R129list.getD i.val (0,0,0,0,0)
theorem hpxR129_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK129) (R129_2 i)) := by decide
theorem hcardq129_2 : Nat.card (Coordinate 2 ⧸ reps rK129) = 5 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (129, 0) twin -/

def T129_0_2 : Fin 5 → Coordinate 2 := fun i => T129_0list.getD i.val (0,0,0,0,0)

theorem hfix129_0_2 : ∀ i, ((T129_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK129)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK129) :=
  repsFix_of_siftB2 rK129 ⟨0, by decide⟩ T129_0_2 (by decide)

theorem hinj129_0_2 : Function.Injective
    (fun i => ((T129_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK129)) :=
  repsInj_of_reduceAux2 rK129 T129_0_2 (by decide)

theorem hcardT129_0_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK129)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK129 ⟨0, by decide⟩ R129_2 hpxR129_2 hcardq129_2 (by decide)).symm

/-- **Cell (129, 0) twin (q=2).** -/
theorem cell129_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK129) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK129) (charOfVec2 rK129 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK129 e (h : Coordinate 2) T129_0_2 i :=
  species_entry_eq_sum rK129 ⟨0, by decide⟩ e heK h T129_0_2 hfix129_0_2 hinj129_0_2 hcardT129_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK129) (T129_0_2 i) (hfix129_0_2 i) h)

/-! ### Cell (129, 3) twin -/

def T129_3_2 : Fin 5 → Coordinate 2 := fun i => T129_3list.getD i.val (0,0,0,0,0)

theorem hfix129_3_2 : ∀ i, ((T129_3_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK129)
    ∈ fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK129) :=
  repsFix_of_siftB2 rK129 ⟨3, by decide⟩ T129_3_2 (by decide)

theorem hinj129_3_2 : Function.Injective
    (fun i => ((T129_3_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK129)) :=
  repsInj_of_reduceAux2 rK129 T129_3_2 (by decide)

theorem hcardT129_3_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK129)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK129 ⟨3, by decide⟩ R129_2 hpxR129_2 hcardq129_2 (by decide)).symm

/-- **Cell (129, 3) twin (q=2).** -/
theorem cell129_3_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK129) e = true)
    (h : ↥(reps (⟨3, by decide⟩ : Fin 148))) :
    species (reps (⟨3, by decide⟩ : Fin 148)) h (basisElt (reps rK129) (charOfVec2 rK129 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK129 e (h : Coordinate 2) T129_3_2 i :=
  species_entry_eq_sum rK129 ⟨3, by decide⟩ e heK h T129_3_2 hfix129_3_2 hinj129_3_2 hcardT129_3_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨3, by decide⟩) (reps rK129) (T129_3_2 i) (hfix129_3_2 i) h)

/-! ### Cell (129, 10) twin -/

def T129_10_2 : Fin 5 → Coordinate 2 := fun i => T129_10list.getD i.val (0,0,0,0,0)

theorem hfix129_10_2 : ∀ i, ((T129_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK129)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK129) :=
  repsFix_of_siftB2 rK129 ⟨10, by decide⟩ T129_10_2 (by decide)

theorem hinj129_10_2 : Function.Injective
    (fun i => ((T129_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK129)) :=
  repsInj_of_reduceAux2 rK129 T129_10_2 (by decide)

theorem hcardT129_10_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK129)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK129 ⟨10, by decide⟩ R129_2 hpxR129_2 hcardq129_2 (by decide)).symm

/-- **Cell (129, 10) twin (q=2).** -/
theorem cell129_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK129) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK129) (charOfVec2 rK129 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK129 e (h : Coordinate 2) T129_10_2 i :=
  species_entry_eq_sum rK129 ⟨10, by decide⟩ e heK h T129_10_2 hfix129_10_2 hinj129_10_2 hcardT129_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK129) (T129_10_2 i) (hfix129_10_2 i) h)

/-! ### Cell (129, 12) twin -/

def T129_12_2 : Fin 5 → Coordinate 2 := fun i => T129_12list.getD i.val (0,0,0,0,0)

theorem hfix129_12_2 : ∀ i, ((T129_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK129)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK129) :=
  repsFix_of_siftB2 rK129 ⟨12, by decide⟩ T129_12_2 (by decide)

theorem hinj129_12_2 : Function.Injective
    (fun i => ((T129_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK129)) :=
  repsInj_of_reduceAux2 rK129 T129_12_2 (by decide)

theorem hcardT129_12_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK129)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK129 ⟨12, by decide⟩ R129_2 hpxR129_2 hcardq129_2 (by decide)).symm

/-- **Cell (129, 12) twin (q=2).** -/
theorem cell129_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK129) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK129) (charOfVec2 rK129 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK129 e (h : Coordinate 2) T129_12_2 i :=
  species_entry_eq_sum rK129 ⟨12, by decide⟩ e heK h T129_12_2 hfix129_12_2 hinj129_12_2 hcardT129_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK129) (T129_12_2 i) (hfix129_12_2 i) h)

/-! ### Cell (129, 21) twin -/

def T129_21_2 : Fin 5 → Coordinate 2 := fun i => T129_21list.getD i.val (0,0,0,0,0)

theorem hfix129_21_2 : ∀ i, ((T129_21_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK129)
    ∈ fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK129) :=
  repsFix_of_siftB2 rK129 ⟨21, by decide⟩ T129_21_2 (by decide)

theorem hinj129_21_2 : Function.Injective
    (fun i => ((T129_21_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK129)) :=
  repsInj_of_reduceAux2 rK129 T129_21_2 (by decide)

theorem hcardT129_21_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK129)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK129 ⟨21, by decide⟩ R129_2 hpxR129_2 hcardq129_2 (by decide)).symm

/-- **Cell (129, 21) twin (q=2).** -/
theorem cell129_21_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK129) e = true)
    (h : ↥(reps (⟨21, by decide⟩ : Fin 148))) :
    species (reps (⟨21, by decide⟩ : Fin 148)) h (basisElt (reps rK129) (charOfVec2 rK129 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK129 e (h : Coordinate 2) T129_21_2 i :=
  species_entry_eq_sum rK129 ⟨21, by decide⟩ e heK h T129_21_2 hfix129_21_2 hinj129_21_2 hcardT129_21_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨21, by decide⟩) (reps rK129) (T129_21_2 i) (hfix129_21_2 i) h)

/-! ### Cell (129, 29) twin -/

def T129_29_2 : Fin 5 → Coordinate 2 := fun i => T129_29list.getD i.val (0,0,0,0,0)

theorem hfix129_29_2 : ∀ i, ((T129_29_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK129)
    ∈ fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK129) :=
  repsFix_of_siftB2 rK129 ⟨29, by decide⟩ T129_29_2 (by decide)

theorem hinj129_29_2 : Function.Injective
    (fun i => ((T129_29_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK129)) :=
  repsInj_of_reduceAux2 rK129 T129_29_2 (by decide)

theorem hcardT129_29_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK129)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK129 ⟨29, by decide⟩ R129_2 hpxR129_2 hcardq129_2 (by decide)).symm

/-- **Cell (129, 29) twin (q=2).** -/
theorem cell129_29_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK129) e = true)
    (h : ↥(reps (⟨29, by decide⟩ : Fin 148))) :
    species (reps (⟨29, by decide⟩ : Fin 148)) h (basisElt (reps rK129) (charOfVec2 rK129 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK129 e (h : Coordinate 2) T129_29_2 i :=
  species_entry_eq_sum rK129 ⟨29, by decide⟩ e heK h T129_29_2 hfix129_29_2 hinj129_29_2 hcardT129_29_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨29, by decide⟩) (reps rK129) (T129_29_2 i) (hfix129_29_2 i) h)

/-! ### Cell (129, 35) twin -/

def T129_35_2 : Fin 5 → Coordinate 2 := fun i => T129_35list.getD i.val (0,0,0,0,0)

theorem hfix129_35_2 : ∀ i, ((T129_35_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK129)
    ∈ fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK129) :=
  repsFix_of_siftB2 rK129 ⟨35, by decide⟩ T129_35_2 (by decide)

theorem hinj129_35_2 : Function.Injective
    (fun i => ((T129_35_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK129)) :=
  repsInj_of_reduceAux2 rK129 T129_35_2 (by decide)

theorem hcardT129_35_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK129)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK129 ⟨35, by decide⟩ R129_2 hpxR129_2 hcardq129_2 (by decide)).symm

/-- **Cell (129, 35) twin (q=2).** -/
theorem cell129_35_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK129) e = true)
    (h : ↥(reps (⟨35, by decide⟩ : Fin 148))) :
    species (reps (⟨35, by decide⟩ : Fin 148)) h (basisElt (reps rK129) (charOfVec2 rK129 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK129 e (h : Coordinate 2) T129_35_2 i :=
  species_entry_eq_sum rK129 ⟨35, by decide⟩ e heK h T129_35_2 hfix129_35_2 hinj129_35_2 hcardT129_35_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨35, by decide⟩) (reps rK129) (T129_35_2 i) (hfix129_35_2 i) h)

/-! ### Cell (129, 42) twin -/

def T129_42_2 : Fin 5 → Coordinate 2 := fun i => T129_42list.getD i.val (0,0,0,0,0)

theorem hfix129_42_2 : ∀ i, ((T129_42_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK129)
    ∈ fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK129) :=
  repsFix_of_siftB2 rK129 ⟨42, by decide⟩ T129_42_2 (by decide)

theorem hinj129_42_2 : Function.Injective
    (fun i => ((T129_42_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK129)) :=
  repsInj_of_reduceAux2 rK129 T129_42_2 (by decide)

theorem hcardT129_42_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK129)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK129 ⟨42, by decide⟩ R129_2 hpxR129_2 hcardq129_2 (by decide)).symm

/-- **Cell (129, 42) twin (q=2).** -/
theorem cell129_42_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK129) e = true)
    (h : ↥(reps (⟨42, by decide⟩ : Fin 148))) :
    species (reps (⟨42, by decide⟩ : Fin 148)) h (basisElt (reps rK129) (charOfVec2 rK129 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK129 e (h : Coordinate 2) T129_42_2 i :=
  species_entry_eq_sum rK129 ⟨42, by decide⟩ e heK h T129_42_2 hfix129_42_2 hinj129_42_2 hcardT129_42_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨42, by decide⟩) (reps rK129) (T129_42_2 i) (hfix129_42_2 i) h)

/-! ### Cell (129, 43) twin -/

def T129_43_2 : Fin 5 → Coordinate 2 := fun i => T129_43list.getD i.val (0,0,0,0,0)

theorem hfix129_43_2 : ∀ i, ((T129_43_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK129)
    ∈ fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK129) :=
  repsFix_of_siftB2 rK129 ⟨43, by decide⟩ T129_43_2 (by decide)

theorem hinj129_43_2 : Function.Injective
    (fun i => ((T129_43_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK129)) :=
  repsInj_of_reduceAux2 rK129 T129_43_2 (by decide)

theorem hcardT129_43_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK129)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK129 ⟨43, by decide⟩ R129_2 hpxR129_2 hcardq129_2 (by decide)).symm

/-- **Cell (129, 43) twin (q=2).** -/
theorem cell129_43_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK129) e = true)
    (h : ↥(reps (⟨43, by decide⟩ : Fin 148))) :
    species (reps (⟨43, by decide⟩ : Fin 148)) h (basisElt (reps rK129) (charOfVec2 rK129 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK129 e (h : Coordinate 2) T129_43_2 i :=
  species_entry_eq_sum rK129 ⟨43, by decide⟩ e heK h T129_43_2 hfix129_43_2 hinj129_43_2 hcardT129_43_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨43, by decide⟩) (reps rK129) (T129_43_2 i) (hfix129_43_2 i) h)

/-! ### Cell (129, 51) twin -/

def T129_51_2 : Fin 5 → Coordinate 2 := fun i => T129_51list.getD i.val (0,0,0,0,0)

theorem hfix129_51_2 : ∀ i, ((T129_51_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK129)
    ∈ fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK129) :=
  repsFix_of_siftB2 rK129 ⟨51, by decide⟩ T129_51_2 (by decide)

theorem hinj129_51_2 : Function.Injective
    (fun i => ((T129_51_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK129)) :=
  repsInj_of_reduceAux2 rK129 T129_51_2 (by decide)

theorem hcardT129_51_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK129)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK129 ⟨51, by decide⟩ R129_2 hpxR129_2 hcardq129_2 (by decide)).symm

/-- **Cell (129, 51) twin (q=2).** -/
theorem cell129_51_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK129) e = true)
    (h : ↥(reps (⟨51, by decide⟩ : Fin 148))) :
    species (reps (⟨51, by decide⟩ : Fin 148)) h (basisElt (reps rK129) (charOfVec2 rK129 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK129 e (h : Coordinate 2) T129_51_2 i :=
  species_entry_eq_sum rK129 ⟨51, by decide⟩ e heK h T129_51_2 hfix129_51_2 hinj129_51_2 hcardT129_51_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨51, by decide⟩) (reps rK129) (T129_51_2 i) (hfix129_51_2 i) h)

/-! ### Cell (129, 53) twin -/

def T129_53_2 : Fin 5 → Coordinate 2 := fun i => T129_53list.getD i.val (0,0,0,0,0)

theorem hfix129_53_2 : ∀ i, ((T129_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK129)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK129) :=
  repsFix_of_siftB2 rK129 ⟨53, by decide⟩ T129_53_2 (by decide)

theorem hinj129_53_2 : Function.Injective
    (fun i => ((T129_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK129)) :=
  repsInj_of_reduceAux2 rK129 T129_53_2 (by decide)

theorem hcardT129_53_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK129)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK129 ⟨53, by decide⟩ R129_2 hpxR129_2 hcardq129_2 (by decide)).symm

/-- **Cell (129, 53) twin (q=2).** -/
theorem cell129_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK129) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK129) (charOfVec2 rK129 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK129 e (h : Coordinate 2) T129_53_2 i :=
  species_entry_eq_sum rK129 ⟨53, by decide⟩ e heK h T129_53_2 hfix129_53_2 hinj129_53_2 hcardT129_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK129) (T129_53_2 i) (hfix129_53_2 i) h)

/-! ### Cell (129, 82) twin -/

def T129_82_2 : Fin 5 → Coordinate 2 := fun i => T129_82list.getD i.val (0,0,0,0,0)

theorem hfix129_82_2 : ∀ i, ((T129_82_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK129)
    ∈ fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK129) :=
  repsFix_of_siftB2 rK129 ⟨82, by decide⟩ T129_82_2 (by decide)

theorem hinj129_82_2 : Function.Injective
    (fun i => ((T129_82_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK129)) :=
  repsInj_of_reduceAux2 rK129 T129_82_2 (by decide)

theorem hcardT129_82_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK129)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK129 ⟨82, by decide⟩ R129_2 hpxR129_2 hcardq129_2 (by decide)).symm

/-- **Cell (129, 82) twin (q=2).** -/
theorem cell129_82_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK129) e = true)
    (h : ↥(reps (⟨82, by decide⟩ : Fin 148))) :
    species (reps (⟨82, by decide⟩ : Fin 148)) h (basisElt (reps rK129) (charOfVec2 rK129 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK129 e (h : Coordinate 2) T129_82_2 i :=
  species_entry_eq_sum rK129 ⟨82, by decide⟩ e heK h T129_82_2 hfix129_82_2 hinj129_82_2 hcardT129_82_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨82, by decide⟩) (reps rK129) (T129_82_2 i) (hfix129_82_2 i) h)

/-! ### Cell (129, 91) twin -/

def T129_91_2 : Fin 5 → Coordinate 2 := fun i => T129_91list.getD i.val (0,0,0,0,0)

theorem hfix129_91_2 : ∀ i, ((T129_91_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK129)
    ∈ fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK129) :=
  repsFix_of_siftB2 rK129 ⟨91, by decide⟩ T129_91_2 (by decide)

theorem hinj129_91_2 : Function.Injective
    (fun i => ((T129_91_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK129)) :=
  repsInj_of_reduceAux2 rK129 T129_91_2 (by decide)

theorem hcardT129_91_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK129)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK129 ⟨91, by decide⟩ R129_2 hpxR129_2 hcardq129_2 (by decide)).symm

/-- **Cell (129, 91) twin (q=2).** -/
theorem cell129_91_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK129) e = true)
    (h : ↥(reps (⟨91, by decide⟩ : Fin 148))) :
    species (reps (⟨91, by decide⟩ : Fin 148)) h (basisElt (reps rK129) (charOfVec2 rK129 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK129 e (h : Coordinate 2) T129_91_2 i :=
  species_entry_eq_sum rK129 ⟨91, by decide⟩ e heK h T129_91_2 hfix129_91_2 hinj129_91_2 hcardT129_91_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨91, by decide⟩) (reps rK129) (T129_91_2 i) (hfix129_91_2 i) h)

/-! ### Cell (129, 97) twin -/

def T129_97_2 : Fin 5 → Coordinate 2 := fun i => T129_97list.getD i.val (0,0,0,0,0)

theorem hfix129_97_2 : ∀ i, ((T129_97_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK129)
    ∈ fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK129) :=
  repsFix_of_siftB2 rK129 ⟨97, by decide⟩ T129_97_2 (by decide)

theorem hinj129_97_2 : Function.Injective
    (fun i => ((T129_97_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK129)) :=
  repsInj_of_reduceAux2 rK129 T129_97_2 (by decide)

theorem hcardT129_97_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK129)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK129 ⟨97, by decide⟩ R129_2 hpxR129_2 hcardq129_2 (by decide)).symm

/-- **Cell (129, 97) twin (q=2).** -/
theorem cell129_97_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK129) e = true)
    (h : ↥(reps (⟨97, by decide⟩ : Fin 148))) :
    species (reps (⟨97, by decide⟩ : Fin 148)) h (basisElt (reps rK129) (charOfVec2 rK129 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK129 e (h : Coordinate 2) T129_97_2 i :=
  species_entry_eq_sum rK129 ⟨97, by decide⟩ e heK h T129_97_2 hfix129_97_2 hinj129_97_2 hcardT129_97_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨97, by decide⟩) (reps rK129) (T129_97_2 i) (hfix129_97_2 i) h)

/-! ### Cell (129, 104) twin -/

def T129_104_2 : Fin 5 → Coordinate 2 := fun i => T129_104list.getD i.val (0,0,0,0,0)

theorem hfix129_104_2 : ∀ i, ((T129_104_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK129)
    ∈ fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK129) :=
  repsFix_of_siftB2 rK129 ⟨104, by decide⟩ T129_104_2 (by decide)

theorem hinj129_104_2 : Function.Injective
    (fun i => ((T129_104_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK129)) :=
  repsInj_of_reduceAux2 rK129 T129_104_2 (by decide)

theorem hcardT129_104_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK129)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK129 ⟨104, by decide⟩ R129_2 hpxR129_2 hcardq129_2 (by decide)).symm

/-- **Cell (129, 104) twin (q=2).** -/
theorem cell129_104_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK129) e = true)
    (h : ↥(reps (⟨104, by decide⟩ : Fin 148))) :
    species (reps (⟨104, by decide⟩ : Fin 148)) h (basisElt (reps rK129) (charOfVec2 rK129 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK129 e (h : Coordinate 2) T129_104_2 i :=
  species_entry_eq_sum rK129 ⟨104, by decide⟩ e heK h T129_104_2 hfix129_104_2 hinj129_104_2 hcardT129_104_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨104, by decide⟩) (reps rK129) (T129_104_2 i) (hfix129_104_2 i) h)

/-! ### Cell (129, 105) twin -/

def T129_105_2 : Fin 5 → Coordinate 2 := fun i => T129_105list.getD i.val (0,0,0,0,0)

theorem hfix129_105_2 : ∀ i, ((T129_105_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK129)
    ∈ fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK129) :=
  repsFix_of_siftB2 rK129 ⟨105, by decide⟩ T129_105_2 (by decide)

theorem hinj129_105_2 : Function.Injective
    (fun i => ((T129_105_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK129)) :=
  repsInj_of_reduceAux2 rK129 T129_105_2 (by decide)

theorem hcardT129_105_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK129)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK129 ⟨105, by decide⟩ R129_2 hpxR129_2 hcardq129_2 (by decide)).symm

/-- **Cell (129, 105) twin (q=2).** -/
theorem cell129_105_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK129) e = true)
    (h : ↥(reps (⟨105, by decide⟩ : Fin 148))) :
    species (reps (⟨105, by decide⟩ : Fin 148)) h (basisElt (reps rK129) (charOfVec2 rK129 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK129 e (h : Coordinate 2) T129_105_2 i :=
  species_entry_eq_sum rK129 ⟨105, by decide⟩ e heK h T129_105_2 hfix129_105_2 hinj129_105_2 hcardT129_105_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨105, by decide⟩) (reps rK129) (T129_105_2 i) (hfix129_105_2 i) h)

/-! ### Cell (129, 113) twin -/

def T129_113_2 : Fin 5 → Coordinate 2 := fun i => T129_113list.getD i.val (0,0,0,0,0)

theorem hfix129_113_2 : ∀ i, ((T129_113_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK129)
    ∈ fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK129) :=
  repsFix_of_siftB2 rK129 ⟨113, by decide⟩ T129_113_2 (by decide)

theorem hinj129_113_2 : Function.Injective
    (fun i => ((T129_113_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK129)) :=
  repsInj_of_reduceAux2 rK129 T129_113_2 (by decide)

theorem hcardT129_113_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK129)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK129 ⟨113, by decide⟩ R129_2 hpxR129_2 hcardq129_2 (by decide)).symm

/-- **Cell (129, 113) twin (q=2).** -/
theorem cell129_113_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK129) e = true)
    (h : ↥(reps (⟨113, by decide⟩ : Fin 148))) :
    species (reps (⟨113, by decide⟩ : Fin 148)) h (basisElt (reps rK129) (charOfVec2 rK129 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK129 e (h : Coordinate 2) T129_113_2 i :=
  species_entry_eq_sum rK129 ⟨113, by decide⟩ e heK h T129_113_2 hfix129_113_2 hinj129_113_2 hcardT129_113_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨113, by decide⟩) (reps rK129) (T129_113_2 i) (hfix129_113_2 i) h)

/-! ### Cell (129, 129) twin -/

def T129_129_2 : Fin 5 → Coordinate 2 := fun i => T129_129list.getD i.val (0,0,0,0,0)

theorem hfix129_129_2 : ∀ i, ((T129_129_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK129)
    ∈ fixedPoints (reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK129) :=
  repsFix_of_siftB2 rK129 ⟨129, by decide⟩ T129_129_2 (by decide)

theorem hinj129_129_2 : Function.Injective
    (fun i => ((T129_129_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK129)) :=
  repsInj_of_reduceAux2 rK129 T129_129_2 (by decide)

theorem hcardT129_129_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK129)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK129 ⟨129, by decide⟩ R129_2 hpxR129_2 hcardq129_2 (by decide)).symm

/-- **Cell (129, 129) twin (q=2).** -/
theorem cell129_129_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK129) e = true)
    (h : ↥(reps (⟨129, by decide⟩ : Fin 148))) :
    species (reps (⟨129, by decide⟩ : Fin 148)) h (basisElt (reps rK129) (charOfVec2 rK129 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK129 e (h : Coordinate 2) T129_129_2 i :=
  species_entry_eq_sum rK129 ⟨129, by decide⟩ e heK h T129_129_2 hfix129_129_2 hinj129_129_2 hcardT129_129_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨129, by decide⟩) (reps rK129) (T129_129_2 i) (hfix129_129_2 i) h)

end Q2

end LeanDring.P5Presentation
