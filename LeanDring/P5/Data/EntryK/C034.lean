/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, K-strata data (5^4 stratum, rK 130-131): certified per-cell species-entry instantiations, both
twins.

Covers K-classes 130, 131 (order-5^4 K, |R|=5).  For each nonzero `H`-column
(`(G/K)^H ≠ ∅`), the full coset transversal `R130..` and each `H`-fixed
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

/-! # K-class rK = 130  (|G/K| = 5) -/

def rK130 : Fin 148 := ⟨130, by decide⟩

def R130list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def R130 : Fin 5 → Coordinate 1 := fun i => R130list.getD i.val (0,0,0,0,0)

theorem hpxR130 : Function.Injective (fun i => reduceAux 1 (basisAt rK130) (R130 i)) := by decide
theorem hcardq130 : Nat.card (Coordinate 1 ⧸ reps rK130) = 5 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (130, 0): |T| = 5 -/

def T130_0list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T130_0 : Fin 5 → Coordinate 1 := fun i => T130_0list.getD i.val (0,0,0,0,0)

theorem hfix130_0 : ∀ i, ((T130_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK130)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130) :=
  repsFix_of_siftB rK130 ⟨0, by decide⟩ T130_0 (by decide)

theorem hinj130_0 : Function.Injective
    (fun i => ((T130_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK130)) :=
  repsInj_of_reduceAux rK130 T130_0 (by decide)

theorem hcardT130_0 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK130 ⟨0, by decide⟩ R130 hpxR130 hcardq130 (by decide)).symm

/-- **Cell (130, 0).** -/
theorem cell130_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK130) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK130) (charOfVec rK130 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK130 e (h : Coordinate 1) T130_0 i :=
  species_entry_eq_sum rK130 ⟨0, by decide⟩ e heK h T130_0 hfix130_0 hinj130_0 hcardT130_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK130) (T130_0 i) (hfix130_0 i) h)

/-! ## Cell (130, 3): |T| = 5 -/

def T130_3list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T130_3 : Fin 5 → Coordinate 1 := fun i => T130_3list.getD i.val (0,0,0,0,0)

theorem hfix130_3 : ∀ i, ((T130_3 i : Coordinate 1) : Coordinate 1 ⧸ reps rK130)
    ∈ fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130) :=
  repsFix_of_siftB rK130 ⟨3, by decide⟩ T130_3 (by decide)

theorem hinj130_3 : Function.Injective
    (fun i => ((T130_3 i : Coordinate 1) : Coordinate 1 ⧸ reps rK130)) :=
  repsInj_of_reduceAux rK130 T130_3 (by decide)

theorem hcardT130_3 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK130 ⟨3, by decide⟩ R130 hpxR130 hcardq130 (by decide)).symm

/-- **Cell (130, 3).** -/
theorem cell130_3 (e : List (ZMod 25)) (heK : charOK (basisAt rK130) e = true)
    (h : ↥(reps (⟨3, by decide⟩ : Fin 148))) :
    species (reps (⟨3, by decide⟩ : Fin 148)) h (basisElt (reps rK130) (charOfVec rK130 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK130 e (h : Coordinate 1) T130_3 i :=
  species_entry_eq_sum rK130 ⟨3, by decide⟩ e heK h T130_3 hfix130_3 hinj130_3 hcardT130_3
    (fun i => conj_mem_of_fixedPoints (reps ⟨3, by decide⟩) (reps rK130) (T130_3 i) (hfix130_3 i) h)

/-! ## Cell (130, 10): |T| = 5 -/

def T130_10list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T130_10 : Fin 5 → Coordinate 1 := fun i => T130_10list.getD i.val (0,0,0,0,0)

theorem hfix130_10 : ∀ i, ((T130_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK130)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130) :=
  repsFix_of_siftB rK130 ⟨10, by decide⟩ T130_10 (by decide)

theorem hinj130_10 : Function.Injective
    (fun i => ((T130_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK130)) :=
  repsInj_of_reduceAux rK130 T130_10 (by decide)

theorem hcardT130_10 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK130 ⟨10, by decide⟩ R130 hpxR130 hcardq130 (by decide)).symm

/-- **Cell (130, 10).** -/
theorem cell130_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK130) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK130) (charOfVec rK130 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK130 e (h : Coordinate 1) T130_10 i :=
  species_entry_eq_sum rK130 ⟨10, by decide⟩ e heK h T130_10 hfix130_10 hinj130_10 hcardT130_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK130) (T130_10 i) (hfix130_10 i) h)

/-! ## Cell (130, 12): |T| = 5 -/

def T130_12list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T130_12 : Fin 5 → Coordinate 1 := fun i => T130_12list.getD i.val (0,0,0,0,0)

theorem hfix130_12 : ∀ i, ((T130_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK130)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130) :=
  repsFix_of_siftB rK130 ⟨12, by decide⟩ T130_12 (by decide)

theorem hinj130_12 : Function.Injective
    (fun i => ((T130_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK130)) :=
  repsInj_of_reduceAux rK130 T130_12 (by decide)

theorem hcardT130_12 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK130 ⟨12, by decide⟩ R130 hpxR130 hcardq130 (by decide)).symm

/-- **Cell (130, 12).** -/
theorem cell130_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK130) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK130) (charOfVec rK130 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK130 e (h : Coordinate 1) T130_12 i :=
  species_entry_eq_sum rK130 ⟨12, by decide⟩ e heK h T130_12 hfix130_12 hinj130_12 hcardT130_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK130) (T130_12 i) (hfix130_12 i) h)

/-! ## Cell (130, 21): |T| = 5 -/

def T130_21list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T130_21 : Fin 5 → Coordinate 1 := fun i => T130_21list.getD i.val (0,0,0,0,0)

theorem hfix130_21 : ∀ i, ((T130_21 i : Coordinate 1) : Coordinate 1 ⧸ reps rK130)
    ∈ fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130) :=
  repsFix_of_siftB rK130 ⟨21, by decide⟩ T130_21 (by decide)

theorem hinj130_21 : Function.Injective
    (fun i => ((T130_21 i : Coordinate 1) : Coordinate 1 ⧸ reps rK130)) :=
  repsInj_of_reduceAux rK130 T130_21 (by decide)

theorem hcardT130_21 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK130 ⟨21, by decide⟩ R130 hpxR130 hcardq130 (by decide)).symm

/-- **Cell (130, 21).** -/
theorem cell130_21 (e : List (ZMod 25)) (heK : charOK (basisAt rK130) e = true)
    (h : ↥(reps (⟨21, by decide⟩ : Fin 148))) :
    species (reps (⟨21, by decide⟩ : Fin 148)) h (basisElt (reps rK130) (charOfVec rK130 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK130 e (h : Coordinate 1) T130_21 i :=
  species_entry_eq_sum rK130 ⟨21, by decide⟩ e heK h T130_21 hfix130_21 hinj130_21 hcardT130_21
    (fun i => conj_mem_of_fixedPoints (reps ⟨21, by decide⟩) (reps rK130) (T130_21 i) (hfix130_21 i) h)

/-! ## Cell (130, 30): |T| = 5 -/

def T130_30list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T130_30 : Fin 5 → Coordinate 1 := fun i => T130_30list.getD i.val (0,0,0,0,0)

theorem hfix130_30 : ∀ i, ((T130_30 i : Coordinate 1) : Coordinate 1 ⧸ reps rK130)
    ∈ fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130) :=
  repsFix_of_siftB rK130 ⟨30, by decide⟩ T130_30 (by decide)

theorem hinj130_30 : Function.Injective
    (fun i => ((T130_30 i : Coordinate 1) : Coordinate 1 ⧸ reps rK130)) :=
  repsInj_of_reduceAux rK130 T130_30 (by decide)

theorem hcardT130_30 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK130 ⟨30, by decide⟩ R130 hpxR130 hcardq130 (by decide)).symm

/-- **Cell (130, 30).** -/
theorem cell130_30 (e : List (ZMod 25)) (heK : charOK (basisAt rK130) e = true)
    (h : ↥(reps (⟨30, by decide⟩ : Fin 148))) :
    species (reps (⟨30, by decide⟩ : Fin 148)) h (basisElt (reps rK130) (charOfVec rK130 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK130 e (h : Coordinate 1) T130_30 i :=
  species_entry_eq_sum rK130 ⟨30, by decide⟩ e heK h T130_30 hfix130_30 hinj130_30 hcardT130_30
    (fun i => conj_mem_of_fixedPoints (reps ⟨30, by decide⟩) (reps rK130) (T130_30 i) (hfix130_30 i) h)

/-! ## Cell (130, 36): |T| = 5 -/

def T130_36list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T130_36 : Fin 5 → Coordinate 1 := fun i => T130_36list.getD i.val (0,0,0,0,0)

theorem hfix130_36 : ∀ i, ((T130_36 i : Coordinate 1) : Coordinate 1 ⧸ reps rK130)
    ∈ fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130) :=
  repsFix_of_siftB rK130 ⟨36, by decide⟩ T130_36 (by decide)

theorem hinj130_36 : Function.Injective
    (fun i => ((T130_36 i : Coordinate 1) : Coordinate 1 ⧸ reps rK130)) :=
  repsInj_of_reduceAux rK130 T130_36 (by decide)

theorem hcardT130_36 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK130 ⟨36, by decide⟩ R130 hpxR130 hcardq130 (by decide)).symm

/-- **Cell (130, 36).** -/
theorem cell130_36 (e : List (ZMod 25)) (heK : charOK (basisAt rK130) e = true)
    (h : ↥(reps (⟨36, by decide⟩ : Fin 148))) :
    species (reps (⟨36, by decide⟩ : Fin 148)) h (basisElt (reps rK130) (charOfVec rK130 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK130 e (h : Coordinate 1) T130_36 i :=
  species_entry_eq_sum rK130 ⟨36, by decide⟩ e heK h T130_36 hfix130_36 hinj130_36 hcardT130_36
    (fun i => conj_mem_of_fixedPoints (reps ⟨36, by decide⟩) (reps rK130) (T130_36 i) (hfix130_36 i) h)

/-! ## Cell (130, 38): |T| = 5 -/

def T130_38list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T130_38 : Fin 5 → Coordinate 1 := fun i => T130_38list.getD i.val (0,0,0,0,0)

theorem hfix130_38 : ∀ i, ((T130_38 i : Coordinate 1) : Coordinate 1 ⧸ reps rK130)
    ∈ fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130) :=
  repsFix_of_siftB rK130 ⟨38, by decide⟩ T130_38 (by decide)

theorem hinj130_38 : Function.Injective
    (fun i => ((T130_38 i : Coordinate 1) : Coordinate 1 ⧸ reps rK130)) :=
  repsInj_of_reduceAux rK130 T130_38 (by decide)

theorem hcardT130_38 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK130 ⟨38, by decide⟩ R130 hpxR130 hcardq130 (by decide)).symm

/-- **Cell (130, 38).** -/
theorem cell130_38 (e : List (ZMod 25)) (heK : charOK (basisAt rK130) e = true)
    (h : ↥(reps (⟨38, by decide⟩ : Fin 148))) :
    species (reps (⟨38, by decide⟩ : Fin 148)) h (basisElt (reps rK130) (charOfVec rK130 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK130 e (h : Coordinate 1) T130_38 i :=
  species_entry_eq_sum rK130 ⟨38, by decide⟩ e heK h T130_38 hfix130_38 hinj130_38 hcardT130_38
    (fun i => conj_mem_of_fixedPoints (reps ⟨38, by decide⟩) (reps rK130) (T130_38 i) (hfix130_38 i) h)

/-! ## Cell (130, 44): |T| = 5 -/

def T130_44list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T130_44 : Fin 5 → Coordinate 1 := fun i => T130_44list.getD i.val (0,0,0,0,0)

theorem hfix130_44 : ∀ i, ((T130_44 i : Coordinate 1) : Coordinate 1 ⧸ reps rK130)
    ∈ fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130) :=
  repsFix_of_siftB rK130 ⟨44, by decide⟩ T130_44 (by decide)

theorem hinj130_44 : Function.Injective
    (fun i => ((T130_44 i : Coordinate 1) : Coordinate 1 ⧸ reps rK130)) :=
  repsInj_of_reduceAux rK130 T130_44 (by decide)

theorem hcardT130_44 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK130 ⟨44, by decide⟩ R130 hpxR130 hcardq130 (by decide)).symm

/-- **Cell (130, 44).** -/
theorem cell130_44 (e : List (ZMod 25)) (heK : charOK (basisAt rK130) e = true)
    (h : ↥(reps (⟨44, by decide⟩ : Fin 148))) :
    species (reps (⟨44, by decide⟩ : Fin 148)) h (basisElt (reps rK130) (charOfVec rK130 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK130 e (h : Coordinate 1) T130_44 i :=
  species_entry_eq_sum rK130 ⟨44, by decide⟩ e heK h T130_44 hfix130_44 hinj130_44 hcardT130_44
    (fun i => conj_mem_of_fixedPoints (reps ⟨44, by decide⟩) (reps rK130) (T130_44 i) (hfix130_44 i) h)

/-! ## Cell (130, 52): |T| = 5 -/

def T130_52list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T130_52 : Fin 5 → Coordinate 1 := fun i => T130_52list.getD i.val (0,0,0,0,0)

theorem hfix130_52 : ∀ i, ((T130_52 i : Coordinate 1) : Coordinate 1 ⧸ reps rK130)
    ∈ fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130) :=
  repsFix_of_siftB rK130 ⟨52, by decide⟩ T130_52 (by decide)

theorem hinj130_52 : Function.Injective
    (fun i => ((T130_52 i : Coordinate 1) : Coordinate 1 ⧸ reps rK130)) :=
  repsInj_of_reduceAux rK130 T130_52 (by decide)

theorem hcardT130_52 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK130 ⟨52, by decide⟩ R130 hpxR130 hcardq130 (by decide)).symm

/-- **Cell (130, 52).** -/
theorem cell130_52 (e : List (ZMod 25)) (heK : charOK (basisAt rK130) e = true)
    (h : ↥(reps (⟨52, by decide⟩ : Fin 148))) :
    species (reps (⟨52, by decide⟩ : Fin 148)) h (basisElt (reps rK130) (charOfVec rK130 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK130 e (h : Coordinate 1) T130_52 i :=
  species_entry_eq_sum rK130 ⟨52, by decide⟩ e heK h T130_52 hfix130_52 hinj130_52 hcardT130_52
    (fun i => conj_mem_of_fixedPoints (reps ⟨52, by decide⟩) (reps rK130) (T130_52 i) (hfix130_52 i) h)

/-! ## Cell (130, 53): |T| = 5 -/

def T130_53list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T130_53 : Fin 5 → Coordinate 1 := fun i => T130_53list.getD i.val (0,0,0,0,0)

theorem hfix130_53 : ∀ i, ((T130_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK130)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130) :=
  repsFix_of_siftB rK130 ⟨53, by decide⟩ T130_53 (by decide)

theorem hinj130_53 : Function.Injective
    (fun i => ((T130_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK130)) :=
  repsInj_of_reduceAux rK130 T130_53 (by decide)

theorem hcardT130_53 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK130 ⟨53, by decide⟩ R130 hpxR130 hcardq130 (by decide)).symm

/-- **Cell (130, 53).** -/
theorem cell130_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK130) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK130) (charOfVec rK130 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK130 e (h : Coordinate 1) T130_53 i :=
  species_entry_eq_sum rK130 ⟨53, by decide⟩ e heK h T130_53 hfix130_53 hinj130_53 hcardT130_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK130) (T130_53 i) (hfix130_53 i) h)

/-! ## Cell (130, 82): |T| = 5 -/

def T130_82list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T130_82 : Fin 5 → Coordinate 1 := fun i => T130_82list.getD i.val (0,0,0,0,0)

theorem hfix130_82 : ∀ i, ((T130_82 i : Coordinate 1) : Coordinate 1 ⧸ reps rK130)
    ∈ fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130) :=
  repsFix_of_siftB rK130 ⟨82, by decide⟩ T130_82 (by decide)

theorem hinj130_82 : Function.Injective
    (fun i => ((T130_82 i : Coordinate 1) : Coordinate 1 ⧸ reps rK130)) :=
  repsInj_of_reduceAux rK130 T130_82 (by decide)

theorem hcardT130_82 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK130 ⟨82, by decide⟩ R130 hpxR130 hcardq130 (by decide)).symm

/-- **Cell (130, 82).** -/
theorem cell130_82 (e : List (ZMod 25)) (heK : charOK (basisAt rK130) e = true)
    (h : ↥(reps (⟨82, by decide⟩ : Fin 148))) :
    species (reps (⟨82, by decide⟩ : Fin 148)) h (basisElt (reps rK130) (charOfVec rK130 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK130 e (h : Coordinate 1) T130_82 i :=
  species_entry_eq_sum rK130 ⟨82, by decide⟩ e heK h T130_82 hfix130_82 hinj130_82 hcardT130_82
    (fun i => conj_mem_of_fixedPoints (reps ⟨82, by decide⟩) (reps rK130) (T130_82 i) (hfix130_82 i) h)

/-! ## Cell (130, 92): |T| = 5 -/

def T130_92list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T130_92 : Fin 5 → Coordinate 1 := fun i => T130_92list.getD i.val (0,0,0,0,0)

theorem hfix130_92 : ∀ i, ((T130_92 i : Coordinate 1) : Coordinate 1 ⧸ reps rK130)
    ∈ fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130) :=
  repsFix_of_siftB rK130 ⟨92, by decide⟩ T130_92 (by decide)

theorem hinj130_92 : Function.Injective
    (fun i => ((T130_92 i : Coordinate 1) : Coordinate 1 ⧸ reps rK130)) :=
  repsInj_of_reduceAux rK130 T130_92 (by decide)

theorem hcardT130_92 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK130 ⟨92, by decide⟩ R130 hpxR130 hcardq130 (by decide)).symm

/-- **Cell (130, 92).** -/
theorem cell130_92 (e : List (ZMod 25)) (heK : charOK (basisAt rK130) e = true)
    (h : ↥(reps (⟨92, by decide⟩ : Fin 148))) :
    species (reps (⟨92, by decide⟩ : Fin 148)) h (basisElt (reps rK130) (charOfVec rK130 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK130 e (h : Coordinate 1) T130_92 i :=
  species_entry_eq_sum rK130 ⟨92, by decide⟩ e heK h T130_92 hfix130_92 hinj130_92 hcardT130_92
    (fun i => conj_mem_of_fixedPoints (reps ⟨92, by decide⟩) (reps rK130) (T130_92 i) (hfix130_92 i) h)

/-! ## Cell (130, 98): |T| = 5 -/

def T130_98list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T130_98 : Fin 5 → Coordinate 1 := fun i => T130_98list.getD i.val (0,0,0,0,0)

theorem hfix130_98 : ∀ i, ((T130_98 i : Coordinate 1) : Coordinate 1 ⧸ reps rK130)
    ∈ fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130) :=
  repsFix_of_siftB rK130 ⟨98, by decide⟩ T130_98 (by decide)

theorem hinj130_98 : Function.Injective
    (fun i => ((T130_98 i : Coordinate 1) : Coordinate 1 ⧸ reps rK130)) :=
  repsInj_of_reduceAux rK130 T130_98 (by decide)

theorem hcardT130_98 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK130 ⟨98, by decide⟩ R130 hpxR130 hcardq130 (by decide)).symm

/-- **Cell (130, 98).** -/
theorem cell130_98 (e : List (ZMod 25)) (heK : charOK (basisAt rK130) e = true)
    (h : ↥(reps (⟨98, by decide⟩ : Fin 148))) :
    species (reps (⟨98, by decide⟩ : Fin 148)) h (basisElt (reps rK130) (charOfVec rK130 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK130 e (h : Coordinate 1) T130_98 i :=
  species_entry_eq_sum rK130 ⟨98, by decide⟩ e heK h T130_98 hfix130_98 hinj130_98 hcardT130_98
    (fun i => conj_mem_of_fixedPoints (reps ⟨98, by decide⟩) (reps rK130) (T130_98 i) (hfix130_98 i) h)

/-! ## Cell (130, 100): |T| = 5 -/

def T130_100list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T130_100 : Fin 5 → Coordinate 1 := fun i => T130_100list.getD i.val (0,0,0,0,0)

theorem hfix130_100 : ∀ i, ((T130_100 i : Coordinate 1) : Coordinate 1 ⧸ reps rK130)
    ∈ fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130) :=
  repsFix_of_siftB rK130 ⟨100, by decide⟩ T130_100 (by decide)

theorem hinj130_100 : Function.Injective
    (fun i => ((T130_100 i : Coordinate 1) : Coordinate 1 ⧸ reps rK130)) :=
  repsInj_of_reduceAux rK130 T130_100 (by decide)

theorem hcardT130_100 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK130 ⟨100, by decide⟩ R130 hpxR130 hcardq130 (by decide)).symm

/-- **Cell (130, 100).** -/
theorem cell130_100 (e : List (ZMod 25)) (heK : charOK (basisAt rK130) e = true)
    (h : ↥(reps (⟨100, by decide⟩ : Fin 148))) :
    species (reps (⟨100, by decide⟩ : Fin 148)) h (basisElt (reps rK130) (charOfVec rK130 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK130 e (h : Coordinate 1) T130_100 i :=
  species_entry_eq_sum rK130 ⟨100, by decide⟩ e heK h T130_100 hfix130_100 hinj130_100 hcardT130_100
    (fun i => conj_mem_of_fixedPoints (reps ⟨100, by decide⟩) (reps rK130) (T130_100 i) (hfix130_100 i) h)

/-! ## Cell (130, 106): |T| = 5 -/

def T130_106list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T130_106 : Fin 5 → Coordinate 1 := fun i => T130_106list.getD i.val (0,0,0,0,0)

theorem hfix130_106 : ∀ i, ((T130_106 i : Coordinate 1) : Coordinate 1 ⧸ reps rK130)
    ∈ fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130) :=
  repsFix_of_siftB rK130 ⟨106, by decide⟩ T130_106 (by decide)

theorem hinj130_106 : Function.Injective
    (fun i => ((T130_106 i : Coordinate 1) : Coordinate 1 ⧸ reps rK130)) :=
  repsInj_of_reduceAux rK130 T130_106 (by decide)

theorem hcardT130_106 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK130 ⟨106, by decide⟩ R130 hpxR130 hcardq130 (by decide)).symm

/-- **Cell (130, 106).** -/
theorem cell130_106 (e : List (ZMod 25)) (heK : charOK (basisAt rK130) e = true)
    (h : ↥(reps (⟨106, by decide⟩ : Fin 148))) :
    species (reps (⟨106, by decide⟩ : Fin 148)) h (basisElt (reps rK130) (charOfVec rK130 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK130 e (h : Coordinate 1) T130_106 i :=
  species_entry_eq_sum rK130 ⟨106, by decide⟩ e heK h T130_106 hfix130_106 hinj130_106 hcardT130_106
    (fun i => conj_mem_of_fixedPoints (reps ⟨106, by decide⟩) (reps rK130) (T130_106 i) (hfix130_106 i) h)

/-! ## Cell (130, 114): |T| = 5 -/

def T130_114list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T130_114 : Fin 5 → Coordinate 1 := fun i => T130_114list.getD i.val (0,0,0,0,0)

theorem hfix130_114 : ∀ i, ((T130_114 i : Coordinate 1) : Coordinate 1 ⧸ reps rK130)
    ∈ fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130) :=
  repsFix_of_siftB rK130 ⟨114, by decide⟩ T130_114 (by decide)

theorem hinj130_114 : Function.Injective
    (fun i => ((T130_114 i : Coordinate 1) : Coordinate 1 ⧸ reps rK130)) :=
  repsInj_of_reduceAux rK130 T130_114 (by decide)

theorem hcardT130_114 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK130 ⟨114, by decide⟩ R130 hpxR130 hcardq130 (by decide)).symm

/-- **Cell (130, 114).** -/
theorem cell130_114 (e : List (ZMod 25)) (heK : charOK (basisAt rK130) e = true)
    (h : ↥(reps (⟨114, by decide⟩ : Fin 148))) :
    species (reps (⟨114, by decide⟩ : Fin 148)) h (basisElt (reps rK130) (charOfVec rK130 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK130 e (h : Coordinate 1) T130_114 i :=
  species_entry_eq_sum rK130 ⟨114, by decide⟩ e heK h T130_114 hfix130_114 hinj130_114 hcardT130_114
    (fun i => conj_mem_of_fixedPoints (reps ⟨114, by decide⟩) (reps rK130) (T130_114 i) (hfix130_114 i) h)

/-! ## Cell (130, 130): |T| = 5 -/

def T130_130list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T130_130 : Fin 5 → Coordinate 1 := fun i => T130_130list.getD i.val (0,0,0,0,0)

theorem hfix130_130 : ∀ i, ((T130_130 i : Coordinate 1) : Coordinate 1 ⧸ reps rK130)
    ∈ fixedPoints (reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130) :=
  repsFix_of_siftB rK130 ⟨130, by decide⟩ T130_130 (by decide)

theorem hinj130_130 : Function.Injective
    (fun i => ((T130_130 i : Coordinate 1) : Coordinate 1 ⧸ reps rK130)) :=
  repsInj_of_reduceAux rK130 T130_130 (by decide)

theorem hcardT130_130 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK130 ⟨130, by decide⟩ R130 hpxR130 hcardq130 (by decide)).symm

/-- **Cell (130, 130).** -/
theorem cell130_130 (e : List (ZMod 25)) (heK : charOK (basisAt rK130) e = true)
    (h : ↥(reps (⟨130, by decide⟩ : Fin 148))) :
    species (reps (⟨130, by decide⟩ : Fin 148)) h (basisElt (reps rK130) (charOfVec rK130 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK130 e (h : Coordinate 1) T130_130 i :=
  species_entry_eq_sum rK130 ⟨130, by decide⟩ e heK h T130_130 hfix130_130 hinj130_130 hcardT130_130
    (fun i => conj_mem_of_fixedPoints (reps ⟨130, by decide⟩) (reps rK130) (T130_130 i) (hfix130_130 i) h)

namespace Q2

def R130_2 : Fin 5 → Coordinate 2 := fun i => R130list.getD i.val (0,0,0,0,0)
theorem hpxR130_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK130) (R130_2 i)) := by decide
theorem hcardq130_2 : Nat.card (Coordinate 2 ⧸ reps rK130) = 5 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (130, 0) twin -/

def T130_0_2 : Fin 5 → Coordinate 2 := fun i => T130_0list.getD i.val (0,0,0,0,0)

theorem hfix130_0_2 : ∀ i, ((T130_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK130)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK130) :=
  repsFix_of_siftB2 rK130 ⟨0, by decide⟩ T130_0_2 (by decide)

theorem hinj130_0_2 : Function.Injective
    (fun i => ((T130_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK130)) :=
  repsInj_of_reduceAux2 rK130 T130_0_2 (by decide)

theorem hcardT130_0_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK130)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK130 ⟨0, by decide⟩ R130_2 hpxR130_2 hcardq130_2 (by decide)).symm

/-- **Cell (130, 0) twin (q=2).** -/
theorem cell130_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK130) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK130) (charOfVec2 rK130 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK130 e (h : Coordinate 2) T130_0_2 i :=
  species_entry_eq_sum rK130 ⟨0, by decide⟩ e heK h T130_0_2 hfix130_0_2 hinj130_0_2 hcardT130_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK130) (T130_0_2 i) (hfix130_0_2 i) h)

/-! ### Cell (130, 3) twin -/

def T130_3_2 : Fin 5 → Coordinate 2 := fun i => T130_3list.getD i.val (0,0,0,0,0)

theorem hfix130_3_2 : ∀ i, ((T130_3_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK130)
    ∈ fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK130) :=
  repsFix_of_siftB2 rK130 ⟨3, by decide⟩ T130_3_2 (by decide)

theorem hinj130_3_2 : Function.Injective
    (fun i => ((T130_3_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK130)) :=
  repsInj_of_reduceAux2 rK130 T130_3_2 (by decide)

theorem hcardT130_3_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK130)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK130 ⟨3, by decide⟩ R130_2 hpxR130_2 hcardq130_2 (by decide)).symm

/-- **Cell (130, 3) twin (q=2).** -/
theorem cell130_3_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK130) e = true)
    (h : ↥(reps (⟨3, by decide⟩ : Fin 148))) :
    species (reps (⟨3, by decide⟩ : Fin 148)) h (basisElt (reps rK130) (charOfVec2 rK130 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK130 e (h : Coordinate 2) T130_3_2 i :=
  species_entry_eq_sum rK130 ⟨3, by decide⟩ e heK h T130_3_2 hfix130_3_2 hinj130_3_2 hcardT130_3_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨3, by decide⟩) (reps rK130) (T130_3_2 i) (hfix130_3_2 i) h)

/-! ### Cell (130, 10) twin -/

def T130_10_2 : Fin 5 → Coordinate 2 := fun i => T130_10list.getD i.val (0,0,0,0,0)

theorem hfix130_10_2 : ∀ i, ((T130_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK130)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK130) :=
  repsFix_of_siftB2 rK130 ⟨10, by decide⟩ T130_10_2 (by decide)

theorem hinj130_10_2 : Function.Injective
    (fun i => ((T130_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK130)) :=
  repsInj_of_reduceAux2 rK130 T130_10_2 (by decide)

theorem hcardT130_10_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK130)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK130 ⟨10, by decide⟩ R130_2 hpxR130_2 hcardq130_2 (by decide)).symm

/-- **Cell (130, 10) twin (q=2).** -/
theorem cell130_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK130) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK130) (charOfVec2 rK130 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK130 e (h : Coordinate 2) T130_10_2 i :=
  species_entry_eq_sum rK130 ⟨10, by decide⟩ e heK h T130_10_2 hfix130_10_2 hinj130_10_2 hcardT130_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK130) (T130_10_2 i) (hfix130_10_2 i) h)

/-! ### Cell (130, 12) twin -/

def T130_12_2 : Fin 5 → Coordinate 2 := fun i => T130_12list.getD i.val (0,0,0,0,0)

theorem hfix130_12_2 : ∀ i, ((T130_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK130)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK130) :=
  repsFix_of_siftB2 rK130 ⟨12, by decide⟩ T130_12_2 (by decide)

theorem hinj130_12_2 : Function.Injective
    (fun i => ((T130_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK130)) :=
  repsInj_of_reduceAux2 rK130 T130_12_2 (by decide)

theorem hcardT130_12_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK130)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK130 ⟨12, by decide⟩ R130_2 hpxR130_2 hcardq130_2 (by decide)).symm

/-- **Cell (130, 12) twin (q=2).** -/
theorem cell130_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK130) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK130) (charOfVec2 rK130 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK130 e (h : Coordinate 2) T130_12_2 i :=
  species_entry_eq_sum rK130 ⟨12, by decide⟩ e heK h T130_12_2 hfix130_12_2 hinj130_12_2 hcardT130_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK130) (T130_12_2 i) (hfix130_12_2 i) h)

/-! ### Cell (130, 21) twin -/

def T130_21_2 : Fin 5 → Coordinate 2 := fun i => T130_21list.getD i.val (0,0,0,0,0)

theorem hfix130_21_2 : ∀ i, ((T130_21_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK130)
    ∈ fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK130) :=
  repsFix_of_siftB2 rK130 ⟨21, by decide⟩ T130_21_2 (by decide)

theorem hinj130_21_2 : Function.Injective
    (fun i => ((T130_21_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK130)) :=
  repsInj_of_reduceAux2 rK130 T130_21_2 (by decide)

theorem hcardT130_21_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK130)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK130 ⟨21, by decide⟩ R130_2 hpxR130_2 hcardq130_2 (by decide)).symm

/-- **Cell (130, 21) twin (q=2).** -/
theorem cell130_21_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK130) e = true)
    (h : ↥(reps (⟨21, by decide⟩ : Fin 148))) :
    species (reps (⟨21, by decide⟩ : Fin 148)) h (basisElt (reps rK130) (charOfVec2 rK130 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK130 e (h : Coordinate 2) T130_21_2 i :=
  species_entry_eq_sum rK130 ⟨21, by decide⟩ e heK h T130_21_2 hfix130_21_2 hinj130_21_2 hcardT130_21_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨21, by decide⟩) (reps rK130) (T130_21_2 i) (hfix130_21_2 i) h)

/-! ### Cell (130, 30) twin -/

def T130_30_2 : Fin 5 → Coordinate 2 := fun i => T130_30list.getD i.val (0,0,0,0,0)

theorem hfix130_30_2 : ∀ i, ((T130_30_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK130)
    ∈ fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK130) :=
  repsFix_of_siftB2 rK130 ⟨30, by decide⟩ T130_30_2 (by decide)

theorem hinj130_30_2 : Function.Injective
    (fun i => ((T130_30_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK130)) :=
  repsInj_of_reduceAux2 rK130 T130_30_2 (by decide)

theorem hcardT130_30_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK130)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK130 ⟨30, by decide⟩ R130_2 hpxR130_2 hcardq130_2 (by decide)).symm

/-- **Cell (130, 30) twin (q=2).** -/
theorem cell130_30_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK130) e = true)
    (h : ↥(reps (⟨30, by decide⟩ : Fin 148))) :
    species (reps (⟨30, by decide⟩ : Fin 148)) h (basisElt (reps rK130) (charOfVec2 rK130 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK130 e (h : Coordinate 2) T130_30_2 i :=
  species_entry_eq_sum rK130 ⟨30, by decide⟩ e heK h T130_30_2 hfix130_30_2 hinj130_30_2 hcardT130_30_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨30, by decide⟩) (reps rK130) (T130_30_2 i) (hfix130_30_2 i) h)

/-! ### Cell (130, 36) twin -/

def T130_36_2 : Fin 5 → Coordinate 2 := fun i => T130_36list.getD i.val (0,0,0,0,0)

theorem hfix130_36_2 : ∀ i, ((T130_36_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK130)
    ∈ fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK130) :=
  repsFix_of_siftB2 rK130 ⟨36, by decide⟩ T130_36_2 (by decide)

theorem hinj130_36_2 : Function.Injective
    (fun i => ((T130_36_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK130)) :=
  repsInj_of_reduceAux2 rK130 T130_36_2 (by decide)

theorem hcardT130_36_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK130)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK130 ⟨36, by decide⟩ R130_2 hpxR130_2 hcardq130_2 (by decide)).symm

/-- **Cell (130, 36) twin (q=2).** -/
theorem cell130_36_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK130) e = true)
    (h : ↥(reps (⟨36, by decide⟩ : Fin 148))) :
    species (reps (⟨36, by decide⟩ : Fin 148)) h (basisElt (reps rK130) (charOfVec2 rK130 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK130 e (h : Coordinate 2) T130_36_2 i :=
  species_entry_eq_sum rK130 ⟨36, by decide⟩ e heK h T130_36_2 hfix130_36_2 hinj130_36_2 hcardT130_36_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨36, by decide⟩) (reps rK130) (T130_36_2 i) (hfix130_36_2 i) h)

/-! ### Cell (130, 38) twin -/

def T130_38_2 : Fin 5 → Coordinate 2 := fun i => T130_38list.getD i.val (0,0,0,0,0)

theorem hfix130_38_2 : ∀ i, ((T130_38_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK130)
    ∈ fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK130) :=
  repsFix_of_siftB2 rK130 ⟨38, by decide⟩ T130_38_2 (by decide)

theorem hinj130_38_2 : Function.Injective
    (fun i => ((T130_38_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK130)) :=
  repsInj_of_reduceAux2 rK130 T130_38_2 (by decide)

theorem hcardT130_38_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK130)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK130 ⟨38, by decide⟩ R130_2 hpxR130_2 hcardq130_2 (by decide)).symm

/-- **Cell (130, 38) twin (q=2).** -/
theorem cell130_38_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK130) e = true)
    (h : ↥(reps (⟨38, by decide⟩ : Fin 148))) :
    species (reps (⟨38, by decide⟩ : Fin 148)) h (basisElt (reps rK130) (charOfVec2 rK130 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK130 e (h : Coordinate 2) T130_38_2 i :=
  species_entry_eq_sum rK130 ⟨38, by decide⟩ e heK h T130_38_2 hfix130_38_2 hinj130_38_2 hcardT130_38_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨38, by decide⟩) (reps rK130) (T130_38_2 i) (hfix130_38_2 i) h)

/-! ### Cell (130, 44) twin -/

def T130_44_2 : Fin 5 → Coordinate 2 := fun i => T130_44list.getD i.val (0,0,0,0,0)

theorem hfix130_44_2 : ∀ i, ((T130_44_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK130)
    ∈ fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK130) :=
  repsFix_of_siftB2 rK130 ⟨44, by decide⟩ T130_44_2 (by decide)

theorem hinj130_44_2 : Function.Injective
    (fun i => ((T130_44_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK130)) :=
  repsInj_of_reduceAux2 rK130 T130_44_2 (by decide)

theorem hcardT130_44_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK130)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK130 ⟨44, by decide⟩ R130_2 hpxR130_2 hcardq130_2 (by decide)).symm

/-- **Cell (130, 44) twin (q=2).** -/
theorem cell130_44_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK130) e = true)
    (h : ↥(reps (⟨44, by decide⟩ : Fin 148))) :
    species (reps (⟨44, by decide⟩ : Fin 148)) h (basisElt (reps rK130) (charOfVec2 rK130 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK130 e (h : Coordinate 2) T130_44_2 i :=
  species_entry_eq_sum rK130 ⟨44, by decide⟩ e heK h T130_44_2 hfix130_44_2 hinj130_44_2 hcardT130_44_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨44, by decide⟩) (reps rK130) (T130_44_2 i) (hfix130_44_2 i) h)

/-! ### Cell (130, 52) twin -/

def T130_52_2 : Fin 5 → Coordinate 2 := fun i => T130_52list.getD i.val (0,0,0,0,0)

theorem hfix130_52_2 : ∀ i, ((T130_52_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK130)
    ∈ fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK130) :=
  repsFix_of_siftB2 rK130 ⟨52, by decide⟩ T130_52_2 (by decide)

theorem hinj130_52_2 : Function.Injective
    (fun i => ((T130_52_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK130)) :=
  repsInj_of_reduceAux2 rK130 T130_52_2 (by decide)

theorem hcardT130_52_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK130)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK130 ⟨52, by decide⟩ R130_2 hpxR130_2 hcardq130_2 (by decide)).symm

/-- **Cell (130, 52) twin (q=2).** -/
theorem cell130_52_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK130) e = true)
    (h : ↥(reps (⟨52, by decide⟩ : Fin 148))) :
    species (reps (⟨52, by decide⟩ : Fin 148)) h (basisElt (reps rK130) (charOfVec2 rK130 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK130 e (h : Coordinate 2) T130_52_2 i :=
  species_entry_eq_sum rK130 ⟨52, by decide⟩ e heK h T130_52_2 hfix130_52_2 hinj130_52_2 hcardT130_52_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨52, by decide⟩) (reps rK130) (T130_52_2 i) (hfix130_52_2 i) h)

/-! ### Cell (130, 53) twin -/

def T130_53_2 : Fin 5 → Coordinate 2 := fun i => T130_53list.getD i.val (0,0,0,0,0)

theorem hfix130_53_2 : ∀ i, ((T130_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK130)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK130) :=
  repsFix_of_siftB2 rK130 ⟨53, by decide⟩ T130_53_2 (by decide)

theorem hinj130_53_2 : Function.Injective
    (fun i => ((T130_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK130)) :=
  repsInj_of_reduceAux2 rK130 T130_53_2 (by decide)

theorem hcardT130_53_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK130)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK130 ⟨53, by decide⟩ R130_2 hpxR130_2 hcardq130_2 (by decide)).symm

/-- **Cell (130, 53) twin (q=2).** -/
theorem cell130_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK130) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK130) (charOfVec2 rK130 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK130 e (h : Coordinate 2) T130_53_2 i :=
  species_entry_eq_sum rK130 ⟨53, by decide⟩ e heK h T130_53_2 hfix130_53_2 hinj130_53_2 hcardT130_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK130) (T130_53_2 i) (hfix130_53_2 i) h)

/-! ### Cell (130, 82) twin -/

def T130_82_2 : Fin 5 → Coordinate 2 := fun i => T130_82list.getD i.val (0,0,0,0,0)

theorem hfix130_82_2 : ∀ i, ((T130_82_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK130)
    ∈ fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK130) :=
  repsFix_of_siftB2 rK130 ⟨82, by decide⟩ T130_82_2 (by decide)

theorem hinj130_82_2 : Function.Injective
    (fun i => ((T130_82_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK130)) :=
  repsInj_of_reduceAux2 rK130 T130_82_2 (by decide)

theorem hcardT130_82_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK130)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK130 ⟨82, by decide⟩ R130_2 hpxR130_2 hcardq130_2 (by decide)).symm

/-- **Cell (130, 82) twin (q=2).** -/
theorem cell130_82_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK130) e = true)
    (h : ↥(reps (⟨82, by decide⟩ : Fin 148))) :
    species (reps (⟨82, by decide⟩ : Fin 148)) h (basisElt (reps rK130) (charOfVec2 rK130 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK130 e (h : Coordinate 2) T130_82_2 i :=
  species_entry_eq_sum rK130 ⟨82, by decide⟩ e heK h T130_82_2 hfix130_82_2 hinj130_82_2 hcardT130_82_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨82, by decide⟩) (reps rK130) (T130_82_2 i) (hfix130_82_2 i) h)

/-! ### Cell (130, 92) twin -/

def T130_92_2 : Fin 5 → Coordinate 2 := fun i => T130_92list.getD i.val (0,0,0,0,0)

theorem hfix130_92_2 : ∀ i, ((T130_92_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK130)
    ∈ fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK130) :=
  repsFix_of_siftB2 rK130 ⟨92, by decide⟩ T130_92_2 (by decide)

theorem hinj130_92_2 : Function.Injective
    (fun i => ((T130_92_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK130)) :=
  repsInj_of_reduceAux2 rK130 T130_92_2 (by decide)

theorem hcardT130_92_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK130)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK130 ⟨92, by decide⟩ R130_2 hpxR130_2 hcardq130_2 (by decide)).symm

/-- **Cell (130, 92) twin (q=2).** -/
theorem cell130_92_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK130) e = true)
    (h : ↥(reps (⟨92, by decide⟩ : Fin 148))) :
    species (reps (⟨92, by decide⟩ : Fin 148)) h (basisElt (reps rK130) (charOfVec2 rK130 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK130 e (h : Coordinate 2) T130_92_2 i :=
  species_entry_eq_sum rK130 ⟨92, by decide⟩ e heK h T130_92_2 hfix130_92_2 hinj130_92_2 hcardT130_92_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨92, by decide⟩) (reps rK130) (T130_92_2 i) (hfix130_92_2 i) h)

/-! ### Cell (130, 98) twin -/

def T130_98_2 : Fin 5 → Coordinate 2 := fun i => T130_98list.getD i.val (0,0,0,0,0)

theorem hfix130_98_2 : ∀ i, ((T130_98_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK130)
    ∈ fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK130) :=
  repsFix_of_siftB2 rK130 ⟨98, by decide⟩ T130_98_2 (by decide)

theorem hinj130_98_2 : Function.Injective
    (fun i => ((T130_98_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK130)) :=
  repsInj_of_reduceAux2 rK130 T130_98_2 (by decide)

theorem hcardT130_98_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK130)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK130 ⟨98, by decide⟩ R130_2 hpxR130_2 hcardq130_2 (by decide)).symm

/-- **Cell (130, 98) twin (q=2).** -/
theorem cell130_98_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK130) e = true)
    (h : ↥(reps (⟨98, by decide⟩ : Fin 148))) :
    species (reps (⟨98, by decide⟩ : Fin 148)) h (basisElt (reps rK130) (charOfVec2 rK130 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK130 e (h : Coordinate 2) T130_98_2 i :=
  species_entry_eq_sum rK130 ⟨98, by decide⟩ e heK h T130_98_2 hfix130_98_2 hinj130_98_2 hcardT130_98_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨98, by decide⟩) (reps rK130) (T130_98_2 i) (hfix130_98_2 i) h)

/-! ### Cell (130, 100) twin -/

def T130_100_2 : Fin 5 → Coordinate 2 := fun i => T130_100list.getD i.val (0,0,0,0,0)

theorem hfix130_100_2 : ∀ i, ((T130_100_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK130)
    ∈ fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK130) :=
  repsFix_of_siftB2 rK130 ⟨100, by decide⟩ T130_100_2 (by decide)

theorem hinj130_100_2 : Function.Injective
    (fun i => ((T130_100_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK130)) :=
  repsInj_of_reduceAux2 rK130 T130_100_2 (by decide)

theorem hcardT130_100_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK130)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK130 ⟨100, by decide⟩ R130_2 hpxR130_2 hcardq130_2 (by decide)).symm

/-- **Cell (130, 100) twin (q=2).** -/
theorem cell130_100_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK130) e = true)
    (h : ↥(reps (⟨100, by decide⟩ : Fin 148))) :
    species (reps (⟨100, by decide⟩ : Fin 148)) h (basisElt (reps rK130) (charOfVec2 rK130 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK130 e (h : Coordinate 2) T130_100_2 i :=
  species_entry_eq_sum rK130 ⟨100, by decide⟩ e heK h T130_100_2 hfix130_100_2 hinj130_100_2 hcardT130_100_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨100, by decide⟩) (reps rK130) (T130_100_2 i) (hfix130_100_2 i) h)

/-! ### Cell (130, 106) twin -/

def T130_106_2 : Fin 5 → Coordinate 2 := fun i => T130_106list.getD i.val (0,0,0,0,0)

theorem hfix130_106_2 : ∀ i, ((T130_106_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK130)
    ∈ fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK130) :=
  repsFix_of_siftB2 rK130 ⟨106, by decide⟩ T130_106_2 (by decide)

theorem hinj130_106_2 : Function.Injective
    (fun i => ((T130_106_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK130)) :=
  repsInj_of_reduceAux2 rK130 T130_106_2 (by decide)

theorem hcardT130_106_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK130)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK130 ⟨106, by decide⟩ R130_2 hpxR130_2 hcardq130_2 (by decide)).symm

/-- **Cell (130, 106) twin (q=2).** -/
theorem cell130_106_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK130) e = true)
    (h : ↥(reps (⟨106, by decide⟩ : Fin 148))) :
    species (reps (⟨106, by decide⟩ : Fin 148)) h (basisElt (reps rK130) (charOfVec2 rK130 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK130 e (h : Coordinate 2) T130_106_2 i :=
  species_entry_eq_sum rK130 ⟨106, by decide⟩ e heK h T130_106_2 hfix130_106_2 hinj130_106_2 hcardT130_106_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨106, by decide⟩) (reps rK130) (T130_106_2 i) (hfix130_106_2 i) h)

/-! ### Cell (130, 114) twin -/

def T130_114_2 : Fin 5 → Coordinate 2 := fun i => T130_114list.getD i.val (0,0,0,0,0)

theorem hfix130_114_2 : ∀ i, ((T130_114_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK130)
    ∈ fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK130) :=
  repsFix_of_siftB2 rK130 ⟨114, by decide⟩ T130_114_2 (by decide)

theorem hinj130_114_2 : Function.Injective
    (fun i => ((T130_114_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK130)) :=
  repsInj_of_reduceAux2 rK130 T130_114_2 (by decide)

theorem hcardT130_114_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK130)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK130 ⟨114, by decide⟩ R130_2 hpxR130_2 hcardq130_2 (by decide)).symm

/-- **Cell (130, 114) twin (q=2).** -/
theorem cell130_114_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK130) e = true)
    (h : ↥(reps (⟨114, by decide⟩ : Fin 148))) :
    species (reps (⟨114, by decide⟩ : Fin 148)) h (basisElt (reps rK130) (charOfVec2 rK130 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK130 e (h : Coordinate 2) T130_114_2 i :=
  species_entry_eq_sum rK130 ⟨114, by decide⟩ e heK h T130_114_2 hfix130_114_2 hinj130_114_2 hcardT130_114_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨114, by decide⟩) (reps rK130) (T130_114_2 i) (hfix130_114_2 i) h)

/-! ### Cell (130, 130) twin -/

def T130_130_2 : Fin 5 → Coordinate 2 := fun i => T130_130list.getD i.val (0,0,0,0,0)

theorem hfix130_130_2 : ∀ i, ((T130_130_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK130)
    ∈ fixedPoints (reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK130) :=
  repsFix_of_siftB2 rK130 ⟨130, by decide⟩ T130_130_2 (by decide)

theorem hinj130_130_2 : Function.Injective
    (fun i => ((T130_130_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK130)) :=
  repsInj_of_reduceAux2 rK130 T130_130_2 (by decide)

theorem hcardT130_130_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK130)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK130 ⟨130, by decide⟩ R130_2 hpxR130_2 hcardq130_2 (by decide)).symm

/-- **Cell (130, 130) twin (q=2).** -/
theorem cell130_130_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK130) e = true)
    (h : ↥(reps (⟨130, by decide⟩ : Fin 148))) :
    species (reps (⟨130, by decide⟩ : Fin 148)) h (basisElt (reps rK130) (charOfVec2 rK130 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK130 e (h : Coordinate 2) T130_130_2 i :=
  species_entry_eq_sum rK130 ⟨130, by decide⟩ e heK h T130_130_2 hfix130_130_2 hinj130_130_2 hcardT130_130_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨130, by decide⟩) (reps rK130) (T130_130_2 i) (hfix130_130_2 i) h)

end Q2

/-! # K-class rK = 131  (|G/K| = 5) -/

def rK131 : Fin 148 := ⟨131, by decide⟩

def R131list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def R131 : Fin 5 → Coordinate 1 := fun i => R131list.getD i.val (0,0,0,0,0)

theorem hpxR131 : Function.Injective (fun i => reduceAux 1 (basisAt rK131) (R131 i)) := by decide
theorem hcardq131 : Nat.card (Coordinate 1 ⧸ reps rK131) = 5 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (131, 0): |T| = 5 -/

def T131_0list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T131_0 : Fin 5 → Coordinate 1 := fun i => T131_0list.getD i.val (0,0,0,0,0)

theorem hfix131_0 : ∀ i, ((T131_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK131)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131) :=
  repsFix_of_siftB rK131 ⟨0, by decide⟩ T131_0 (by decide)

theorem hinj131_0 : Function.Injective
    (fun i => ((T131_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK131)) :=
  repsInj_of_reduceAux rK131 T131_0 (by decide)

theorem hcardT131_0 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK131 ⟨0, by decide⟩ R131 hpxR131 hcardq131 (by decide)).symm

/-- **Cell (131, 0).** -/
theorem cell131_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK131) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK131) (charOfVec rK131 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK131 e (h : Coordinate 1) T131_0 i :=
  species_entry_eq_sum rK131 ⟨0, by decide⟩ e heK h T131_0 hfix131_0 hinj131_0 hcardT131_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK131) (T131_0 i) (hfix131_0 i) h)

/-! ## Cell (131, 4): |T| = 5 -/

def T131_4list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T131_4 : Fin 5 → Coordinate 1 := fun i => T131_4list.getD i.val (0,0,0,0,0)

theorem hfix131_4 : ∀ i, ((T131_4 i : Coordinate 1) : Coordinate 1 ⧸ reps rK131)
    ∈ fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131) :=
  repsFix_of_siftB rK131 ⟨4, by decide⟩ T131_4 (by decide)

theorem hinj131_4 : Function.Injective
    (fun i => ((T131_4 i : Coordinate 1) : Coordinate 1 ⧸ reps rK131)) :=
  repsInj_of_reduceAux rK131 T131_4 (by decide)

theorem hcardT131_4 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK131 ⟨4, by decide⟩ R131 hpxR131 hcardq131 (by decide)).symm

/-- **Cell (131, 4).** -/
theorem cell131_4 (e : List (ZMod 25)) (heK : charOK (basisAt rK131) e = true)
    (h : ↥(reps (⟨4, by decide⟩ : Fin 148))) :
    species (reps (⟨4, by decide⟩ : Fin 148)) h (basisElt (reps rK131) (charOfVec rK131 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK131 e (h : Coordinate 1) T131_4 i :=
  species_entry_eq_sum rK131 ⟨4, by decide⟩ e heK h T131_4 hfix131_4 hinj131_4 hcardT131_4
    (fun i => conj_mem_of_fixedPoints (reps ⟨4, by decide⟩) (reps rK131) (T131_4 i) (hfix131_4 i) h)

/-! ## Cell (131, 10): |T| = 5 -/

def T131_10list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T131_10 : Fin 5 → Coordinate 1 := fun i => T131_10list.getD i.val (0,0,0,0,0)

theorem hfix131_10 : ∀ i, ((T131_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK131)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131) :=
  repsFix_of_siftB rK131 ⟨10, by decide⟩ T131_10 (by decide)

theorem hinj131_10 : Function.Injective
    (fun i => ((T131_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK131)) :=
  repsInj_of_reduceAux rK131 T131_10 (by decide)

theorem hcardT131_10 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK131 ⟨10, by decide⟩ R131 hpxR131 hcardq131 (by decide)).symm

/-- **Cell (131, 10).** -/
theorem cell131_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK131) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK131) (charOfVec rK131 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK131 e (h : Coordinate 1) T131_10 i :=
  species_entry_eq_sum rK131 ⟨10, by decide⟩ e heK h T131_10 hfix131_10 hinj131_10 hcardT131_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK131) (T131_10 i) (hfix131_10 i) h)

/-! ## Cell (131, 12): |T| = 5 -/

def T131_12list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T131_12 : Fin 5 → Coordinate 1 := fun i => T131_12list.getD i.val (0,0,0,0,0)

theorem hfix131_12 : ∀ i, ((T131_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK131)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131) :=
  repsFix_of_siftB rK131 ⟨12, by decide⟩ T131_12 (by decide)

theorem hinj131_12 : Function.Injective
    (fun i => ((T131_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK131)) :=
  repsInj_of_reduceAux rK131 T131_12 (by decide)

theorem hcardT131_12 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK131 ⟨12, by decide⟩ R131 hpxR131 hcardq131 (by decide)).symm

/-- **Cell (131, 12).** -/
theorem cell131_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK131) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK131) (charOfVec rK131 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK131 e (h : Coordinate 1) T131_12 i :=
  species_entry_eq_sum rK131 ⟨12, by decide⟩ e heK h T131_12 hfix131_12 hinj131_12 hcardT131_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK131) (T131_12 i) (hfix131_12 i) h)

/-! ## Cell (131, 22): |T| = 5 -/

def T131_22list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T131_22 : Fin 5 → Coordinate 1 := fun i => T131_22list.getD i.val (0,0,0,0,0)

theorem hfix131_22 : ∀ i, ((T131_22 i : Coordinate 1) : Coordinate 1 ⧸ reps rK131)
    ∈ fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131) :=
  repsFix_of_siftB rK131 ⟨22, by decide⟩ T131_22 (by decide)

theorem hinj131_22 : Function.Injective
    (fun i => ((T131_22 i : Coordinate 1) : Coordinate 1 ⧸ reps rK131)) :=
  repsInj_of_reduceAux rK131 T131_22 (by decide)

theorem hcardT131_22 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK131 ⟨22, by decide⟩ R131 hpxR131 hcardq131 (by decide)).symm

/-- **Cell (131, 22).** -/
theorem cell131_22 (e : List (ZMod 25)) (heK : charOK (basisAt rK131) e = true)
    (h : ↥(reps (⟨22, by decide⟩ : Fin 148))) :
    species (reps (⟨22, by decide⟩ : Fin 148)) h (basisElt (reps rK131) (charOfVec rK131 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK131 e (h : Coordinate 1) T131_22 i :=
  species_entry_eq_sum rK131 ⟨22, by decide⟩ e heK h T131_22 hfix131_22 hinj131_22 hcardT131_22
    (fun i => conj_mem_of_fixedPoints (reps ⟨22, by decide⟩) (reps rK131) (T131_22 i) (hfix131_22 i) h)

/-! ## Cell (131, 30): |T| = 5 -/

def T131_30list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T131_30 : Fin 5 → Coordinate 1 := fun i => T131_30list.getD i.val (0,0,0,0,0)

theorem hfix131_30 : ∀ i, ((T131_30 i : Coordinate 1) : Coordinate 1 ⧸ reps rK131)
    ∈ fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131) :=
  repsFix_of_siftB rK131 ⟨30, by decide⟩ T131_30 (by decide)

theorem hinj131_30 : Function.Injective
    (fun i => ((T131_30 i : Coordinate 1) : Coordinate 1 ⧸ reps rK131)) :=
  repsInj_of_reduceAux rK131 T131_30 (by decide)

theorem hcardT131_30 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK131 ⟨30, by decide⟩ R131 hpxR131 hcardq131 (by decide)).symm

/-- **Cell (131, 30).** -/
theorem cell131_30 (e : List (ZMod 25)) (heK : charOK (basisAt rK131) e = true)
    (h : ↥(reps (⟨30, by decide⟩ : Fin 148))) :
    species (reps (⟨30, by decide⟩ : Fin 148)) h (basisElt (reps rK131) (charOfVec rK131 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK131 e (h : Coordinate 1) T131_30 i :=
  species_entry_eq_sum rK131 ⟨30, by decide⟩ e heK h T131_30 hfix131_30 hinj131_30 hcardT131_30
    (fun i => conj_mem_of_fixedPoints (reps ⟨30, by decide⟩) (reps rK131) (T131_30 i) (hfix131_30 i) h)

/-! ## Cell (131, 34): |T| = 5 -/

def T131_34list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T131_34 : Fin 5 → Coordinate 1 := fun i => T131_34list.getD i.val (0,0,0,0,0)

theorem hfix131_34 : ∀ i, ((T131_34 i : Coordinate 1) : Coordinate 1 ⧸ reps rK131)
    ∈ fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131) :=
  repsFix_of_siftB rK131 ⟨34, by decide⟩ T131_34 (by decide)

theorem hinj131_34 : Function.Injective
    (fun i => ((T131_34 i : Coordinate 1) : Coordinate 1 ⧸ reps rK131)) :=
  repsInj_of_reduceAux rK131 T131_34 (by decide)

theorem hcardT131_34 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK131 ⟨34, by decide⟩ R131 hpxR131 hcardq131 (by decide)).symm

/-- **Cell (131, 34).** -/
theorem cell131_34 (e : List (ZMod 25)) (heK : charOK (basisAt rK131) e = true)
    (h : ↥(reps (⟨34, by decide⟩ : Fin 148))) :
    species (reps (⟨34, by decide⟩ : Fin 148)) h (basisElt (reps rK131) (charOfVec rK131 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK131 e (h : Coordinate 1) T131_34 i :=
  species_entry_eq_sum rK131 ⟨34, by decide⟩ e heK h T131_34 hfix131_34 hinj131_34 hcardT131_34
    (fun i => conj_mem_of_fixedPoints (reps ⟨34, by decide⟩) (reps rK131) (T131_34 i) (hfix131_34 i) h)

/-! ## Cell (131, 42): |T| = 5 -/

def T131_42list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T131_42 : Fin 5 → Coordinate 1 := fun i => T131_42list.getD i.val (0,0,0,0,0)

theorem hfix131_42 : ∀ i, ((T131_42 i : Coordinate 1) : Coordinate 1 ⧸ reps rK131)
    ∈ fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131) :=
  repsFix_of_siftB rK131 ⟨42, by decide⟩ T131_42 (by decide)

theorem hinj131_42 : Function.Injective
    (fun i => ((T131_42 i : Coordinate 1) : Coordinate 1 ⧸ reps rK131)) :=
  repsInj_of_reduceAux rK131 T131_42 (by decide)

theorem hcardT131_42 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK131 ⟨42, by decide⟩ R131 hpxR131 hcardq131 (by decide)).symm

/-- **Cell (131, 42).** -/
theorem cell131_42 (e : List (ZMod 25)) (heK : charOK (basisAt rK131) e = true)
    (h : ↥(reps (⟨42, by decide⟩ : Fin 148))) :
    species (reps (⟨42, by decide⟩ : Fin 148)) h (basisElt (reps rK131) (charOfVec rK131 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK131 e (h : Coordinate 1) T131_42 i :=
  species_entry_eq_sum rK131 ⟨42, by decide⟩ e heK h T131_42 hfix131_42 hinj131_42 hcardT131_42
    (fun i => conj_mem_of_fixedPoints (reps ⟨42, by decide⟩) (reps rK131) (T131_42 i) (hfix131_42 i) h)

/-! ## Cell (131, 46): |T| = 5 -/

def T131_46list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T131_46 : Fin 5 → Coordinate 1 := fun i => T131_46list.getD i.val (0,0,0,0,0)

theorem hfix131_46 : ∀ i, ((T131_46 i : Coordinate 1) : Coordinate 1 ⧸ reps rK131)
    ∈ fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131) :=
  repsFix_of_siftB rK131 ⟨46, by decide⟩ T131_46 (by decide)

theorem hinj131_46 : Function.Injective
    (fun i => ((T131_46 i : Coordinate 1) : Coordinate 1 ⧸ reps rK131)) :=
  repsInj_of_reduceAux rK131 T131_46 (by decide)

theorem hcardT131_46 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK131 ⟨46, by decide⟩ R131 hpxR131 hcardq131 (by decide)).symm

/-- **Cell (131, 46).** -/
theorem cell131_46 (e : List (ZMod 25)) (heK : charOK (basisAt rK131) e = true)
    (h : ↥(reps (⟨46, by decide⟩ : Fin 148))) :
    species (reps (⟨46, by decide⟩ : Fin 148)) h (basisElt (reps rK131) (charOfVec rK131 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK131 e (h : Coordinate 1) T131_46 i :=
  species_entry_eq_sum rK131 ⟨46, by decide⟩ e heK h T131_46 hfix131_46 hinj131_46 hcardT131_46
    (fun i => conj_mem_of_fixedPoints (reps ⟨46, by decide⟩) (reps rK131) (T131_46 i) (hfix131_46 i) h)

/-! ## Cell (131, 48): |T| = 5 -/

def T131_48list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T131_48 : Fin 5 → Coordinate 1 := fun i => T131_48list.getD i.val (0,0,0,0,0)

theorem hfix131_48 : ∀ i, ((T131_48 i : Coordinate 1) : Coordinate 1 ⧸ reps rK131)
    ∈ fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131) :=
  repsFix_of_siftB rK131 ⟨48, by decide⟩ T131_48 (by decide)

theorem hinj131_48 : Function.Injective
    (fun i => ((T131_48 i : Coordinate 1) : Coordinate 1 ⧸ reps rK131)) :=
  repsInj_of_reduceAux rK131 T131_48 (by decide)

theorem hcardT131_48 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK131 ⟨48, by decide⟩ R131 hpxR131 hcardq131 (by decide)).symm

/-- **Cell (131, 48).** -/
theorem cell131_48 (e : List (ZMod 25)) (heK : charOK (basisAt rK131) e = true)
    (h : ↥(reps (⟨48, by decide⟩ : Fin 148))) :
    species (reps (⟨48, by decide⟩ : Fin 148)) h (basisElt (reps rK131) (charOfVec rK131 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK131 e (h : Coordinate 1) T131_48 i :=
  species_entry_eq_sum rK131 ⟨48, by decide⟩ e heK h T131_48 hfix131_48 hinj131_48 hcardT131_48
    (fun i => conj_mem_of_fixedPoints (reps ⟨48, by decide⟩) (reps rK131) (T131_48 i) (hfix131_48 i) h)

/-! ## Cell (131, 53): |T| = 5 -/

def T131_53list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T131_53 : Fin 5 → Coordinate 1 := fun i => T131_53list.getD i.val (0,0,0,0,0)

theorem hfix131_53 : ∀ i, ((T131_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK131)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131) :=
  repsFix_of_siftB rK131 ⟨53, by decide⟩ T131_53 (by decide)

theorem hinj131_53 : Function.Injective
    (fun i => ((T131_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK131)) :=
  repsInj_of_reduceAux rK131 T131_53 (by decide)

theorem hcardT131_53 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK131 ⟨53, by decide⟩ R131 hpxR131 hcardq131 (by decide)).symm

/-- **Cell (131, 53).** -/
theorem cell131_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK131) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK131) (charOfVec rK131 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK131 e (h : Coordinate 1) T131_53 i :=
  species_entry_eq_sum rK131 ⟨53, by decide⟩ e heK h T131_53 hfix131_53 hinj131_53 hcardT131_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK131) (T131_53 i) (hfix131_53 i) h)

/-! ## Cell (131, 83): |T| = 5 -/

def T131_83list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T131_83 : Fin 5 → Coordinate 1 := fun i => T131_83list.getD i.val (0,0,0,0,0)

theorem hfix131_83 : ∀ i, ((T131_83 i : Coordinate 1) : Coordinate 1 ⧸ reps rK131)
    ∈ fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131) :=
  repsFix_of_siftB rK131 ⟨83, by decide⟩ T131_83 (by decide)

theorem hinj131_83 : Function.Injective
    (fun i => ((T131_83 i : Coordinate 1) : Coordinate 1 ⧸ reps rK131)) :=
  repsInj_of_reduceAux rK131 T131_83 (by decide)

theorem hcardT131_83 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK131 ⟨83, by decide⟩ R131 hpxR131 hcardq131 (by decide)).symm

/-- **Cell (131, 83).** -/
theorem cell131_83 (e : List (ZMod 25)) (heK : charOK (basisAt rK131) e = true)
    (h : ↥(reps (⟨83, by decide⟩ : Fin 148))) :
    species (reps (⟨83, by decide⟩ : Fin 148)) h (basisElt (reps rK131) (charOfVec rK131 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK131 e (h : Coordinate 1) T131_83 i :=
  species_entry_eq_sum rK131 ⟨83, by decide⟩ e heK h T131_83 hfix131_83 hinj131_83 hcardT131_83
    (fun i => conj_mem_of_fixedPoints (reps ⟨83, by decide⟩) (reps rK131) (T131_83 i) (hfix131_83 i) h)

/-! ## Cell (131, 92): |T| = 5 -/

def T131_92list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T131_92 : Fin 5 → Coordinate 1 := fun i => T131_92list.getD i.val (0,0,0,0,0)

theorem hfix131_92 : ∀ i, ((T131_92 i : Coordinate 1) : Coordinate 1 ⧸ reps rK131)
    ∈ fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131) :=
  repsFix_of_siftB rK131 ⟨92, by decide⟩ T131_92 (by decide)

theorem hinj131_92 : Function.Injective
    (fun i => ((T131_92 i : Coordinate 1) : Coordinate 1 ⧸ reps rK131)) :=
  repsInj_of_reduceAux rK131 T131_92 (by decide)

theorem hcardT131_92 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK131 ⟨92, by decide⟩ R131 hpxR131 hcardq131 (by decide)).symm

/-- **Cell (131, 92).** -/
theorem cell131_92 (e : List (ZMod 25)) (heK : charOK (basisAt rK131) e = true)
    (h : ↥(reps (⟨92, by decide⟩ : Fin 148))) :
    species (reps (⟨92, by decide⟩ : Fin 148)) h (basisElt (reps rK131) (charOfVec rK131 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK131 e (h : Coordinate 1) T131_92 i :=
  species_entry_eq_sum rK131 ⟨92, by decide⟩ e heK h T131_92 hfix131_92 hinj131_92 hcardT131_92
    (fun i => conj_mem_of_fixedPoints (reps ⟨92, by decide⟩) (reps rK131) (T131_92 i) (hfix131_92 i) h)

/-! ## Cell (131, 96): |T| = 5 -/

def T131_96list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T131_96 : Fin 5 → Coordinate 1 := fun i => T131_96list.getD i.val (0,0,0,0,0)

theorem hfix131_96 : ∀ i, ((T131_96 i : Coordinate 1) : Coordinate 1 ⧸ reps rK131)
    ∈ fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131) :=
  repsFix_of_siftB rK131 ⟨96, by decide⟩ T131_96 (by decide)

theorem hinj131_96 : Function.Injective
    (fun i => ((T131_96 i : Coordinate 1) : Coordinate 1 ⧸ reps rK131)) :=
  repsInj_of_reduceAux rK131 T131_96 (by decide)

theorem hcardT131_96 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK131 ⟨96, by decide⟩ R131 hpxR131 hcardq131 (by decide)).symm

/-- **Cell (131, 96).** -/
theorem cell131_96 (e : List (ZMod 25)) (heK : charOK (basisAt rK131) e = true)
    (h : ↥(reps (⟨96, by decide⟩ : Fin 148))) :
    species (reps (⟨96, by decide⟩ : Fin 148)) h (basisElt (reps rK131) (charOfVec rK131 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK131 e (h : Coordinate 1) T131_96 i :=
  species_entry_eq_sum rK131 ⟨96, by decide⟩ e heK h T131_96 hfix131_96 hinj131_96 hcardT131_96
    (fun i => conj_mem_of_fixedPoints (reps ⟨96, by decide⟩) (reps rK131) (T131_96 i) (hfix131_96 i) h)

/-! ## Cell (131, 104): |T| = 5 -/

def T131_104list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T131_104 : Fin 5 → Coordinate 1 := fun i => T131_104list.getD i.val (0,0,0,0,0)

theorem hfix131_104 : ∀ i, ((T131_104 i : Coordinate 1) : Coordinate 1 ⧸ reps rK131)
    ∈ fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131) :=
  repsFix_of_siftB rK131 ⟨104, by decide⟩ T131_104 (by decide)

theorem hinj131_104 : Function.Injective
    (fun i => ((T131_104 i : Coordinate 1) : Coordinate 1 ⧸ reps rK131)) :=
  repsInj_of_reduceAux rK131 T131_104 (by decide)

theorem hcardT131_104 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK131 ⟨104, by decide⟩ R131 hpxR131 hcardq131 (by decide)).symm

/-- **Cell (131, 104).** -/
theorem cell131_104 (e : List (ZMod 25)) (heK : charOK (basisAt rK131) e = true)
    (h : ↥(reps (⟨104, by decide⟩ : Fin 148))) :
    species (reps (⟨104, by decide⟩ : Fin 148)) h (basisElt (reps rK131) (charOfVec rK131 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK131 e (h : Coordinate 1) T131_104 i :=
  species_entry_eq_sum rK131 ⟨104, by decide⟩ e heK h T131_104 hfix131_104 hinj131_104 hcardT131_104
    (fun i => conj_mem_of_fixedPoints (reps ⟨104, by decide⟩) (reps rK131) (T131_104 i) (hfix131_104 i) h)

/-! ## Cell (131, 108): |T| = 5 -/

def T131_108list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T131_108 : Fin 5 → Coordinate 1 := fun i => T131_108list.getD i.val (0,0,0,0,0)

theorem hfix131_108 : ∀ i, ((T131_108 i : Coordinate 1) : Coordinate 1 ⧸ reps rK131)
    ∈ fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131) :=
  repsFix_of_siftB rK131 ⟨108, by decide⟩ T131_108 (by decide)

theorem hinj131_108 : Function.Injective
    (fun i => ((T131_108 i : Coordinate 1) : Coordinate 1 ⧸ reps rK131)) :=
  repsInj_of_reduceAux rK131 T131_108 (by decide)

theorem hcardT131_108 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK131 ⟨108, by decide⟩ R131 hpxR131 hcardq131 (by decide)).symm

/-- **Cell (131, 108).** -/
theorem cell131_108 (e : List (ZMod 25)) (heK : charOK (basisAt rK131) e = true)
    (h : ↥(reps (⟨108, by decide⟩ : Fin 148))) :
    species (reps (⟨108, by decide⟩ : Fin 148)) h (basisElt (reps rK131) (charOfVec rK131 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK131 e (h : Coordinate 1) T131_108 i :=
  species_entry_eq_sum rK131 ⟨108, by decide⟩ e heK h T131_108 hfix131_108 hinj131_108 hcardT131_108
    (fun i => conj_mem_of_fixedPoints (reps ⟨108, by decide⟩) (reps rK131) (T131_108 i) (hfix131_108 i) h)

/-! ## Cell (131, 110): |T| = 5 -/

def T131_110list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T131_110 : Fin 5 → Coordinate 1 := fun i => T131_110list.getD i.val (0,0,0,0,0)

theorem hfix131_110 : ∀ i, ((T131_110 i : Coordinate 1) : Coordinate 1 ⧸ reps rK131)
    ∈ fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131) :=
  repsFix_of_siftB rK131 ⟨110, by decide⟩ T131_110 (by decide)

theorem hinj131_110 : Function.Injective
    (fun i => ((T131_110 i : Coordinate 1) : Coordinate 1 ⧸ reps rK131)) :=
  repsInj_of_reduceAux rK131 T131_110 (by decide)

theorem hcardT131_110 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK131 ⟨110, by decide⟩ R131 hpxR131 hcardq131 (by decide)).symm

/-- **Cell (131, 110).** -/
theorem cell131_110 (e : List (ZMod 25)) (heK : charOK (basisAt rK131) e = true)
    (h : ↥(reps (⟨110, by decide⟩ : Fin 148))) :
    species (reps (⟨110, by decide⟩ : Fin 148)) h (basisElt (reps rK131) (charOfVec rK131 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK131 e (h : Coordinate 1) T131_110 i :=
  species_entry_eq_sum rK131 ⟨110, by decide⟩ e heK h T131_110 hfix131_110 hinj131_110 hcardT131_110
    (fun i => conj_mem_of_fixedPoints (reps ⟨110, by decide⟩) (reps rK131) (T131_110 i) (hfix131_110 i) h)

/-! ## Cell (131, 131): |T| = 5 -/

def T131_131list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T131_131 : Fin 5 → Coordinate 1 := fun i => T131_131list.getD i.val (0,0,0,0,0)

theorem hfix131_131 : ∀ i, ((T131_131 i : Coordinate 1) : Coordinate 1 ⧸ reps rK131)
    ∈ fixedPoints (reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131) :=
  repsFix_of_siftB rK131 ⟨131, by decide⟩ T131_131 (by decide)

theorem hinj131_131 : Function.Injective
    (fun i => ((T131_131 i : Coordinate 1) : Coordinate 1 ⧸ reps rK131)) :=
  repsInj_of_reduceAux rK131 T131_131 (by decide)

theorem hcardT131_131 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK131 ⟨131, by decide⟩ R131 hpxR131 hcardq131 (by decide)).symm

/-- **Cell (131, 131).** -/
theorem cell131_131 (e : List (ZMod 25)) (heK : charOK (basisAt rK131) e = true)
    (h : ↥(reps (⟨131, by decide⟩ : Fin 148))) :
    species (reps (⟨131, by decide⟩ : Fin 148)) h (basisElt (reps rK131) (charOfVec rK131 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK131 e (h : Coordinate 1) T131_131 i :=
  species_entry_eq_sum rK131 ⟨131, by decide⟩ e heK h T131_131 hfix131_131 hinj131_131 hcardT131_131
    (fun i => conj_mem_of_fixedPoints (reps ⟨131, by decide⟩) (reps rK131) (T131_131 i) (hfix131_131 i) h)

namespace Q2

def R131_2 : Fin 5 → Coordinate 2 := fun i => R131list.getD i.val (0,0,0,0,0)
theorem hpxR131_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK131) (R131_2 i)) := by decide
theorem hcardq131_2 : Nat.card (Coordinate 2 ⧸ reps rK131) = 5 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (131, 0) twin -/

def T131_0_2 : Fin 5 → Coordinate 2 := fun i => T131_0list.getD i.val (0,0,0,0,0)

theorem hfix131_0_2 : ∀ i, ((T131_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK131)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK131) :=
  repsFix_of_siftB2 rK131 ⟨0, by decide⟩ T131_0_2 (by decide)

theorem hinj131_0_2 : Function.Injective
    (fun i => ((T131_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK131)) :=
  repsInj_of_reduceAux2 rK131 T131_0_2 (by decide)

theorem hcardT131_0_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK131)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK131 ⟨0, by decide⟩ R131_2 hpxR131_2 hcardq131_2 (by decide)).symm

/-- **Cell (131, 0) twin (q=2).** -/
theorem cell131_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK131) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK131) (charOfVec2 rK131 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK131 e (h : Coordinate 2) T131_0_2 i :=
  species_entry_eq_sum rK131 ⟨0, by decide⟩ e heK h T131_0_2 hfix131_0_2 hinj131_0_2 hcardT131_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK131) (T131_0_2 i) (hfix131_0_2 i) h)

/-! ### Cell (131, 4) twin -/

def T131_4_2 : Fin 5 → Coordinate 2 := fun i => T131_4list.getD i.val (0,0,0,0,0)

theorem hfix131_4_2 : ∀ i, ((T131_4_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK131)
    ∈ fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK131) :=
  repsFix_of_siftB2 rK131 ⟨4, by decide⟩ T131_4_2 (by decide)

theorem hinj131_4_2 : Function.Injective
    (fun i => ((T131_4_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK131)) :=
  repsInj_of_reduceAux2 rK131 T131_4_2 (by decide)

theorem hcardT131_4_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK131)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK131 ⟨4, by decide⟩ R131_2 hpxR131_2 hcardq131_2 (by decide)).symm

/-- **Cell (131, 4) twin (q=2).** -/
theorem cell131_4_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK131) e = true)
    (h : ↥(reps (⟨4, by decide⟩ : Fin 148))) :
    species (reps (⟨4, by decide⟩ : Fin 148)) h (basisElt (reps rK131) (charOfVec2 rK131 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK131 e (h : Coordinate 2) T131_4_2 i :=
  species_entry_eq_sum rK131 ⟨4, by decide⟩ e heK h T131_4_2 hfix131_4_2 hinj131_4_2 hcardT131_4_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨4, by decide⟩) (reps rK131) (T131_4_2 i) (hfix131_4_2 i) h)

/-! ### Cell (131, 10) twin -/

def T131_10_2 : Fin 5 → Coordinate 2 := fun i => T131_10list.getD i.val (0,0,0,0,0)

theorem hfix131_10_2 : ∀ i, ((T131_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK131)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK131) :=
  repsFix_of_siftB2 rK131 ⟨10, by decide⟩ T131_10_2 (by decide)

theorem hinj131_10_2 : Function.Injective
    (fun i => ((T131_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK131)) :=
  repsInj_of_reduceAux2 rK131 T131_10_2 (by decide)

theorem hcardT131_10_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK131)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK131 ⟨10, by decide⟩ R131_2 hpxR131_2 hcardq131_2 (by decide)).symm

/-- **Cell (131, 10) twin (q=2).** -/
theorem cell131_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK131) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK131) (charOfVec2 rK131 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK131 e (h : Coordinate 2) T131_10_2 i :=
  species_entry_eq_sum rK131 ⟨10, by decide⟩ e heK h T131_10_2 hfix131_10_2 hinj131_10_2 hcardT131_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK131) (T131_10_2 i) (hfix131_10_2 i) h)

/-! ### Cell (131, 12) twin -/

def T131_12_2 : Fin 5 → Coordinate 2 := fun i => T131_12list.getD i.val (0,0,0,0,0)

theorem hfix131_12_2 : ∀ i, ((T131_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK131)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK131) :=
  repsFix_of_siftB2 rK131 ⟨12, by decide⟩ T131_12_2 (by decide)

theorem hinj131_12_2 : Function.Injective
    (fun i => ((T131_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK131)) :=
  repsInj_of_reduceAux2 rK131 T131_12_2 (by decide)

theorem hcardT131_12_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK131)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK131 ⟨12, by decide⟩ R131_2 hpxR131_2 hcardq131_2 (by decide)).symm

/-- **Cell (131, 12) twin (q=2).** -/
theorem cell131_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK131) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK131) (charOfVec2 rK131 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK131 e (h : Coordinate 2) T131_12_2 i :=
  species_entry_eq_sum rK131 ⟨12, by decide⟩ e heK h T131_12_2 hfix131_12_2 hinj131_12_2 hcardT131_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK131) (T131_12_2 i) (hfix131_12_2 i) h)

/-! ### Cell (131, 22) twin -/

def T131_22_2 : Fin 5 → Coordinate 2 := fun i => T131_22list.getD i.val (0,0,0,0,0)

theorem hfix131_22_2 : ∀ i, ((T131_22_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK131)
    ∈ fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK131) :=
  repsFix_of_siftB2 rK131 ⟨22, by decide⟩ T131_22_2 (by decide)

theorem hinj131_22_2 : Function.Injective
    (fun i => ((T131_22_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK131)) :=
  repsInj_of_reduceAux2 rK131 T131_22_2 (by decide)

theorem hcardT131_22_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK131)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK131 ⟨22, by decide⟩ R131_2 hpxR131_2 hcardq131_2 (by decide)).symm

/-- **Cell (131, 22) twin (q=2).** -/
theorem cell131_22_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK131) e = true)
    (h : ↥(reps (⟨22, by decide⟩ : Fin 148))) :
    species (reps (⟨22, by decide⟩ : Fin 148)) h (basisElt (reps rK131) (charOfVec2 rK131 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK131 e (h : Coordinate 2) T131_22_2 i :=
  species_entry_eq_sum rK131 ⟨22, by decide⟩ e heK h T131_22_2 hfix131_22_2 hinj131_22_2 hcardT131_22_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨22, by decide⟩) (reps rK131) (T131_22_2 i) (hfix131_22_2 i) h)

/-! ### Cell (131, 30) twin -/

def T131_30_2 : Fin 5 → Coordinate 2 := fun i => T131_30list.getD i.val (0,0,0,0,0)

theorem hfix131_30_2 : ∀ i, ((T131_30_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK131)
    ∈ fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK131) :=
  repsFix_of_siftB2 rK131 ⟨30, by decide⟩ T131_30_2 (by decide)

theorem hinj131_30_2 : Function.Injective
    (fun i => ((T131_30_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK131)) :=
  repsInj_of_reduceAux2 rK131 T131_30_2 (by decide)

theorem hcardT131_30_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK131)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK131 ⟨30, by decide⟩ R131_2 hpxR131_2 hcardq131_2 (by decide)).symm

/-- **Cell (131, 30) twin (q=2).** -/
theorem cell131_30_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK131) e = true)
    (h : ↥(reps (⟨30, by decide⟩ : Fin 148))) :
    species (reps (⟨30, by decide⟩ : Fin 148)) h (basisElt (reps rK131) (charOfVec2 rK131 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK131 e (h : Coordinate 2) T131_30_2 i :=
  species_entry_eq_sum rK131 ⟨30, by decide⟩ e heK h T131_30_2 hfix131_30_2 hinj131_30_2 hcardT131_30_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨30, by decide⟩) (reps rK131) (T131_30_2 i) (hfix131_30_2 i) h)

/-! ### Cell (131, 34) twin -/

def T131_34_2 : Fin 5 → Coordinate 2 := fun i => T131_34list.getD i.val (0,0,0,0,0)

theorem hfix131_34_2 : ∀ i, ((T131_34_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK131)
    ∈ fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK131) :=
  repsFix_of_siftB2 rK131 ⟨34, by decide⟩ T131_34_2 (by decide)

theorem hinj131_34_2 : Function.Injective
    (fun i => ((T131_34_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK131)) :=
  repsInj_of_reduceAux2 rK131 T131_34_2 (by decide)

theorem hcardT131_34_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK131)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK131 ⟨34, by decide⟩ R131_2 hpxR131_2 hcardq131_2 (by decide)).symm

/-- **Cell (131, 34) twin (q=2).** -/
theorem cell131_34_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK131) e = true)
    (h : ↥(reps (⟨34, by decide⟩ : Fin 148))) :
    species (reps (⟨34, by decide⟩ : Fin 148)) h (basisElt (reps rK131) (charOfVec2 rK131 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK131 e (h : Coordinate 2) T131_34_2 i :=
  species_entry_eq_sum rK131 ⟨34, by decide⟩ e heK h T131_34_2 hfix131_34_2 hinj131_34_2 hcardT131_34_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨34, by decide⟩) (reps rK131) (T131_34_2 i) (hfix131_34_2 i) h)

/-! ### Cell (131, 42) twin -/

def T131_42_2 : Fin 5 → Coordinate 2 := fun i => T131_42list.getD i.val (0,0,0,0,0)

theorem hfix131_42_2 : ∀ i, ((T131_42_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK131)
    ∈ fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK131) :=
  repsFix_of_siftB2 rK131 ⟨42, by decide⟩ T131_42_2 (by decide)

theorem hinj131_42_2 : Function.Injective
    (fun i => ((T131_42_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK131)) :=
  repsInj_of_reduceAux2 rK131 T131_42_2 (by decide)

theorem hcardT131_42_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK131)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK131 ⟨42, by decide⟩ R131_2 hpxR131_2 hcardq131_2 (by decide)).symm

/-- **Cell (131, 42) twin (q=2).** -/
theorem cell131_42_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK131) e = true)
    (h : ↥(reps (⟨42, by decide⟩ : Fin 148))) :
    species (reps (⟨42, by decide⟩ : Fin 148)) h (basisElt (reps rK131) (charOfVec2 rK131 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK131 e (h : Coordinate 2) T131_42_2 i :=
  species_entry_eq_sum rK131 ⟨42, by decide⟩ e heK h T131_42_2 hfix131_42_2 hinj131_42_2 hcardT131_42_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨42, by decide⟩) (reps rK131) (T131_42_2 i) (hfix131_42_2 i) h)

/-! ### Cell (131, 46) twin -/

def T131_46_2 : Fin 5 → Coordinate 2 := fun i => T131_46list.getD i.val (0,0,0,0,0)

theorem hfix131_46_2 : ∀ i, ((T131_46_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK131)
    ∈ fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK131) :=
  repsFix_of_siftB2 rK131 ⟨46, by decide⟩ T131_46_2 (by decide)

theorem hinj131_46_2 : Function.Injective
    (fun i => ((T131_46_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK131)) :=
  repsInj_of_reduceAux2 rK131 T131_46_2 (by decide)

theorem hcardT131_46_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK131)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK131 ⟨46, by decide⟩ R131_2 hpxR131_2 hcardq131_2 (by decide)).symm

/-- **Cell (131, 46) twin (q=2).** -/
theorem cell131_46_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK131) e = true)
    (h : ↥(reps (⟨46, by decide⟩ : Fin 148))) :
    species (reps (⟨46, by decide⟩ : Fin 148)) h (basisElt (reps rK131) (charOfVec2 rK131 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK131 e (h : Coordinate 2) T131_46_2 i :=
  species_entry_eq_sum rK131 ⟨46, by decide⟩ e heK h T131_46_2 hfix131_46_2 hinj131_46_2 hcardT131_46_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨46, by decide⟩) (reps rK131) (T131_46_2 i) (hfix131_46_2 i) h)

/-! ### Cell (131, 48) twin -/

def T131_48_2 : Fin 5 → Coordinate 2 := fun i => T131_48list.getD i.val (0,0,0,0,0)

theorem hfix131_48_2 : ∀ i, ((T131_48_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK131)
    ∈ fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK131) :=
  repsFix_of_siftB2 rK131 ⟨48, by decide⟩ T131_48_2 (by decide)

theorem hinj131_48_2 : Function.Injective
    (fun i => ((T131_48_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK131)) :=
  repsInj_of_reduceAux2 rK131 T131_48_2 (by decide)

theorem hcardT131_48_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK131)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK131 ⟨48, by decide⟩ R131_2 hpxR131_2 hcardq131_2 (by decide)).symm

/-- **Cell (131, 48) twin (q=2).** -/
theorem cell131_48_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK131) e = true)
    (h : ↥(reps (⟨48, by decide⟩ : Fin 148))) :
    species (reps (⟨48, by decide⟩ : Fin 148)) h (basisElt (reps rK131) (charOfVec2 rK131 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK131 e (h : Coordinate 2) T131_48_2 i :=
  species_entry_eq_sum rK131 ⟨48, by decide⟩ e heK h T131_48_2 hfix131_48_2 hinj131_48_2 hcardT131_48_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨48, by decide⟩) (reps rK131) (T131_48_2 i) (hfix131_48_2 i) h)

/-! ### Cell (131, 53) twin -/

def T131_53_2 : Fin 5 → Coordinate 2 := fun i => T131_53list.getD i.val (0,0,0,0,0)

theorem hfix131_53_2 : ∀ i, ((T131_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK131)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK131) :=
  repsFix_of_siftB2 rK131 ⟨53, by decide⟩ T131_53_2 (by decide)

theorem hinj131_53_2 : Function.Injective
    (fun i => ((T131_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK131)) :=
  repsInj_of_reduceAux2 rK131 T131_53_2 (by decide)

theorem hcardT131_53_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK131)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK131 ⟨53, by decide⟩ R131_2 hpxR131_2 hcardq131_2 (by decide)).symm

/-- **Cell (131, 53) twin (q=2).** -/
theorem cell131_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK131) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK131) (charOfVec2 rK131 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK131 e (h : Coordinate 2) T131_53_2 i :=
  species_entry_eq_sum rK131 ⟨53, by decide⟩ e heK h T131_53_2 hfix131_53_2 hinj131_53_2 hcardT131_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK131) (T131_53_2 i) (hfix131_53_2 i) h)

/-! ### Cell (131, 83) twin -/

def T131_83_2 : Fin 5 → Coordinate 2 := fun i => T131_83list.getD i.val (0,0,0,0,0)

theorem hfix131_83_2 : ∀ i, ((T131_83_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK131)
    ∈ fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK131) :=
  repsFix_of_siftB2 rK131 ⟨83, by decide⟩ T131_83_2 (by decide)

theorem hinj131_83_2 : Function.Injective
    (fun i => ((T131_83_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK131)) :=
  repsInj_of_reduceAux2 rK131 T131_83_2 (by decide)

theorem hcardT131_83_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK131)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK131 ⟨83, by decide⟩ R131_2 hpxR131_2 hcardq131_2 (by decide)).symm

/-- **Cell (131, 83) twin (q=2).** -/
theorem cell131_83_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK131) e = true)
    (h : ↥(reps (⟨83, by decide⟩ : Fin 148))) :
    species (reps (⟨83, by decide⟩ : Fin 148)) h (basisElt (reps rK131) (charOfVec2 rK131 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK131 e (h : Coordinate 2) T131_83_2 i :=
  species_entry_eq_sum rK131 ⟨83, by decide⟩ e heK h T131_83_2 hfix131_83_2 hinj131_83_2 hcardT131_83_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨83, by decide⟩) (reps rK131) (T131_83_2 i) (hfix131_83_2 i) h)

/-! ### Cell (131, 92) twin -/

def T131_92_2 : Fin 5 → Coordinate 2 := fun i => T131_92list.getD i.val (0,0,0,0,0)

theorem hfix131_92_2 : ∀ i, ((T131_92_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK131)
    ∈ fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK131) :=
  repsFix_of_siftB2 rK131 ⟨92, by decide⟩ T131_92_2 (by decide)

theorem hinj131_92_2 : Function.Injective
    (fun i => ((T131_92_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK131)) :=
  repsInj_of_reduceAux2 rK131 T131_92_2 (by decide)

theorem hcardT131_92_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK131)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK131 ⟨92, by decide⟩ R131_2 hpxR131_2 hcardq131_2 (by decide)).symm

/-- **Cell (131, 92) twin (q=2).** -/
theorem cell131_92_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK131) e = true)
    (h : ↥(reps (⟨92, by decide⟩ : Fin 148))) :
    species (reps (⟨92, by decide⟩ : Fin 148)) h (basisElt (reps rK131) (charOfVec2 rK131 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK131 e (h : Coordinate 2) T131_92_2 i :=
  species_entry_eq_sum rK131 ⟨92, by decide⟩ e heK h T131_92_2 hfix131_92_2 hinj131_92_2 hcardT131_92_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨92, by decide⟩) (reps rK131) (T131_92_2 i) (hfix131_92_2 i) h)

/-! ### Cell (131, 96) twin -/

def T131_96_2 : Fin 5 → Coordinate 2 := fun i => T131_96list.getD i.val (0,0,0,0,0)

theorem hfix131_96_2 : ∀ i, ((T131_96_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK131)
    ∈ fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK131) :=
  repsFix_of_siftB2 rK131 ⟨96, by decide⟩ T131_96_2 (by decide)

theorem hinj131_96_2 : Function.Injective
    (fun i => ((T131_96_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK131)) :=
  repsInj_of_reduceAux2 rK131 T131_96_2 (by decide)

theorem hcardT131_96_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK131)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK131 ⟨96, by decide⟩ R131_2 hpxR131_2 hcardq131_2 (by decide)).symm

/-- **Cell (131, 96) twin (q=2).** -/
theorem cell131_96_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK131) e = true)
    (h : ↥(reps (⟨96, by decide⟩ : Fin 148))) :
    species (reps (⟨96, by decide⟩ : Fin 148)) h (basisElt (reps rK131) (charOfVec2 rK131 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK131 e (h : Coordinate 2) T131_96_2 i :=
  species_entry_eq_sum rK131 ⟨96, by decide⟩ e heK h T131_96_2 hfix131_96_2 hinj131_96_2 hcardT131_96_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨96, by decide⟩) (reps rK131) (T131_96_2 i) (hfix131_96_2 i) h)

/-! ### Cell (131, 104) twin -/

def T131_104_2 : Fin 5 → Coordinate 2 := fun i => T131_104list.getD i.val (0,0,0,0,0)

theorem hfix131_104_2 : ∀ i, ((T131_104_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK131)
    ∈ fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK131) :=
  repsFix_of_siftB2 rK131 ⟨104, by decide⟩ T131_104_2 (by decide)

theorem hinj131_104_2 : Function.Injective
    (fun i => ((T131_104_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK131)) :=
  repsInj_of_reduceAux2 rK131 T131_104_2 (by decide)

theorem hcardT131_104_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK131)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK131 ⟨104, by decide⟩ R131_2 hpxR131_2 hcardq131_2 (by decide)).symm

/-- **Cell (131, 104) twin (q=2).** -/
theorem cell131_104_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK131) e = true)
    (h : ↥(reps (⟨104, by decide⟩ : Fin 148))) :
    species (reps (⟨104, by decide⟩ : Fin 148)) h (basisElt (reps rK131) (charOfVec2 rK131 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK131 e (h : Coordinate 2) T131_104_2 i :=
  species_entry_eq_sum rK131 ⟨104, by decide⟩ e heK h T131_104_2 hfix131_104_2 hinj131_104_2 hcardT131_104_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨104, by decide⟩) (reps rK131) (T131_104_2 i) (hfix131_104_2 i) h)

/-! ### Cell (131, 108) twin -/

def T131_108_2 : Fin 5 → Coordinate 2 := fun i => T131_108list.getD i.val (0,0,0,0,0)

theorem hfix131_108_2 : ∀ i, ((T131_108_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK131)
    ∈ fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK131) :=
  repsFix_of_siftB2 rK131 ⟨108, by decide⟩ T131_108_2 (by decide)

theorem hinj131_108_2 : Function.Injective
    (fun i => ((T131_108_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK131)) :=
  repsInj_of_reduceAux2 rK131 T131_108_2 (by decide)

theorem hcardT131_108_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK131)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK131 ⟨108, by decide⟩ R131_2 hpxR131_2 hcardq131_2 (by decide)).symm

/-- **Cell (131, 108) twin (q=2).** -/
theorem cell131_108_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK131) e = true)
    (h : ↥(reps (⟨108, by decide⟩ : Fin 148))) :
    species (reps (⟨108, by decide⟩ : Fin 148)) h (basisElt (reps rK131) (charOfVec2 rK131 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK131 e (h : Coordinate 2) T131_108_2 i :=
  species_entry_eq_sum rK131 ⟨108, by decide⟩ e heK h T131_108_2 hfix131_108_2 hinj131_108_2 hcardT131_108_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨108, by decide⟩) (reps rK131) (T131_108_2 i) (hfix131_108_2 i) h)

/-! ### Cell (131, 110) twin -/

def T131_110_2 : Fin 5 → Coordinate 2 := fun i => T131_110list.getD i.val (0,0,0,0,0)

theorem hfix131_110_2 : ∀ i, ((T131_110_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK131)
    ∈ fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK131) :=
  repsFix_of_siftB2 rK131 ⟨110, by decide⟩ T131_110_2 (by decide)

theorem hinj131_110_2 : Function.Injective
    (fun i => ((T131_110_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK131)) :=
  repsInj_of_reduceAux2 rK131 T131_110_2 (by decide)

theorem hcardT131_110_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK131)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK131 ⟨110, by decide⟩ R131_2 hpxR131_2 hcardq131_2 (by decide)).symm

/-- **Cell (131, 110) twin (q=2).** -/
theorem cell131_110_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK131) e = true)
    (h : ↥(reps (⟨110, by decide⟩ : Fin 148))) :
    species (reps (⟨110, by decide⟩ : Fin 148)) h (basisElt (reps rK131) (charOfVec2 rK131 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK131 e (h : Coordinate 2) T131_110_2 i :=
  species_entry_eq_sum rK131 ⟨110, by decide⟩ e heK h T131_110_2 hfix131_110_2 hinj131_110_2 hcardT131_110_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨110, by decide⟩) (reps rK131) (T131_110_2 i) (hfix131_110_2 i) h)

/-! ### Cell (131, 131) twin -/

def T131_131_2 : Fin 5 → Coordinate 2 := fun i => T131_131list.getD i.val (0,0,0,0,0)

theorem hfix131_131_2 : ∀ i, ((T131_131_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK131)
    ∈ fixedPoints (reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK131) :=
  repsFix_of_siftB2 rK131 ⟨131, by decide⟩ T131_131_2 (by decide)

theorem hinj131_131_2 : Function.Injective
    (fun i => ((T131_131_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK131)) :=
  repsInj_of_reduceAux2 rK131 T131_131_2 (by decide)

theorem hcardT131_131_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK131)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK131 ⟨131, by decide⟩ R131_2 hpxR131_2 hcardq131_2 (by decide)).symm

/-- **Cell (131, 131) twin (q=2).** -/
theorem cell131_131_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK131) e = true)
    (h : ↥(reps (⟨131, by decide⟩ : Fin 148))) :
    species (reps (⟨131, by decide⟩ : Fin 148)) h (basisElt (reps rK131) (charOfVec2 rK131 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK131 e (h : Coordinate 2) T131_131_2 i :=
  species_entry_eq_sum rK131 ⟨131, by decide⟩ e heK h T131_131_2 hfix131_131_2 hinj131_131_2 hcardT131_131_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨131, by decide⟩) (reps rK131) (T131_131_2 i) (hfix131_131_2 i) h)

end Q2

end LeanDring.P5Presentation
