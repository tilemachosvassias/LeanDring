/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, K-strata data (5^4 stratum, rK 140-140): certified per-cell species-entry instantiations, both
twins.

Covers K-classes 140 (order-5^4 K, |R|=5).  For each nonzero `H`-column
(`(G/K)^H ≠ ∅`), the full coset transversal `R140..` and each `H`-fixed
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

/-! # K-class rK = 140  (|G/K| = 5) -/

def rK140 : Fin 148 := ⟨140, by decide⟩

def R140list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def R140 : Fin 5 → Coordinate 1 := fun i => R140list.getD i.val (0,0,0,0,0)

theorem hpxR140 : Function.Injective (fun i => reduceAux 1 (basisAt rK140) (R140 i)) := by decide
theorem hcardq140 : Nat.card (Coordinate 1 ⧸ reps rK140) = 5 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (140, 0): |T| = 5 -/

def T140_0list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T140_0 : Fin 5 → Coordinate 1 := fun i => T140_0list.getD i.val (0,0,0,0,0)

theorem hfix140_0 : ∀ i, ((T140_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK140)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140) :=
  repsFix_of_siftB rK140 ⟨0, by decide⟩ T140_0 (by decide)

theorem hinj140_0 : Function.Injective
    (fun i => ((T140_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK140)) :=
  repsInj_of_reduceAux rK140 T140_0 (by decide)

theorem hcardT140_0 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK140 ⟨0, by decide⟩ R140 hpxR140 hcardq140 (by decide)).symm

/-- **Cell (140, 0).** -/
theorem cell140_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK140) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK140) (charOfVec rK140 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK140 e (h : Coordinate 1) T140_0 i :=
  species_entry_eq_sum rK140 ⟨0, by decide⟩ e heK h T140_0 hfix140_0 hinj140_0 hcardT140_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK140) (T140_0 i) (hfix140_0 i) h)

/-! ## Cell (140, 5): |T| = 5 -/

def T140_5list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T140_5 : Fin 5 → Coordinate 1 := fun i => T140_5list.getD i.val (0,0,0,0,0)

theorem hfix140_5 : ∀ i, ((T140_5 i : Coordinate 1) : Coordinate 1 ⧸ reps rK140)
    ∈ fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140) :=
  repsFix_of_siftB rK140 ⟨5, by decide⟩ T140_5 (by decide)

theorem hinj140_5 : Function.Injective
    (fun i => ((T140_5 i : Coordinate 1) : Coordinate 1 ⧸ reps rK140)) :=
  repsInj_of_reduceAux rK140 T140_5 (by decide)

theorem hcardT140_5 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK140 ⟨5, by decide⟩ R140 hpxR140 hcardq140 (by decide)).symm

/-- **Cell (140, 5).** -/
theorem cell140_5 (e : List (ZMod 25)) (heK : charOK (basisAt rK140) e = true)
    (h : ↥(reps (⟨5, by decide⟩ : Fin 148))) :
    species (reps (⟨5, by decide⟩ : Fin 148)) h (basisElt (reps rK140) (charOfVec rK140 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK140 e (h : Coordinate 1) T140_5 i :=
  species_entry_eq_sum rK140 ⟨5, by decide⟩ e heK h T140_5 hfix140_5 hinj140_5 hcardT140_5
    (fun i => conj_mem_of_fixedPoints (reps ⟨5, by decide⟩) (reps rK140) (T140_5 i) (hfix140_5 i) h)

/-! ## Cell (140, 10): |T| = 5 -/

def T140_10list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T140_10 : Fin 5 → Coordinate 1 := fun i => T140_10list.getD i.val (0,0,0,0,0)

theorem hfix140_10 : ∀ i, ((T140_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK140)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140) :=
  repsFix_of_siftB rK140 ⟨10, by decide⟩ T140_10 (by decide)

theorem hinj140_10 : Function.Injective
    (fun i => ((T140_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK140)) :=
  repsInj_of_reduceAux rK140 T140_10 (by decide)

theorem hcardT140_10 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK140 ⟨10, by decide⟩ R140 hpxR140 hcardq140 (by decide)).symm

/-- **Cell (140, 10).** -/
theorem cell140_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK140) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK140) (charOfVec rK140 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK140 e (h : Coordinate 1) T140_10 i :=
  species_entry_eq_sum rK140 ⟨10, by decide⟩ e heK h T140_10 hfix140_10 hinj140_10 hcardT140_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK140) (T140_10 i) (hfix140_10 i) h)

/-! ## Cell (140, 12): |T| = 5 -/

def T140_12list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T140_12 : Fin 5 → Coordinate 1 := fun i => T140_12list.getD i.val (0,0,0,0,0)

theorem hfix140_12 : ∀ i, ((T140_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK140)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140) :=
  repsFix_of_siftB rK140 ⟨12, by decide⟩ T140_12 (by decide)

theorem hinj140_12 : Function.Injective
    (fun i => ((T140_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK140)) :=
  repsInj_of_reduceAux rK140 T140_12 (by decide)

theorem hcardT140_12 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK140 ⟨12, by decide⟩ R140 hpxR140 hcardq140 (by decide)).symm

/-- **Cell (140, 12).** -/
theorem cell140_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK140) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK140) (charOfVec rK140 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK140 e (h : Coordinate 1) T140_12 i :=
  species_entry_eq_sum rK140 ⟨12, by decide⟩ e heK h T140_12 hfix140_12 hinj140_12 hcardT140_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK140) (T140_12 i) (hfix140_12 i) h)

/-! ## Cell (140, 23): |T| = 5 -/

def T140_23list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T140_23 : Fin 5 → Coordinate 1 := fun i => T140_23list.getD i.val (0,0,0,0,0)

theorem hfix140_23 : ∀ i, ((T140_23 i : Coordinate 1) : Coordinate 1 ⧸ reps rK140)
    ∈ fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140) :=
  repsFix_of_siftB rK140 ⟨23, by decide⟩ T140_23 (by decide)

theorem hinj140_23 : Function.Injective
    (fun i => ((T140_23 i : Coordinate 1) : Coordinate 1 ⧸ reps rK140)) :=
  repsInj_of_reduceAux rK140 T140_23 (by decide)

theorem hcardT140_23 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK140 ⟨23, by decide⟩ R140 hpxR140 hcardq140 (by decide)).symm

/-- **Cell (140, 23).** -/
theorem cell140_23 (e : List (ZMod 25)) (heK : charOK (basisAt rK140) e = true)
    (h : ↥(reps (⟨23, by decide⟩ : Fin 148))) :
    species (reps (⟨23, by decide⟩ : Fin 148)) h (basisElt (reps rK140) (charOfVec rK140 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK140 e (h : Coordinate 1) T140_23 i :=
  species_entry_eq_sum rK140 ⟨23, by decide⟩ e heK h T140_23 hfix140_23 hinj140_23 hcardT140_23
    (fun i => conj_mem_of_fixedPoints (reps ⟨23, by decide⟩) (reps rK140) (T140_23 i) (hfix140_23 i) h)

/-! ## Cell (140, 28): |T| = 5 -/

def T140_28list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T140_28 : Fin 5 → Coordinate 1 := fun i => T140_28list.getD i.val (0,0,0,0,0)

theorem hfix140_28 : ∀ i, ((T140_28 i : Coordinate 1) : Coordinate 1 ⧸ reps rK140)
    ∈ fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140) :=
  repsFix_of_siftB rK140 ⟨28, by decide⟩ T140_28 (by decide)

theorem hinj140_28 : Function.Injective
    (fun i => ((T140_28 i : Coordinate 1) : Coordinate 1 ⧸ reps rK140)) :=
  repsInj_of_reduceAux rK140 T140_28 (by decide)

theorem hcardT140_28 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK140 ⟨28, by decide⟩ R140 hpxR140 hcardq140 (by decide)).symm

/-- **Cell (140, 28).** -/
theorem cell140_28 (e : List (ZMod 25)) (heK : charOK (basisAt rK140) e = true)
    (h : ↥(reps (⟨28, by decide⟩ : Fin 148))) :
    species (reps (⟨28, by decide⟩ : Fin 148)) h (basisElt (reps rK140) (charOfVec rK140 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK140 e (h : Coordinate 1) T140_28 i :=
  species_entry_eq_sum rK140 ⟨28, by decide⟩ e heK h T140_28 hfix140_28 hinj140_28 hcardT140_28
    (fun i => conj_mem_of_fixedPoints (reps ⟨28, by decide⟩) (reps rK140) (T140_28 i) (hfix140_28 i) h)

/-! ## Cell (140, 35): |T| = 5 -/

def T140_35list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T140_35 : Fin 5 → Coordinate 1 := fun i => T140_35list.getD i.val (0,0,0,0,0)

theorem hfix140_35 : ∀ i, ((T140_35 i : Coordinate 1) : Coordinate 1 ⧸ reps rK140)
    ∈ fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140) :=
  repsFix_of_siftB rK140 ⟨35, by decide⟩ T140_35 (by decide)

theorem hinj140_35 : Function.Injective
    (fun i => ((T140_35 i : Coordinate 1) : Coordinate 1 ⧸ reps rK140)) :=
  repsInj_of_reduceAux rK140 T140_35 (by decide)

theorem hcardT140_35 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK140 ⟨35, by decide⟩ R140 hpxR140 hcardq140 (by decide)).symm

/-- **Cell (140, 35).** -/
theorem cell140_35 (e : List (ZMod 25)) (heK : charOK (basisAt rK140) e = true)
    (h : ↥(reps (⟨35, by decide⟩ : Fin 148))) :
    species (reps (⟨35, by decide⟩ : Fin 148)) h (basisElt (reps rK140) (charOfVec rK140 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK140 e (h : Coordinate 1) T140_35 i :=
  species_entry_eq_sum rK140 ⟨35, by decide⟩ e heK h T140_35 hfix140_35 hinj140_35 hcardT140_35
    (fun i => conj_mem_of_fixedPoints (reps ⟨35, by decide⟩) (reps rK140) (T140_35 i) (hfix140_35 i) h)

/-! ## Cell (140, 39): |T| = 5 -/

def T140_39list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T140_39 : Fin 5 → Coordinate 1 := fun i => T140_39list.getD i.val (0,0,0,0,0)

theorem hfix140_39 : ∀ i, ((T140_39 i : Coordinate 1) : Coordinate 1 ⧸ reps rK140)
    ∈ fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140) :=
  repsFix_of_siftB rK140 ⟨39, by decide⟩ T140_39 (by decide)

theorem hinj140_39 : Function.Injective
    (fun i => ((T140_39 i : Coordinate 1) : Coordinate 1 ⧸ reps rK140)) :=
  repsInj_of_reduceAux rK140 T140_39 (by decide)

theorem hcardT140_39 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK140 ⟨39, by decide⟩ R140 hpxR140 hcardq140 (by decide)).symm

/-- **Cell (140, 39).** -/
theorem cell140_39 (e : List (ZMod 25)) (heK : charOK (basisAt rK140) e = true)
    (h : ↥(reps (⟨39, by decide⟩ : Fin 148))) :
    species (reps (⟨39, by decide⟩ : Fin 148)) h (basisElt (reps rK140) (charOfVec rK140 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK140 e (h : Coordinate 1) T140_39 i :=
  species_entry_eq_sum rK140 ⟨39, by decide⟩ e heK h T140_39 hfix140_39 hinj140_39 hcardT140_39
    (fun i => conj_mem_of_fixedPoints (reps ⟨39, by decide⟩) (reps rK140) (T140_39 i) (hfix140_39 i) h)

/-! ## Cell (140, 46): |T| = 5 -/

def T140_46list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T140_46 : Fin 5 → Coordinate 1 := fun i => T140_46list.getD i.val (0,0,0,0,0)

theorem hfix140_46 : ∀ i, ((T140_46 i : Coordinate 1) : Coordinate 1 ⧸ reps rK140)
    ∈ fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140) :=
  repsFix_of_siftB rK140 ⟨46, by decide⟩ T140_46 (by decide)

theorem hinj140_46 : Function.Injective
    (fun i => ((T140_46 i : Coordinate 1) : Coordinate 1 ⧸ reps rK140)) :=
  repsInj_of_reduceAux rK140 T140_46 (by decide)

theorem hcardT140_46 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK140 ⟨46, by decide⟩ R140 hpxR140 hcardq140 (by decide)).symm

/-- **Cell (140, 46).** -/
theorem cell140_46 (e : List (ZMod 25)) (heK : charOK (basisAt rK140) e = true)
    (h : ↥(reps (⟨46, by decide⟩ : Fin 148))) :
    species (reps (⟨46, by decide⟩ : Fin 148)) h (basisElt (reps rK140) (charOfVec rK140 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK140 e (h : Coordinate 1) T140_46 i :=
  species_entry_eq_sum rK140 ⟨46, by decide⟩ e heK h T140_46 hfix140_46 hinj140_46 hcardT140_46
    (fun i => conj_mem_of_fixedPoints (reps ⟨46, by decide⟩) (reps rK140) (T140_46 i) (hfix140_46 i) h)

/-! ## Cell (140, 52): |T| = 5 -/

def T140_52list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T140_52 : Fin 5 → Coordinate 1 := fun i => T140_52list.getD i.val (0,0,0,0,0)

theorem hfix140_52 : ∀ i, ((T140_52 i : Coordinate 1) : Coordinate 1 ⧸ reps rK140)
    ∈ fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140) :=
  repsFix_of_siftB rK140 ⟨52, by decide⟩ T140_52 (by decide)

theorem hinj140_52 : Function.Injective
    (fun i => ((T140_52 i : Coordinate 1) : Coordinate 1 ⧸ reps rK140)) :=
  repsInj_of_reduceAux rK140 T140_52 (by decide)

theorem hcardT140_52 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK140 ⟨52, by decide⟩ R140 hpxR140 hcardq140 (by decide)).symm

/-- **Cell (140, 52).** -/
theorem cell140_52 (e : List (ZMod 25)) (heK : charOK (basisAt rK140) e = true)
    (h : ↥(reps (⟨52, by decide⟩ : Fin 148))) :
    species (reps (⟨52, by decide⟩ : Fin 148)) h (basisElt (reps rK140) (charOfVec rK140 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK140 e (h : Coordinate 1) T140_52 i :=
  species_entry_eq_sum rK140 ⟨52, by decide⟩ e heK h T140_52 hfix140_52 hinj140_52 hcardT140_52
    (fun i => conj_mem_of_fixedPoints (reps ⟨52, by decide⟩) (reps rK140) (T140_52 i) (hfix140_52 i) h)

/-! ## Cell (140, 53): |T| = 5 -/

def T140_53list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T140_53 : Fin 5 → Coordinate 1 := fun i => T140_53list.getD i.val (0,0,0,0,0)

theorem hfix140_53 : ∀ i, ((T140_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK140)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140) :=
  repsFix_of_siftB rK140 ⟨53, by decide⟩ T140_53 (by decide)

theorem hinj140_53 : Function.Injective
    (fun i => ((T140_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK140)) :=
  repsInj_of_reduceAux rK140 T140_53 (by decide)

theorem hcardT140_53 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK140 ⟨53, by decide⟩ R140 hpxR140 hcardq140 (by decide)).symm

/-- **Cell (140, 53).** -/
theorem cell140_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK140) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK140) (charOfVec rK140 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK140 e (h : Coordinate 1) T140_53 i :=
  species_entry_eq_sum rK140 ⟨53, by decide⟩ e heK h T140_53 hfix140_53 hinj140_53 hcardT140_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK140) (T140_53 i) (hfix140_53 i) h)

/-! ## Cell (140, 84): |T| = 5 -/

def T140_84list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T140_84 : Fin 5 → Coordinate 1 := fun i => T140_84list.getD i.val (0,0,0,0,0)

theorem hfix140_84 : ∀ i, ((T140_84 i : Coordinate 1) : Coordinate 1 ⧸ reps rK140)
    ∈ fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140) :=
  repsFix_of_siftB rK140 ⟨84, by decide⟩ T140_84 (by decide)

theorem hinj140_84 : Function.Injective
    (fun i => ((T140_84 i : Coordinate 1) : Coordinate 1 ⧸ reps rK140)) :=
  repsInj_of_reduceAux rK140 T140_84 (by decide)

theorem hcardT140_84 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK140 ⟨84, by decide⟩ R140 hpxR140 hcardq140 (by decide)).symm

/-- **Cell (140, 84).** -/
theorem cell140_84 (e : List (ZMod 25)) (heK : charOK (basisAt rK140) e = true)
    (h : ↥(reps (⟨84, by decide⟩ : Fin 148))) :
    species (reps (⟨84, by decide⟩ : Fin 148)) h (basisElt (reps rK140) (charOfVec rK140 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK140 e (h : Coordinate 1) T140_84 i :=
  species_entry_eq_sum rK140 ⟨84, by decide⟩ e heK h T140_84 hfix140_84 hinj140_84 hcardT140_84
    (fun i => conj_mem_of_fixedPoints (reps ⟨84, by decide⟩) (reps rK140) (T140_84 i) (hfix140_84 i) h)

/-! ## Cell (140, 90): |T| = 5 -/

def T140_90list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T140_90 : Fin 5 → Coordinate 1 := fun i => T140_90list.getD i.val (0,0,0,0,0)

theorem hfix140_90 : ∀ i, ((T140_90 i : Coordinate 1) : Coordinate 1 ⧸ reps rK140)
    ∈ fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140) :=
  repsFix_of_siftB rK140 ⟨90, by decide⟩ T140_90 (by decide)

theorem hinj140_90 : Function.Injective
    (fun i => ((T140_90 i : Coordinate 1) : Coordinate 1 ⧸ reps rK140)) :=
  repsInj_of_reduceAux rK140 T140_90 (by decide)

theorem hcardT140_90 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK140 ⟨90, by decide⟩ R140 hpxR140 hcardq140 (by decide)).symm

/-- **Cell (140, 90).** -/
theorem cell140_90 (e : List (ZMod 25)) (heK : charOK (basisAt rK140) e = true)
    (h : ↥(reps (⟨90, by decide⟩ : Fin 148))) :
    species (reps (⟨90, by decide⟩ : Fin 148)) h (basisElt (reps rK140) (charOfVec rK140 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK140 e (h : Coordinate 1) T140_90 i :=
  species_entry_eq_sum rK140 ⟨90, by decide⟩ e heK h T140_90 hfix140_90 hinj140_90 hcardT140_90
    (fun i => conj_mem_of_fixedPoints (reps ⟨90, by decide⟩) (reps rK140) (T140_90 i) (hfix140_90 i) h)

/-! ## Cell (140, 97): |T| = 5 -/

def T140_97list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T140_97 : Fin 5 → Coordinate 1 := fun i => T140_97list.getD i.val (0,0,0,0,0)

theorem hfix140_97 : ∀ i, ((T140_97 i : Coordinate 1) : Coordinate 1 ⧸ reps rK140)
    ∈ fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140) :=
  repsFix_of_siftB rK140 ⟨97, by decide⟩ T140_97 (by decide)

theorem hinj140_97 : Function.Injective
    (fun i => ((T140_97 i : Coordinate 1) : Coordinate 1 ⧸ reps rK140)) :=
  repsInj_of_reduceAux rK140 T140_97 (by decide)

theorem hcardT140_97 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK140 ⟨97, by decide⟩ R140 hpxR140 hcardq140 (by decide)).symm

/-- **Cell (140, 97).** -/
theorem cell140_97 (e : List (ZMod 25)) (heK : charOK (basisAt rK140) e = true)
    (h : ↥(reps (⟨97, by decide⟩ : Fin 148))) :
    species (reps (⟨97, by decide⟩ : Fin 148)) h (basisElt (reps rK140) (charOfVec rK140 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK140 e (h : Coordinate 1) T140_97 i :=
  species_entry_eq_sum rK140 ⟨97, by decide⟩ e heK h T140_97 hfix140_97 hinj140_97 hcardT140_97
    (fun i => conj_mem_of_fixedPoints (reps ⟨97, by decide⟩) (reps rK140) (T140_97 i) (hfix140_97 i) h)

/-! ## Cell (140, 101): |T| = 5 -/

def T140_101list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T140_101 : Fin 5 → Coordinate 1 := fun i => T140_101list.getD i.val (0,0,0,0,0)

theorem hfix140_101 : ∀ i, ((T140_101 i : Coordinate 1) : Coordinate 1 ⧸ reps rK140)
    ∈ fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140) :=
  repsFix_of_siftB rK140 ⟨101, by decide⟩ T140_101 (by decide)

theorem hinj140_101 : Function.Injective
    (fun i => ((T140_101 i : Coordinate 1) : Coordinate 1 ⧸ reps rK140)) :=
  repsInj_of_reduceAux rK140 T140_101 (by decide)

theorem hcardT140_101 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK140 ⟨101, by decide⟩ R140 hpxR140 hcardq140 (by decide)).symm

/-- **Cell (140, 101).** -/
theorem cell140_101 (e : List (ZMod 25)) (heK : charOK (basisAt rK140) e = true)
    (h : ↥(reps (⟨101, by decide⟩ : Fin 148))) :
    species (reps (⟨101, by decide⟩ : Fin 148)) h (basisElt (reps rK140) (charOfVec rK140 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK140 e (h : Coordinate 1) T140_101 i :=
  species_entry_eq_sum rK140 ⟨101, by decide⟩ e heK h T140_101 hfix140_101 hinj140_101 hcardT140_101
    (fun i => conj_mem_of_fixedPoints (reps ⟨101, by decide⟩) (reps rK140) (T140_101 i) (hfix140_101 i) h)

/-! ## Cell (140, 108): |T| = 5 -/

def T140_108list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T140_108 : Fin 5 → Coordinate 1 := fun i => T140_108list.getD i.val (0,0,0,0,0)

theorem hfix140_108 : ∀ i, ((T140_108 i : Coordinate 1) : Coordinate 1 ⧸ reps rK140)
    ∈ fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140) :=
  repsFix_of_siftB rK140 ⟨108, by decide⟩ T140_108 (by decide)

theorem hinj140_108 : Function.Injective
    (fun i => ((T140_108 i : Coordinate 1) : Coordinate 1 ⧸ reps rK140)) :=
  repsInj_of_reduceAux rK140 T140_108 (by decide)

theorem hcardT140_108 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK140 ⟨108, by decide⟩ R140 hpxR140 hcardq140 (by decide)).symm

/-- **Cell (140, 108).** -/
theorem cell140_108 (e : List (ZMod 25)) (heK : charOK (basisAt rK140) e = true)
    (h : ↥(reps (⟨108, by decide⟩ : Fin 148))) :
    species (reps (⟨108, by decide⟩ : Fin 148)) h (basisElt (reps rK140) (charOfVec rK140 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK140 e (h : Coordinate 1) T140_108 i :=
  species_entry_eq_sum rK140 ⟨108, by decide⟩ e heK h T140_108 hfix140_108 hinj140_108 hcardT140_108
    (fun i => conj_mem_of_fixedPoints (reps ⟨108, by decide⟩) (reps rK140) (T140_108 i) (hfix140_108 i) h)

/-! ## Cell (140, 114): |T| = 5 -/

def T140_114list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T140_114 : Fin 5 → Coordinate 1 := fun i => T140_114list.getD i.val (0,0,0,0,0)

theorem hfix140_114 : ∀ i, ((T140_114 i : Coordinate 1) : Coordinate 1 ⧸ reps rK140)
    ∈ fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140) :=
  repsFix_of_siftB rK140 ⟨114, by decide⟩ T140_114 (by decide)

theorem hinj140_114 : Function.Injective
    (fun i => ((T140_114 i : Coordinate 1) : Coordinate 1 ⧸ reps rK140)) :=
  repsInj_of_reduceAux rK140 T140_114 (by decide)

theorem hcardT140_114 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK140 ⟨114, by decide⟩ R140 hpxR140 hcardq140 (by decide)).symm

/-- **Cell (140, 114).** -/
theorem cell140_114 (e : List (ZMod 25)) (heK : charOK (basisAt rK140) e = true)
    (h : ↥(reps (⟨114, by decide⟩ : Fin 148))) :
    species (reps (⟨114, by decide⟩ : Fin 148)) h (basisElt (reps rK140) (charOfVec rK140 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK140 e (h : Coordinate 1) T140_114 i :=
  species_entry_eq_sum rK140 ⟨114, by decide⟩ e heK h T140_114 hfix140_114 hinj140_114 hcardT140_114
    (fun i => conj_mem_of_fixedPoints (reps ⟨114, by decide⟩) (reps rK140) (T140_114 i) (hfix140_114 i) h)

/-! ## Cell (140, 140): |T| = 5 -/

def T140_140list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T140_140 : Fin 5 → Coordinate 1 := fun i => T140_140list.getD i.val (0,0,0,0,0)

theorem hfix140_140 : ∀ i, ((T140_140 i : Coordinate 1) : Coordinate 1 ⧸ reps rK140)
    ∈ fixedPoints (reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140) :=
  repsFix_of_siftB rK140 ⟨140, by decide⟩ T140_140 (by decide)

theorem hinj140_140 : Function.Injective
    (fun i => ((T140_140 i : Coordinate 1) : Coordinate 1 ⧸ reps rK140)) :=
  repsInj_of_reduceAux rK140 T140_140 (by decide)

theorem hcardT140_140 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK140 ⟨140, by decide⟩ R140 hpxR140 hcardq140 (by decide)).symm

/-- **Cell (140, 140).** -/
theorem cell140_140 (e : List (ZMod 25)) (heK : charOK (basisAt rK140) e = true)
    (h : ↥(reps (⟨140, by decide⟩ : Fin 148))) :
    species (reps (⟨140, by decide⟩ : Fin 148)) h (basisElt (reps rK140) (charOfVec rK140 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK140 e (h : Coordinate 1) T140_140 i :=
  species_entry_eq_sum rK140 ⟨140, by decide⟩ e heK h T140_140 hfix140_140 hinj140_140 hcardT140_140
    (fun i => conj_mem_of_fixedPoints (reps ⟨140, by decide⟩) (reps rK140) (T140_140 i) (hfix140_140 i) h)

namespace Q2

def R140_2 : Fin 5 → Coordinate 2 := fun i => R140list.getD i.val (0,0,0,0,0)
theorem hpxR140_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK140) (R140_2 i)) := by decide
theorem hcardq140_2 : Nat.card (Coordinate 2 ⧸ reps rK140) = 5 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (140, 0) twin -/

def T140_0_2 : Fin 5 → Coordinate 2 := fun i => T140_0list.getD i.val (0,0,0,0,0)

theorem hfix140_0_2 : ∀ i, ((T140_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK140)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK140) :=
  repsFix_of_siftB2 rK140 ⟨0, by decide⟩ T140_0_2 (by decide)

theorem hinj140_0_2 : Function.Injective
    (fun i => ((T140_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK140)) :=
  repsInj_of_reduceAux2 rK140 T140_0_2 (by decide)

theorem hcardT140_0_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK140)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK140 ⟨0, by decide⟩ R140_2 hpxR140_2 hcardq140_2 (by decide)).symm

/-- **Cell (140, 0) twin (q=2).** -/
theorem cell140_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK140) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK140) (charOfVec2 rK140 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK140 e (h : Coordinate 2) T140_0_2 i :=
  species_entry_eq_sum rK140 ⟨0, by decide⟩ e heK h T140_0_2 hfix140_0_2 hinj140_0_2 hcardT140_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK140) (T140_0_2 i) (hfix140_0_2 i) h)

/-! ### Cell (140, 5) twin -/

def T140_5_2 : Fin 5 → Coordinate 2 := fun i => T140_5list.getD i.val (0,0,0,0,0)

theorem hfix140_5_2 : ∀ i, ((T140_5_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK140)
    ∈ fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK140) :=
  repsFix_of_siftB2 rK140 ⟨5, by decide⟩ T140_5_2 (by decide)

theorem hinj140_5_2 : Function.Injective
    (fun i => ((T140_5_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK140)) :=
  repsInj_of_reduceAux2 rK140 T140_5_2 (by decide)

theorem hcardT140_5_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK140)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK140 ⟨5, by decide⟩ R140_2 hpxR140_2 hcardq140_2 (by decide)).symm

/-- **Cell (140, 5) twin (q=2).** -/
theorem cell140_5_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK140) e = true)
    (h : ↥(reps (⟨5, by decide⟩ : Fin 148))) :
    species (reps (⟨5, by decide⟩ : Fin 148)) h (basisElt (reps rK140) (charOfVec2 rK140 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK140 e (h : Coordinate 2) T140_5_2 i :=
  species_entry_eq_sum rK140 ⟨5, by decide⟩ e heK h T140_5_2 hfix140_5_2 hinj140_5_2 hcardT140_5_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨5, by decide⟩) (reps rK140) (T140_5_2 i) (hfix140_5_2 i) h)

/-! ### Cell (140, 10) twin -/

def T140_10_2 : Fin 5 → Coordinate 2 := fun i => T140_10list.getD i.val (0,0,0,0,0)

theorem hfix140_10_2 : ∀ i, ((T140_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK140)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK140) :=
  repsFix_of_siftB2 rK140 ⟨10, by decide⟩ T140_10_2 (by decide)

theorem hinj140_10_2 : Function.Injective
    (fun i => ((T140_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK140)) :=
  repsInj_of_reduceAux2 rK140 T140_10_2 (by decide)

theorem hcardT140_10_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK140)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK140 ⟨10, by decide⟩ R140_2 hpxR140_2 hcardq140_2 (by decide)).symm

/-- **Cell (140, 10) twin (q=2).** -/
theorem cell140_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK140) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK140) (charOfVec2 rK140 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK140 e (h : Coordinate 2) T140_10_2 i :=
  species_entry_eq_sum rK140 ⟨10, by decide⟩ e heK h T140_10_2 hfix140_10_2 hinj140_10_2 hcardT140_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK140) (T140_10_2 i) (hfix140_10_2 i) h)

/-! ### Cell (140, 12) twin -/

def T140_12_2 : Fin 5 → Coordinate 2 := fun i => T140_12list.getD i.val (0,0,0,0,0)

theorem hfix140_12_2 : ∀ i, ((T140_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK140)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK140) :=
  repsFix_of_siftB2 rK140 ⟨12, by decide⟩ T140_12_2 (by decide)

theorem hinj140_12_2 : Function.Injective
    (fun i => ((T140_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK140)) :=
  repsInj_of_reduceAux2 rK140 T140_12_2 (by decide)

theorem hcardT140_12_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK140)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK140 ⟨12, by decide⟩ R140_2 hpxR140_2 hcardq140_2 (by decide)).symm

/-- **Cell (140, 12) twin (q=2).** -/
theorem cell140_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK140) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK140) (charOfVec2 rK140 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK140 e (h : Coordinate 2) T140_12_2 i :=
  species_entry_eq_sum rK140 ⟨12, by decide⟩ e heK h T140_12_2 hfix140_12_2 hinj140_12_2 hcardT140_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK140) (T140_12_2 i) (hfix140_12_2 i) h)

/-! ### Cell (140, 23) twin -/

def T140_23_2 : Fin 5 → Coordinate 2 := fun i => T140_23list.getD i.val (0,0,0,0,0)

theorem hfix140_23_2 : ∀ i, ((T140_23_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK140)
    ∈ fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK140) :=
  repsFix_of_siftB2 rK140 ⟨23, by decide⟩ T140_23_2 (by decide)

theorem hinj140_23_2 : Function.Injective
    (fun i => ((T140_23_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK140)) :=
  repsInj_of_reduceAux2 rK140 T140_23_2 (by decide)

theorem hcardT140_23_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK140)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK140 ⟨23, by decide⟩ R140_2 hpxR140_2 hcardq140_2 (by decide)).symm

/-- **Cell (140, 23) twin (q=2).** -/
theorem cell140_23_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK140) e = true)
    (h : ↥(reps (⟨23, by decide⟩ : Fin 148))) :
    species (reps (⟨23, by decide⟩ : Fin 148)) h (basisElt (reps rK140) (charOfVec2 rK140 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK140 e (h : Coordinate 2) T140_23_2 i :=
  species_entry_eq_sum rK140 ⟨23, by decide⟩ e heK h T140_23_2 hfix140_23_2 hinj140_23_2 hcardT140_23_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨23, by decide⟩) (reps rK140) (T140_23_2 i) (hfix140_23_2 i) h)

/-! ### Cell (140, 28) twin -/

def T140_28_2 : Fin 5 → Coordinate 2 := fun i => T140_28list.getD i.val (0,0,0,0,0)

theorem hfix140_28_2 : ∀ i, ((T140_28_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK140)
    ∈ fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK140) :=
  repsFix_of_siftB2 rK140 ⟨28, by decide⟩ T140_28_2 (by decide)

theorem hinj140_28_2 : Function.Injective
    (fun i => ((T140_28_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK140)) :=
  repsInj_of_reduceAux2 rK140 T140_28_2 (by decide)

theorem hcardT140_28_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK140)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK140 ⟨28, by decide⟩ R140_2 hpxR140_2 hcardq140_2 (by decide)).symm

/-- **Cell (140, 28) twin (q=2).** -/
theorem cell140_28_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK140) e = true)
    (h : ↥(reps (⟨28, by decide⟩ : Fin 148))) :
    species (reps (⟨28, by decide⟩ : Fin 148)) h (basisElt (reps rK140) (charOfVec2 rK140 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK140 e (h : Coordinate 2) T140_28_2 i :=
  species_entry_eq_sum rK140 ⟨28, by decide⟩ e heK h T140_28_2 hfix140_28_2 hinj140_28_2 hcardT140_28_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨28, by decide⟩) (reps rK140) (T140_28_2 i) (hfix140_28_2 i) h)

/-! ### Cell (140, 35) twin -/

def T140_35_2 : Fin 5 → Coordinate 2 := fun i => T140_35list.getD i.val (0,0,0,0,0)

theorem hfix140_35_2 : ∀ i, ((T140_35_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK140)
    ∈ fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK140) :=
  repsFix_of_siftB2 rK140 ⟨35, by decide⟩ T140_35_2 (by decide)

theorem hinj140_35_2 : Function.Injective
    (fun i => ((T140_35_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK140)) :=
  repsInj_of_reduceAux2 rK140 T140_35_2 (by decide)

theorem hcardT140_35_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK140)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK140 ⟨35, by decide⟩ R140_2 hpxR140_2 hcardq140_2 (by decide)).symm

/-- **Cell (140, 35) twin (q=2).** -/
theorem cell140_35_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK140) e = true)
    (h : ↥(reps (⟨35, by decide⟩ : Fin 148))) :
    species (reps (⟨35, by decide⟩ : Fin 148)) h (basisElt (reps rK140) (charOfVec2 rK140 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK140 e (h : Coordinate 2) T140_35_2 i :=
  species_entry_eq_sum rK140 ⟨35, by decide⟩ e heK h T140_35_2 hfix140_35_2 hinj140_35_2 hcardT140_35_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨35, by decide⟩) (reps rK140) (T140_35_2 i) (hfix140_35_2 i) h)

/-! ### Cell (140, 39) twin -/

def T140_39_2 : Fin 5 → Coordinate 2 := fun i => T140_39list.getD i.val (0,0,0,0,0)

theorem hfix140_39_2 : ∀ i, ((T140_39_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK140)
    ∈ fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK140) :=
  repsFix_of_siftB2 rK140 ⟨39, by decide⟩ T140_39_2 (by decide)

theorem hinj140_39_2 : Function.Injective
    (fun i => ((T140_39_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK140)) :=
  repsInj_of_reduceAux2 rK140 T140_39_2 (by decide)

theorem hcardT140_39_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK140)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK140 ⟨39, by decide⟩ R140_2 hpxR140_2 hcardq140_2 (by decide)).symm

/-- **Cell (140, 39) twin (q=2).** -/
theorem cell140_39_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK140) e = true)
    (h : ↥(reps (⟨39, by decide⟩ : Fin 148))) :
    species (reps (⟨39, by decide⟩ : Fin 148)) h (basisElt (reps rK140) (charOfVec2 rK140 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK140 e (h : Coordinate 2) T140_39_2 i :=
  species_entry_eq_sum rK140 ⟨39, by decide⟩ e heK h T140_39_2 hfix140_39_2 hinj140_39_2 hcardT140_39_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨39, by decide⟩) (reps rK140) (T140_39_2 i) (hfix140_39_2 i) h)

/-! ### Cell (140, 46) twin -/

def T140_46_2 : Fin 5 → Coordinate 2 := fun i => T140_46list.getD i.val (0,0,0,0,0)

theorem hfix140_46_2 : ∀ i, ((T140_46_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK140)
    ∈ fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK140) :=
  repsFix_of_siftB2 rK140 ⟨46, by decide⟩ T140_46_2 (by decide)

theorem hinj140_46_2 : Function.Injective
    (fun i => ((T140_46_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK140)) :=
  repsInj_of_reduceAux2 rK140 T140_46_2 (by decide)

theorem hcardT140_46_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK140)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK140 ⟨46, by decide⟩ R140_2 hpxR140_2 hcardq140_2 (by decide)).symm

/-- **Cell (140, 46) twin (q=2).** -/
theorem cell140_46_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK140) e = true)
    (h : ↥(reps (⟨46, by decide⟩ : Fin 148))) :
    species (reps (⟨46, by decide⟩ : Fin 148)) h (basisElt (reps rK140) (charOfVec2 rK140 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK140 e (h : Coordinate 2) T140_46_2 i :=
  species_entry_eq_sum rK140 ⟨46, by decide⟩ e heK h T140_46_2 hfix140_46_2 hinj140_46_2 hcardT140_46_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨46, by decide⟩) (reps rK140) (T140_46_2 i) (hfix140_46_2 i) h)

/-! ### Cell (140, 52) twin -/

def T140_52_2 : Fin 5 → Coordinate 2 := fun i => T140_52list.getD i.val (0,0,0,0,0)

theorem hfix140_52_2 : ∀ i, ((T140_52_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK140)
    ∈ fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK140) :=
  repsFix_of_siftB2 rK140 ⟨52, by decide⟩ T140_52_2 (by decide)

theorem hinj140_52_2 : Function.Injective
    (fun i => ((T140_52_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK140)) :=
  repsInj_of_reduceAux2 rK140 T140_52_2 (by decide)

theorem hcardT140_52_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK140)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK140 ⟨52, by decide⟩ R140_2 hpxR140_2 hcardq140_2 (by decide)).symm

/-- **Cell (140, 52) twin (q=2).** -/
theorem cell140_52_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK140) e = true)
    (h : ↥(reps (⟨52, by decide⟩ : Fin 148))) :
    species (reps (⟨52, by decide⟩ : Fin 148)) h (basisElt (reps rK140) (charOfVec2 rK140 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK140 e (h : Coordinate 2) T140_52_2 i :=
  species_entry_eq_sum rK140 ⟨52, by decide⟩ e heK h T140_52_2 hfix140_52_2 hinj140_52_2 hcardT140_52_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨52, by decide⟩) (reps rK140) (T140_52_2 i) (hfix140_52_2 i) h)

/-! ### Cell (140, 53) twin -/

def T140_53_2 : Fin 5 → Coordinate 2 := fun i => T140_53list.getD i.val (0,0,0,0,0)

theorem hfix140_53_2 : ∀ i, ((T140_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK140)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK140) :=
  repsFix_of_siftB2 rK140 ⟨53, by decide⟩ T140_53_2 (by decide)

theorem hinj140_53_2 : Function.Injective
    (fun i => ((T140_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK140)) :=
  repsInj_of_reduceAux2 rK140 T140_53_2 (by decide)

theorem hcardT140_53_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK140)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK140 ⟨53, by decide⟩ R140_2 hpxR140_2 hcardq140_2 (by decide)).symm

/-- **Cell (140, 53) twin (q=2).** -/
theorem cell140_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK140) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK140) (charOfVec2 rK140 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK140 e (h : Coordinate 2) T140_53_2 i :=
  species_entry_eq_sum rK140 ⟨53, by decide⟩ e heK h T140_53_2 hfix140_53_2 hinj140_53_2 hcardT140_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK140) (T140_53_2 i) (hfix140_53_2 i) h)

/-! ### Cell (140, 84) twin -/

def T140_84_2 : Fin 5 → Coordinate 2 := fun i => T140_84list.getD i.val (0,0,0,0,0)

theorem hfix140_84_2 : ∀ i, ((T140_84_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK140)
    ∈ fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK140) :=
  repsFix_of_siftB2 rK140 ⟨84, by decide⟩ T140_84_2 (by decide)

theorem hinj140_84_2 : Function.Injective
    (fun i => ((T140_84_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK140)) :=
  repsInj_of_reduceAux2 rK140 T140_84_2 (by decide)

theorem hcardT140_84_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK140)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK140 ⟨84, by decide⟩ R140_2 hpxR140_2 hcardq140_2 (by decide)).symm

/-- **Cell (140, 84) twin (q=2).** -/
theorem cell140_84_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK140) e = true)
    (h : ↥(reps (⟨84, by decide⟩ : Fin 148))) :
    species (reps (⟨84, by decide⟩ : Fin 148)) h (basisElt (reps rK140) (charOfVec2 rK140 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK140 e (h : Coordinate 2) T140_84_2 i :=
  species_entry_eq_sum rK140 ⟨84, by decide⟩ e heK h T140_84_2 hfix140_84_2 hinj140_84_2 hcardT140_84_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨84, by decide⟩) (reps rK140) (T140_84_2 i) (hfix140_84_2 i) h)

/-! ### Cell (140, 90) twin -/

def T140_90_2 : Fin 5 → Coordinate 2 := fun i => T140_90list.getD i.val (0,0,0,0,0)

theorem hfix140_90_2 : ∀ i, ((T140_90_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK140)
    ∈ fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK140) :=
  repsFix_of_siftB2 rK140 ⟨90, by decide⟩ T140_90_2 (by decide)

theorem hinj140_90_2 : Function.Injective
    (fun i => ((T140_90_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK140)) :=
  repsInj_of_reduceAux2 rK140 T140_90_2 (by decide)

theorem hcardT140_90_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK140)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK140 ⟨90, by decide⟩ R140_2 hpxR140_2 hcardq140_2 (by decide)).symm

/-- **Cell (140, 90) twin (q=2).** -/
theorem cell140_90_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK140) e = true)
    (h : ↥(reps (⟨90, by decide⟩ : Fin 148))) :
    species (reps (⟨90, by decide⟩ : Fin 148)) h (basisElt (reps rK140) (charOfVec2 rK140 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK140 e (h : Coordinate 2) T140_90_2 i :=
  species_entry_eq_sum rK140 ⟨90, by decide⟩ e heK h T140_90_2 hfix140_90_2 hinj140_90_2 hcardT140_90_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨90, by decide⟩) (reps rK140) (T140_90_2 i) (hfix140_90_2 i) h)

/-! ### Cell (140, 97) twin -/

def T140_97_2 : Fin 5 → Coordinate 2 := fun i => T140_97list.getD i.val (0,0,0,0,0)

theorem hfix140_97_2 : ∀ i, ((T140_97_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK140)
    ∈ fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK140) :=
  repsFix_of_siftB2 rK140 ⟨97, by decide⟩ T140_97_2 (by decide)

theorem hinj140_97_2 : Function.Injective
    (fun i => ((T140_97_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK140)) :=
  repsInj_of_reduceAux2 rK140 T140_97_2 (by decide)

theorem hcardT140_97_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK140)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK140 ⟨97, by decide⟩ R140_2 hpxR140_2 hcardq140_2 (by decide)).symm

/-- **Cell (140, 97) twin (q=2).** -/
theorem cell140_97_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK140) e = true)
    (h : ↥(reps (⟨97, by decide⟩ : Fin 148))) :
    species (reps (⟨97, by decide⟩ : Fin 148)) h (basisElt (reps rK140) (charOfVec2 rK140 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK140 e (h : Coordinate 2) T140_97_2 i :=
  species_entry_eq_sum rK140 ⟨97, by decide⟩ e heK h T140_97_2 hfix140_97_2 hinj140_97_2 hcardT140_97_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨97, by decide⟩) (reps rK140) (T140_97_2 i) (hfix140_97_2 i) h)

/-! ### Cell (140, 101) twin -/

def T140_101_2 : Fin 5 → Coordinate 2 := fun i => T140_101list.getD i.val (0,0,0,0,0)

theorem hfix140_101_2 : ∀ i, ((T140_101_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK140)
    ∈ fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK140) :=
  repsFix_of_siftB2 rK140 ⟨101, by decide⟩ T140_101_2 (by decide)

theorem hinj140_101_2 : Function.Injective
    (fun i => ((T140_101_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK140)) :=
  repsInj_of_reduceAux2 rK140 T140_101_2 (by decide)

theorem hcardT140_101_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK140)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK140 ⟨101, by decide⟩ R140_2 hpxR140_2 hcardq140_2 (by decide)).symm

/-- **Cell (140, 101) twin (q=2).** -/
theorem cell140_101_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK140) e = true)
    (h : ↥(reps (⟨101, by decide⟩ : Fin 148))) :
    species (reps (⟨101, by decide⟩ : Fin 148)) h (basisElt (reps rK140) (charOfVec2 rK140 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK140 e (h : Coordinate 2) T140_101_2 i :=
  species_entry_eq_sum rK140 ⟨101, by decide⟩ e heK h T140_101_2 hfix140_101_2 hinj140_101_2 hcardT140_101_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨101, by decide⟩) (reps rK140) (T140_101_2 i) (hfix140_101_2 i) h)

/-! ### Cell (140, 108) twin -/

def T140_108_2 : Fin 5 → Coordinate 2 := fun i => T140_108list.getD i.val (0,0,0,0,0)

theorem hfix140_108_2 : ∀ i, ((T140_108_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK140)
    ∈ fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK140) :=
  repsFix_of_siftB2 rK140 ⟨108, by decide⟩ T140_108_2 (by decide)

theorem hinj140_108_2 : Function.Injective
    (fun i => ((T140_108_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK140)) :=
  repsInj_of_reduceAux2 rK140 T140_108_2 (by decide)

theorem hcardT140_108_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK140)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK140 ⟨108, by decide⟩ R140_2 hpxR140_2 hcardq140_2 (by decide)).symm

/-- **Cell (140, 108) twin (q=2).** -/
theorem cell140_108_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK140) e = true)
    (h : ↥(reps (⟨108, by decide⟩ : Fin 148))) :
    species (reps (⟨108, by decide⟩ : Fin 148)) h (basisElt (reps rK140) (charOfVec2 rK140 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK140 e (h : Coordinate 2) T140_108_2 i :=
  species_entry_eq_sum rK140 ⟨108, by decide⟩ e heK h T140_108_2 hfix140_108_2 hinj140_108_2 hcardT140_108_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨108, by decide⟩) (reps rK140) (T140_108_2 i) (hfix140_108_2 i) h)

/-! ### Cell (140, 114) twin -/

def T140_114_2 : Fin 5 → Coordinate 2 := fun i => T140_114list.getD i.val (0,0,0,0,0)

theorem hfix140_114_2 : ∀ i, ((T140_114_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK140)
    ∈ fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK140) :=
  repsFix_of_siftB2 rK140 ⟨114, by decide⟩ T140_114_2 (by decide)

theorem hinj140_114_2 : Function.Injective
    (fun i => ((T140_114_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK140)) :=
  repsInj_of_reduceAux2 rK140 T140_114_2 (by decide)

theorem hcardT140_114_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK140)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK140 ⟨114, by decide⟩ R140_2 hpxR140_2 hcardq140_2 (by decide)).symm

/-- **Cell (140, 114) twin (q=2).** -/
theorem cell140_114_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK140) e = true)
    (h : ↥(reps (⟨114, by decide⟩ : Fin 148))) :
    species (reps (⟨114, by decide⟩ : Fin 148)) h (basisElt (reps rK140) (charOfVec2 rK140 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK140 e (h : Coordinate 2) T140_114_2 i :=
  species_entry_eq_sum rK140 ⟨114, by decide⟩ e heK h T140_114_2 hfix140_114_2 hinj140_114_2 hcardT140_114_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨114, by decide⟩) (reps rK140) (T140_114_2 i) (hfix140_114_2 i) h)

/-! ### Cell (140, 140) twin -/

def T140_140_2 : Fin 5 → Coordinate 2 := fun i => T140_140list.getD i.val (0,0,0,0,0)

theorem hfix140_140_2 : ∀ i, ((T140_140_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK140)
    ∈ fixedPoints (reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK140) :=
  repsFix_of_siftB2 rK140 ⟨140, by decide⟩ T140_140_2 (by decide)

theorem hinj140_140_2 : Function.Injective
    (fun i => ((T140_140_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK140)) :=
  repsInj_of_reduceAux2 rK140 T140_140_2 (by decide)

theorem hcardT140_140_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK140)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK140 ⟨140, by decide⟩ R140_2 hpxR140_2 hcardq140_2 (by decide)).symm

/-- **Cell (140, 140) twin (q=2).** -/
theorem cell140_140_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK140) e = true)
    (h : ↥(reps (⟨140, by decide⟩ : Fin 148))) :
    species (reps (⟨140, by decide⟩ : Fin 148)) h (basisElt (reps rK140) (charOfVec2 rK140 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK140 e (h : Coordinate 2) T140_140_2 i :=
  species_entry_eq_sum rK140 ⟨140, by decide⟩ e heK h T140_140_2 hfix140_140_2 hinj140_140_2 hcardT140_140_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨140, by decide⟩) (reps rK140) (T140_140_2 i) (hfix140_140_2 i) h)

end Q2

end LeanDring.P5Presentation
