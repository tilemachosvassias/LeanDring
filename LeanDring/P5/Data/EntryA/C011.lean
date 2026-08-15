/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, A-block data (rK = 23): certified per-cell species-entry instantiations, both twins.

Emit-embed-decide loop for order-25 A-block class `rK = 23` (`|G/K| = 125`).
All nonzero `H`-columns (`|gH| ≤ 2`, `t⁻¹Ht ⊆ K`).  Full 125-coset transversal
`R23` and each `H`-fixed sub-transversal `T23_rH` embedded as kernel data and
re-verified by `decide` through the `LeanDring/P5/Certificate/SpeciesTable/EntryTransA.lean` adapters.  Transversal data is
SHARED between the twins (`reduceAux` normal forms coincide; verified in the
emitter and re-checked by the `q=2` decides below).
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false
set_option linter.style.setOption false

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

def rK23 : Fin 148 := ⟨23, by decide⟩

def R23list : List Coordinates := [(0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0)]
def R23 : Fin 125 → Coordinate 1 := fun i => R23list.getD i.val (0,0,0,0,0)

theorem hpxR23 : Function.Injective (fun i => reduceAux 1 (basisAt rK23) (R23 i)) := by decide
theorem hcardq23 : Nat.card (Coordinate 1 ⧸ reps rK23) = 125 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (23, 0): |T| = 125 -/

def T23_0list : List Coordinates := [(0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0)]
def T23_0 : Fin 125 → Coordinate 1 := fun i => T23_0list.getD i.val (0,0,0,0,0)

theorem hfix23_0 : ∀ i, ((T23_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK23)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23) :=
  repsFix_of_siftB rK23 ⟨0, by decide⟩ T23_0 (by decide)

theorem hinj23_0 : Function.Injective
    (fun i => ((T23_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK23)) :=
  repsInj_of_reduceAux rK23 T23_0 (by decide)

theorem hcardT23_0 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK23 ⟨0, by decide⟩ R23 hpxR23 hcardq23 (by decide)).symm

/-- **Cell (23, 0).** -/
theorem cell23_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK23) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK23) (charOfVec rK23 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK23 e (h : Coordinate 1) T23_0 i :=
  species_entry_eq_sum rK23 ⟨0, by decide⟩ e heK h T23_0 hfix23_0 hinj23_0 hcardT23_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK23) (T23_0 i) (hfix23_0 i) h)

/-! ## Cell (23, 5): |T| = 25 -/

def T23_5list : List Coordinates := [(0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0)]
def T23_5 : Fin 25 → Coordinate 1 := fun i => T23_5list.getD i.val (0,0,0,0,0)

theorem hfix23_5 : ∀ i, ((T23_5 i : Coordinate 1) : Coordinate 1 ⧸ reps rK23)
    ∈ fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23) :=
  repsFix_of_siftB rK23 ⟨5, by decide⟩ T23_5 (by decide)

theorem hinj23_5 : Function.Injective
    (fun i => ((T23_5 i : Coordinate 1) : Coordinate 1 ⧸ reps rK23)) :=
  repsInj_of_reduceAux rK23 T23_5 (by decide)

theorem hcardT23_5 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK23 ⟨5, by decide⟩ R23 hpxR23 hcardq23 (by decide)).symm

/-- **Cell (23, 5).** -/
theorem cell23_5 (e : List (ZMod 25)) (heK : charOK (basisAt rK23) e = true)
    (h : ↥(reps (⟨5, by decide⟩ : Fin 148))) :
    species (reps (⟨5, by decide⟩ : Fin 148)) h (basisElt (reps rK23) (charOfVec rK23 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK23 e (h : Coordinate 1) T23_5 i :=
  species_entry_eq_sum rK23 ⟨5, by decide⟩ e heK h T23_5 hfix23_5 hinj23_5 hcardT23_5
    (fun i => conj_mem_of_fixedPoints (reps ⟨5, by decide⟩) (reps rK23) (T23_5 i) (hfix23_5 i) h)

/-! ## Cell (23, 12): |T| = 125 -/

def T23_12list : List Coordinates := [(0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0)]
def T23_12 : Fin 125 → Coordinate 1 := fun i => T23_12list.getD i.val (0,0,0,0,0)

theorem hfix23_12 : ∀ i, ((T23_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK23)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23) :=
  repsFix_of_siftB rK23 ⟨12, by decide⟩ T23_12 (by decide)

theorem hinj23_12 : Function.Injective
    (fun i => ((T23_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK23)) :=
  repsInj_of_reduceAux rK23 T23_12 (by decide)

theorem hcardT23_12 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK23 ⟨12, by decide⟩ R23 hpxR23 hcardq23 (by decide)).symm

/-- **Cell (23, 12).** -/
theorem cell23_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK23) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK23) (charOfVec rK23 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK23 e (h : Coordinate 1) T23_12 i :=
  species_entry_eq_sum rK23 ⟨12, by decide⟩ e heK h T23_12 hfix23_12 hinj23_12 hcardT23_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK23) (T23_12 i) (hfix23_12 i) h)

/-! ## Cell (23, 23): |T| = 25 -/

def T23_23list : List Coordinates := [(0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0)]
def T23_23 : Fin 25 → Coordinate 1 := fun i => T23_23list.getD i.val (0,0,0,0,0)

theorem hfix23_23 : ∀ i, ((T23_23 i : Coordinate 1) : Coordinate 1 ⧸ reps rK23)
    ∈ fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23) :=
  repsFix_of_siftB rK23 ⟨23, by decide⟩ T23_23 (by decide)

theorem hinj23_23 : Function.Injective
    (fun i => ((T23_23 i : Coordinate 1) : Coordinate 1 ⧸ reps rK23)) :=
  repsInj_of_reduceAux rK23 T23_23 (by decide)

theorem hcardT23_23 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK23 ⟨23, by decide⟩ R23 hpxR23 hcardq23 (by decide)).symm

/-- **Cell (23, 23).** -/
theorem cell23_23 (e : List (ZMod 25)) (heK : charOK (basisAt rK23) e = true)
    (h : ↥(reps (⟨23, by decide⟩ : Fin 148))) :
    species (reps (⟨23, by decide⟩ : Fin 148)) h (basisElt (reps rK23) (charOfVec rK23 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK23 e (h : Coordinate 1) T23_23 i :=
  species_entry_eq_sum rK23 ⟨23, by decide⟩ e heK h T23_23 hfix23_23 hinj23_23 hcardT23_23
    (fun i => conj_mem_of_fixedPoints (reps ⟨23, by decide⟩) (reps rK23) (T23_23 i) (hfix23_23 i) h)

namespace Q2

def R23_2 : Fin 125 → Coordinate 2 := fun i => R23list.getD i.val (0,0,0,0,0)
theorem hpxR23_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK23) (R23_2 i)) := by decide
theorem hcardq23_2 : Nat.card (Coordinate 2 ⧸ reps rK23) = 125 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (23, 0) twin -/

def T23_0_2 : Fin 125 → Coordinate 2 := fun i => T23_0list.getD i.val (0,0,0,0,0)

theorem hfix23_0_2 : ∀ i, ((T23_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK23)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK23) :=
  repsFix_of_siftB2 rK23 ⟨0, by decide⟩ T23_0_2 (by decide)

theorem hinj23_0_2 : Function.Injective
    (fun i => ((T23_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK23)) :=
  repsInj_of_reduceAux2 rK23 T23_0_2 (by decide)

theorem hcardT23_0_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK23)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK23 ⟨0, by decide⟩ R23_2 hpxR23_2 hcardq23_2 (by decide)).symm

/-- **Cell (23, 0) twin (q=2).** -/
theorem cell23_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK23) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK23) (charOfVec2 rK23 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK23 e (h : Coordinate 2) T23_0_2 i :=
  species_entry_eq_sum rK23 ⟨0, by decide⟩ e heK h T23_0_2 hfix23_0_2 hinj23_0_2 hcardT23_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK23) (T23_0_2 i) (hfix23_0_2 i) h)

/-! ### Cell (23, 5) twin -/

def T23_5_2 : Fin 25 → Coordinate 2 := fun i => T23_5list.getD i.val (0,0,0,0,0)

theorem hfix23_5_2 : ∀ i, ((T23_5_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK23)
    ∈ fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK23) :=
  repsFix_of_siftB2 rK23 ⟨5, by decide⟩ T23_5_2 (by decide)

theorem hinj23_5_2 : Function.Injective
    (fun i => ((T23_5_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK23)) :=
  repsInj_of_reduceAux2 rK23 T23_5_2 (by decide)

theorem hcardT23_5_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK23)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK23 ⟨5, by decide⟩ R23_2 hpxR23_2 hcardq23_2 (by decide)).symm

/-- **Cell (23, 5) twin (q=2).** -/
theorem cell23_5_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK23) e = true)
    (h : ↥(reps (⟨5, by decide⟩ : Fin 148))) :
    species (reps (⟨5, by decide⟩ : Fin 148)) h (basisElt (reps rK23) (charOfVec2 rK23 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK23 e (h : Coordinate 2) T23_5_2 i :=
  species_entry_eq_sum rK23 ⟨5, by decide⟩ e heK h T23_5_2 hfix23_5_2 hinj23_5_2 hcardT23_5_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨5, by decide⟩) (reps rK23) (T23_5_2 i) (hfix23_5_2 i) h)

/-! ### Cell (23, 12) twin -/

def T23_12_2 : Fin 125 → Coordinate 2 := fun i => T23_12list.getD i.val (0,0,0,0,0)

theorem hfix23_12_2 : ∀ i, ((T23_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK23)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK23) :=
  repsFix_of_siftB2 rK23 ⟨12, by decide⟩ T23_12_2 (by decide)

theorem hinj23_12_2 : Function.Injective
    (fun i => ((T23_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK23)) :=
  repsInj_of_reduceAux2 rK23 T23_12_2 (by decide)

theorem hcardT23_12_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK23)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK23 ⟨12, by decide⟩ R23_2 hpxR23_2 hcardq23_2 (by decide)).symm

/-- **Cell (23, 12) twin (q=2).** -/
theorem cell23_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK23) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK23) (charOfVec2 rK23 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK23 e (h : Coordinate 2) T23_12_2 i :=
  species_entry_eq_sum rK23 ⟨12, by decide⟩ e heK h T23_12_2 hfix23_12_2 hinj23_12_2 hcardT23_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK23) (T23_12_2 i) (hfix23_12_2 i) h)

/-! ### Cell (23, 23) twin -/

def T23_23_2 : Fin 25 → Coordinate 2 := fun i => T23_23list.getD i.val (0,0,0,0,0)

theorem hfix23_23_2 : ∀ i, ((T23_23_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK23)
    ∈ fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK23) :=
  repsFix_of_siftB2 rK23 ⟨23, by decide⟩ T23_23_2 (by decide)

theorem hinj23_23_2 : Function.Injective
    (fun i => ((T23_23_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK23)) :=
  repsInj_of_reduceAux2 rK23 T23_23_2 (by decide)

theorem hcardT23_23_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK23)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK23 ⟨23, by decide⟩ R23_2 hpxR23_2 hcardq23_2 (by decide)).symm

/-- **Cell (23, 23) twin (q=2).** -/
theorem cell23_23_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK23) e = true)
    (h : ↥(reps (⟨23, by decide⟩ : Fin 148))) :
    species (reps (⟨23, by decide⟩ : Fin 148)) h (basisElt (reps rK23) (charOfVec2 rK23 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK23 e (h : Coordinate 2) T23_23_2 i :=
  species_entry_eq_sum rK23 ⟨23, by decide⟩ e heK h T23_23_2 hfix23_23_2 hinj23_23_2 hcardT23_23_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨23, by decide⟩) (reps rK23) (T23_23_2 i) (hfix23_23_2 i) h)

end Q2

end LeanDring.P5Presentation
