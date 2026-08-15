/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, A-block data (rK = 51): certified per-cell species-entry instantiations, both twins.

Emit-embed-decide loop for order-25 A-block class `rK = 51` (`|G/K| = 125`).
All nonzero `H`-columns (`|gH| ≤ 2`, `t⁻¹Ht ⊆ K`).  Full 125-coset transversal
`R51` and each `H`-fixed sub-transversal `T51_rH` embedded as kernel data and
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

def rK51 : Fin 148 := ⟨51, by decide⟩

def R51list : List Coordinates := [(0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0)]
def R51 : Fin 125 → Coordinate 1 := fun i => R51list.getD i.val (0,0,0,0,0)

theorem hpxR51 : Function.Injective (fun i => reduceAux 1 (basisAt rK51) (R51 i)) := by decide
theorem hcardq51 : Nat.card (Coordinate 1 ⧸ reps rK51) = 125 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (51, 0): |T| = 125 -/

def T51_0list : List Coordinates := [(0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0)]
def T51_0 : Fin 125 → Coordinate 1 := fun i => T51_0list.getD i.val (0,0,0,0,0)

theorem hfix51_0 : ∀ i, ((T51_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK51)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51) :=
  repsFix_of_siftB rK51 ⟨0, by decide⟩ T51_0 (by decide)

theorem hinj51_0 : Function.Injective
    (fun i => ((T51_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK51)) :=
  repsInj_of_reduceAux rK51 T51_0 (by decide)

theorem hcardT51_0 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK51 ⟨0, by decide⟩ R51 hpxR51 hcardq51 (by decide)).symm

/-- **Cell (51, 0).** -/
theorem cell51_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK51) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK51) (charOfVec rK51 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK51 e (h : Coordinate 1) T51_0 i :=
  species_entry_eq_sum rK51 ⟨0, by decide⟩ e heK h T51_0 hfix51_0 hinj51_0 hcardT51_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK51) (T51_0 i) (hfix51_0 i) h)

/-! ## Cell (51, 12): |T| = 125 -/

def T51_12list : List Coordinates := [(0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0)]
def T51_12 : Fin 125 → Coordinate 1 := fun i => T51_12list.getD i.val (0,0,0,0,0)

theorem hfix51_12 : ∀ i, ((T51_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK51)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51) :=
  repsFix_of_siftB rK51 ⟨12, by decide⟩ T51_12 (by decide)

theorem hinj51_12 : Function.Injective
    (fun i => ((T51_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK51)) :=
  repsInj_of_reduceAux rK51 T51_12 (by decide)

theorem hcardT51_12 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK51 ⟨12, by decide⟩ R51 hpxR51 hcardq51 (by decide)).symm

/-- **Cell (51, 12).** -/
theorem cell51_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK51) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK51) (charOfVec rK51 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK51 e (h : Coordinate 1) T51_12 i :=
  species_entry_eq_sum rK51 ⟨12, by decide⟩ e heK h T51_12 hfix51_12 hinj51_12 hcardT51_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK51) (T51_12 i) (hfix51_12 i) h)

/-! ## Cell (51, 51): |T| = 25 -/

def T51_51list : List Coordinates := [(0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0)]
def T51_51 : Fin 25 → Coordinate 1 := fun i => T51_51list.getD i.val (0,0,0,0,0)

theorem hfix51_51 : ∀ i, ((T51_51 i : Coordinate 1) : Coordinate 1 ⧸ reps rK51)
    ∈ fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51) :=
  repsFix_of_siftB rK51 ⟨51, by decide⟩ T51_51 (by decide)

theorem hinj51_51 : Function.Injective
    (fun i => ((T51_51 i : Coordinate 1) : Coordinate 1 ⧸ reps rK51)) :=
  repsInj_of_reduceAux rK51 T51_51 (by decide)

theorem hcardT51_51 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK51 ⟨51, by decide⟩ R51 hpxR51 hcardq51 (by decide)).symm

/-- **Cell (51, 51).** -/
theorem cell51_51 (e : List (ZMod 25)) (heK : charOK (basisAt rK51) e = true)
    (h : ↥(reps (⟨51, by decide⟩ : Fin 148))) :
    species (reps (⟨51, by decide⟩ : Fin 148)) h (basisElt (reps rK51) (charOfVec rK51 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK51 e (h : Coordinate 1) T51_51 i :=
  species_entry_eq_sum rK51 ⟨51, by decide⟩ e heK h T51_51 hfix51_51 hinj51_51 hcardT51_51
    (fun i => conj_mem_of_fixedPoints (reps ⟨51, by decide⟩) (reps rK51) (T51_51 i) (hfix51_51 i) h)

namespace Q2

def R51_2 : Fin 125 → Coordinate 2 := fun i => R51list.getD i.val (0,0,0,0,0)
theorem hpxR51_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK51) (R51_2 i)) := by decide
theorem hcardq51_2 : Nat.card (Coordinate 2 ⧸ reps rK51) = 125 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (51, 0) twin -/

def T51_0_2 : Fin 125 → Coordinate 2 := fun i => T51_0list.getD i.val (0,0,0,0,0)

theorem hfix51_0_2 : ∀ i, ((T51_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK51)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK51) :=
  repsFix_of_siftB2 rK51 ⟨0, by decide⟩ T51_0_2 (by decide)

theorem hinj51_0_2 : Function.Injective
    (fun i => ((T51_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK51)) :=
  repsInj_of_reduceAux2 rK51 T51_0_2 (by decide)

theorem hcardT51_0_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK51)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK51 ⟨0, by decide⟩ R51_2 hpxR51_2 hcardq51_2 (by decide)).symm

/-- **Cell (51, 0) twin (q=2).** -/
theorem cell51_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK51) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK51) (charOfVec2 rK51 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK51 e (h : Coordinate 2) T51_0_2 i :=
  species_entry_eq_sum rK51 ⟨0, by decide⟩ e heK h T51_0_2 hfix51_0_2 hinj51_0_2 hcardT51_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK51) (T51_0_2 i) (hfix51_0_2 i) h)

/-! ### Cell (51, 12) twin -/

def T51_12_2 : Fin 125 → Coordinate 2 := fun i => T51_12list.getD i.val (0,0,0,0,0)

theorem hfix51_12_2 : ∀ i, ((T51_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK51)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK51) :=
  repsFix_of_siftB2 rK51 ⟨12, by decide⟩ T51_12_2 (by decide)

theorem hinj51_12_2 : Function.Injective
    (fun i => ((T51_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK51)) :=
  repsInj_of_reduceAux2 rK51 T51_12_2 (by decide)

theorem hcardT51_12_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK51)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK51 ⟨12, by decide⟩ R51_2 hpxR51_2 hcardq51_2 (by decide)).symm

/-- **Cell (51, 12) twin (q=2).** -/
theorem cell51_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK51) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK51) (charOfVec2 rK51 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK51 e (h : Coordinate 2) T51_12_2 i :=
  species_entry_eq_sum rK51 ⟨12, by decide⟩ e heK h T51_12_2 hfix51_12_2 hinj51_12_2 hcardT51_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK51) (T51_12_2 i) (hfix51_12_2 i) h)

/-! ### Cell (51, 51) twin -/

def T51_51_2 : Fin 25 → Coordinate 2 := fun i => T51_51list.getD i.val (0,0,0,0,0)

theorem hfix51_51_2 : ∀ i, ((T51_51_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK51)
    ∈ fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK51) :=
  repsFix_of_siftB2 rK51 ⟨51, by decide⟩ T51_51_2 (by decide)

theorem hinj51_51_2 : Function.Injective
    (fun i => ((T51_51_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK51)) :=
  repsInj_of_reduceAux2 rK51 T51_51_2 (by decide)

theorem hcardT51_51_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK51)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK51 ⟨51, by decide⟩ R51_2 hpxR51_2 hcardq51_2 (by decide)).symm

/-- **Cell (51, 51) twin (q=2).** -/
theorem cell51_51_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK51) e = true)
    (h : ↥(reps (⟨51, by decide⟩ : Fin 148))) :
    species (reps (⟨51, by decide⟩ : Fin 148)) h (basisElt (reps rK51) (charOfVec2 rK51 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK51 e (h : Coordinate 2) T51_51_2 i :=
  species_entry_eq_sum rK51 ⟨51, by decide⟩ e heK h T51_51_2 hfix51_51_2 hinj51_51_2 hcardT51_51_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨51, by decide⟩) (reps rK51) (T51_51_2 i) (hfix51_51_2 i) h)

end Q2

end LeanDring.P5Presentation
