/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, A-block data (rK = 39): certified per-cell species-entry instantiations, both twins.

Emit-embed-decide loop for order-25 A-block class `rK = 39` (`|G/K| = 125`).
All nonzero `H`-columns (`|gH| ≤ 2`, `t⁻¹Ht ⊆ K`).  Full 125-coset transversal
`R39` and each `H`-fixed sub-transversal `T39_rH` embedded as kernel data and
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

def rK39 : Fin 148 := ⟨39, by decide⟩

def R39list : List Coordinates := [(0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,1,1,0)]
def R39 : Fin 125 → Coordinate 1 := fun i => R39list.getD i.val (0,0,0,0,0)

theorem hpxR39 : Function.Injective (fun i => reduceAux 1 (basisAt rK39) (R39 i)) := by decide
theorem hcardq39 : Nat.card (Coordinate 1 ⧸ reps rK39) = 125 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (39, 0): |T| = 125 -/

def T39_0list : List Coordinates := [(0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,1,1,0)]
def T39_0 : Fin 125 → Coordinate 1 := fun i => T39_0list.getD i.val (0,0,0,0,0)

theorem hfix39_0 : ∀ i, ((T39_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK39)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39) :=
  repsFix_of_siftB rK39 ⟨0, by decide⟩ T39_0 (by decide)

theorem hinj39_0 : Function.Injective
    (fun i => ((T39_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK39)) :=
  repsInj_of_reduceAux rK39 T39_0 (by decide)

theorem hcardT39_0 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK39 ⟨0, by decide⟩ R39 hpxR39 hcardq39 (by decide)).symm

/-- **Cell (39, 0).** -/
theorem cell39_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK39) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK39) (charOfVec rK39 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK39 e (h : Coordinate 1) T39_0 i :=
  species_entry_eq_sum rK39 ⟨0, by decide⟩ e heK h T39_0 hfix39_0 hinj39_0 hcardT39_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK39) (T39_0 i) (hfix39_0 i) h)

/-! ## Cell (39, 12): |T| = 125 -/

def T39_12list : List Coordinates := [(0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,1,1,0)]
def T39_12 : Fin 125 → Coordinate 1 := fun i => T39_12list.getD i.val (0,0,0,0,0)

theorem hfix39_12 : ∀ i, ((T39_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK39)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39) :=
  repsFix_of_siftB rK39 ⟨12, by decide⟩ T39_12 (by decide)

theorem hinj39_12 : Function.Injective
    (fun i => ((T39_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK39)) :=
  repsInj_of_reduceAux rK39 T39_12 (by decide)

theorem hcardT39_12 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK39 ⟨12, by decide⟩ R39 hpxR39 hcardq39 (by decide)).symm

/-- **Cell (39, 12).** -/
theorem cell39_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK39) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK39) (charOfVec rK39 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK39 e (h : Coordinate 1) T39_12 i :=
  species_entry_eq_sum rK39 ⟨12, by decide⟩ e heK h T39_12 hfix39_12 hinj39_12 hcardT39_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK39) (T39_12 i) (hfix39_12 i) h)

/-! ## Cell (39, 39): |T| = 25 -/

def T39_39list : List Coordinates := [(0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0)]
def T39_39 : Fin 25 → Coordinate 1 := fun i => T39_39list.getD i.val (0,0,0,0,0)

theorem hfix39_39 : ∀ i, ((T39_39 i : Coordinate 1) : Coordinate 1 ⧸ reps rK39)
    ∈ fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39) :=
  repsFix_of_siftB rK39 ⟨39, by decide⟩ T39_39 (by decide)

theorem hinj39_39 : Function.Injective
    (fun i => ((T39_39 i : Coordinate 1) : Coordinate 1 ⧸ reps rK39)) :=
  repsInj_of_reduceAux rK39 T39_39 (by decide)

theorem hcardT39_39 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK39 ⟨39, by decide⟩ R39 hpxR39 hcardq39 (by decide)).symm

/-- **Cell (39, 39).** -/
theorem cell39_39 (e : List (ZMod 25)) (heK : charOK (basisAt rK39) e = true)
    (h : ↥(reps (⟨39, by decide⟩ : Fin 148))) :
    species (reps (⟨39, by decide⟩ : Fin 148)) h (basisElt (reps rK39) (charOfVec rK39 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK39 e (h : Coordinate 1) T39_39 i :=
  species_entry_eq_sum rK39 ⟨39, by decide⟩ e heK h T39_39 hfix39_39 hinj39_39 hcardT39_39
    (fun i => conj_mem_of_fixedPoints (reps ⟨39, by decide⟩) (reps rK39) (T39_39 i) (hfix39_39 i) h)

namespace Q2

def R39_2 : Fin 125 → Coordinate 2 := fun i => R39list.getD i.val (0,0,0,0,0)
theorem hpxR39_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK39) (R39_2 i)) := by decide
theorem hcardq39_2 : Nat.card (Coordinate 2 ⧸ reps rK39) = 125 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (39, 0) twin -/

def T39_0_2 : Fin 125 → Coordinate 2 := fun i => T39_0list.getD i.val (0,0,0,0,0)

theorem hfix39_0_2 : ∀ i, ((T39_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK39)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK39) :=
  repsFix_of_siftB2 rK39 ⟨0, by decide⟩ T39_0_2 (by decide)

theorem hinj39_0_2 : Function.Injective
    (fun i => ((T39_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK39)) :=
  repsInj_of_reduceAux2 rK39 T39_0_2 (by decide)

theorem hcardT39_0_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK39)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK39 ⟨0, by decide⟩ R39_2 hpxR39_2 hcardq39_2 (by decide)).symm

/-- **Cell (39, 0) twin (q=2).** -/
theorem cell39_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK39) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK39) (charOfVec2 rK39 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK39 e (h : Coordinate 2) T39_0_2 i :=
  species_entry_eq_sum rK39 ⟨0, by decide⟩ e heK h T39_0_2 hfix39_0_2 hinj39_0_2 hcardT39_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK39) (T39_0_2 i) (hfix39_0_2 i) h)

/-! ### Cell (39, 12) twin -/

def T39_12_2 : Fin 125 → Coordinate 2 := fun i => T39_12list.getD i.val (0,0,0,0,0)

theorem hfix39_12_2 : ∀ i, ((T39_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK39)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK39) :=
  repsFix_of_siftB2 rK39 ⟨12, by decide⟩ T39_12_2 (by decide)

theorem hinj39_12_2 : Function.Injective
    (fun i => ((T39_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK39)) :=
  repsInj_of_reduceAux2 rK39 T39_12_2 (by decide)

theorem hcardT39_12_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK39)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK39 ⟨12, by decide⟩ R39_2 hpxR39_2 hcardq39_2 (by decide)).symm

/-- **Cell (39, 12) twin (q=2).** -/
theorem cell39_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK39) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK39) (charOfVec2 rK39 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK39 e (h : Coordinate 2) T39_12_2 i :=
  species_entry_eq_sum rK39 ⟨12, by decide⟩ e heK h T39_12_2 hfix39_12_2 hinj39_12_2 hcardT39_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK39) (T39_12_2 i) (hfix39_12_2 i) h)

/-! ### Cell (39, 39) twin -/

def T39_39_2 : Fin 25 → Coordinate 2 := fun i => T39_39list.getD i.val (0,0,0,0,0)

theorem hfix39_39_2 : ∀ i, ((T39_39_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK39)
    ∈ fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK39) :=
  repsFix_of_siftB2 rK39 ⟨39, by decide⟩ T39_39_2 (by decide)

theorem hinj39_39_2 : Function.Injective
    (fun i => ((T39_39_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK39)) :=
  repsInj_of_reduceAux2 rK39 T39_39_2 (by decide)

theorem hcardT39_39_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK39)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK39 ⟨39, by decide⟩ R39_2 hpxR39_2 hcardq39_2 (by decide)).symm

/-- **Cell (39, 39) twin (q=2).** -/
theorem cell39_39_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK39) e = true)
    (h : ↥(reps (⟨39, by decide⟩ : Fin 148))) :
    species (reps (⟨39, by decide⟩ : Fin 148)) h (basisElt (reps rK39) (charOfVec2 rK39 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK39 e (h : Coordinate 2) T39_39_2 i :=
  species_entry_eq_sum rK39 ⟨39, by decide⟩ e heK h T39_39_2 hfix39_39_2 hinj39_39_2 hcardT39_39_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨39, by decide⟩) (reps rK39) (T39_39_2 i) (hfix39_39_2 i) h)

end Q2

end LeanDring.P5Presentation
