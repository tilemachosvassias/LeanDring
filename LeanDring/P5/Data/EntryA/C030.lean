/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, A-block data (rK = 42): certified per-cell species-entry instantiations, both twins.

Emit-embed-decide loop for order-25 A-block class `rK = 42` (`|G/K| = 125`).
All nonzero `H`-columns (`|gH| ≤ 2`, `t⁻¹Ht ⊆ K`).  Full 125-coset transversal
`R42` and each `H`-fixed sub-transversal `T42_rH` embedded as kernel data and
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

def rK42 : Fin 148 := ⟨42, by decide⟩

def R42list : List Coordinates := [(0,1,3,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0)]
def R42 : Fin 125 → Coordinate 1 := fun i => R42list.getD i.val (0,0,0,0,0)

theorem hpxR42 : Function.Injective (fun i => reduceAux 1 (basisAt rK42) (R42 i)) := by decide
theorem hcardq42 : Nat.card (Coordinate 1 ⧸ reps rK42) = 125 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (42, 0): |T| = 125 -/

def T42_0list : List Coordinates := [(0,1,3,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0)]
def T42_0 : Fin 125 → Coordinate 1 := fun i => T42_0list.getD i.val (0,0,0,0,0)

theorem hfix42_0 : ∀ i, ((T42_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK42)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42) :=
  repsFix_of_siftB rK42 ⟨0, by decide⟩ T42_0 (by decide)

theorem hinj42_0 : Function.Injective
    (fun i => ((T42_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK42)) :=
  repsInj_of_reduceAux rK42 T42_0 (by decide)

theorem hcardT42_0 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK42 ⟨0, by decide⟩ R42 hpxR42 hcardq42 (by decide)).symm

/-- **Cell (42, 0).** -/
theorem cell42_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK42) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK42) (charOfVec rK42 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK42 e (h : Coordinate 1) T42_0 i :=
  species_entry_eq_sum rK42 ⟨0, by decide⟩ e heK h T42_0 hfix42_0 hinj42_0 hcardT42_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK42) (T42_0 i) (hfix42_0 i) h)

/-! ## Cell (42, 12): |T| = 125 -/

def T42_12list : List Coordinates := [(0,1,3,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0)]
def T42_12 : Fin 125 → Coordinate 1 := fun i => T42_12list.getD i.val (0,0,0,0,0)

theorem hfix42_12 : ∀ i, ((T42_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK42)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42) :=
  repsFix_of_siftB rK42 ⟨12, by decide⟩ T42_12 (by decide)

theorem hinj42_12 : Function.Injective
    (fun i => ((T42_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK42)) :=
  repsInj_of_reduceAux rK42 T42_12 (by decide)

theorem hcardT42_12 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK42 ⟨12, by decide⟩ R42 hpxR42 hcardq42 (by decide)).symm

/-- **Cell (42, 12).** -/
theorem cell42_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK42) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK42) (charOfVec rK42 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK42 e (h : Coordinate 1) T42_12 i :=
  species_entry_eq_sum rK42 ⟨12, by decide⟩ e heK h T42_12 hfix42_12 hinj42_12 hcardT42_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK42) (T42_12 i) (hfix42_12 i) h)

/-! ## Cell (42, 42): |T| = 25 -/

def T42_42list : List Coordinates := [(0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0)]
def T42_42 : Fin 25 → Coordinate 1 := fun i => T42_42list.getD i.val (0,0,0,0,0)

theorem hfix42_42 : ∀ i, ((T42_42 i : Coordinate 1) : Coordinate 1 ⧸ reps rK42)
    ∈ fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42) :=
  repsFix_of_siftB rK42 ⟨42, by decide⟩ T42_42 (by decide)

theorem hinj42_42 : Function.Injective
    (fun i => ((T42_42 i : Coordinate 1) : Coordinate 1 ⧸ reps rK42)) :=
  repsInj_of_reduceAux rK42 T42_42 (by decide)

theorem hcardT42_42 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK42 ⟨42, by decide⟩ R42 hpxR42 hcardq42 (by decide)).symm

/-- **Cell (42, 42).** -/
theorem cell42_42 (e : List (ZMod 25)) (heK : charOK (basisAt rK42) e = true)
    (h : ↥(reps (⟨42, by decide⟩ : Fin 148))) :
    species (reps (⟨42, by decide⟩ : Fin 148)) h (basisElt (reps rK42) (charOfVec rK42 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK42 e (h : Coordinate 1) T42_42 i :=
  species_entry_eq_sum rK42 ⟨42, by decide⟩ e heK h T42_42 hfix42_42 hinj42_42 hcardT42_42
    (fun i => conj_mem_of_fixedPoints (reps ⟨42, by decide⟩) (reps rK42) (T42_42 i) (hfix42_42 i) h)

namespace Q2

def R42_2 : Fin 125 → Coordinate 2 := fun i => R42list.getD i.val (0,0,0,0,0)
theorem hpxR42_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK42) (R42_2 i)) := by decide
theorem hcardq42_2 : Nat.card (Coordinate 2 ⧸ reps rK42) = 125 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (42, 0) twin -/

def T42_0_2 : Fin 125 → Coordinate 2 := fun i => T42_0list.getD i.val (0,0,0,0,0)

theorem hfix42_0_2 : ∀ i, ((T42_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK42)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK42) :=
  repsFix_of_siftB2 rK42 ⟨0, by decide⟩ T42_0_2 (by decide)

theorem hinj42_0_2 : Function.Injective
    (fun i => ((T42_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK42)) :=
  repsInj_of_reduceAux2 rK42 T42_0_2 (by decide)

theorem hcardT42_0_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK42)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK42 ⟨0, by decide⟩ R42_2 hpxR42_2 hcardq42_2 (by decide)).symm

/-- **Cell (42, 0) twin (q=2).** -/
theorem cell42_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK42) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK42) (charOfVec2 rK42 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK42 e (h : Coordinate 2) T42_0_2 i :=
  species_entry_eq_sum rK42 ⟨0, by decide⟩ e heK h T42_0_2 hfix42_0_2 hinj42_0_2 hcardT42_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK42) (T42_0_2 i) (hfix42_0_2 i) h)

/-! ### Cell (42, 12) twin -/

def T42_12_2 : Fin 125 → Coordinate 2 := fun i => T42_12list.getD i.val (0,0,0,0,0)

theorem hfix42_12_2 : ∀ i, ((T42_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK42)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK42) :=
  repsFix_of_siftB2 rK42 ⟨12, by decide⟩ T42_12_2 (by decide)

theorem hinj42_12_2 : Function.Injective
    (fun i => ((T42_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK42)) :=
  repsInj_of_reduceAux2 rK42 T42_12_2 (by decide)

theorem hcardT42_12_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK42)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK42 ⟨12, by decide⟩ R42_2 hpxR42_2 hcardq42_2 (by decide)).symm

/-- **Cell (42, 12) twin (q=2).** -/
theorem cell42_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK42) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK42) (charOfVec2 rK42 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK42 e (h : Coordinate 2) T42_12_2 i :=
  species_entry_eq_sum rK42 ⟨12, by decide⟩ e heK h T42_12_2 hfix42_12_2 hinj42_12_2 hcardT42_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK42) (T42_12_2 i) (hfix42_12_2 i) h)

/-! ### Cell (42, 42) twin -/

def T42_42_2 : Fin 25 → Coordinate 2 := fun i => T42_42list.getD i.val (0,0,0,0,0)

theorem hfix42_42_2 : ∀ i, ((T42_42_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK42)
    ∈ fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK42) :=
  repsFix_of_siftB2 rK42 ⟨42, by decide⟩ T42_42_2 (by decide)

theorem hinj42_42_2 : Function.Injective
    (fun i => ((T42_42_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK42)) :=
  repsInj_of_reduceAux2 rK42 T42_42_2 (by decide)

theorem hcardT42_42_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK42)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK42 ⟨42, by decide⟩ R42_2 hpxR42_2 hcardq42_2 (by decide)).symm

/-- **Cell (42, 42) twin (q=2).** -/
theorem cell42_42_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK42) e = true)
    (h : ↥(reps (⟨42, by decide⟩ : Fin 148))) :
    species (reps (⟨42, by decide⟩ : Fin 148)) h (basisElt (reps rK42) (charOfVec2 rK42 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK42 e (h : Coordinate 2) T42_42_2 i :=
  species_entry_eq_sum rK42 ⟨42, by decide⟩ e heK h T42_42_2 hfix42_42_2 hinj42_42_2 hcardT42_42_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨42, by decide⟩) (reps rK42) (T42_42_2 i) (hfix42_42_2 i) h)

end Q2

end LeanDring.P5Presentation
