/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, A-block data (rK = 49): certified per-cell species-entry instantiations, both twins.

Emit-embed-decide loop for order-25 A-block class `rK = 49` (`|G/K| = 125`).
All nonzero `H`-columns (`|gH| ≤ 2`, `t⁻¹Ht ⊆ K`).  Full 125-coset transversal
`R49` and each `H`-fixed sub-transversal `T49_rH` embedded as kernel data and
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

def rK49 : Fin 148 := ⟨49, by decide⟩

def R49list : List Coordinates := [(0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,4,1,0)]
def R49 : Fin 125 → Coordinate 1 := fun i => R49list.getD i.val (0,0,0,0,0)

theorem hpxR49 : Function.Injective (fun i => reduceAux 1 (basisAt rK49) (R49 i)) := by decide
theorem hcardq49 : Nat.card (Coordinate 1 ⧸ reps rK49) = 125 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (49, 0): |T| = 125 -/

def T49_0list : List Coordinates := [(0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,4,1,0)]
def T49_0 : Fin 125 → Coordinate 1 := fun i => T49_0list.getD i.val (0,0,0,0,0)

theorem hfix49_0 : ∀ i, ((T49_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK49)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49) :=
  repsFix_of_siftB rK49 ⟨0, by decide⟩ T49_0 (by decide)

theorem hinj49_0 : Function.Injective
    (fun i => ((T49_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK49)) :=
  repsInj_of_reduceAux rK49 T49_0 (by decide)

theorem hcardT49_0 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK49 ⟨0, by decide⟩ R49 hpxR49 hcardq49 (by decide)).symm

/-- **Cell (49, 0).** -/
theorem cell49_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK49) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK49) (charOfVec rK49 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK49 e (h : Coordinate 1) T49_0 i :=
  species_entry_eq_sum rK49 ⟨0, by decide⟩ e heK h T49_0 hfix49_0 hinj49_0 hcardT49_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK49) (T49_0 i) (hfix49_0 i) h)

/-! ## Cell (49, 12): |T| = 125 -/

def T49_12list : List Coordinates := [(0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,4,1,0)]
def T49_12 : Fin 125 → Coordinate 1 := fun i => T49_12list.getD i.val (0,0,0,0,0)

theorem hfix49_12 : ∀ i, ((T49_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK49)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49) :=
  repsFix_of_siftB rK49 ⟨12, by decide⟩ T49_12 (by decide)

theorem hinj49_12 : Function.Injective
    (fun i => ((T49_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK49)) :=
  repsInj_of_reduceAux rK49 T49_12 (by decide)

theorem hcardT49_12 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK49 ⟨12, by decide⟩ R49 hpxR49 hcardq49 (by decide)).symm

/-- **Cell (49, 12).** -/
theorem cell49_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK49) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK49) (charOfVec rK49 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK49 e (h : Coordinate 1) T49_12 i :=
  species_entry_eq_sum rK49 ⟨12, by decide⟩ e heK h T49_12 hfix49_12 hinj49_12 hcardT49_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK49) (T49_12 i) (hfix49_12 i) h)

/-! ## Cell (49, 49): |T| = 25 -/

def T49_49list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0)]
def T49_49 : Fin 25 → Coordinate 1 := fun i => T49_49list.getD i.val (0,0,0,0,0)

theorem hfix49_49 : ∀ i, ((T49_49 i : Coordinate 1) : Coordinate 1 ⧸ reps rK49)
    ∈ fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49) :=
  repsFix_of_siftB rK49 ⟨49, by decide⟩ T49_49 (by decide)

theorem hinj49_49 : Function.Injective
    (fun i => ((T49_49 i : Coordinate 1) : Coordinate 1 ⧸ reps rK49)) :=
  repsInj_of_reduceAux rK49 T49_49 (by decide)

theorem hcardT49_49 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK49 ⟨49, by decide⟩ R49 hpxR49 hcardq49 (by decide)).symm

/-- **Cell (49, 49).** -/
theorem cell49_49 (e : List (ZMod 25)) (heK : charOK (basisAt rK49) e = true)
    (h : ↥(reps (⟨49, by decide⟩ : Fin 148))) :
    species (reps (⟨49, by decide⟩ : Fin 148)) h (basisElt (reps rK49) (charOfVec rK49 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK49 e (h : Coordinate 1) T49_49 i :=
  species_entry_eq_sum rK49 ⟨49, by decide⟩ e heK h T49_49 hfix49_49 hinj49_49 hcardT49_49
    (fun i => conj_mem_of_fixedPoints (reps ⟨49, by decide⟩) (reps rK49) (T49_49 i) (hfix49_49 i) h)

namespace Q2

def R49_2 : Fin 125 → Coordinate 2 := fun i => R49list.getD i.val (0,0,0,0,0)
theorem hpxR49_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK49) (R49_2 i)) := by decide
theorem hcardq49_2 : Nat.card (Coordinate 2 ⧸ reps rK49) = 125 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (49, 0) twin -/

def T49_0_2 : Fin 125 → Coordinate 2 := fun i => T49_0list.getD i.val (0,0,0,0,0)

theorem hfix49_0_2 : ∀ i, ((T49_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK49)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK49) :=
  repsFix_of_siftB2 rK49 ⟨0, by decide⟩ T49_0_2 (by decide)

theorem hinj49_0_2 : Function.Injective
    (fun i => ((T49_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK49)) :=
  repsInj_of_reduceAux2 rK49 T49_0_2 (by decide)

theorem hcardT49_0_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK49)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK49 ⟨0, by decide⟩ R49_2 hpxR49_2 hcardq49_2 (by decide)).symm

/-- **Cell (49, 0) twin (q=2).** -/
theorem cell49_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK49) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK49) (charOfVec2 rK49 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK49 e (h : Coordinate 2) T49_0_2 i :=
  species_entry_eq_sum rK49 ⟨0, by decide⟩ e heK h T49_0_2 hfix49_0_2 hinj49_0_2 hcardT49_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK49) (T49_0_2 i) (hfix49_0_2 i) h)

/-! ### Cell (49, 12) twin -/

def T49_12_2 : Fin 125 → Coordinate 2 := fun i => T49_12list.getD i.val (0,0,0,0,0)

theorem hfix49_12_2 : ∀ i, ((T49_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK49)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK49) :=
  repsFix_of_siftB2 rK49 ⟨12, by decide⟩ T49_12_2 (by decide)

theorem hinj49_12_2 : Function.Injective
    (fun i => ((T49_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK49)) :=
  repsInj_of_reduceAux2 rK49 T49_12_2 (by decide)

theorem hcardT49_12_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK49)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK49 ⟨12, by decide⟩ R49_2 hpxR49_2 hcardq49_2 (by decide)).symm

/-- **Cell (49, 12) twin (q=2).** -/
theorem cell49_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK49) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK49) (charOfVec2 rK49 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK49 e (h : Coordinate 2) T49_12_2 i :=
  species_entry_eq_sum rK49 ⟨12, by decide⟩ e heK h T49_12_2 hfix49_12_2 hinj49_12_2 hcardT49_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK49) (T49_12_2 i) (hfix49_12_2 i) h)

/-! ### Cell (49, 49) twin -/

def T49_49_2 : Fin 25 → Coordinate 2 := fun i => T49_49list.getD i.val (0,0,0,0,0)

theorem hfix49_49_2 : ∀ i, ((T49_49_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK49)
    ∈ fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK49) :=
  repsFix_of_siftB2 rK49 ⟨49, by decide⟩ T49_49_2 (by decide)

theorem hinj49_49_2 : Function.Injective
    (fun i => ((T49_49_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK49)) :=
  repsInj_of_reduceAux2 rK49 T49_49_2 (by decide)

theorem hcardT49_49_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK49)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK49 ⟨49, by decide⟩ R49_2 hpxR49_2 hcardq49_2 (by decide)).symm

/-- **Cell (49, 49) twin (q=2).** -/
theorem cell49_49_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK49) e = true)
    (h : ↥(reps (⟨49, by decide⟩ : Fin 148))) :
    species (reps (⟨49, by decide⟩ : Fin 148)) h (basisElt (reps rK49) (charOfVec2 rK49 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK49 e (h : Coordinate 2) T49_49_2 i :=
  species_entry_eq_sum rK49 ⟨49, by decide⟩ e heK h T49_49_2 hfix49_49_2 hinj49_49_2 hcardT49_49_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨49, by decide⟩) (reps rK49) (T49_49_2 i) (hfix49_49_2 i) h)

end Q2

end LeanDring.P5Presentation
