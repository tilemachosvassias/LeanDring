/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, A-block data (rK = 36): certified per-cell species-entry instantiations, both twins.

Emit-embed-decide loop for order-25 A-block class `rK = 36` (`|G/K| = 125`).
All nonzero `H`-columns (`|gH| ≤ 2`, `t⁻¹Ht ⊆ K`).  Full 125-coset transversal
`R36` and each `H`-fixed sub-transversal `T36_rH` embedded as kernel data and
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

def rK36 : Fin 148 := ⟨36, by decide⟩

def R36list : List Coordinates := [(0,3,1,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0)]
def R36 : Fin 125 → Coordinate 1 := fun i => R36list.getD i.val (0,0,0,0,0)

theorem hpxR36 : Function.Injective (fun i => reduceAux 1 (basisAt rK36) (R36 i)) := by decide
theorem hcardq36 : Nat.card (Coordinate 1 ⧸ reps rK36) = 125 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (36, 0): |T| = 125 -/

def T36_0list : List Coordinates := [(0,3,1,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0)]
def T36_0 : Fin 125 → Coordinate 1 := fun i => T36_0list.getD i.val (0,0,0,0,0)

theorem hfix36_0 : ∀ i, ((T36_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK36)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36) :=
  repsFix_of_siftB rK36 ⟨0, by decide⟩ T36_0 (by decide)

theorem hinj36_0 : Function.Injective
    (fun i => ((T36_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK36)) :=
  repsInj_of_reduceAux rK36 T36_0 (by decide)

theorem hcardT36_0 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK36 ⟨0, by decide⟩ R36 hpxR36 hcardq36 (by decide)).symm

/-- **Cell (36, 0).** -/
theorem cell36_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK36) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK36) (charOfVec rK36 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK36 e (h : Coordinate 1) T36_0 i :=
  species_entry_eq_sum rK36 ⟨0, by decide⟩ e heK h T36_0 hfix36_0 hinj36_0 hcardT36_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK36) (T36_0 i) (hfix36_0 i) h)

/-! ## Cell (36, 12): |T| = 125 -/

def T36_12list : List Coordinates := [(0,3,1,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0)]
def T36_12 : Fin 125 → Coordinate 1 := fun i => T36_12list.getD i.val (0,0,0,0,0)

theorem hfix36_12 : ∀ i, ((T36_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK36)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36) :=
  repsFix_of_siftB rK36 ⟨12, by decide⟩ T36_12 (by decide)

theorem hinj36_12 : Function.Injective
    (fun i => ((T36_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK36)) :=
  repsInj_of_reduceAux rK36 T36_12 (by decide)

theorem hcardT36_12 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK36 ⟨12, by decide⟩ R36 hpxR36 hcardq36 (by decide)).symm

/-- **Cell (36, 12).** -/
theorem cell36_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK36) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK36) (charOfVec rK36 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK36 e (h : Coordinate 1) T36_12 i :=
  species_entry_eq_sum rK36 ⟨12, by decide⟩ e heK h T36_12 hfix36_12 hinj36_12 hcardT36_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK36) (T36_12 i) (hfix36_12 i) h)

/-! ## Cell (36, 36): |T| = 25 -/

def T36_36list : List Coordinates := [(0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0)]
def T36_36 : Fin 25 → Coordinate 1 := fun i => T36_36list.getD i.val (0,0,0,0,0)

theorem hfix36_36 : ∀ i, ((T36_36 i : Coordinate 1) : Coordinate 1 ⧸ reps rK36)
    ∈ fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36) :=
  repsFix_of_siftB rK36 ⟨36, by decide⟩ T36_36 (by decide)

theorem hinj36_36 : Function.Injective
    (fun i => ((T36_36 i : Coordinate 1) : Coordinate 1 ⧸ reps rK36)) :=
  repsInj_of_reduceAux rK36 T36_36 (by decide)

theorem hcardT36_36 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK36 ⟨36, by decide⟩ R36 hpxR36 hcardq36 (by decide)).symm

/-- **Cell (36, 36).** -/
theorem cell36_36 (e : List (ZMod 25)) (heK : charOK (basisAt rK36) e = true)
    (h : ↥(reps (⟨36, by decide⟩ : Fin 148))) :
    species (reps (⟨36, by decide⟩ : Fin 148)) h (basisElt (reps rK36) (charOfVec rK36 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK36 e (h : Coordinate 1) T36_36 i :=
  species_entry_eq_sum rK36 ⟨36, by decide⟩ e heK h T36_36 hfix36_36 hinj36_36 hcardT36_36
    (fun i => conj_mem_of_fixedPoints (reps ⟨36, by decide⟩) (reps rK36) (T36_36 i) (hfix36_36 i) h)

namespace Q2

def R36_2 : Fin 125 → Coordinate 2 := fun i => R36list.getD i.val (0,0,0,0,0)
theorem hpxR36_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK36) (R36_2 i)) := by decide
theorem hcardq36_2 : Nat.card (Coordinate 2 ⧸ reps rK36) = 125 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (36, 0) twin -/

def T36_0_2 : Fin 125 → Coordinate 2 := fun i => T36_0list.getD i.val (0,0,0,0,0)

theorem hfix36_0_2 : ∀ i, ((T36_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK36)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK36) :=
  repsFix_of_siftB2 rK36 ⟨0, by decide⟩ T36_0_2 (by decide)

theorem hinj36_0_2 : Function.Injective
    (fun i => ((T36_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK36)) :=
  repsInj_of_reduceAux2 rK36 T36_0_2 (by decide)

theorem hcardT36_0_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK36)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK36 ⟨0, by decide⟩ R36_2 hpxR36_2 hcardq36_2 (by decide)).symm

/-- **Cell (36, 0) twin (q=2).** -/
theorem cell36_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK36) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK36) (charOfVec2 rK36 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK36 e (h : Coordinate 2) T36_0_2 i :=
  species_entry_eq_sum rK36 ⟨0, by decide⟩ e heK h T36_0_2 hfix36_0_2 hinj36_0_2 hcardT36_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK36) (T36_0_2 i) (hfix36_0_2 i) h)

/-! ### Cell (36, 12) twin -/

def T36_12_2 : Fin 125 → Coordinate 2 := fun i => T36_12list.getD i.val (0,0,0,0,0)

theorem hfix36_12_2 : ∀ i, ((T36_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK36)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK36) :=
  repsFix_of_siftB2 rK36 ⟨12, by decide⟩ T36_12_2 (by decide)

theorem hinj36_12_2 : Function.Injective
    (fun i => ((T36_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK36)) :=
  repsInj_of_reduceAux2 rK36 T36_12_2 (by decide)

theorem hcardT36_12_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK36)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK36 ⟨12, by decide⟩ R36_2 hpxR36_2 hcardq36_2 (by decide)).symm

/-- **Cell (36, 12) twin (q=2).** -/
theorem cell36_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK36) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK36) (charOfVec2 rK36 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK36 e (h : Coordinate 2) T36_12_2 i :=
  species_entry_eq_sum rK36 ⟨12, by decide⟩ e heK h T36_12_2 hfix36_12_2 hinj36_12_2 hcardT36_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK36) (T36_12_2 i) (hfix36_12_2 i) h)

/-! ### Cell (36, 36) twin -/

def T36_36_2 : Fin 25 → Coordinate 2 := fun i => T36_36list.getD i.val (0,0,0,0,0)

theorem hfix36_36_2 : ∀ i, ((T36_36_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK36)
    ∈ fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK36) :=
  repsFix_of_siftB2 rK36 ⟨36, by decide⟩ T36_36_2 (by decide)

theorem hinj36_36_2 : Function.Injective
    (fun i => ((T36_36_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK36)) :=
  repsInj_of_reduceAux2 rK36 T36_36_2 (by decide)

theorem hcardT36_36_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK36)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK36 ⟨36, by decide⟩ R36_2 hpxR36_2 hcardq36_2 (by decide)).symm

/-- **Cell (36, 36) twin (q=2).** -/
theorem cell36_36_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK36) e = true)
    (h : ↥(reps (⟨36, by decide⟩ : Fin 148))) :
    species (reps (⟨36, by decide⟩ : Fin 148)) h (basisElt (reps rK36) (charOfVec2 rK36 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK36 e (h : Coordinate 2) T36_36_2 i :=
  species_entry_eq_sum rK36 ⟨36, by decide⟩ e heK h T36_36_2 hfix36_36_2 hinj36_36_2 hcardT36_36_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨36, by decide⟩) (reps rK36) (T36_36_2 i) (hfix36_36_2 i) h)

end Q2

end LeanDring.P5Presentation
