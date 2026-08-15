/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, A-block data (rK = 40): certified per-cell species-entry instantiations, both twins.

Emit-embed-decide loop for order-25 A-block class `rK = 40` (`|G/K| = 125`).
All nonzero `H`-columns (`|gH| ≤ 2`, `t⁻¹Ht ⊆ K`).  Full 125-coset transversal
`R40` and each `H`-fixed sub-transversal `T40_rH` embedded as kernel data and
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

def rK40 : Fin 148 := ⟨40, by decide⟩

def R40list : List Coordinates := [(0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0)]
def R40 : Fin 125 → Coordinate 1 := fun i => R40list.getD i.val (0,0,0,0,0)

theorem hpxR40 : Function.Injective (fun i => reduceAux 1 (basisAt rK40) (R40 i)) := by decide
theorem hcardq40 : Nat.card (Coordinate 1 ⧸ reps rK40) = 125 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (40, 0): |T| = 125 -/

def T40_0list : List Coordinates := [(0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0)]
def T40_0 : Fin 125 → Coordinate 1 := fun i => T40_0list.getD i.val (0,0,0,0,0)

theorem hfix40_0 : ∀ i, ((T40_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK40)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40) :=
  repsFix_of_siftB rK40 ⟨0, by decide⟩ T40_0 (by decide)

theorem hinj40_0 : Function.Injective
    (fun i => ((T40_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK40)) :=
  repsInj_of_reduceAux rK40 T40_0 (by decide)

theorem hcardT40_0 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK40 ⟨0, by decide⟩ R40 hpxR40 hcardq40 (by decide)).symm

/-- **Cell (40, 0).** -/
theorem cell40_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK40) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK40) (charOfVec rK40 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK40 e (h : Coordinate 1) T40_0 i :=
  species_entry_eq_sum rK40 ⟨0, by decide⟩ e heK h T40_0 hfix40_0 hinj40_0 hcardT40_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK40) (T40_0 i) (hfix40_0 i) h)

/-! ## Cell (40, 12): |T| = 125 -/

def T40_12list : List Coordinates := [(0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0)]
def T40_12 : Fin 125 → Coordinate 1 := fun i => T40_12list.getD i.val (0,0,0,0,0)

theorem hfix40_12 : ∀ i, ((T40_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK40)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40) :=
  repsFix_of_siftB rK40 ⟨12, by decide⟩ T40_12 (by decide)

theorem hinj40_12 : Function.Injective
    (fun i => ((T40_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK40)) :=
  repsInj_of_reduceAux rK40 T40_12 (by decide)

theorem hcardT40_12 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK40 ⟨12, by decide⟩ R40 hpxR40 hcardq40 (by decide)).symm

/-- **Cell (40, 12).** -/
theorem cell40_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK40) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK40) (charOfVec rK40 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK40 e (h : Coordinate 1) T40_12 i :=
  species_entry_eq_sum rK40 ⟨12, by decide⟩ e heK h T40_12 hfix40_12 hinj40_12 hcardT40_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK40) (T40_12 i) (hfix40_12 i) h)

/-! ## Cell (40, 40): |T| = 25 -/

def T40_40list : List Coordinates := [(0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0)]
def T40_40 : Fin 25 → Coordinate 1 := fun i => T40_40list.getD i.val (0,0,0,0,0)

theorem hfix40_40 : ∀ i, ((T40_40 i : Coordinate 1) : Coordinate 1 ⧸ reps rK40)
    ∈ fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40) :=
  repsFix_of_siftB rK40 ⟨40, by decide⟩ T40_40 (by decide)

theorem hinj40_40 : Function.Injective
    (fun i => ((T40_40 i : Coordinate 1) : Coordinate 1 ⧸ reps rK40)) :=
  repsInj_of_reduceAux rK40 T40_40 (by decide)

theorem hcardT40_40 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK40 ⟨40, by decide⟩ R40 hpxR40 hcardq40 (by decide)).symm

/-- **Cell (40, 40).** -/
theorem cell40_40 (e : List (ZMod 25)) (heK : charOK (basisAt rK40) e = true)
    (h : ↥(reps (⟨40, by decide⟩ : Fin 148))) :
    species (reps (⟨40, by decide⟩ : Fin 148)) h (basisElt (reps rK40) (charOfVec rK40 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK40 e (h : Coordinate 1) T40_40 i :=
  species_entry_eq_sum rK40 ⟨40, by decide⟩ e heK h T40_40 hfix40_40 hinj40_40 hcardT40_40
    (fun i => conj_mem_of_fixedPoints (reps ⟨40, by decide⟩) (reps rK40) (T40_40 i) (hfix40_40 i) h)

namespace Q2

def R40_2 : Fin 125 → Coordinate 2 := fun i => R40list.getD i.val (0,0,0,0,0)
theorem hpxR40_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK40) (R40_2 i)) := by decide
theorem hcardq40_2 : Nat.card (Coordinate 2 ⧸ reps rK40) = 125 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (40, 0) twin -/

def T40_0_2 : Fin 125 → Coordinate 2 := fun i => T40_0list.getD i.val (0,0,0,0,0)

theorem hfix40_0_2 : ∀ i, ((T40_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK40)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK40) :=
  repsFix_of_siftB2 rK40 ⟨0, by decide⟩ T40_0_2 (by decide)

theorem hinj40_0_2 : Function.Injective
    (fun i => ((T40_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK40)) :=
  repsInj_of_reduceAux2 rK40 T40_0_2 (by decide)

theorem hcardT40_0_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK40)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK40 ⟨0, by decide⟩ R40_2 hpxR40_2 hcardq40_2 (by decide)).symm

/-- **Cell (40, 0) twin (q=2).** -/
theorem cell40_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK40) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK40) (charOfVec2 rK40 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK40 e (h : Coordinate 2) T40_0_2 i :=
  species_entry_eq_sum rK40 ⟨0, by decide⟩ e heK h T40_0_2 hfix40_0_2 hinj40_0_2 hcardT40_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK40) (T40_0_2 i) (hfix40_0_2 i) h)

/-! ### Cell (40, 12) twin -/

def T40_12_2 : Fin 125 → Coordinate 2 := fun i => T40_12list.getD i.val (0,0,0,0,0)

theorem hfix40_12_2 : ∀ i, ((T40_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK40)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK40) :=
  repsFix_of_siftB2 rK40 ⟨12, by decide⟩ T40_12_2 (by decide)

theorem hinj40_12_2 : Function.Injective
    (fun i => ((T40_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK40)) :=
  repsInj_of_reduceAux2 rK40 T40_12_2 (by decide)

theorem hcardT40_12_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK40)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK40 ⟨12, by decide⟩ R40_2 hpxR40_2 hcardq40_2 (by decide)).symm

/-- **Cell (40, 12) twin (q=2).** -/
theorem cell40_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK40) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK40) (charOfVec2 rK40 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK40 e (h : Coordinate 2) T40_12_2 i :=
  species_entry_eq_sum rK40 ⟨12, by decide⟩ e heK h T40_12_2 hfix40_12_2 hinj40_12_2 hcardT40_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK40) (T40_12_2 i) (hfix40_12_2 i) h)

/-! ### Cell (40, 40) twin -/

def T40_40_2 : Fin 25 → Coordinate 2 := fun i => T40_40list.getD i.val (0,0,0,0,0)

theorem hfix40_40_2 : ∀ i, ((T40_40_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK40)
    ∈ fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK40) :=
  repsFix_of_siftB2 rK40 ⟨40, by decide⟩ T40_40_2 (by decide)

theorem hinj40_40_2 : Function.Injective
    (fun i => ((T40_40_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK40)) :=
  repsInj_of_reduceAux2 rK40 T40_40_2 (by decide)

theorem hcardT40_40_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK40)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK40 ⟨40, by decide⟩ R40_2 hpxR40_2 hcardq40_2 (by decide)).symm

/-- **Cell (40, 40) twin (q=2).** -/
theorem cell40_40_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK40) e = true)
    (h : ↥(reps (⟨40, by decide⟩ : Fin 148))) :
    species (reps (⟨40, by decide⟩ : Fin 148)) h (basisElt (reps rK40) (charOfVec2 rK40 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK40 e (h : Coordinate 2) T40_40_2 i :=
  species_entry_eq_sum rK40 ⟨40, by decide⟩ e heK h T40_40_2 hfix40_40_2 hinj40_40_2 hcardT40_40_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨40, by decide⟩) (reps rK40) (T40_40_2 i) (hfix40_40_2 i) h)

end Q2

end LeanDring.P5Presentation
