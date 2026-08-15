/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, A-block data (rK = 48): certified per-cell species-entry instantiations, both twins.

Emit-embed-decide loop for order-25 A-block class `rK = 48` (`|G/K| = 125`).
All nonzero `H`-columns (`|gH| ≤ 2`, `t⁻¹Ht ⊆ K`).  Full 125-coset transversal
`R48` and each `H`-fixed sub-transversal `T48_rH` embedded as kernel data and
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

def rK48 : Fin 148 := ⟨48, by decide⟩

def R48list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,0,1,4,0), (1,0,1,0,0), (1,0,1,1,0), (1,0,1,2,0), (1,0,1,3,0), (1,0,2,4,0), (1,0,2,0,0), (1,0,2,1,0), (1,0,2,2,0), (1,0,2,3,0), (1,0,3,4,0), (1,0,3,0,0), (1,0,3,1,0), (1,0,3,2,0), (1,0,3,3,0), (1,0,4,4,0), (1,0,4,0,0), (1,0,4,1,0), (1,0,4,2,0), (1,0,4,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,0,1,4,0), (2,0,1,0,0), (2,0,1,1,0), (2,0,1,2,0), (2,0,1,3,0), (2,0,2,4,0), (2,0,2,0,0), (2,0,2,1,0), (2,0,2,2,0), (2,0,2,3,0), (2,0,3,4,0), (2,0,3,0,0), (2,0,3,1,0), (2,0,3,2,0), (2,0,3,3,0), (2,0,4,4,0), (2,0,4,0,0), (2,0,4,1,0), (2,0,4,2,0), (2,0,4,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,0,1,4,0), (3,0,1,0,0), (3,0,1,1,0), (3,0,1,2,0), (3,0,1,3,0), (3,0,2,4,0), (3,0,2,0,0), (3,0,2,1,0), (3,0,2,2,0), (3,0,2,3,0), (3,0,3,4,0), (3,0,3,0,0), (3,0,3,1,0), (3,0,3,2,0), (3,0,3,3,0), (3,0,4,4,0), (3,0,4,0,0), (3,0,4,1,0), (3,0,4,2,0), (3,0,4,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,0,1,4,0), (4,0,1,0,0), (4,0,1,1,0), (4,0,1,2,0), (4,0,1,3,0), (4,0,2,4,0), (4,0,2,0,0), (4,0,2,1,0), (4,0,2,2,0), (4,0,2,3,0), (4,0,3,4,0), (4,0,3,0,0), (4,0,3,1,0), (4,0,3,2,0), (4,0,3,3,0), (4,0,4,4,0), (4,0,4,0,0), (4,0,4,1,0), (4,0,4,2,0), (4,0,4,3,0)]
def R48 : Fin 125 → Coordinate 1 := fun i => R48list.getD i.val (0,0,0,0,0)

theorem hpxR48 : Function.Injective (fun i => reduceAux 1 (basisAt rK48) (R48 i)) := by decide
theorem hcardq48 : Nat.card (Coordinate 1 ⧸ reps rK48) = 125 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (48, 0): |T| = 125 -/

def T48_0list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,0,1,4,0), (1,0,1,0,0), (1,0,1,1,0), (1,0,1,2,0), (1,0,1,3,0), (1,0,2,4,0), (1,0,2,0,0), (1,0,2,1,0), (1,0,2,2,0), (1,0,2,3,0), (1,0,3,4,0), (1,0,3,0,0), (1,0,3,1,0), (1,0,3,2,0), (1,0,3,3,0), (1,0,4,4,0), (1,0,4,0,0), (1,0,4,1,0), (1,0,4,2,0), (1,0,4,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,0,1,4,0), (2,0,1,0,0), (2,0,1,1,0), (2,0,1,2,0), (2,0,1,3,0), (2,0,2,4,0), (2,0,2,0,0), (2,0,2,1,0), (2,0,2,2,0), (2,0,2,3,0), (2,0,3,4,0), (2,0,3,0,0), (2,0,3,1,0), (2,0,3,2,0), (2,0,3,3,0), (2,0,4,4,0), (2,0,4,0,0), (2,0,4,1,0), (2,0,4,2,0), (2,0,4,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,0,1,4,0), (3,0,1,0,0), (3,0,1,1,0), (3,0,1,2,0), (3,0,1,3,0), (3,0,2,4,0), (3,0,2,0,0), (3,0,2,1,0), (3,0,2,2,0), (3,0,2,3,0), (3,0,3,4,0), (3,0,3,0,0), (3,0,3,1,0), (3,0,3,2,0), (3,0,3,3,0), (3,0,4,4,0), (3,0,4,0,0), (3,0,4,1,0), (3,0,4,2,0), (3,0,4,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,0,1,4,0), (4,0,1,0,0), (4,0,1,1,0), (4,0,1,2,0), (4,0,1,3,0), (4,0,2,4,0), (4,0,2,0,0), (4,0,2,1,0), (4,0,2,2,0), (4,0,2,3,0), (4,0,3,4,0), (4,0,3,0,0), (4,0,3,1,0), (4,0,3,2,0), (4,0,3,3,0), (4,0,4,4,0), (4,0,4,0,0), (4,0,4,1,0), (4,0,4,2,0), (4,0,4,3,0)]
def T48_0 : Fin 125 → Coordinate 1 := fun i => T48_0list.getD i.val (0,0,0,0,0)

theorem hfix48_0 : ∀ i, ((T48_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK48)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48) :=
  repsFix_of_siftB rK48 ⟨0, by decide⟩ T48_0 (by decide)

theorem hinj48_0 : Function.Injective
    (fun i => ((T48_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK48)) :=
  repsInj_of_reduceAux rK48 T48_0 (by decide)

theorem hcardT48_0 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK48 ⟨0, by decide⟩ R48 hpxR48 hcardq48 (by decide)).symm

/-- **Cell (48, 0).** -/
theorem cell48_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK48) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK48) (charOfVec rK48 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK48 e (h : Coordinate 1) T48_0 i :=
  species_entry_eq_sum rK48 ⟨0, by decide⟩ e heK h T48_0 hfix48_0 hinj48_0 hcardT48_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK48) (T48_0 i) (hfix48_0 i) h)

/-! ## Cell (48, 12): |T| = 125 -/

def T48_12list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,0,1,4,0), (1,0,1,0,0), (1,0,1,1,0), (1,0,1,2,0), (1,0,1,3,0), (1,0,2,4,0), (1,0,2,0,0), (1,0,2,1,0), (1,0,2,2,0), (1,0,2,3,0), (1,0,3,4,0), (1,0,3,0,0), (1,0,3,1,0), (1,0,3,2,0), (1,0,3,3,0), (1,0,4,4,0), (1,0,4,0,0), (1,0,4,1,0), (1,0,4,2,0), (1,0,4,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,0,1,4,0), (2,0,1,0,0), (2,0,1,1,0), (2,0,1,2,0), (2,0,1,3,0), (2,0,2,4,0), (2,0,2,0,0), (2,0,2,1,0), (2,0,2,2,0), (2,0,2,3,0), (2,0,3,4,0), (2,0,3,0,0), (2,0,3,1,0), (2,0,3,2,0), (2,0,3,3,0), (2,0,4,4,0), (2,0,4,0,0), (2,0,4,1,0), (2,0,4,2,0), (2,0,4,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,0,1,4,0), (3,0,1,0,0), (3,0,1,1,0), (3,0,1,2,0), (3,0,1,3,0), (3,0,2,4,0), (3,0,2,0,0), (3,0,2,1,0), (3,0,2,2,0), (3,0,2,3,0), (3,0,3,4,0), (3,0,3,0,0), (3,0,3,1,0), (3,0,3,2,0), (3,0,3,3,0), (3,0,4,4,0), (3,0,4,0,0), (3,0,4,1,0), (3,0,4,2,0), (3,0,4,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,0,1,4,0), (4,0,1,0,0), (4,0,1,1,0), (4,0,1,2,0), (4,0,1,3,0), (4,0,2,4,0), (4,0,2,0,0), (4,0,2,1,0), (4,0,2,2,0), (4,0,2,3,0), (4,0,3,4,0), (4,0,3,0,0), (4,0,3,1,0), (4,0,3,2,0), (4,0,3,3,0), (4,0,4,4,0), (4,0,4,0,0), (4,0,4,1,0), (4,0,4,2,0), (4,0,4,3,0)]
def T48_12 : Fin 125 → Coordinate 1 := fun i => T48_12list.getD i.val (0,0,0,0,0)

theorem hfix48_12 : ∀ i, ((T48_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK48)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48) :=
  repsFix_of_siftB rK48 ⟨12, by decide⟩ T48_12 (by decide)

theorem hinj48_12 : Function.Injective
    (fun i => ((T48_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK48)) :=
  repsInj_of_reduceAux rK48 T48_12 (by decide)

theorem hcardT48_12 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK48 ⟨12, by decide⟩ R48 hpxR48 hcardq48 (by decide)).symm

/-- **Cell (48, 12).** -/
theorem cell48_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK48) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK48) (charOfVec rK48 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK48 e (h : Coordinate 1) T48_12 i :=
  species_entry_eq_sum rK48 ⟨12, by decide⟩ e heK h T48_12 hfix48_12 hinj48_12 hcardT48_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK48) (T48_12 i) (hfix48_12 i) h)

/-! ## Cell (48, 48): |T| = 25 -/

def T48_48list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0)]
def T48_48 : Fin 25 → Coordinate 1 := fun i => T48_48list.getD i.val (0,0,0,0,0)

theorem hfix48_48 : ∀ i, ((T48_48 i : Coordinate 1) : Coordinate 1 ⧸ reps rK48)
    ∈ fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48) :=
  repsFix_of_siftB rK48 ⟨48, by decide⟩ T48_48 (by decide)

theorem hinj48_48 : Function.Injective
    (fun i => ((T48_48 i : Coordinate 1) : Coordinate 1 ⧸ reps rK48)) :=
  repsInj_of_reduceAux rK48 T48_48 (by decide)

theorem hcardT48_48 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK48 ⟨48, by decide⟩ R48 hpxR48 hcardq48 (by decide)).symm

/-- **Cell (48, 48).** -/
theorem cell48_48 (e : List (ZMod 25)) (heK : charOK (basisAt rK48) e = true)
    (h : ↥(reps (⟨48, by decide⟩ : Fin 148))) :
    species (reps (⟨48, by decide⟩ : Fin 148)) h (basisElt (reps rK48) (charOfVec rK48 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK48 e (h : Coordinate 1) T48_48 i :=
  species_entry_eq_sum rK48 ⟨48, by decide⟩ e heK h T48_48 hfix48_48 hinj48_48 hcardT48_48
    (fun i => conj_mem_of_fixedPoints (reps ⟨48, by decide⟩) (reps rK48) (T48_48 i) (hfix48_48 i) h)

namespace Q2

def R48_2 : Fin 125 → Coordinate 2 := fun i => R48list.getD i.val (0,0,0,0,0)
theorem hpxR48_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK48) (R48_2 i)) := by decide
theorem hcardq48_2 : Nat.card (Coordinate 2 ⧸ reps rK48) = 125 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (48, 0) twin -/

def T48_0_2 : Fin 125 → Coordinate 2 := fun i => T48_0list.getD i.val (0,0,0,0,0)

theorem hfix48_0_2 : ∀ i, ((T48_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK48)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK48) :=
  repsFix_of_siftB2 rK48 ⟨0, by decide⟩ T48_0_2 (by decide)

theorem hinj48_0_2 : Function.Injective
    (fun i => ((T48_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK48)) :=
  repsInj_of_reduceAux2 rK48 T48_0_2 (by decide)

theorem hcardT48_0_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK48)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK48 ⟨0, by decide⟩ R48_2 hpxR48_2 hcardq48_2 (by decide)).symm

/-- **Cell (48, 0) twin (q=2).** -/
theorem cell48_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK48) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK48) (charOfVec2 rK48 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK48 e (h : Coordinate 2) T48_0_2 i :=
  species_entry_eq_sum rK48 ⟨0, by decide⟩ e heK h T48_0_2 hfix48_0_2 hinj48_0_2 hcardT48_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK48) (T48_0_2 i) (hfix48_0_2 i) h)

/-! ### Cell (48, 12) twin -/

def T48_12_2 : Fin 125 → Coordinate 2 := fun i => T48_12list.getD i.val (0,0,0,0,0)

theorem hfix48_12_2 : ∀ i, ((T48_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK48)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK48) :=
  repsFix_of_siftB2 rK48 ⟨12, by decide⟩ T48_12_2 (by decide)

theorem hinj48_12_2 : Function.Injective
    (fun i => ((T48_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK48)) :=
  repsInj_of_reduceAux2 rK48 T48_12_2 (by decide)

theorem hcardT48_12_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK48)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK48 ⟨12, by decide⟩ R48_2 hpxR48_2 hcardq48_2 (by decide)).symm

/-- **Cell (48, 12) twin (q=2).** -/
theorem cell48_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK48) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK48) (charOfVec2 rK48 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK48 e (h : Coordinate 2) T48_12_2 i :=
  species_entry_eq_sum rK48 ⟨12, by decide⟩ e heK h T48_12_2 hfix48_12_2 hinj48_12_2 hcardT48_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK48) (T48_12_2 i) (hfix48_12_2 i) h)

/-! ### Cell (48, 48) twin -/

def T48_48_2 : Fin 25 → Coordinate 2 := fun i => T48_48list.getD i.val (0,0,0,0,0)

theorem hfix48_48_2 : ∀ i, ((T48_48_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK48)
    ∈ fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK48) :=
  repsFix_of_siftB2 rK48 ⟨48, by decide⟩ T48_48_2 (by decide)

theorem hinj48_48_2 : Function.Injective
    (fun i => ((T48_48_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK48)) :=
  repsInj_of_reduceAux2 rK48 T48_48_2 (by decide)

theorem hcardT48_48_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK48)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK48 ⟨48, by decide⟩ R48_2 hpxR48_2 hcardq48_2 (by decide)).symm

/-- **Cell (48, 48) twin (q=2).** -/
theorem cell48_48_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK48) e = true)
    (h : ↥(reps (⟨48, by decide⟩ : Fin 148))) :
    species (reps (⟨48, by decide⟩ : Fin 148)) h (basisElt (reps rK48) (charOfVec2 rK48 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK48 e (h : Coordinate 2) T48_48_2 i :=
  species_entry_eq_sum rK48 ⟨48, by decide⟩ e heK h T48_48_2 hfix48_48_2 hinj48_48_2 hcardT48_48_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨48, by decide⟩) (reps rK48) (T48_48_2 i) (hfix48_48_2 i) h)

end Q2

end LeanDring.P5Presentation
