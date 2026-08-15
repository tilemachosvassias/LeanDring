/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, A-block data (rK = 50): certified per-cell species-entry instantiations, both twins.

Emit-embed-decide loop for order-25 A-block class `rK = 50` (`|G/K| = 125`).
All nonzero `H`-columns (`|gH| ≤ 2`, `t⁻¹Ht ⊆ K`).  Full 125-coset transversal
`R50` and each `H`-fixed sub-transversal `T50_rH` embedded as kernel data and
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

def rK50 : Fin 148 := ⟨50, by decide⟩

def R50list : List Coordinates := [(0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,4,0,0)]
def R50 : Fin 125 → Coordinate 1 := fun i => R50list.getD i.val (0,0,0,0,0)

theorem hpxR50 : Function.Injective (fun i => reduceAux 1 (basisAt rK50) (R50 i)) := by decide
theorem hcardq50 : Nat.card (Coordinate 1 ⧸ reps rK50) = 125 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (50, 0): |T| = 125 -/

def T50_0list : List Coordinates := [(0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,4,0,0)]
def T50_0 : Fin 125 → Coordinate 1 := fun i => T50_0list.getD i.val (0,0,0,0,0)

theorem hfix50_0 : ∀ i, ((T50_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK50)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50) :=
  repsFix_of_siftB rK50 ⟨0, by decide⟩ T50_0 (by decide)

theorem hinj50_0 : Function.Injective
    (fun i => ((T50_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK50)) :=
  repsInj_of_reduceAux rK50 T50_0 (by decide)

theorem hcardT50_0 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK50 ⟨0, by decide⟩ R50 hpxR50 hcardq50 (by decide)).symm

/-- **Cell (50, 0).** -/
theorem cell50_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK50) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK50) (charOfVec rK50 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK50 e (h : Coordinate 1) T50_0 i :=
  species_entry_eq_sum rK50 ⟨0, by decide⟩ e heK h T50_0 hfix50_0 hinj50_0 hcardT50_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK50) (T50_0 i) (hfix50_0 i) h)

/-! ## Cell (50, 12): |T| = 125 -/

def T50_12list : List Coordinates := [(0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,4,0,0)]
def T50_12 : Fin 125 → Coordinate 1 := fun i => T50_12list.getD i.val (0,0,0,0,0)

theorem hfix50_12 : ∀ i, ((T50_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK50)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50) :=
  repsFix_of_siftB rK50 ⟨12, by decide⟩ T50_12 (by decide)

theorem hinj50_12 : Function.Injective
    (fun i => ((T50_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK50)) :=
  repsInj_of_reduceAux rK50 T50_12 (by decide)

theorem hcardT50_12 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK50 ⟨12, by decide⟩ R50 hpxR50 hcardq50 (by decide)).symm

/-- **Cell (50, 12).** -/
theorem cell50_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK50) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK50) (charOfVec rK50 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK50 e (h : Coordinate 1) T50_12 i :=
  species_entry_eq_sum rK50 ⟨12, by decide⟩ e heK h T50_12 hfix50_12 hinj50_12 hcardT50_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK50) (T50_12 i) (hfix50_12 i) h)

/-! ## Cell (50, 50): |T| = 25 -/

def T50_50list : List Coordinates := [(0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0)]
def T50_50 : Fin 25 → Coordinate 1 := fun i => T50_50list.getD i.val (0,0,0,0,0)

theorem hfix50_50 : ∀ i, ((T50_50 i : Coordinate 1) : Coordinate 1 ⧸ reps rK50)
    ∈ fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50) :=
  repsFix_of_siftB rK50 ⟨50, by decide⟩ T50_50 (by decide)

theorem hinj50_50 : Function.Injective
    (fun i => ((T50_50 i : Coordinate 1) : Coordinate 1 ⧸ reps rK50)) :=
  repsInj_of_reduceAux rK50 T50_50 (by decide)

theorem hcardT50_50 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK50 ⟨50, by decide⟩ R50 hpxR50 hcardq50 (by decide)).symm

/-- **Cell (50, 50).** -/
theorem cell50_50 (e : List (ZMod 25)) (heK : charOK (basisAt rK50) e = true)
    (h : ↥(reps (⟨50, by decide⟩ : Fin 148))) :
    species (reps (⟨50, by decide⟩ : Fin 148)) h (basisElt (reps rK50) (charOfVec rK50 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK50 e (h : Coordinate 1) T50_50 i :=
  species_entry_eq_sum rK50 ⟨50, by decide⟩ e heK h T50_50 hfix50_50 hinj50_50 hcardT50_50
    (fun i => conj_mem_of_fixedPoints (reps ⟨50, by decide⟩) (reps rK50) (T50_50 i) (hfix50_50 i) h)

namespace Q2

def R50_2 : Fin 125 → Coordinate 2 := fun i => R50list.getD i.val (0,0,0,0,0)
theorem hpxR50_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK50) (R50_2 i)) := by decide
theorem hcardq50_2 : Nat.card (Coordinate 2 ⧸ reps rK50) = 125 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (50, 0) twin -/

def T50_0_2 : Fin 125 → Coordinate 2 := fun i => T50_0list.getD i.val (0,0,0,0,0)

theorem hfix50_0_2 : ∀ i, ((T50_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK50)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK50) :=
  repsFix_of_siftB2 rK50 ⟨0, by decide⟩ T50_0_2 (by decide)

theorem hinj50_0_2 : Function.Injective
    (fun i => ((T50_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK50)) :=
  repsInj_of_reduceAux2 rK50 T50_0_2 (by decide)

theorem hcardT50_0_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK50)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK50 ⟨0, by decide⟩ R50_2 hpxR50_2 hcardq50_2 (by decide)).symm

/-- **Cell (50, 0) twin (q=2).** -/
theorem cell50_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK50) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK50) (charOfVec2 rK50 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK50 e (h : Coordinate 2) T50_0_2 i :=
  species_entry_eq_sum rK50 ⟨0, by decide⟩ e heK h T50_0_2 hfix50_0_2 hinj50_0_2 hcardT50_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK50) (T50_0_2 i) (hfix50_0_2 i) h)

/-! ### Cell (50, 12) twin -/

def T50_12_2 : Fin 125 → Coordinate 2 := fun i => T50_12list.getD i.val (0,0,0,0,0)

theorem hfix50_12_2 : ∀ i, ((T50_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK50)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK50) :=
  repsFix_of_siftB2 rK50 ⟨12, by decide⟩ T50_12_2 (by decide)

theorem hinj50_12_2 : Function.Injective
    (fun i => ((T50_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK50)) :=
  repsInj_of_reduceAux2 rK50 T50_12_2 (by decide)

theorem hcardT50_12_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK50)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK50 ⟨12, by decide⟩ R50_2 hpxR50_2 hcardq50_2 (by decide)).symm

/-- **Cell (50, 12) twin (q=2).** -/
theorem cell50_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK50) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK50) (charOfVec2 rK50 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK50 e (h : Coordinate 2) T50_12_2 i :=
  species_entry_eq_sum rK50 ⟨12, by decide⟩ e heK h T50_12_2 hfix50_12_2 hinj50_12_2 hcardT50_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK50) (T50_12_2 i) (hfix50_12_2 i) h)

/-! ### Cell (50, 50) twin -/

def T50_50_2 : Fin 25 → Coordinate 2 := fun i => T50_50list.getD i.val (0,0,0,0,0)

theorem hfix50_50_2 : ∀ i, ((T50_50_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK50)
    ∈ fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK50) :=
  repsFix_of_siftB2 rK50 ⟨50, by decide⟩ T50_50_2 (by decide)

theorem hinj50_50_2 : Function.Injective
    (fun i => ((T50_50_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK50)) :=
  repsInj_of_reduceAux2 rK50 T50_50_2 (by decide)

theorem hcardT50_50_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK50)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK50 ⟨50, by decide⟩ R50_2 hpxR50_2 hcardq50_2 (by decide)).symm

/-- **Cell (50, 50) twin (q=2).** -/
theorem cell50_50_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK50) e = true)
    (h : ↥(reps (⟨50, by decide⟩ : Fin 148))) :
    species (reps (⟨50, by decide⟩ : Fin 148)) h (basisElt (reps rK50) (charOfVec2 rK50 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK50 e (h : Coordinate 2) T50_50_2 i :=
  species_entry_eq_sum rK50 ⟨50, by decide⟩ e heK h T50_50_2 hfix50_50_2 hinj50_50_2 hcardT50_50_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨50, by decide⟩) (reps rK50) (T50_50_2 i) (hfix50_50_2 i) h)

end Q2

end LeanDring.P5Presentation
