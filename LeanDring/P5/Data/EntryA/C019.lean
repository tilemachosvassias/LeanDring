/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, A-block data (rK = 31): certified per-cell species-entry instantiations, both twins.

Emit-embed-decide loop for order-25 A-block class `rK = 31` (`|G/K| = 125`).
All nonzero `H`-columns (`|gH| ≤ 2`, `t⁻¹Ht ⊆ K`).  Full 125-coset transversal
`R31` and each `H`-fixed sub-transversal `T31_rH` embedded as kernel data and
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

def rK31 : Fin 148 := ⟨31, by decide⟩

def R31list : List Coordinates := [(0,3,2,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0)]
def R31 : Fin 125 → Coordinate 1 := fun i => R31list.getD i.val (0,0,0,0,0)

theorem hpxR31 : Function.Injective (fun i => reduceAux 1 (basisAt rK31) (R31 i)) := by decide
theorem hcardq31 : Nat.card (Coordinate 1 ⧸ reps rK31) = 125 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (31, 0): |T| = 125 -/

def T31_0list : List Coordinates := [(0,3,2,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0)]
def T31_0 : Fin 125 → Coordinate 1 := fun i => T31_0list.getD i.val (0,0,0,0,0)

theorem hfix31_0 : ∀ i, ((T31_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK31)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31) :=
  repsFix_of_siftB rK31 ⟨0, by decide⟩ T31_0 (by decide)

theorem hinj31_0 : Function.Injective
    (fun i => ((T31_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK31)) :=
  repsInj_of_reduceAux rK31 T31_0 (by decide)

theorem hcardT31_0 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK31 ⟨0, by decide⟩ R31 hpxR31 hcardq31 (by decide)).symm

/-- **Cell (31, 0).** -/
theorem cell31_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK31) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK31) (charOfVec rK31 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK31 e (h : Coordinate 1) T31_0 i :=
  species_entry_eq_sum rK31 ⟨0, by decide⟩ e heK h T31_0 hfix31_0 hinj31_0 hcardT31_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK31) (T31_0 i) (hfix31_0 i) h)

/-! ## Cell (31, 12): |T| = 125 -/

def T31_12list : List Coordinates := [(0,3,2,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0)]
def T31_12 : Fin 125 → Coordinate 1 := fun i => T31_12list.getD i.val (0,0,0,0,0)

theorem hfix31_12 : ∀ i, ((T31_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK31)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31) :=
  repsFix_of_siftB rK31 ⟨12, by decide⟩ T31_12 (by decide)

theorem hinj31_12 : Function.Injective
    (fun i => ((T31_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK31)) :=
  repsInj_of_reduceAux rK31 T31_12 (by decide)

theorem hcardT31_12 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK31 ⟨12, by decide⟩ R31 hpxR31 hcardq31 (by decide)).symm

/-- **Cell (31, 12).** -/
theorem cell31_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK31) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK31) (charOfVec rK31 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK31 e (h : Coordinate 1) T31_12 i :=
  species_entry_eq_sum rK31 ⟨12, by decide⟩ e heK h T31_12 hfix31_12 hinj31_12 hcardT31_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK31) (T31_12 i) (hfix31_12 i) h)

/-! ## Cell (31, 31): |T| = 25 -/

def T31_31list : List Coordinates := [(0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0)]
def T31_31 : Fin 25 → Coordinate 1 := fun i => T31_31list.getD i.val (0,0,0,0,0)

theorem hfix31_31 : ∀ i, ((T31_31 i : Coordinate 1) : Coordinate 1 ⧸ reps rK31)
    ∈ fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31) :=
  repsFix_of_siftB rK31 ⟨31, by decide⟩ T31_31 (by decide)

theorem hinj31_31 : Function.Injective
    (fun i => ((T31_31 i : Coordinate 1) : Coordinate 1 ⧸ reps rK31)) :=
  repsInj_of_reduceAux rK31 T31_31 (by decide)

theorem hcardT31_31 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK31 ⟨31, by decide⟩ R31 hpxR31 hcardq31 (by decide)).symm

/-- **Cell (31, 31).** -/
theorem cell31_31 (e : List (ZMod 25)) (heK : charOK (basisAt rK31) e = true)
    (h : ↥(reps (⟨31, by decide⟩ : Fin 148))) :
    species (reps (⟨31, by decide⟩ : Fin 148)) h (basisElt (reps rK31) (charOfVec rK31 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK31 e (h : Coordinate 1) T31_31 i :=
  species_entry_eq_sum rK31 ⟨31, by decide⟩ e heK h T31_31 hfix31_31 hinj31_31 hcardT31_31
    (fun i => conj_mem_of_fixedPoints (reps ⟨31, by decide⟩) (reps rK31) (T31_31 i) (hfix31_31 i) h)

namespace Q2

def R31_2 : Fin 125 → Coordinate 2 := fun i => R31list.getD i.val (0,0,0,0,0)
theorem hpxR31_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK31) (R31_2 i)) := by decide
theorem hcardq31_2 : Nat.card (Coordinate 2 ⧸ reps rK31) = 125 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (31, 0) twin -/

def T31_0_2 : Fin 125 → Coordinate 2 := fun i => T31_0list.getD i.val (0,0,0,0,0)

theorem hfix31_0_2 : ∀ i, ((T31_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK31)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK31) :=
  repsFix_of_siftB2 rK31 ⟨0, by decide⟩ T31_0_2 (by decide)

theorem hinj31_0_2 : Function.Injective
    (fun i => ((T31_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK31)) :=
  repsInj_of_reduceAux2 rK31 T31_0_2 (by decide)

theorem hcardT31_0_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK31)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK31 ⟨0, by decide⟩ R31_2 hpxR31_2 hcardq31_2 (by decide)).symm

/-- **Cell (31, 0) twin (q=2).** -/
theorem cell31_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK31) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK31) (charOfVec2 rK31 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK31 e (h : Coordinate 2) T31_0_2 i :=
  species_entry_eq_sum rK31 ⟨0, by decide⟩ e heK h T31_0_2 hfix31_0_2 hinj31_0_2 hcardT31_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK31) (T31_0_2 i) (hfix31_0_2 i) h)

/-! ### Cell (31, 12) twin -/

def T31_12_2 : Fin 125 → Coordinate 2 := fun i => T31_12list.getD i.val (0,0,0,0,0)

theorem hfix31_12_2 : ∀ i, ((T31_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK31)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK31) :=
  repsFix_of_siftB2 rK31 ⟨12, by decide⟩ T31_12_2 (by decide)

theorem hinj31_12_2 : Function.Injective
    (fun i => ((T31_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK31)) :=
  repsInj_of_reduceAux2 rK31 T31_12_2 (by decide)

theorem hcardT31_12_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK31)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK31 ⟨12, by decide⟩ R31_2 hpxR31_2 hcardq31_2 (by decide)).symm

/-- **Cell (31, 12) twin (q=2).** -/
theorem cell31_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK31) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK31) (charOfVec2 rK31 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK31 e (h : Coordinate 2) T31_12_2 i :=
  species_entry_eq_sum rK31 ⟨12, by decide⟩ e heK h T31_12_2 hfix31_12_2 hinj31_12_2 hcardT31_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK31) (T31_12_2 i) (hfix31_12_2 i) h)

/-! ### Cell (31, 31) twin -/

def T31_31_2 : Fin 25 → Coordinate 2 := fun i => T31_31list.getD i.val (0,0,0,0,0)

theorem hfix31_31_2 : ∀ i, ((T31_31_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK31)
    ∈ fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK31) :=
  repsFix_of_siftB2 rK31 ⟨31, by decide⟩ T31_31_2 (by decide)

theorem hinj31_31_2 : Function.Injective
    (fun i => ((T31_31_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK31)) :=
  repsInj_of_reduceAux2 rK31 T31_31_2 (by decide)

theorem hcardT31_31_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK31)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK31 ⟨31, by decide⟩ R31_2 hpxR31_2 hcardq31_2 (by decide)).symm

/-- **Cell (31, 31) twin (q=2).** -/
theorem cell31_31_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK31) e = true)
    (h : ↥(reps (⟨31, by decide⟩ : Fin 148))) :
    species (reps (⟨31, by decide⟩ : Fin 148)) h (basisElt (reps rK31) (charOfVec2 rK31 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK31 e (h : Coordinate 2) T31_31_2 i :=
  species_entry_eq_sum rK31 ⟨31, by decide⟩ e heK h T31_31_2 hfix31_31_2 hinj31_31_2 hcardT31_31_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨31, by decide⟩) (reps rK31) (T31_31_2 i) (hfix31_31_2 i) h)

end Q2

end LeanDring.P5Presentation
