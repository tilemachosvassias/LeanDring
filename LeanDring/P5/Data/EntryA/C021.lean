/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, A-block data (rK = 33): certified per-cell species-entry instantiations, both twins.

Emit-embed-decide loop for order-25 A-block class `rK = 33` (`|G/K| = 125`).
All nonzero `H`-columns (`|gH| ≤ 2`, `t⁻¹Ht ⊆ K`).  Full 125-coset transversal
`R33` and each `H`-fixed sub-transversal `T33_rH` embedded as kernel data and
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

def rK33 : Fin 148 := ⟨33, by decide⟩

def R33list : List Coordinates := [(0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (1,0,2,4,0), (1,0,2,0,0), (1,0,2,1,0), (1,0,2,2,0), (1,0,2,3,0), (1,0,3,4,0), (1,0,3,0,0), (1,0,3,1,0), (1,0,3,2,0), (1,0,3,3,0), (1,0,4,4,0), (1,0,4,0,0), (1,0,4,1,0), (1,0,4,2,0), (1,0,4,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,0,1,4,0), (1,0,1,0,0), (1,0,1,1,0), (1,0,1,2,0), (1,0,1,3,0), (2,0,2,4,0), (2,0,2,0,0), (2,0,2,1,0), (2,0,2,2,0), (2,0,2,3,0), (2,0,3,4,0), (2,0,3,0,0), (2,0,3,1,0), (2,0,3,2,0), (2,0,3,3,0), (2,0,4,4,0), (2,0,4,0,0), (2,0,4,1,0), (2,0,4,2,0), (2,0,4,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,0,1,4,0), (2,0,1,0,0), (2,0,1,1,0), (2,0,1,2,0), (2,0,1,3,0), (3,0,2,4,0), (3,0,2,0,0), (3,0,2,1,0), (3,0,2,2,0), (3,0,2,3,0), (3,0,3,4,0), (3,0,3,0,0), (3,0,3,1,0), (3,0,3,2,0), (3,0,3,3,0), (3,0,4,4,0), (3,0,4,0,0), (3,0,4,1,0), (3,0,4,2,0), (3,0,4,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,0,1,4,0), (3,0,1,0,0), (3,0,1,1,0), (3,0,1,2,0), (3,0,1,3,0), (4,0,2,4,0), (4,0,2,0,0), (4,0,2,1,0), (4,0,2,2,0), (4,0,2,3,0), (4,0,3,4,0), (4,0,3,0,0), (4,0,3,1,0), (4,0,3,2,0), (4,0,3,3,0), (4,0,4,4,0), (4,0,4,0,0), (4,0,4,1,0), (4,0,4,2,0), (4,0,4,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,0,1,4,0), (4,0,1,0,0), (4,0,1,1,0), (4,0,1,2,0), (4,0,1,3,0)]
def R33 : Fin 125 → Coordinate 1 := fun i => R33list.getD i.val (0,0,0,0,0)

theorem hpxR33 : Function.Injective (fun i => reduceAux 1 (basisAt rK33) (R33 i)) := by decide
theorem hcardq33 : Nat.card (Coordinate 1 ⧸ reps rK33) = 125 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (33, 0): |T| = 125 -/

def T33_0list : List Coordinates := [(0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (1,0,2,4,0), (1,0,2,0,0), (1,0,2,1,0), (1,0,2,2,0), (1,0,2,3,0), (1,0,3,4,0), (1,0,3,0,0), (1,0,3,1,0), (1,0,3,2,0), (1,0,3,3,0), (1,0,4,4,0), (1,0,4,0,0), (1,0,4,1,0), (1,0,4,2,0), (1,0,4,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,0,1,4,0), (1,0,1,0,0), (1,0,1,1,0), (1,0,1,2,0), (1,0,1,3,0), (2,0,2,4,0), (2,0,2,0,0), (2,0,2,1,0), (2,0,2,2,0), (2,0,2,3,0), (2,0,3,4,0), (2,0,3,0,0), (2,0,3,1,0), (2,0,3,2,0), (2,0,3,3,0), (2,0,4,4,0), (2,0,4,0,0), (2,0,4,1,0), (2,0,4,2,0), (2,0,4,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,0,1,4,0), (2,0,1,0,0), (2,0,1,1,0), (2,0,1,2,0), (2,0,1,3,0), (3,0,2,4,0), (3,0,2,0,0), (3,0,2,1,0), (3,0,2,2,0), (3,0,2,3,0), (3,0,3,4,0), (3,0,3,0,0), (3,0,3,1,0), (3,0,3,2,0), (3,0,3,3,0), (3,0,4,4,0), (3,0,4,0,0), (3,0,4,1,0), (3,0,4,2,0), (3,0,4,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,0,1,4,0), (3,0,1,0,0), (3,0,1,1,0), (3,0,1,2,0), (3,0,1,3,0), (4,0,2,4,0), (4,0,2,0,0), (4,0,2,1,0), (4,0,2,2,0), (4,0,2,3,0), (4,0,3,4,0), (4,0,3,0,0), (4,0,3,1,0), (4,0,3,2,0), (4,0,3,3,0), (4,0,4,4,0), (4,0,4,0,0), (4,0,4,1,0), (4,0,4,2,0), (4,0,4,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,0,1,4,0), (4,0,1,0,0), (4,0,1,1,0), (4,0,1,2,0), (4,0,1,3,0)]
def T33_0 : Fin 125 → Coordinate 1 := fun i => T33_0list.getD i.val (0,0,0,0,0)

theorem hfix33_0 : ∀ i, ((T33_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK33)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33) :=
  repsFix_of_siftB rK33 ⟨0, by decide⟩ T33_0 (by decide)

theorem hinj33_0 : Function.Injective
    (fun i => ((T33_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK33)) :=
  repsInj_of_reduceAux rK33 T33_0 (by decide)

theorem hcardT33_0 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK33 ⟨0, by decide⟩ R33 hpxR33 hcardq33 (by decide)).symm

/-- **Cell (33, 0).** -/
theorem cell33_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK33) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK33) (charOfVec rK33 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK33 e (h : Coordinate 1) T33_0 i :=
  species_entry_eq_sum rK33 ⟨0, by decide⟩ e heK h T33_0 hfix33_0 hinj33_0 hcardT33_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK33) (T33_0 i) (hfix33_0 i) h)

/-! ## Cell (33, 12): |T| = 125 -/

def T33_12list : List Coordinates := [(0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (1,0,2,4,0), (1,0,2,0,0), (1,0,2,1,0), (1,0,2,2,0), (1,0,2,3,0), (1,0,3,4,0), (1,0,3,0,0), (1,0,3,1,0), (1,0,3,2,0), (1,0,3,3,0), (1,0,4,4,0), (1,0,4,0,0), (1,0,4,1,0), (1,0,4,2,0), (1,0,4,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,0,1,4,0), (1,0,1,0,0), (1,0,1,1,0), (1,0,1,2,0), (1,0,1,3,0), (2,0,2,4,0), (2,0,2,0,0), (2,0,2,1,0), (2,0,2,2,0), (2,0,2,3,0), (2,0,3,4,0), (2,0,3,0,0), (2,0,3,1,0), (2,0,3,2,0), (2,0,3,3,0), (2,0,4,4,0), (2,0,4,0,0), (2,0,4,1,0), (2,0,4,2,0), (2,0,4,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,0,1,4,0), (2,0,1,0,0), (2,0,1,1,0), (2,0,1,2,0), (2,0,1,3,0), (3,0,2,4,0), (3,0,2,0,0), (3,0,2,1,0), (3,0,2,2,0), (3,0,2,3,0), (3,0,3,4,0), (3,0,3,0,0), (3,0,3,1,0), (3,0,3,2,0), (3,0,3,3,0), (3,0,4,4,0), (3,0,4,0,0), (3,0,4,1,0), (3,0,4,2,0), (3,0,4,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,0,1,4,0), (3,0,1,0,0), (3,0,1,1,0), (3,0,1,2,0), (3,0,1,3,0), (4,0,2,4,0), (4,0,2,0,0), (4,0,2,1,0), (4,0,2,2,0), (4,0,2,3,0), (4,0,3,4,0), (4,0,3,0,0), (4,0,3,1,0), (4,0,3,2,0), (4,0,3,3,0), (4,0,4,4,0), (4,0,4,0,0), (4,0,4,1,0), (4,0,4,2,0), (4,0,4,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,0,1,4,0), (4,0,1,0,0), (4,0,1,1,0), (4,0,1,2,0), (4,0,1,3,0)]
def T33_12 : Fin 125 → Coordinate 1 := fun i => T33_12list.getD i.val (0,0,0,0,0)

theorem hfix33_12 : ∀ i, ((T33_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK33)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33) :=
  repsFix_of_siftB rK33 ⟨12, by decide⟩ T33_12 (by decide)

theorem hinj33_12 : Function.Injective
    (fun i => ((T33_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK33)) :=
  repsInj_of_reduceAux rK33 T33_12 (by decide)

theorem hcardT33_12 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK33 ⟨12, by decide⟩ R33 hpxR33 hcardq33 (by decide)).symm

/-- **Cell (33, 12).** -/
theorem cell33_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK33) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK33) (charOfVec rK33 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK33 e (h : Coordinate 1) T33_12 i :=
  species_entry_eq_sum rK33 ⟨12, by decide⟩ e heK h T33_12 hfix33_12 hinj33_12 hcardT33_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK33) (T33_12 i) (hfix33_12 i) h)

/-! ## Cell (33, 33): |T| = 25 -/

def T33_33list : List Coordinates := [(0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0)]
def T33_33 : Fin 25 → Coordinate 1 := fun i => T33_33list.getD i.val (0,0,0,0,0)

theorem hfix33_33 : ∀ i, ((T33_33 i : Coordinate 1) : Coordinate 1 ⧸ reps rK33)
    ∈ fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33) :=
  repsFix_of_siftB rK33 ⟨33, by decide⟩ T33_33 (by decide)

theorem hinj33_33 : Function.Injective
    (fun i => ((T33_33 i : Coordinate 1) : Coordinate 1 ⧸ reps rK33)) :=
  repsInj_of_reduceAux rK33 T33_33 (by decide)

theorem hcardT33_33 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK33 ⟨33, by decide⟩ R33 hpxR33 hcardq33 (by decide)).symm

/-- **Cell (33, 33).** -/
theorem cell33_33 (e : List (ZMod 25)) (heK : charOK (basisAt rK33) e = true)
    (h : ↥(reps (⟨33, by decide⟩ : Fin 148))) :
    species (reps (⟨33, by decide⟩ : Fin 148)) h (basisElt (reps rK33) (charOfVec rK33 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK33 e (h : Coordinate 1) T33_33 i :=
  species_entry_eq_sum rK33 ⟨33, by decide⟩ e heK h T33_33 hfix33_33 hinj33_33 hcardT33_33
    (fun i => conj_mem_of_fixedPoints (reps ⟨33, by decide⟩) (reps rK33) (T33_33 i) (hfix33_33 i) h)

namespace Q2

def R33_2 : Fin 125 → Coordinate 2 := fun i => R33list.getD i.val (0,0,0,0,0)
theorem hpxR33_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK33) (R33_2 i)) := by decide
theorem hcardq33_2 : Nat.card (Coordinate 2 ⧸ reps rK33) = 125 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (33, 0) twin -/

def T33_0_2 : Fin 125 → Coordinate 2 := fun i => T33_0list.getD i.val (0,0,0,0,0)

theorem hfix33_0_2 : ∀ i, ((T33_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK33)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK33) :=
  repsFix_of_siftB2 rK33 ⟨0, by decide⟩ T33_0_2 (by decide)

theorem hinj33_0_2 : Function.Injective
    (fun i => ((T33_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK33)) :=
  repsInj_of_reduceAux2 rK33 T33_0_2 (by decide)

theorem hcardT33_0_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK33)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK33 ⟨0, by decide⟩ R33_2 hpxR33_2 hcardq33_2 (by decide)).symm

/-- **Cell (33, 0) twin (q=2).** -/
theorem cell33_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK33) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK33) (charOfVec2 rK33 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK33 e (h : Coordinate 2) T33_0_2 i :=
  species_entry_eq_sum rK33 ⟨0, by decide⟩ e heK h T33_0_2 hfix33_0_2 hinj33_0_2 hcardT33_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK33) (T33_0_2 i) (hfix33_0_2 i) h)

/-! ### Cell (33, 12) twin -/

def T33_12_2 : Fin 125 → Coordinate 2 := fun i => T33_12list.getD i.val (0,0,0,0,0)

theorem hfix33_12_2 : ∀ i, ((T33_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK33)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK33) :=
  repsFix_of_siftB2 rK33 ⟨12, by decide⟩ T33_12_2 (by decide)

theorem hinj33_12_2 : Function.Injective
    (fun i => ((T33_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK33)) :=
  repsInj_of_reduceAux2 rK33 T33_12_2 (by decide)

theorem hcardT33_12_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK33)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK33 ⟨12, by decide⟩ R33_2 hpxR33_2 hcardq33_2 (by decide)).symm

/-- **Cell (33, 12) twin (q=2).** -/
theorem cell33_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK33) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK33) (charOfVec2 rK33 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK33 e (h : Coordinate 2) T33_12_2 i :=
  species_entry_eq_sum rK33 ⟨12, by decide⟩ e heK h T33_12_2 hfix33_12_2 hinj33_12_2 hcardT33_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK33) (T33_12_2 i) (hfix33_12_2 i) h)

/-! ### Cell (33, 33) twin -/

def T33_33_2 : Fin 25 → Coordinate 2 := fun i => T33_33list.getD i.val (0,0,0,0,0)

theorem hfix33_33_2 : ∀ i, ((T33_33_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK33)
    ∈ fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK33) :=
  repsFix_of_siftB2 rK33 ⟨33, by decide⟩ T33_33_2 (by decide)

theorem hinj33_33_2 : Function.Injective
    (fun i => ((T33_33_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK33)) :=
  repsInj_of_reduceAux2 rK33 T33_33_2 (by decide)

theorem hcardT33_33_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK33)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK33 ⟨33, by decide⟩ R33_2 hpxR33_2 hcardq33_2 (by decide)).symm

/-- **Cell (33, 33) twin (q=2).** -/
theorem cell33_33_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK33) e = true)
    (h : ↥(reps (⟨33, by decide⟩ : Fin 148))) :
    species (reps (⟨33, by decide⟩ : Fin 148)) h (basisElt (reps rK33) (charOfVec2 rK33 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK33 e (h : Coordinate 2) T33_33_2 i :=
  species_entry_eq_sum rK33 ⟨33, by decide⟩ e heK h T33_33_2 hfix33_33_2 hinj33_33_2 hcardT33_33_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨33, by decide⟩) (reps rK33) (T33_33_2 i) (hfix33_33_2 i) h)

end Q2

end LeanDring.P5Presentation
