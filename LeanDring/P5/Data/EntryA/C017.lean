/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, A-block data (rK = 29): certified per-cell species-entry instantiations, both twins.

Emit-embed-decide loop for order-25 A-block class `rK = 29` (`|G/K| = 125`).
All nonzero `H`-columns (`|gH| ≤ 2`, `t⁻¹Ht ⊆ K`).  Full 125-coset transversal
`R29` and each `H`-fixed sub-transversal `T29_rH` embedded as kernel data and
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

def rK29 : Fin 148 := ⟨29, by decide⟩

def R29list : List Coordinates := [(0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0)]
def R29 : Fin 125 → Coordinate 1 := fun i => R29list.getD i.val (0,0,0,0,0)

theorem hpxR29 : Function.Injective (fun i => reduceAux 1 (basisAt rK29) (R29 i)) := by decide
theorem hcardq29 : Nat.card (Coordinate 1 ⧸ reps rK29) = 125 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (29, 0): |T| = 125 -/

def T29_0list : List Coordinates := [(0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0)]
def T29_0 : Fin 125 → Coordinate 1 := fun i => T29_0list.getD i.val (0,0,0,0,0)

theorem hfix29_0 : ∀ i, ((T29_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK29)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29) :=
  repsFix_of_siftB rK29 ⟨0, by decide⟩ T29_0 (by decide)

theorem hinj29_0 : Function.Injective
    (fun i => ((T29_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK29)) :=
  repsInj_of_reduceAux rK29 T29_0 (by decide)

theorem hcardT29_0 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK29 ⟨0, by decide⟩ R29 hpxR29 hcardq29 (by decide)).symm

/-- **Cell (29, 0).** -/
theorem cell29_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK29) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK29) (charOfVec rK29 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK29 e (h : Coordinate 1) T29_0 i :=
  species_entry_eq_sum rK29 ⟨0, by decide⟩ e heK h T29_0 hfix29_0 hinj29_0 hcardT29_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK29) (T29_0 i) (hfix29_0 i) h)

/-! ## Cell (29, 12): |T| = 125 -/

def T29_12list : List Coordinates := [(0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0)]
def T29_12 : Fin 125 → Coordinate 1 := fun i => T29_12list.getD i.val (0,0,0,0,0)

theorem hfix29_12 : ∀ i, ((T29_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK29)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29) :=
  repsFix_of_siftB rK29 ⟨12, by decide⟩ T29_12 (by decide)

theorem hinj29_12 : Function.Injective
    (fun i => ((T29_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK29)) :=
  repsInj_of_reduceAux rK29 T29_12 (by decide)

theorem hcardT29_12 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK29 ⟨12, by decide⟩ R29 hpxR29 hcardq29 (by decide)).symm

/-- **Cell (29, 12).** -/
theorem cell29_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK29) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK29) (charOfVec rK29 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK29 e (h : Coordinate 1) T29_12 i :=
  species_entry_eq_sum rK29 ⟨12, by decide⟩ e heK h T29_12 hfix29_12 hinj29_12 hcardT29_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK29) (T29_12 i) (hfix29_12 i) h)

/-! ## Cell (29, 29): |T| = 25 -/

def T29_29list : List Coordinates := [(0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0)]
def T29_29 : Fin 25 → Coordinate 1 := fun i => T29_29list.getD i.val (0,0,0,0,0)

theorem hfix29_29 : ∀ i, ((T29_29 i : Coordinate 1) : Coordinate 1 ⧸ reps rK29)
    ∈ fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29) :=
  repsFix_of_siftB rK29 ⟨29, by decide⟩ T29_29 (by decide)

theorem hinj29_29 : Function.Injective
    (fun i => ((T29_29 i : Coordinate 1) : Coordinate 1 ⧸ reps rK29)) :=
  repsInj_of_reduceAux rK29 T29_29 (by decide)

theorem hcardT29_29 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK29 ⟨29, by decide⟩ R29 hpxR29 hcardq29 (by decide)).symm

/-- **Cell (29, 29).** -/
theorem cell29_29 (e : List (ZMod 25)) (heK : charOK (basisAt rK29) e = true)
    (h : ↥(reps (⟨29, by decide⟩ : Fin 148))) :
    species (reps (⟨29, by decide⟩ : Fin 148)) h (basisElt (reps rK29) (charOfVec rK29 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK29 e (h : Coordinate 1) T29_29 i :=
  species_entry_eq_sum rK29 ⟨29, by decide⟩ e heK h T29_29 hfix29_29 hinj29_29 hcardT29_29
    (fun i => conj_mem_of_fixedPoints (reps ⟨29, by decide⟩) (reps rK29) (T29_29 i) (hfix29_29 i) h)

namespace Q2

def R29_2 : Fin 125 → Coordinate 2 := fun i => R29list.getD i.val (0,0,0,0,0)
theorem hpxR29_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK29) (R29_2 i)) := by decide
theorem hcardq29_2 : Nat.card (Coordinate 2 ⧸ reps rK29) = 125 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (29, 0) twin -/

def T29_0_2 : Fin 125 → Coordinate 2 := fun i => T29_0list.getD i.val (0,0,0,0,0)

theorem hfix29_0_2 : ∀ i, ((T29_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK29)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK29) :=
  repsFix_of_siftB2 rK29 ⟨0, by decide⟩ T29_0_2 (by decide)

theorem hinj29_0_2 : Function.Injective
    (fun i => ((T29_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK29)) :=
  repsInj_of_reduceAux2 rK29 T29_0_2 (by decide)

theorem hcardT29_0_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK29)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK29 ⟨0, by decide⟩ R29_2 hpxR29_2 hcardq29_2 (by decide)).symm

/-- **Cell (29, 0) twin (q=2).** -/
theorem cell29_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK29) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK29) (charOfVec2 rK29 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK29 e (h : Coordinate 2) T29_0_2 i :=
  species_entry_eq_sum rK29 ⟨0, by decide⟩ e heK h T29_0_2 hfix29_0_2 hinj29_0_2 hcardT29_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK29) (T29_0_2 i) (hfix29_0_2 i) h)

/-! ### Cell (29, 12) twin -/

def T29_12_2 : Fin 125 → Coordinate 2 := fun i => T29_12list.getD i.val (0,0,0,0,0)

theorem hfix29_12_2 : ∀ i, ((T29_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK29)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK29) :=
  repsFix_of_siftB2 rK29 ⟨12, by decide⟩ T29_12_2 (by decide)

theorem hinj29_12_2 : Function.Injective
    (fun i => ((T29_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK29)) :=
  repsInj_of_reduceAux2 rK29 T29_12_2 (by decide)

theorem hcardT29_12_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK29)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK29 ⟨12, by decide⟩ R29_2 hpxR29_2 hcardq29_2 (by decide)).symm

/-- **Cell (29, 12) twin (q=2).** -/
theorem cell29_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK29) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK29) (charOfVec2 rK29 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK29 e (h : Coordinate 2) T29_12_2 i :=
  species_entry_eq_sum rK29 ⟨12, by decide⟩ e heK h T29_12_2 hfix29_12_2 hinj29_12_2 hcardT29_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK29) (T29_12_2 i) (hfix29_12_2 i) h)

/-! ### Cell (29, 29) twin -/

def T29_29_2 : Fin 25 → Coordinate 2 := fun i => T29_29list.getD i.val (0,0,0,0,0)

theorem hfix29_29_2 : ∀ i, ((T29_29_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK29)
    ∈ fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK29) :=
  repsFix_of_siftB2 rK29 ⟨29, by decide⟩ T29_29_2 (by decide)

theorem hinj29_29_2 : Function.Injective
    (fun i => ((T29_29_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK29)) :=
  repsInj_of_reduceAux2 rK29 T29_29_2 (by decide)

theorem hcardT29_29_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK29)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK29 ⟨29, by decide⟩ R29_2 hpxR29_2 hcardq29_2 (by decide)).symm

/-- **Cell (29, 29) twin (q=2).** -/
theorem cell29_29_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK29) e = true)
    (h : ↥(reps (⟨29, by decide⟩ : Fin 148))) :
    species (reps (⟨29, by decide⟩ : Fin 148)) h (basisElt (reps rK29) (charOfVec2 rK29 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK29 e (h : Coordinate 2) T29_29_2 i :=
  species_entry_eq_sum rK29 ⟨29, by decide⟩ e heK h T29_29_2 hfix29_29_2 hinj29_29_2 hcardT29_29_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨29, by decide⟩) (reps rK29) (T29_29_2 i) (hfix29_29_2 i) h)

end Q2

end LeanDring.P5Presentation
