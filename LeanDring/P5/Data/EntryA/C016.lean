/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, A-block data (rK = 28): certified per-cell species-entry instantiations, both twins.

Emit-embed-decide loop for order-25 A-block class `rK = 28` (`|G/K| = 125`).
All nonzero `H`-columns (`|gH| ≤ 2`, `t⁻¹Ht ⊆ K`).  Full 125-coset transversal
`R28` and each `H`-fixed sub-transversal `T28_rH` embedded as kernel data and
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

def rK28 : Fin 148 := ⟨28, by decide⟩

def R28list : List Coordinates := [(0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (1,0,4,4,0), (1,0,4,0,0), (1,0,4,1,0), (1,0,4,2,0), (1,0,4,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,0,1,4,0), (1,0,1,0,0), (1,0,1,1,0), (1,0,1,2,0), (1,0,1,3,0), (1,0,2,4,0), (1,0,2,0,0), (1,0,2,1,0), (1,0,2,2,0), (1,0,2,3,0), (1,0,3,4,0), (1,0,3,0,0), (1,0,3,1,0), (1,0,3,2,0), (1,0,3,3,0), (2,0,4,4,0), (2,0,4,0,0), (2,0,4,1,0), (2,0,4,2,0), (2,0,4,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,0,1,4,0), (2,0,1,0,0), (2,0,1,1,0), (2,0,1,2,0), (2,0,1,3,0), (2,0,2,4,0), (2,0,2,0,0), (2,0,2,1,0), (2,0,2,2,0), (2,0,2,3,0), (2,0,3,4,0), (2,0,3,0,0), (2,0,3,1,0), (2,0,3,2,0), (2,0,3,3,0), (3,0,4,4,0), (3,0,4,0,0), (3,0,4,1,0), (3,0,4,2,0), (3,0,4,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,0,1,4,0), (3,0,1,0,0), (3,0,1,1,0), (3,0,1,2,0), (3,0,1,3,0), (3,0,2,4,0), (3,0,2,0,0), (3,0,2,1,0), (3,0,2,2,0), (3,0,2,3,0), (3,0,3,4,0), (3,0,3,0,0), (3,0,3,1,0), (3,0,3,2,0), (3,0,3,3,0), (4,0,4,4,0), (4,0,4,0,0), (4,0,4,1,0), (4,0,4,2,0), (4,0,4,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,0,1,4,0), (4,0,1,0,0), (4,0,1,1,0), (4,0,1,2,0), (4,0,1,3,0), (4,0,2,4,0), (4,0,2,0,0), (4,0,2,1,0), (4,0,2,2,0), (4,0,2,3,0), (4,0,3,4,0), (4,0,3,0,0), (4,0,3,1,0), (4,0,3,2,0), (4,0,3,3,0)]
def R28 : Fin 125 → Coordinate 1 := fun i => R28list.getD i.val (0,0,0,0,0)

theorem hpxR28 : Function.Injective (fun i => reduceAux 1 (basisAt rK28) (R28 i)) := by decide
theorem hcardq28 : Nat.card (Coordinate 1 ⧸ reps rK28) = 125 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (28, 0): |T| = 125 -/

def T28_0list : List Coordinates := [(0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (1,0,4,4,0), (1,0,4,0,0), (1,0,4,1,0), (1,0,4,2,0), (1,0,4,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,0,1,4,0), (1,0,1,0,0), (1,0,1,1,0), (1,0,1,2,0), (1,0,1,3,0), (1,0,2,4,0), (1,0,2,0,0), (1,0,2,1,0), (1,0,2,2,0), (1,0,2,3,0), (1,0,3,4,0), (1,0,3,0,0), (1,0,3,1,0), (1,0,3,2,0), (1,0,3,3,0), (2,0,4,4,0), (2,0,4,0,0), (2,0,4,1,0), (2,0,4,2,0), (2,0,4,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,0,1,4,0), (2,0,1,0,0), (2,0,1,1,0), (2,0,1,2,0), (2,0,1,3,0), (2,0,2,4,0), (2,0,2,0,0), (2,0,2,1,0), (2,0,2,2,0), (2,0,2,3,0), (2,0,3,4,0), (2,0,3,0,0), (2,0,3,1,0), (2,0,3,2,0), (2,0,3,3,0), (3,0,4,4,0), (3,0,4,0,0), (3,0,4,1,0), (3,0,4,2,0), (3,0,4,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,0,1,4,0), (3,0,1,0,0), (3,0,1,1,0), (3,0,1,2,0), (3,0,1,3,0), (3,0,2,4,0), (3,0,2,0,0), (3,0,2,1,0), (3,0,2,2,0), (3,0,2,3,0), (3,0,3,4,0), (3,0,3,0,0), (3,0,3,1,0), (3,0,3,2,0), (3,0,3,3,0), (4,0,4,4,0), (4,0,4,0,0), (4,0,4,1,0), (4,0,4,2,0), (4,0,4,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,0,1,4,0), (4,0,1,0,0), (4,0,1,1,0), (4,0,1,2,0), (4,0,1,3,0), (4,0,2,4,0), (4,0,2,0,0), (4,0,2,1,0), (4,0,2,2,0), (4,0,2,3,0), (4,0,3,4,0), (4,0,3,0,0), (4,0,3,1,0), (4,0,3,2,0), (4,0,3,3,0)]
def T28_0 : Fin 125 → Coordinate 1 := fun i => T28_0list.getD i.val (0,0,0,0,0)

theorem hfix28_0 : ∀ i, ((T28_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK28)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28) :=
  repsFix_of_siftB rK28 ⟨0, by decide⟩ T28_0 (by decide)

theorem hinj28_0 : Function.Injective
    (fun i => ((T28_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK28)) :=
  repsInj_of_reduceAux rK28 T28_0 (by decide)

theorem hcardT28_0 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK28 ⟨0, by decide⟩ R28 hpxR28 hcardq28 (by decide)).symm

/-- **Cell (28, 0).** -/
theorem cell28_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK28) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK28) (charOfVec rK28 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK28 e (h : Coordinate 1) T28_0 i :=
  species_entry_eq_sum rK28 ⟨0, by decide⟩ e heK h T28_0 hfix28_0 hinj28_0 hcardT28_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK28) (T28_0 i) (hfix28_0 i) h)

/-! ## Cell (28, 12): |T| = 125 -/

def T28_12list : List Coordinates := [(0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (1,0,4,4,0), (1,0,4,0,0), (1,0,4,1,0), (1,0,4,2,0), (1,0,4,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,0,1,4,0), (1,0,1,0,0), (1,0,1,1,0), (1,0,1,2,0), (1,0,1,3,0), (1,0,2,4,0), (1,0,2,0,0), (1,0,2,1,0), (1,0,2,2,0), (1,0,2,3,0), (1,0,3,4,0), (1,0,3,0,0), (1,0,3,1,0), (1,0,3,2,0), (1,0,3,3,0), (2,0,4,4,0), (2,0,4,0,0), (2,0,4,1,0), (2,0,4,2,0), (2,0,4,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,0,1,4,0), (2,0,1,0,0), (2,0,1,1,0), (2,0,1,2,0), (2,0,1,3,0), (2,0,2,4,0), (2,0,2,0,0), (2,0,2,1,0), (2,0,2,2,0), (2,0,2,3,0), (2,0,3,4,0), (2,0,3,0,0), (2,0,3,1,0), (2,0,3,2,0), (2,0,3,3,0), (3,0,4,4,0), (3,0,4,0,0), (3,0,4,1,0), (3,0,4,2,0), (3,0,4,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,0,1,4,0), (3,0,1,0,0), (3,0,1,1,0), (3,0,1,2,0), (3,0,1,3,0), (3,0,2,4,0), (3,0,2,0,0), (3,0,2,1,0), (3,0,2,2,0), (3,0,2,3,0), (3,0,3,4,0), (3,0,3,0,0), (3,0,3,1,0), (3,0,3,2,0), (3,0,3,3,0), (4,0,4,4,0), (4,0,4,0,0), (4,0,4,1,0), (4,0,4,2,0), (4,0,4,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,0,1,4,0), (4,0,1,0,0), (4,0,1,1,0), (4,0,1,2,0), (4,0,1,3,0), (4,0,2,4,0), (4,0,2,0,0), (4,0,2,1,0), (4,0,2,2,0), (4,0,2,3,0), (4,0,3,4,0), (4,0,3,0,0), (4,0,3,1,0), (4,0,3,2,0), (4,0,3,3,0)]
def T28_12 : Fin 125 → Coordinate 1 := fun i => T28_12list.getD i.val (0,0,0,0,0)

theorem hfix28_12 : ∀ i, ((T28_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK28)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28) :=
  repsFix_of_siftB rK28 ⟨12, by decide⟩ T28_12 (by decide)

theorem hinj28_12 : Function.Injective
    (fun i => ((T28_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK28)) :=
  repsInj_of_reduceAux rK28 T28_12 (by decide)

theorem hcardT28_12 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK28 ⟨12, by decide⟩ R28 hpxR28 hcardq28 (by decide)).symm

/-- **Cell (28, 12).** -/
theorem cell28_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK28) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK28) (charOfVec rK28 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK28 e (h : Coordinate 1) T28_12 i :=
  species_entry_eq_sum rK28 ⟨12, by decide⟩ e heK h T28_12 hfix28_12 hinj28_12 hcardT28_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK28) (T28_12 i) (hfix28_12 i) h)

/-! ## Cell (28, 28): |T| = 25 -/

def T28_28list : List Coordinates := [(0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0)]
def T28_28 : Fin 25 → Coordinate 1 := fun i => T28_28list.getD i.val (0,0,0,0,0)

theorem hfix28_28 : ∀ i, ((T28_28 i : Coordinate 1) : Coordinate 1 ⧸ reps rK28)
    ∈ fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28) :=
  repsFix_of_siftB rK28 ⟨28, by decide⟩ T28_28 (by decide)

theorem hinj28_28 : Function.Injective
    (fun i => ((T28_28 i : Coordinate 1) : Coordinate 1 ⧸ reps rK28)) :=
  repsInj_of_reduceAux rK28 T28_28 (by decide)

theorem hcardT28_28 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK28 ⟨28, by decide⟩ R28 hpxR28 hcardq28 (by decide)).symm

/-- **Cell (28, 28).** -/
theorem cell28_28 (e : List (ZMod 25)) (heK : charOK (basisAt rK28) e = true)
    (h : ↥(reps (⟨28, by decide⟩ : Fin 148))) :
    species (reps (⟨28, by decide⟩ : Fin 148)) h (basisElt (reps rK28) (charOfVec rK28 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK28 e (h : Coordinate 1) T28_28 i :=
  species_entry_eq_sum rK28 ⟨28, by decide⟩ e heK h T28_28 hfix28_28 hinj28_28 hcardT28_28
    (fun i => conj_mem_of_fixedPoints (reps ⟨28, by decide⟩) (reps rK28) (T28_28 i) (hfix28_28 i) h)

namespace Q2

def R28_2 : Fin 125 → Coordinate 2 := fun i => R28list.getD i.val (0,0,0,0,0)
theorem hpxR28_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK28) (R28_2 i)) := by decide
theorem hcardq28_2 : Nat.card (Coordinate 2 ⧸ reps rK28) = 125 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (28, 0) twin -/

def T28_0_2 : Fin 125 → Coordinate 2 := fun i => T28_0list.getD i.val (0,0,0,0,0)

theorem hfix28_0_2 : ∀ i, ((T28_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK28)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK28) :=
  repsFix_of_siftB2 rK28 ⟨0, by decide⟩ T28_0_2 (by decide)

theorem hinj28_0_2 : Function.Injective
    (fun i => ((T28_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK28)) :=
  repsInj_of_reduceAux2 rK28 T28_0_2 (by decide)

theorem hcardT28_0_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK28)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK28 ⟨0, by decide⟩ R28_2 hpxR28_2 hcardq28_2 (by decide)).symm

/-- **Cell (28, 0) twin (q=2).** -/
theorem cell28_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK28) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK28) (charOfVec2 rK28 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK28 e (h : Coordinate 2) T28_0_2 i :=
  species_entry_eq_sum rK28 ⟨0, by decide⟩ e heK h T28_0_2 hfix28_0_2 hinj28_0_2 hcardT28_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK28) (T28_0_2 i) (hfix28_0_2 i) h)

/-! ### Cell (28, 12) twin -/

def T28_12_2 : Fin 125 → Coordinate 2 := fun i => T28_12list.getD i.val (0,0,0,0,0)

theorem hfix28_12_2 : ∀ i, ((T28_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK28)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK28) :=
  repsFix_of_siftB2 rK28 ⟨12, by decide⟩ T28_12_2 (by decide)

theorem hinj28_12_2 : Function.Injective
    (fun i => ((T28_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK28)) :=
  repsInj_of_reduceAux2 rK28 T28_12_2 (by decide)

theorem hcardT28_12_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK28)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK28 ⟨12, by decide⟩ R28_2 hpxR28_2 hcardq28_2 (by decide)).symm

/-- **Cell (28, 12) twin (q=2).** -/
theorem cell28_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK28) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK28) (charOfVec2 rK28 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK28 e (h : Coordinate 2) T28_12_2 i :=
  species_entry_eq_sum rK28 ⟨12, by decide⟩ e heK h T28_12_2 hfix28_12_2 hinj28_12_2 hcardT28_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK28) (T28_12_2 i) (hfix28_12_2 i) h)

/-! ### Cell (28, 28) twin -/

def T28_28_2 : Fin 25 → Coordinate 2 := fun i => T28_28list.getD i.val (0,0,0,0,0)

theorem hfix28_28_2 : ∀ i, ((T28_28_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK28)
    ∈ fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK28) :=
  repsFix_of_siftB2 rK28 ⟨28, by decide⟩ T28_28_2 (by decide)

theorem hinj28_28_2 : Function.Injective
    (fun i => ((T28_28_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK28)) :=
  repsInj_of_reduceAux2 rK28 T28_28_2 (by decide)

theorem hcardT28_28_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK28)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK28 ⟨28, by decide⟩ R28_2 hpxR28_2 hcardq28_2 (by decide)).symm

/-- **Cell (28, 28) twin (q=2).** -/
theorem cell28_28_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK28) e = true)
    (h : ↥(reps (⟨28, by decide⟩ : Fin 148))) :
    species (reps (⟨28, by decide⟩ : Fin 148)) h (basisElt (reps rK28) (charOfVec2 rK28 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK28 e (h : Coordinate 2) T28_28_2 i :=
  species_entry_eq_sum rK28 ⟨28, by decide⟩ e heK h T28_28_2 hfix28_28_2 hinj28_28_2 hcardT28_28_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨28, by decide⟩) (reps rK28) (T28_28_2 i) (hfix28_28_2 i) h)

end Q2

end LeanDring.P5Presentation
