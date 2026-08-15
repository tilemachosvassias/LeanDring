/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, A-block data (rK = 41): certified per-cell species-entry instantiations, both twins.

Emit-embed-decide loop for order-25 A-block class `rK = 41` (`|G/K| = 125`).
All nonzero `H`-columns (`|gH| ≤ 2`, `t⁻¹Ht ⊆ K`).  Full 125-coset transversal
`R41` and each `H`-fixed sub-transversal `T41_rH` embedded as kernel data and
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

def rK41 : Fin 148 := ⟨41, by decide⟩

def R41list : List Coordinates := [(0,3,4,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0)]
def R41 : Fin 125 → Coordinate 1 := fun i => R41list.getD i.val (0,0,0,0,0)

theorem hpxR41 : Function.Injective (fun i => reduceAux 1 (basisAt rK41) (R41 i)) := by decide
theorem hcardq41 : Nat.card (Coordinate 1 ⧸ reps rK41) = 125 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (41, 0): |T| = 125 -/

def T41_0list : List Coordinates := [(0,3,4,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0)]
def T41_0 : Fin 125 → Coordinate 1 := fun i => T41_0list.getD i.val (0,0,0,0,0)

theorem hfix41_0 : ∀ i, ((T41_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK41)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41) :=
  repsFix_of_siftB rK41 ⟨0, by decide⟩ T41_0 (by decide)

theorem hinj41_0 : Function.Injective
    (fun i => ((T41_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK41)) :=
  repsInj_of_reduceAux rK41 T41_0 (by decide)

theorem hcardT41_0 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK41 ⟨0, by decide⟩ R41 hpxR41 hcardq41 (by decide)).symm

/-- **Cell (41, 0).** -/
theorem cell41_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK41) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK41) (charOfVec rK41 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK41 e (h : Coordinate 1) T41_0 i :=
  species_entry_eq_sum rK41 ⟨0, by decide⟩ e heK h T41_0 hfix41_0 hinj41_0 hcardT41_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK41) (T41_0 i) (hfix41_0 i) h)

/-! ## Cell (41, 12): |T| = 125 -/

def T41_12list : List Coordinates := [(0,3,4,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0)]
def T41_12 : Fin 125 → Coordinate 1 := fun i => T41_12list.getD i.val (0,0,0,0,0)

theorem hfix41_12 : ∀ i, ((T41_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK41)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41) :=
  repsFix_of_siftB rK41 ⟨12, by decide⟩ T41_12 (by decide)

theorem hinj41_12 : Function.Injective
    (fun i => ((T41_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK41)) :=
  repsInj_of_reduceAux rK41 T41_12 (by decide)

theorem hcardT41_12 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK41 ⟨12, by decide⟩ R41 hpxR41 hcardq41 (by decide)).symm

/-- **Cell (41, 12).** -/
theorem cell41_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK41) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK41) (charOfVec rK41 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK41 e (h : Coordinate 1) T41_12 i :=
  species_entry_eq_sum rK41 ⟨12, by decide⟩ e heK h T41_12 hfix41_12 hinj41_12 hcardT41_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK41) (T41_12 i) (hfix41_12 i) h)

/-! ## Cell (41, 41): |T| = 25 -/

def T41_41list : List Coordinates := [(0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0)]
def T41_41 : Fin 25 → Coordinate 1 := fun i => T41_41list.getD i.val (0,0,0,0,0)

theorem hfix41_41 : ∀ i, ((T41_41 i : Coordinate 1) : Coordinate 1 ⧸ reps rK41)
    ∈ fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41) :=
  repsFix_of_siftB rK41 ⟨41, by decide⟩ T41_41 (by decide)

theorem hinj41_41 : Function.Injective
    (fun i => ((T41_41 i : Coordinate 1) : Coordinate 1 ⧸ reps rK41)) :=
  repsInj_of_reduceAux rK41 T41_41 (by decide)

theorem hcardT41_41 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK41 ⟨41, by decide⟩ R41 hpxR41 hcardq41 (by decide)).symm

/-- **Cell (41, 41).** -/
theorem cell41_41 (e : List (ZMod 25)) (heK : charOK (basisAt rK41) e = true)
    (h : ↥(reps (⟨41, by decide⟩ : Fin 148))) :
    species (reps (⟨41, by decide⟩ : Fin 148)) h (basisElt (reps rK41) (charOfVec rK41 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK41 e (h : Coordinate 1) T41_41 i :=
  species_entry_eq_sum rK41 ⟨41, by decide⟩ e heK h T41_41 hfix41_41 hinj41_41 hcardT41_41
    (fun i => conj_mem_of_fixedPoints (reps ⟨41, by decide⟩) (reps rK41) (T41_41 i) (hfix41_41 i) h)

namespace Q2

def R41_2 : Fin 125 → Coordinate 2 := fun i => R41list.getD i.val (0,0,0,0,0)
theorem hpxR41_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK41) (R41_2 i)) := by decide
theorem hcardq41_2 : Nat.card (Coordinate 2 ⧸ reps rK41) = 125 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (41, 0) twin -/

def T41_0_2 : Fin 125 → Coordinate 2 := fun i => T41_0list.getD i.val (0,0,0,0,0)

theorem hfix41_0_2 : ∀ i, ((T41_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK41)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK41) :=
  repsFix_of_siftB2 rK41 ⟨0, by decide⟩ T41_0_2 (by decide)

theorem hinj41_0_2 : Function.Injective
    (fun i => ((T41_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK41)) :=
  repsInj_of_reduceAux2 rK41 T41_0_2 (by decide)

theorem hcardT41_0_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK41)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK41 ⟨0, by decide⟩ R41_2 hpxR41_2 hcardq41_2 (by decide)).symm

/-- **Cell (41, 0) twin (q=2).** -/
theorem cell41_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK41) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK41) (charOfVec2 rK41 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK41 e (h : Coordinate 2) T41_0_2 i :=
  species_entry_eq_sum rK41 ⟨0, by decide⟩ e heK h T41_0_2 hfix41_0_2 hinj41_0_2 hcardT41_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK41) (T41_0_2 i) (hfix41_0_2 i) h)

/-! ### Cell (41, 12) twin -/

def T41_12_2 : Fin 125 → Coordinate 2 := fun i => T41_12list.getD i.val (0,0,0,0,0)

theorem hfix41_12_2 : ∀ i, ((T41_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK41)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK41) :=
  repsFix_of_siftB2 rK41 ⟨12, by decide⟩ T41_12_2 (by decide)

theorem hinj41_12_2 : Function.Injective
    (fun i => ((T41_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK41)) :=
  repsInj_of_reduceAux2 rK41 T41_12_2 (by decide)

theorem hcardT41_12_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK41)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK41 ⟨12, by decide⟩ R41_2 hpxR41_2 hcardq41_2 (by decide)).symm

/-- **Cell (41, 12) twin (q=2).** -/
theorem cell41_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK41) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK41) (charOfVec2 rK41 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK41 e (h : Coordinate 2) T41_12_2 i :=
  species_entry_eq_sum rK41 ⟨12, by decide⟩ e heK h T41_12_2 hfix41_12_2 hinj41_12_2 hcardT41_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK41) (T41_12_2 i) (hfix41_12_2 i) h)

/-! ### Cell (41, 41) twin -/

def T41_41_2 : Fin 25 → Coordinate 2 := fun i => T41_41list.getD i.val (0,0,0,0,0)

theorem hfix41_41_2 : ∀ i, ((T41_41_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK41)
    ∈ fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK41) :=
  repsFix_of_siftB2 rK41 ⟨41, by decide⟩ T41_41_2 (by decide)

theorem hinj41_41_2 : Function.Injective
    (fun i => ((T41_41_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK41)) :=
  repsInj_of_reduceAux2 rK41 T41_41_2 (by decide)

theorem hcardT41_41_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK41)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK41 ⟨41, by decide⟩ R41_2 hpxR41_2 hcardq41_2 (by decide)).symm

/-- **Cell (41, 41) twin (q=2).** -/
theorem cell41_41_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK41) e = true)
    (h : ↥(reps (⟨41, by decide⟩ : Fin 148))) :
    species (reps (⟨41, by decide⟩ : Fin 148)) h (basisElt (reps rK41) (charOfVec2 rK41 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK41 e (h : Coordinate 2) T41_41_2 i :=
  species_entry_eq_sum rK41 ⟨41, by decide⟩ e heK h T41_41_2 hfix41_41_2 hinj41_41_2 hcardT41_41_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨41, by decide⟩) (reps rK41) (T41_41_2 i) (hfix41_41_2 i) h)

end Q2

end LeanDring.P5Presentation
