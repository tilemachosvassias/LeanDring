/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, A-block data (rK = 44): certified per-cell species-entry instantiations, both twins.

Emit-embed-decide loop for order-25 A-block class `rK = 44` (`|G/K| = 125`).
All nonzero `H`-columns (`|gH| ≤ 2`, `t⁻¹Ht ⊆ K`).  Full 125-coset transversal
`R44` and each `H`-fixed sub-transversal `T44_rH` embedded as kernel data and
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

def rK44 : Fin 148 := ⟨44, by decide⟩

def R44list : List Coordinates := [(0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,3,1,0)]
def R44 : Fin 125 → Coordinate 1 := fun i => R44list.getD i.val (0,0,0,0,0)

theorem hpxR44 : Function.Injective (fun i => reduceAux 1 (basisAt rK44) (R44 i)) := by decide
theorem hcardq44 : Nat.card (Coordinate 1 ⧸ reps rK44) = 125 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (44, 0): |T| = 125 -/

def T44_0list : List Coordinates := [(0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,3,1,0)]
def T44_0 : Fin 125 → Coordinate 1 := fun i => T44_0list.getD i.val (0,0,0,0,0)

theorem hfix44_0 : ∀ i, ((T44_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK44)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44) :=
  repsFix_of_siftB rK44 ⟨0, by decide⟩ T44_0 (by decide)

theorem hinj44_0 : Function.Injective
    (fun i => ((T44_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK44)) :=
  repsInj_of_reduceAux rK44 T44_0 (by decide)

theorem hcardT44_0 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK44 ⟨0, by decide⟩ R44 hpxR44 hcardq44 (by decide)).symm

/-- **Cell (44, 0).** -/
theorem cell44_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK44) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK44) (charOfVec rK44 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK44 e (h : Coordinate 1) T44_0 i :=
  species_entry_eq_sum rK44 ⟨0, by decide⟩ e heK h T44_0 hfix44_0 hinj44_0 hcardT44_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK44) (T44_0 i) (hfix44_0 i) h)

/-! ## Cell (44, 12): |T| = 125 -/

def T44_12list : List Coordinates := [(0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,3,1,0)]
def T44_12 : Fin 125 → Coordinate 1 := fun i => T44_12list.getD i.val (0,0,0,0,0)

theorem hfix44_12 : ∀ i, ((T44_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK44)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44) :=
  repsFix_of_siftB rK44 ⟨12, by decide⟩ T44_12 (by decide)

theorem hinj44_12 : Function.Injective
    (fun i => ((T44_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK44)) :=
  repsInj_of_reduceAux rK44 T44_12 (by decide)

theorem hcardT44_12 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK44 ⟨12, by decide⟩ R44 hpxR44 hcardq44 (by decide)).symm

/-- **Cell (44, 12).** -/
theorem cell44_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK44) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK44) (charOfVec rK44 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK44 e (h : Coordinate 1) T44_12 i :=
  species_entry_eq_sum rK44 ⟨12, by decide⟩ e heK h T44_12 hfix44_12 hinj44_12 hcardT44_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK44) (T44_12 i) (hfix44_12 i) h)

/-! ## Cell (44, 44): |T| = 25 -/

def T44_44list : List Coordinates := [(0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0)]
def T44_44 : Fin 25 → Coordinate 1 := fun i => T44_44list.getD i.val (0,0,0,0,0)

theorem hfix44_44 : ∀ i, ((T44_44 i : Coordinate 1) : Coordinate 1 ⧸ reps rK44)
    ∈ fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44) :=
  repsFix_of_siftB rK44 ⟨44, by decide⟩ T44_44 (by decide)

theorem hinj44_44 : Function.Injective
    (fun i => ((T44_44 i : Coordinate 1) : Coordinate 1 ⧸ reps rK44)) :=
  repsInj_of_reduceAux rK44 T44_44 (by decide)

theorem hcardT44_44 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK44 ⟨44, by decide⟩ R44 hpxR44 hcardq44 (by decide)).symm

/-- **Cell (44, 44).** -/
theorem cell44_44 (e : List (ZMod 25)) (heK : charOK (basisAt rK44) e = true)
    (h : ↥(reps (⟨44, by decide⟩ : Fin 148))) :
    species (reps (⟨44, by decide⟩ : Fin 148)) h (basisElt (reps rK44) (charOfVec rK44 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK44 e (h : Coordinate 1) T44_44 i :=
  species_entry_eq_sum rK44 ⟨44, by decide⟩ e heK h T44_44 hfix44_44 hinj44_44 hcardT44_44
    (fun i => conj_mem_of_fixedPoints (reps ⟨44, by decide⟩) (reps rK44) (T44_44 i) (hfix44_44 i) h)

namespace Q2

def R44_2 : Fin 125 → Coordinate 2 := fun i => R44list.getD i.val (0,0,0,0,0)
theorem hpxR44_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK44) (R44_2 i)) := by decide
theorem hcardq44_2 : Nat.card (Coordinate 2 ⧸ reps rK44) = 125 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (44, 0) twin -/

def T44_0_2 : Fin 125 → Coordinate 2 := fun i => T44_0list.getD i.val (0,0,0,0,0)

theorem hfix44_0_2 : ∀ i, ((T44_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK44)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK44) :=
  repsFix_of_siftB2 rK44 ⟨0, by decide⟩ T44_0_2 (by decide)

theorem hinj44_0_2 : Function.Injective
    (fun i => ((T44_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK44)) :=
  repsInj_of_reduceAux2 rK44 T44_0_2 (by decide)

theorem hcardT44_0_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK44)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK44 ⟨0, by decide⟩ R44_2 hpxR44_2 hcardq44_2 (by decide)).symm

/-- **Cell (44, 0) twin (q=2).** -/
theorem cell44_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK44) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK44) (charOfVec2 rK44 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK44 e (h : Coordinate 2) T44_0_2 i :=
  species_entry_eq_sum rK44 ⟨0, by decide⟩ e heK h T44_0_2 hfix44_0_2 hinj44_0_2 hcardT44_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK44) (T44_0_2 i) (hfix44_0_2 i) h)

/-! ### Cell (44, 12) twin -/

def T44_12_2 : Fin 125 → Coordinate 2 := fun i => T44_12list.getD i.val (0,0,0,0,0)

theorem hfix44_12_2 : ∀ i, ((T44_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK44)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK44) :=
  repsFix_of_siftB2 rK44 ⟨12, by decide⟩ T44_12_2 (by decide)

theorem hinj44_12_2 : Function.Injective
    (fun i => ((T44_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK44)) :=
  repsInj_of_reduceAux2 rK44 T44_12_2 (by decide)

theorem hcardT44_12_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK44)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK44 ⟨12, by decide⟩ R44_2 hpxR44_2 hcardq44_2 (by decide)).symm

/-- **Cell (44, 12) twin (q=2).** -/
theorem cell44_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK44) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK44) (charOfVec2 rK44 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK44 e (h : Coordinate 2) T44_12_2 i :=
  species_entry_eq_sum rK44 ⟨12, by decide⟩ e heK h T44_12_2 hfix44_12_2 hinj44_12_2 hcardT44_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK44) (T44_12_2 i) (hfix44_12_2 i) h)

/-! ### Cell (44, 44) twin -/

def T44_44_2 : Fin 25 → Coordinate 2 := fun i => T44_44list.getD i.val (0,0,0,0,0)

theorem hfix44_44_2 : ∀ i, ((T44_44_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK44)
    ∈ fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK44) :=
  repsFix_of_siftB2 rK44 ⟨44, by decide⟩ T44_44_2 (by decide)

theorem hinj44_44_2 : Function.Injective
    (fun i => ((T44_44_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK44)) :=
  repsInj_of_reduceAux2 rK44 T44_44_2 (by decide)

theorem hcardT44_44_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK44)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK44 ⟨44, by decide⟩ R44_2 hpxR44_2 hcardq44_2 (by decide)).symm

/-- **Cell (44, 44) twin (q=2).** -/
theorem cell44_44_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK44) e = true)
    (h : ↥(reps (⟨44, by decide⟩ : Fin 148))) :
    species (reps (⟨44, by decide⟩ : Fin 148)) h (basisElt (reps rK44) (charOfVec2 rK44 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK44 e (h : Coordinate 2) T44_44_2 i :=
  species_entry_eq_sum rK44 ⟨44, by decide⟩ e heK h T44_44_2 hfix44_44_2 hinj44_44_2 hcardT44_44_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨44, by decide⟩) (reps rK44) (T44_44_2 i) (hfix44_44_2 i) h)

end Q2

end LeanDring.P5Presentation
