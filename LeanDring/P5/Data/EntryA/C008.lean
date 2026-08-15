/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, A-block data (rK = 20): certified per-cell species-entry instantiations, both twins.

Emit-embed-decide loop for order-25 A-block class `rK = 20` (`|G/K| = 125`).
All nonzero `H`-columns (`|gH| ≤ 2`, `t⁻¹Ht ⊆ K`).  Full 125-coset transversal
`R20` and each `H`-fixed sub-transversal `T20_rH` embedded as kernel data and
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

def rK20 : Fin 148 := ⟨20, by decide⟩

def R20list : List Coordinates := [(0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,3,4,0)]
def R20 : Fin 125 → Coordinate 1 := fun i => R20list.getD i.val (0,0,0,0,0)

theorem hpxR20 : Function.Injective (fun i => reduceAux 1 (basisAt rK20) (R20 i)) := by decide
theorem hcardq20 : Nat.card (Coordinate 1 ⧸ reps rK20) = 125 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (20, 0): |T| = 125 -/

def T20_0list : List Coordinates := [(0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,3,4,0)]
def T20_0 : Fin 125 → Coordinate 1 := fun i => T20_0list.getD i.val (0,0,0,0,0)

theorem hfix20_0 : ∀ i, ((T20_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK20)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20) :=
  repsFix_of_siftB rK20 ⟨0, by decide⟩ T20_0 (by decide)

theorem hinj20_0 : Function.Injective
    (fun i => ((T20_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK20)) :=
  repsInj_of_reduceAux rK20 T20_0 (by decide)

theorem hcardT20_0 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK20 ⟨0, by decide⟩ R20 hpxR20 hcardq20 (by decide)).symm

/-- **Cell (20, 0).** -/
theorem cell20_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK20) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK20) (charOfVec rK20 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK20 e (h : Coordinate 1) T20_0 i :=
  species_entry_eq_sum rK20 ⟨0, by decide⟩ e heK h T20_0 hfix20_0 hinj20_0 hcardT20_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK20) (T20_0 i) (hfix20_0 i) h)

/-! ## Cell (20, 2): |T| = 25 -/

def T20_2list : List Coordinates := [(0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0)]
def T20_2 : Fin 25 → Coordinate 1 := fun i => T20_2list.getD i.val (0,0,0,0,0)

theorem hfix20_2 : ∀ i, ((T20_2 i : Coordinate 1) : Coordinate 1 ⧸ reps rK20)
    ∈ fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20) :=
  repsFix_of_siftB rK20 ⟨2, by decide⟩ T20_2 (by decide)

theorem hinj20_2 : Function.Injective
    (fun i => ((T20_2 i : Coordinate 1) : Coordinate 1 ⧸ reps rK20)) :=
  repsInj_of_reduceAux rK20 T20_2 (by decide)

theorem hcardT20_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK20 ⟨2, by decide⟩ R20 hpxR20 hcardq20 (by decide)).symm

/-- **Cell (20, 2).** -/
theorem cell20_2 (e : List (ZMod 25)) (heK : charOK (basisAt rK20) e = true)
    (h : ↥(reps (⟨2, by decide⟩ : Fin 148))) :
    species (reps (⟨2, by decide⟩ : Fin 148)) h (basisElt (reps rK20) (charOfVec rK20 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK20 e (h : Coordinate 1) T20_2 i :=
  species_entry_eq_sum rK20 ⟨2, by decide⟩ e heK h T20_2 hfix20_2 hinj20_2 hcardT20_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨2, by decide⟩) (reps rK20) (T20_2 i) (hfix20_2 i) h)

/-! ## Cell (20, 12): |T| = 125 -/

def T20_12list : List Coordinates := [(0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,3,4,0)]
def T20_12 : Fin 125 → Coordinate 1 := fun i => T20_12list.getD i.val (0,0,0,0,0)

theorem hfix20_12 : ∀ i, ((T20_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK20)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20) :=
  repsFix_of_siftB rK20 ⟨12, by decide⟩ T20_12 (by decide)

theorem hinj20_12 : Function.Injective
    (fun i => ((T20_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK20)) :=
  repsInj_of_reduceAux rK20 T20_12 (by decide)

theorem hcardT20_12 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK20 ⟨12, by decide⟩ R20 hpxR20 hcardq20 (by decide)).symm

/-- **Cell (20, 12).** -/
theorem cell20_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK20) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK20) (charOfVec rK20 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK20 e (h : Coordinate 1) T20_12 i :=
  species_entry_eq_sum rK20 ⟨12, by decide⟩ e heK h T20_12 hfix20_12 hinj20_12 hcardT20_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK20) (T20_12 i) (hfix20_12 i) h)

/-! ## Cell (20, 20): |T| = 25 -/

def T20_20list : List Coordinates := [(0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0)]
def T20_20 : Fin 25 → Coordinate 1 := fun i => T20_20list.getD i.val (0,0,0,0,0)

theorem hfix20_20 : ∀ i, ((T20_20 i : Coordinate 1) : Coordinate 1 ⧸ reps rK20)
    ∈ fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20) :=
  repsFix_of_siftB rK20 ⟨20, by decide⟩ T20_20 (by decide)

theorem hinj20_20 : Function.Injective
    (fun i => ((T20_20 i : Coordinate 1) : Coordinate 1 ⧸ reps rK20)) :=
  repsInj_of_reduceAux rK20 T20_20 (by decide)

theorem hcardT20_20 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK20 ⟨20, by decide⟩ R20 hpxR20 hcardq20 (by decide)).symm

/-- **Cell (20, 20).** -/
theorem cell20_20 (e : List (ZMod 25)) (heK : charOK (basisAt rK20) e = true)
    (h : ↥(reps (⟨20, by decide⟩ : Fin 148))) :
    species (reps (⟨20, by decide⟩ : Fin 148)) h (basisElt (reps rK20) (charOfVec rK20 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK20 e (h : Coordinate 1) T20_20 i :=
  species_entry_eq_sum rK20 ⟨20, by decide⟩ e heK h T20_20 hfix20_20 hinj20_20 hcardT20_20
    (fun i => conj_mem_of_fixedPoints (reps ⟨20, by decide⟩) (reps rK20) (T20_20 i) (hfix20_20 i) h)

namespace Q2

def R20_2 : Fin 125 → Coordinate 2 := fun i => R20list.getD i.val (0,0,0,0,0)
theorem hpxR20_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK20) (R20_2 i)) := by decide
theorem hcardq20_2 : Nat.card (Coordinate 2 ⧸ reps rK20) = 125 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (20, 0) twin -/

def T20_0_2 : Fin 125 → Coordinate 2 := fun i => T20_0list.getD i.val (0,0,0,0,0)

theorem hfix20_0_2 : ∀ i, ((T20_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK20)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK20) :=
  repsFix_of_siftB2 rK20 ⟨0, by decide⟩ T20_0_2 (by decide)

theorem hinj20_0_2 : Function.Injective
    (fun i => ((T20_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK20)) :=
  repsInj_of_reduceAux2 rK20 T20_0_2 (by decide)

theorem hcardT20_0_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK20)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK20 ⟨0, by decide⟩ R20_2 hpxR20_2 hcardq20_2 (by decide)).symm

/-- **Cell (20, 0) twin (q=2).** -/
theorem cell20_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK20) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK20) (charOfVec2 rK20 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK20 e (h : Coordinate 2) T20_0_2 i :=
  species_entry_eq_sum rK20 ⟨0, by decide⟩ e heK h T20_0_2 hfix20_0_2 hinj20_0_2 hcardT20_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK20) (T20_0_2 i) (hfix20_0_2 i) h)

/-! ### Cell (20, 2) twin -/

def T20_2_2 : Fin 25 → Coordinate 2 := fun i => T20_2list.getD i.val (0,0,0,0,0)

theorem hfix20_2_2 : ∀ i, ((T20_2_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK20)
    ∈ fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK20) :=
  repsFix_of_siftB2 rK20 ⟨2, by decide⟩ T20_2_2 (by decide)

theorem hinj20_2_2 : Function.Injective
    (fun i => ((T20_2_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK20)) :=
  repsInj_of_reduceAux2 rK20 T20_2_2 (by decide)

theorem hcardT20_2_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK20)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK20 ⟨2, by decide⟩ R20_2 hpxR20_2 hcardq20_2 (by decide)).symm

/-- **Cell (20, 2) twin (q=2).** -/
theorem cell20_2_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK20) e = true)
    (h : ↥(reps (⟨2, by decide⟩ : Fin 148))) :
    species (reps (⟨2, by decide⟩ : Fin 148)) h (basisElt (reps rK20) (charOfVec2 rK20 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK20 e (h : Coordinate 2) T20_2_2 i :=
  species_entry_eq_sum rK20 ⟨2, by decide⟩ e heK h T20_2_2 hfix20_2_2 hinj20_2_2 hcardT20_2_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨2, by decide⟩) (reps rK20) (T20_2_2 i) (hfix20_2_2 i) h)

/-! ### Cell (20, 12) twin -/

def T20_12_2 : Fin 125 → Coordinate 2 := fun i => T20_12list.getD i.val (0,0,0,0,0)

theorem hfix20_12_2 : ∀ i, ((T20_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK20)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK20) :=
  repsFix_of_siftB2 rK20 ⟨12, by decide⟩ T20_12_2 (by decide)

theorem hinj20_12_2 : Function.Injective
    (fun i => ((T20_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK20)) :=
  repsInj_of_reduceAux2 rK20 T20_12_2 (by decide)

theorem hcardT20_12_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK20)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK20 ⟨12, by decide⟩ R20_2 hpxR20_2 hcardq20_2 (by decide)).symm

/-- **Cell (20, 12) twin (q=2).** -/
theorem cell20_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK20) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK20) (charOfVec2 rK20 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK20 e (h : Coordinate 2) T20_12_2 i :=
  species_entry_eq_sum rK20 ⟨12, by decide⟩ e heK h T20_12_2 hfix20_12_2 hinj20_12_2 hcardT20_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK20) (T20_12_2 i) (hfix20_12_2 i) h)

/-! ### Cell (20, 20) twin -/

def T20_20_2 : Fin 25 → Coordinate 2 := fun i => T20_20list.getD i.val (0,0,0,0,0)

theorem hfix20_20_2 : ∀ i, ((T20_20_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK20)
    ∈ fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK20) :=
  repsFix_of_siftB2 rK20 ⟨20, by decide⟩ T20_20_2 (by decide)

theorem hinj20_20_2 : Function.Injective
    (fun i => ((T20_20_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK20)) :=
  repsInj_of_reduceAux2 rK20 T20_20_2 (by decide)

theorem hcardT20_20_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK20)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK20 ⟨20, by decide⟩ R20_2 hpxR20_2 hcardq20_2 (by decide)).symm

/-- **Cell (20, 20) twin (q=2).** -/
theorem cell20_20_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK20) e = true)
    (h : ↥(reps (⟨20, by decide⟩ : Fin 148))) :
    species (reps (⟨20, by decide⟩ : Fin 148)) h (basisElt (reps rK20) (charOfVec2 rK20 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK20 e (h : Coordinate 2) T20_20_2 i :=
  species_entry_eq_sum rK20 ⟨20, by decide⟩ e heK h T20_20_2 hfix20_20_2 hinj20_20_2 hcardT20_20_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨20, by decide⟩) (reps rK20) (T20_20_2 i) (hfix20_20_2 i) h)

end Q2

end LeanDring.P5Presentation
