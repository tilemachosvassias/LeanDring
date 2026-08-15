/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, A-block data (rK = 52): certified per-cell species-entry instantiations, both twins.

Emit-embed-decide loop for order-25 A-block class `rK = 52` (`|G/K| = 125`).
All nonzero `H`-columns (`|gH| ≤ 2`, `t⁻¹Ht ⊆ K`).  Full 125-coset transversal
`R52` and each `H`-fixed sub-transversal `T52_rH` embedded as kernel data and
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

def rK52 : Fin 148 := ⟨52, by decide⟩

def R52list : List Coordinates := [(0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0)]
def R52 : Fin 125 → Coordinate 1 := fun i => R52list.getD i.val (0,0,0,0,0)

theorem hpxR52 : Function.Injective (fun i => reduceAux 1 (basisAt rK52) (R52 i)) := by decide
theorem hcardq52 : Nat.card (Coordinate 1 ⧸ reps rK52) = 125 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (52, 0): |T| = 125 -/

def T52_0list : List Coordinates := [(0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0)]
def T52_0 : Fin 125 → Coordinate 1 := fun i => T52_0list.getD i.val (0,0,0,0,0)

theorem hfix52_0 : ∀ i, ((T52_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK52)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52) :=
  repsFix_of_siftB rK52 ⟨0, by decide⟩ T52_0 (by decide)

theorem hinj52_0 : Function.Injective
    (fun i => ((T52_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK52)) :=
  repsInj_of_reduceAux rK52 T52_0 (by decide)

theorem hcardT52_0 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK52 ⟨0, by decide⟩ R52 hpxR52 hcardq52 (by decide)).symm

/-- **Cell (52, 0).** -/
theorem cell52_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK52) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK52) (charOfVec rK52 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK52 e (h : Coordinate 1) T52_0 i :=
  species_entry_eq_sum rK52 ⟨0, by decide⟩ e heK h T52_0 hfix52_0 hinj52_0 hcardT52_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK52) (T52_0 i) (hfix52_0 i) h)

/-! ## Cell (52, 12): |T| = 125 -/

def T52_12list : List Coordinates := [(0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0)]
def T52_12 : Fin 125 → Coordinate 1 := fun i => T52_12list.getD i.val (0,0,0,0,0)

theorem hfix52_12 : ∀ i, ((T52_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK52)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52) :=
  repsFix_of_siftB rK52 ⟨12, by decide⟩ T52_12 (by decide)

theorem hinj52_12 : Function.Injective
    (fun i => ((T52_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK52)) :=
  repsInj_of_reduceAux rK52 T52_12 (by decide)

theorem hcardT52_12 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK52 ⟨12, by decide⟩ R52 hpxR52 hcardq52 (by decide)).symm

/-- **Cell (52, 12).** -/
theorem cell52_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK52) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK52) (charOfVec rK52 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK52 e (h : Coordinate 1) T52_12 i :=
  species_entry_eq_sum rK52 ⟨12, by decide⟩ e heK h T52_12 hfix52_12 hinj52_12 hcardT52_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK52) (T52_12 i) (hfix52_12 i) h)

/-! ## Cell (52, 52): |T| = 25 -/

def T52_52list : List Coordinates := [(0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0)]
def T52_52 : Fin 25 → Coordinate 1 := fun i => T52_52list.getD i.val (0,0,0,0,0)

theorem hfix52_52 : ∀ i, ((T52_52 i : Coordinate 1) : Coordinate 1 ⧸ reps rK52)
    ∈ fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52) :=
  repsFix_of_siftB rK52 ⟨52, by decide⟩ T52_52 (by decide)

theorem hinj52_52 : Function.Injective
    (fun i => ((T52_52 i : Coordinate 1) : Coordinate 1 ⧸ reps rK52)) :=
  repsInj_of_reduceAux rK52 T52_52 (by decide)

theorem hcardT52_52 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK52 ⟨52, by decide⟩ R52 hpxR52 hcardq52 (by decide)).symm

/-- **Cell (52, 52).** -/
theorem cell52_52 (e : List (ZMod 25)) (heK : charOK (basisAt rK52) e = true)
    (h : ↥(reps (⟨52, by decide⟩ : Fin 148))) :
    species (reps (⟨52, by decide⟩ : Fin 148)) h (basisElt (reps rK52) (charOfVec rK52 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK52 e (h : Coordinate 1) T52_52 i :=
  species_entry_eq_sum rK52 ⟨52, by decide⟩ e heK h T52_52 hfix52_52 hinj52_52 hcardT52_52
    (fun i => conj_mem_of_fixedPoints (reps ⟨52, by decide⟩) (reps rK52) (T52_52 i) (hfix52_52 i) h)

namespace Q2

def R52_2 : Fin 125 → Coordinate 2 := fun i => R52list.getD i.val (0,0,0,0,0)
theorem hpxR52_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK52) (R52_2 i)) := by decide
theorem hcardq52_2 : Nat.card (Coordinate 2 ⧸ reps rK52) = 125 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (52, 0) twin -/

def T52_0_2 : Fin 125 → Coordinate 2 := fun i => T52_0list.getD i.val (0,0,0,0,0)

theorem hfix52_0_2 : ∀ i, ((T52_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK52)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK52) :=
  repsFix_of_siftB2 rK52 ⟨0, by decide⟩ T52_0_2 (by decide)

theorem hinj52_0_2 : Function.Injective
    (fun i => ((T52_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK52)) :=
  repsInj_of_reduceAux2 rK52 T52_0_2 (by decide)

theorem hcardT52_0_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK52)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK52 ⟨0, by decide⟩ R52_2 hpxR52_2 hcardq52_2 (by decide)).symm

/-- **Cell (52, 0) twin (q=2).** -/
theorem cell52_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK52) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK52) (charOfVec2 rK52 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK52 e (h : Coordinate 2) T52_0_2 i :=
  species_entry_eq_sum rK52 ⟨0, by decide⟩ e heK h T52_0_2 hfix52_0_2 hinj52_0_2 hcardT52_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK52) (T52_0_2 i) (hfix52_0_2 i) h)

/-! ### Cell (52, 12) twin -/

def T52_12_2 : Fin 125 → Coordinate 2 := fun i => T52_12list.getD i.val (0,0,0,0,0)

theorem hfix52_12_2 : ∀ i, ((T52_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK52)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK52) :=
  repsFix_of_siftB2 rK52 ⟨12, by decide⟩ T52_12_2 (by decide)

theorem hinj52_12_2 : Function.Injective
    (fun i => ((T52_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK52)) :=
  repsInj_of_reduceAux2 rK52 T52_12_2 (by decide)

theorem hcardT52_12_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK52)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK52 ⟨12, by decide⟩ R52_2 hpxR52_2 hcardq52_2 (by decide)).symm

/-- **Cell (52, 12) twin (q=2).** -/
theorem cell52_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK52) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK52) (charOfVec2 rK52 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK52 e (h : Coordinate 2) T52_12_2 i :=
  species_entry_eq_sum rK52 ⟨12, by decide⟩ e heK h T52_12_2 hfix52_12_2 hinj52_12_2 hcardT52_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK52) (T52_12_2 i) (hfix52_12_2 i) h)

/-! ### Cell (52, 52) twin -/

def T52_52_2 : Fin 25 → Coordinate 2 := fun i => T52_52list.getD i.val (0,0,0,0,0)

theorem hfix52_52_2 : ∀ i, ((T52_52_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK52)
    ∈ fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK52) :=
  repsFix_of_siftB2 rK52 ⟨52, by decide⟩ T52_52_2 (by decide)

theorem hinj52_52_2 : Function.Injective
    (fun i => ((T52_52_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK52)) :=
  repsInj_of_reduceAux2 rK52 T52_52_2 (by decide)

theorem hcardT52_52_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK52)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK52 ⟨52, by decide⟩ R52_2 hpxR52_2 hcardq52_2 (by decide)).symm

/-- **Cell (52, 52) twin (q=2).** -/
theorem cell52_52_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK52) e = true)
    (h : ↥(reps (⟨52, by decide⟩ : Fin 148))) :
    species (reps (⟨52, by decide⟩ : Fin 148)) h (basisElt (reps rK52) (charOfVec2 rK52 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK52 e (h : Coordinate 2) T52_52_2 i :=
  species_entry_eq_sum rK52 ⟨52, by decide⟩ e heK h T52_52_2 hfix52_52_2 hinj52_52_2 hcardT52_52_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨52, by decide⟩) (reps rK52) (T52_52_2 i) (hfix52_52_2 i) h)

end Q2

end LeanDring.P5Presentation
