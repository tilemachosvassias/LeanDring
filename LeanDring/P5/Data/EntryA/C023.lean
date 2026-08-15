/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, A-block data (rK = 35): certified per-cell species-entry instantiations, both twins.

Emit-embed-decide loop for order-25 A-block class `rK = 35` (`|G/K| = 125`).
All nonzero `H`-columns (`|gH| ≤ 2`, `t⁻¹Ht ⊆ K`).  Full 125-coset transversal
`R35` and each `H`-fixed sub-transversal `T35_rH` embedded as kernel data and
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

def rK35 : Fin 148 := ⟨35, by decide⟩

def R35list : List Coordinates := [(0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,3,0,0)]
def R35 : Fin 125 → Coordinate 1 := fun i => R35list.getD i.val (0,0,0,0,0)

theorem hpxR35 : Function.Injective (fun i => reduceAux 1 (basisAt rK35) (R35 i)) := by decide
theorem hcardq35 : Nat.card (Coordinate 1 ⧸ reps rK35) = 125 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (35, 0): |T| = 125 -/

def T35_0list : List Coordinates := [(0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,3,0,0)]
def T35_0 : Fin 125 → Coordinate 1 := fun i => T35_0list.getD i.val (0,0,0,0,0)

theorem hfix35_0 : ∀ i, ((T35_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK35)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35) :=
  repsFix_of_siftB rK35 ⟨0, by decide⟩ T35_0 (by decide)

theorem hinj35_0 : Function.Injective
    (fun i => ((T35_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK35)) :=
  repsInj_of_reduceAux rK35 T35_0 (by decide)

theorem hcardT35_0 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK35 ⟨0, by decide⟩ R35 hpxR35 hcardq35 (by decide)).symm

/-- **Cell (35, 0).** -/
theorem cell35_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK35) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK35) (charOfVec rK35 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK35 e (h : Coordinate 1) T35_0 i :=
  species_entry_eq_sum rK35 ⟨0, by decide⟩ e heK h T35_0 hfix35_0 hinj35_0 hcardT35_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK35) (T35_0 i) (hfix35_0 i) h)

/-! ## Cell (35, 12): |T| = 125 -/

def T35_12list : List Coordinates := [(0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,3,0,0)]
def T35_12 : Fin 125 → Coordinate 1 := fun i => T35_12list.getD i.val (0,0,0,0,0)

theorem hfix35_12 : ∀ i, ((T35_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK35)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35) :=
  repsFix_of_siftB rK35 ⟨12, by decide⟩ T35_12 (by decide)

theorem hinj35_12 : Function.Injective
    (fun i => ((T35_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK35)) :=
  repsInj_of_reduceAux rK35 T35_12 (by decide)

theorem hcardT35_12 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK35 ⟨12, by decide⟩ R35 hpxR35 hcardq35 (by decide)).symm

/-- **Cell (35, 12).** -/
theorem cell35_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK35) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK35) (charOfVec rK35 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK35 e (h : Coordinate 1) T35_12 i :=
  species_entry_eq_sum rK35 ⟨12, by decide⟩ e heK h T35_12 hfix35_12 hinj35_12 hcardT35_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK35) (T35_12 i) (hfix35_12 i) h)

/-! ## Cell (35, 35): |T| = 25 -/

def T35_35list : List Coordinates := [(0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0)]
def T35_35 : Fin 25 → Coordinate 1 := fun i => T35_35list.getD i.val (0,0,0,0,0)

theorem hfix35_35 : ∀ i, ((T35_35 i : Coordinate 1) : Coordinate 1 ⧸ reps rK35)
    ∈ fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35) :=
  repsFix_of_siftB rK35 ⟨35, by decide⟩ T35_35 (by decide)

theorem hinj35_35 : Function.Injective
    (fun i => ((T35_35 i : Coordinate 1) : Coordinate 1 ⧸ reps rK35)) :=
  repsInj_of_reduceAux rK35 T35_35 (by decide)

theorem hcardT35_35 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK35 ⟨35, by decide⟩ R35 hpxR35 hcardq35 (by decide)).symm

/-- **Cell (35, 35).** -/
theorem cell35_35 (e : List (ZMod 25)) (heK : charOK (basisAt rK35) e = true)
    (h : ↥(reps (⟨35, by decide⟩ : Fin 148))) :
    species (reps (⟨35, by decide⟩ : Fin 148)) h (basisElt (reps rK35) (charOfVec rK35 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK35 e (h : Coordinate 1) T35_35 i :=
  species_entry_eq_sum rK35 ⟨35, by decide⟩ e heK h T35_35 hfix35_35 hinj35_35 hcardT35_35
    (fun i => conj_mem_of_fixedPoints (reps ⟨35, by decide⟩) (reps rK35) (T35_35 i) (hfix35_35 i) h)

namespace Q2

def R35_2 : Fin 125 → Coordinate 2 := fun i => R35list.getD i.val (0,0,0,0,0)
theorem hpxR35_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK35) (R35_2 i)) := by decide
theorem hcardq35_2 : Nat.card (Coordinate 2 ⧸ reps rK35) = 125 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (35, 0) twin -/

def T35_0_2 : Fin 125 → Coordinate 2 := fun i => T35_0list.getD i.val (0,0,0,0,0)

theorem hfix35_0_2 : ∀ i, ((T35_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK35)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK35) :=
  repsFix_of_siftB2 rK35 ⟨0, by decide⟩ T35_0_2 (by decide)

theorem hinj35_0_2 : Function.Injective
    (fun i => ((T35_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK35)) :=
  repsInj_of_reduceAux2 rK35 T35_0_2 (by decide)

theorem hcardT35_0_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK35)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK35 ⟨0, by decide⟩ R35_2 hpxR35_2 hcardq35_2 (by decide)).symm

/-- **Cell (35, 0) twin (q=2).** -/
theorem cell35_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK35) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK35) (charOfVec2 rK35 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK35 e (h : Coordinate 2) T35_0_2 i :=
  species_entry_eq_sum rK35 ⟨0, by decide⟩ e heK h T35_0_2 hfix35_0_2 hinj35_0_2 hcardT35_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK35) (T35_0_2 i) (hfix35_0_2 i) h)

/-! ### Cell (35, 12) twin -/

def T35_12_2 : Fin 125 → Coordinate 2 := fun i => T35_12list.getD i.val (0,0,0,0,0)

theorem hfix35_12_2 : ∀ i, ((T35_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK35)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK35) :=
  repsFix_of_siftB2 rK35 ⟨12, by decide⟩ T35_12_2 (by decide)

theorem hinj35_12_2 : Function.Injective
    (fun i => ((T35_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK35)) :=
  repsInj_of_reduceAux2 rK35 T35_12_2 (by decide)

theorem hcardT35_12_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK35)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK35 ⟨12, by decide⟩ R35_2 hpxR35_2 hcardq35_2 (by decide)).symm

/-- **Cell (35, 12) twin (q=2).** -/
theorem cell35_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK35) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK35) (charOfVec2 rK35 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK35 e (h : Coordinate 2) T35_12_2 i :=
  species_entry_eq_sum rK35 ⟨12, by decide⟩ e heK h T35_12_2 hfix35_12_2 hinj35_12_2 hcardT35_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK35) (T35_12_2 i) (hfix35_12_2 i) h)

/-! ### Cell (35, 35) twin -/

def T35_35_2 : Fin 25 → Coordinate 2 := fun i => T35_35list.getD i.val (0,0,0,0,0)

theorem hfix35_35_2 : ∀ i, ((T35_35_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK35)
    ∈ fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK35) :=
  repsFix_of_siftB2 rK35 ⟨35, by decide⟩ T35_35_2 (by decide)

theorem hinj35_35_2 : Function.Injective
    (fun i => ((T35_35_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK35)) :=
  repsInj_of_reduceAux2 rK35 T35_35_2 (by decide)

theorem hcardT35_35_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK35)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK35 ⟨35, by decide⟩ R35_2 hpxR35_2 hcardq35_2 (by decide)).symm

/-- **Cell (35, 35) twin (q=2).** -/
theorem cell35_35_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK35) e = true)
    (h : ↥(reps (⟨35, by decide⟩ : Fin 148))) :
    species (reps (⟨35, by decide⟩ : Fin 148)) h (basisElt (reps rK35) (charOfVec2 rK35 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK35 e (h : Coordinate 2) T35_35_2 i :=
  species_entry_eq_sum rK35 ⟨35, by decide⟩ e heK h T35_35_2 hfix35_35_2 hinj35_35_2 hcardT35_35_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨35, by decide⟩) (reps rK35) (T35_35_2 i) (hfix35_35_2 i) h)

end Q2

end LeanDring.P5Presentation
