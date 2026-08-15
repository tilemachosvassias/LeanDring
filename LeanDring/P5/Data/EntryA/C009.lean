/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, A-block data (rK = 21): certified per-cell species-entry instantiations, both twins.

Emit-embed-decide loop for order-25 A-block class `rK = 21` (`|G/K| = 125`).
All nonzero `H`-columns (`|gH| ≤ 2`, `t⁻¹Ht ⊆ K`).  Full 125-coset transversal
`R21` and each `H`-fixed sub-transversal `T21_rH` embedded as kernel data and
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

def rK21 : Fin 148 := ⟨21, by decide⟩

def R21list : List Coordinates := [(0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0)]
def R21 : Fin 125 → Coordinate 1 := fun i => R21list.getD i.val (0,0,0,0,0)

theorem hpxR21 : Function.Injective (fun i => reduceAux 1 (basisAt rK21) (R21 i)) := by decide
theorem hcardq21 : Nat.card (Coordinate 1 ⧸ reps rK21) = 125 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (21, 0): |T| = 125 -/

def T21_0list : List Coordinates := [(0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0)]
def T21_0 : Fin 125 → Coordinate 1 := fun i => T21_0list.getD i.val (0,0,0,0,0)

theorem hfix21_0 : ∀ i, ((T21_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK21)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21) :=
  repsFix_of_siftB rK21 ⟨0, by decide⟩ T21_0 (by decide)

theorem hinj21_0 : Function.Injective
    (fun i => ((T21_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK21)) :=
  repsInj_of_reduceAux rK21 T21_0 (by decide)

theorem hcardT21_0 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK21 ⟨0, by decide⟩ R21 hpxR21 hcardq21 (by decide)).symm

/-- **Cell (21, 0).** -/
theorem cell21_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK21) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK21) (charOfVec rK21 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK21 e (h : Coordinate 1) T21_0 i :=
  species_entry_eq_sum rK21 ⟨0, by decide⟩ e heK h T21_0 hfix21_0 hinj21_0 hcardT21_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK21) (T21_0 i) (hfix21_0 i) h)

/-! ## Cell (21, 3): |T| = 25 -/

def T21_3list : List Coordinates := [(0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0)]
def T21_3 : Fin 25 → Coordinate 1 := fun i => T21_3list.getD i.val (0,0,0,0,0)

theorem hfix21_3 : ∀ i, ((T21_3 i : Coordinate 1) : Coordinate 1 ⧸ reps rK21)
    ∈ fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21) :=
  repsFix_of_siftB rK21 ⟨3, by decide⟩ T21_3 (by decide)

theorem hinj21_3 : Function.Injective
    (fun i => ((T21_3 i : Coordinate 1) : Coordinate 1 ⧸ reps rK21)) :=
  repsInj_of_reduceAux rK21 T21_3 (by decide)

theorem hcardT21_3 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK21 ⟨3, by decide⟩ R21 hpxR21 hcardq21 (by decide)).symm

/-- **Cell (21, 3).** -/
theorem cell21_3 (e : List (ZMod 25)) (heK : charOK (basisAt rK21) e = true)
    (h : ↥(reps (⟨3, by decide⟩ : Fin 148))) :
    species (reps (⟨3, by decide⟩ : Fin 148)) h (basisElt (reps rK21) (charOfVec rK21 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK21 e (h : Coordinate 1) T21_3 i :=
  species_entry_eq_sum rK21 ⟨3, by decide⟩ e heK h T21_3 hfix21_3 hinj21_3 hcardT21_3
    (fun i => conj_mem_of_fixedPoints (reps ⟨3, by decide⟩) (reps rK21) (T21_3 i) (hfix21_3 i) h)

/-! ## Cell (21, 12): |T| = 125 -/

def T21_12list : List Coordinates := [(0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0)]
def T21_12 : Fin 125 → Coordinate 1 := fun i => T21_12list.getD i.val (0,0,0,0,0)

theorem hfix21_12 : ∀ i, ((T21_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK21)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21) :=
  repsFix_of_siftB rK21 ⟨12, by decide⟩ T21_12 (by decide)

theorem hinj21_12 : Function.Injective
    (fun i => ((T21_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK21)) :=
  repsInj_of_reduceAux rK21 T21_12 (by decide)

theorem hcardT21_12 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK21 ⟨12, by decide⟩ R21 hpxR21 hcardq21 (by decide)).symm

/-- **Cell (21, 12).** -/
theorem cell21_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK21) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK21) (charOfVec rK21 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK21 e (h : Coordinate 1) T21_12 i :=
  species_entry_eq_sum rK21 ⟨12, by decide⟩ e heK h T21_12 hfix21_12 hinj21_12 hcardT21_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK21) (T21_12 i) (hfix21_12 i) h)

/-! ## Cell (21, 21): |T| = 25 -/

def T21_21list : List Coordinates := [(0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0)]
def T21_21 : Fin 25 → Coordinate 1 := fun i => T21_21list.getD i.val (0,0,0,0,0)

theorem hfix21_21 : ∀ i, ((T21_21 i : Coordinate 1) : Coordinate 1 ⧸ reps rK21)
    ∈ fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21) :=
  repsFix_of_siftB rK21 ⟨21, by decide⟩ T21_21 (by decide)

theorem hinj21_21 : Function.Injective
    (fun i => ((T21_21 i : Coordinate 1) : Coordinate 1 ⧸ reps rK21)) :=
  repsInj_of_reduceAux rK21 T21_21 (by decide)

theorem hcardT21_21 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK21 ⟨21, by decide⟩ R21 hpxR21 hcardq21 (by decide)).symm

/-- **Cell (21, 21).** -/
theorem cell21_21 (e : List (ZMod 25)) (heK : charOK (basisAt rK21) e = true)
    (h : ↥(reps (⟨21, by decide⟩ : Fin 148))) :
    species (reps (⟨21, by decide⟩ : Fin 148)) h (basisElt (reps rK21) (charOfVec rK21 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK21 e (h : Coordinate 1) T21_21 i :=
  species_entry_eq_sum rK21 ⟨21, by decide⟩ e heK h T21_21 hfix21_21 hinj21_21 hcardT21_21
    (fun i => conj_mem_of_fixedPoints (reps ⟨21, by decide⟩) (reps rK21) (T21_21 i) (hfix21_21 i) h)

namespace Q2

def R21_2 : Fin 125 → Coordinate 2 := fun i => R21list.getD i.val (0,0,0,0,0)
theorem hpxR21_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK21) (R21_2 i)) := by decide
theorem hcardq21_2 : Nat.card (Coordinate 2 ⧸ reps rK21) = 125 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (21, 0) twin -/

def T21_0_2 : Fin 125 → Coordinate 2 := fun i => T21_0list.getD i.val (0,0,0,0,0)

theorem hfix21_0_2 : ∀ i, ((T21_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK21)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK21) :=
  repsFix_of_siftB2 rK21 ⟨0, by decide⟩ T21_0_2 (by decide)

theorem hinj21_0_2 : Function.Injective
    (fun i => ((T21_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK21)) :=
  repsInj_of_reduceAux2 rK21 T21_0_2 (by decide)

theorem hcardT21_0_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK21)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK21 ⟨0, by decide⟩ R21_2 hpxR21_2 hcardq21_2 (by decide)).symm

/-- **Cell (21, 0) twin (q=2).** -/
theorem cell21_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK21) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK21) (charOfVec2 rK21 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK21 e (h : Coordinate 2) T21_0_2 i :=
  species_entry_eq_sum rK21 ⟨0, by decide⟩ e heK h T21_0_2 hfix21_0_2 hinj21_0_2 hcardT21_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK21) (T21_0_2 i) (hfix21_0_2 i) h)

/-! ### Cell (21, 3) twin -/

def T21_3_2 : Fin 25 → Coordinate 2 := fun i => T21_3list.getD i.val (0,0,0,0,0)

theorem hfix21_3_2 : ∀ i, ((T21_3_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK21)
    ∈ fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK21) :=
  repsFix_of_siftB2 rK21 ⟨3, by decide⟩ T21_3_2 (by decide)

theorem hinj21_3_2 : Function.Injective
    (fun i => ((T21_3_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK21)) :=
  repsInj_of_reduceAux2 rK21 T21_3_2 (by decide)

theorem hcardT21_3_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK21)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK21 ⟨3, by decide⟩ R21_2 hpxR21_2 hcardq21_2 (by decide)).symm

/-- **Cell (21, 3) twin (q=2).** -/
theorem cell21_3_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK21) e = true)
    (h : ↥(reps (⟨3, by decide⟩ : Fin 148))) :
    species (reps (⟨3, by decide⟩ : Fin 148)) h (basisElt (reps rK21) (charOfVec2 rK21 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK21 e (h : Coordinate 2) T21_3_2 i :=
  species_entry_eq_sum rK21 ⟨3, by decide⟩ e heK h T21_3_2 hfix21_3_2 hinj21_3_2 hcardT21_3_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨3, by decide⟩) (reps rK21) (T21_3_2 i) (hfix21_3_2 i) h)

/-! ### Cell (21, 12) twin -/

def T21_12_2 : Fin 125 → Coordinate 2 := fun i => T21_12list.getD i.val (0,0,0,0,0)

theorem hfix21_12_2 : ∀ i, ((T21_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK21)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK21) :=
  repsFix_of_siftB2 rK21 ⟨12, by decide⟩ T21_12_2 (by decide)

theorem hinj21_12_2 : Function.Injective
    (fun i => ((T21_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK21)) :=
  repsInj_of_reduceAux2 rK21 T21_12_2 (by decide)

theorem hcardT21_12_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK21)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK21 ⟨12, by decide⟩ R21_2 hpxR21_2 hcardq21_2 (by decide)).symm

/-- **Cell (21, 12) twin (q=2).** -/
theorem cell21_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK21) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK21) (charOfVec2 rK21 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK21 e (h : Coordinate 2) T21_12_2 i :=
  species_entry_eq_sum rK21 ⟨12, by decide⟩ e heK h T21_12_2 hfix21_12_2 hinj21_12_2 hcardT21_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK21) (T21_12_2 i) (hfix21_12_2 i) h)

/-! ### Cell (21, 21) twin -/

def T21_21_2 : Fin 25 → Coordinate 2 := fun i => T21_21list.getD i.val (0,0,0,0,0)

theorem hfix21_21_2 : ∀ i, ((T21_21_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK21)
    ∈ fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK21) :=
  repsFix_of_siftB2 rK21 ⟨21, by decide⟩ T21_21_2 (by decide)

theorem hinj21_21_2 : Function.Injective
    (fun i => ((T21_21_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK21)) :=
  repsInj_of_reduceAux2 rK21 T21_21_2 (by decide)

theorem hcardT21_21_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK21)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK21 ⟨21, by decide⟩ R21_2 hpxR21_2 hcardq21_2 (by decide)).symm

/-- **Cell (21, 21) twin (q=2).** -/
theorem cell21_21_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK21) e = true)
    (h : ↥(reps (⟨21, by decide⟩ : Fin 148))) :
    species (reps (⟨21, by decide⟩ : Fin 148)) h (basisElt (reps rK21) (charOfVec2 rK21 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK21 e (h : Coordinate 2) T21_21_2 i :=
  species_entry_eq_sum rK21 ⟨21, by decide⟩ e heK h T21_21_2 hfix21_21_2 hinj21_21_2 hcardT21_21_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨21, by decide⟩) (reps rK21) (T21_21_2 i) (hfix21_21_2 i) h)

end Q2

end LeanDring.P5Presentation
