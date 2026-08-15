/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, A-block data (rK = 22): certified per-cell species-entry instantiations, both twins.

Emit-embed-decide loop for order-25 A-block class `rK = 22` (`|G/K| = 125`).
All nonzero `H`-columns (`|gH| ≤ 2`, `t⁻¹Ht ⊆ K`).  Full 125-coset transversal
`R22` and each `H`-fixed sub-transversal `T22_rH` embedded as kernel data and
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

def rK22 : Fin 148 := ⟨22, by decide⟩

def R22list : List Coordinates := [(0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0)]
def R22 : Fin 125 → Coordinate 1 := fun i => R22list.getD i.val (0,0,0,0,0)

theorem hpxR22 : Function.Injective (fun i => reduceAux 1 (basisAt rK22) (R22 i)) := by decide
theorem hcardq22 : Nat.card (Coordinate 1 ⧸ reps rK22) = 125 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (22, 0): |T| = 125 -/

def T22_0list : List Coordinates := [(0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0)]
def T22_0 : Fin 125 → Coordinate 1 := fun i => T22_0list.getD i.val (0,0,0,0,0)

theorem hfix22_0 : ∀ i, ((T22_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK22)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22) :=
  repsFix_of_siftB rK22 ⟨0, by decide⟩ T22_0 (by decide)

theorem hinj22_0 : Function.Injective
    (fun i => ((T22_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK22)) :=
  repsInj_of_reduceAux rK22 T22_0 (by decide)

theorem hcardT22_0 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK22 ⟨0, by decide⟩ R22 hpxR22 hcardq22 (by decide)).symm

/-- **Cell (22, 0).** -/
theorem cell22_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK22) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK22) (charOfVec rK22 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK22 e (h : Coordinate 1) T22_0 i :=
  species_entry_eq_sum rK22 ⟨0, by decide⟩ e heK h T22_0 hfix22_0 hinj22_0 hcardT22_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK22) (T22_0 i) (hfix22_0 i) h)

/-! ## Cell (22, 4): |T| = 25 -/

def T22_4list : List Coordinates := [(0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0)]
def T22_4 : Fin 25 → Coordinate 1 := fun i => T22_4list.getD i.val (0,0,0,0,0)

theorem hfix22_4 : ∀ i, ((T22_4 i : Coordinate 1) : Coordinate 1 ⧸ reps rK22)
    ∈ fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22) :=
  repsFix_of_siftB rK22 ⟨4, by decide⟩ T22_4 (by decide)

theorem hinj22_4 : Function.Injective
    (fun i => ((T22_4 i : Coordinate 1) : Coordinate 1 ⧸ reps rK22)) :=
  repsInj_of_reduceAux rK22 T22_4 (by decide)

theorem hcardT22_4 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK22 ⟨4, by decide⟩ R22 hpxR22 hcardq22 (by decide)).symm

/-- **Cell (22, 4).** -/
theorem cell22_4 (e : List (ZMod 25)) (heK : charOK (basisAt rK22) e = true)
    (h : ↥(reps (⟨4, by decide⟩ : Fin 148))) :
    species (reps (⟨4, by decide⟩ : Fin 148)) h (basisElt (reps rK22) (charOfVec rK22 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK22 e (h : Coordinate 1) T22_4 i :=
  species_entry_eq_sum rK22 ⟨4, by decide⟩ e heK h T22_4 hfix22_4 hinj22_4 hcardT22_4
    (fun i => conj_mem_of_fixedPoints (reps ⟨4, by decide⟩) (reps rK22) (T22_4 i) (hfix22_4 i) h)

/-! ## Cell (22, 12): |T| = 125 -/

def T22_12list : List Coordinates := [(0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0)]
def T22_12 : Fin 125 → Coordinate 1 := fun i => T22_12list.getD i.val (0,0,0,0,0)

theorem hfix22_12 : ∀ i, ((T22_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK22)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22) :=
  repsFix_of_siftB rK22 ⟨12, by decide⟩ T22_12 (by decide)

theorem hinj22_12 : Function.Injective
    (fun i => ((T22_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK22)) :=
  repsInj_of_reduceAux rK22 T22_12 (by decide)

theorem hcardT22_12 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK22 ⟨12, by decide⟩ R22 hpxR22 hcardq22 (by decide)).symm

/-- **Cell (22, 12).** -/
theorem cell22_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK22) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK22) (charOfVec rK22 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK22 e (h : Coordinate 1) T22_12 i :=
  species_entry_eq_sum rK22 ⟨12, by decide⟩ e heK h T22_12 hfix22_12 hinj22_12 hcardT22_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK22) (T22_12 i) (hfix22_12 i) h)

/-! ## Cell (22, 22): |T| = 25 -/

def T22_22list : List Coordinates := [(0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0)]
def T22_22 : Fin 25 → Coordinate 1 := fun i => T22_22list.getD i.val (0,0,0,0,0)

theorem hfix22_22 : ∀ i, ((T22_22 i : Coordinate 1) : Coordinate 1 ⧸ reps rK22)
    ∈ fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22) :=
  repsFix_of_siftB rK22 ⟨22, by decide⟩ T22_22 (by decide)

theorem hinj22_22 : Function.Injective
    (fun i => ((T22_22 i : Coordinate 1) : Coordinate 1 ⧸ reps rK22)) :=
  repsInj_of_reduceAux rK22 T22_22 (by decide)

theorem hcardT22_22 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK22 ⟨22, by decide⟩ R22 hpxR22 hcardq22 (by decide)).symm

/-- **Cell (22, 22).** -/
theorem cell22_22 (e : List (ZMod 25)) (heK : charOK (basisAt rK22) e = true)
    (h : ↥(reps (⟨22, by decide⟩ : Fin 148))) :
    species (reps (⟨22, by decide⟩ : Fin 148)) h (basisElt (reps rK22) (charOfVec rK22 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK22 e (h : Coordinate 1) T22_22 i :=
  species_entry_eq_sum rK22 ⟨22, by decide⟩ e heK h T22_22 hfix22_22 hinj22_22 hcardT22_22
    (fun i => conj_mem_of_fixedPoints (reps ⟨22, by decide⟩) (reps rK22) (T22_22 i) (hfix22_22 i) h)

namespace Q2

def R22_2 : Fin 125 → Coordinate 2 := fun i => R22list.getD i.val (0,0,0,0,0)
theorem hpxR22_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK22) (R22_2 i)) := by decide
theorem hcardq22_2 : Nat.card (Coordinate 2 ⧸ reps rK22) = 125 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (22, 0) twin -/

def T22_0_2 : Fin 125 → Coordinate 2 := fun i => T22_0list.getD i.val (0,0,0,0,0)

theorem hfix22_0_2 : ∀ i, ((T22_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK22)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK22) :=
  repsFix_of_siftB2 rK22 ⟨0, by decide⟩ T22_0_2 (by decide)

theorem hinj22_0_2 : Function.Injective
    (fun i => ((T22_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK22)) :=
  repsInj_of_reduceAux2 rK22 T22_0_2 (by decide)

theorem hcardT22_0_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK22)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK22 ⟨0, by decide⟩ R22_2 hpxR22_2 hcardq22_2 (by decide)).symm

/-- **Cell (22, 0) twin (q=2).** -/
theorem cell22_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK22) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK22) (charOfVec2 rK22 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK22 e (h : Coordinate 2) T22_0_2 i :=
  species_entry_eq_sum rK22 ⟨0, by decide⟩ e heK h T22_0_2 hfix22_0_2 hinj22_0_2 hcardT22_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK22) (T22_0_2 i) (hfix22_0_2 i) h)

/-! ### Cell (22, 4) twin -/

def T22_4_2 : Fin 25 → Coordinate 2 := fun i => T22_4list.getD i.val (0,0,0,0,0)

theorem hfix22_4_2 : ∀ i, ((T22_4_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK22)
    ∈ fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK22) :=
  repsFix_of_siftB2 rK22 ⟨4, by decide⟩ T22_4_2 (by decide)

theorem hinj22_4_2 : Function.Injective
    (fun i => ((T22_4_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK22)) :=
  repsInj_of_reduceAux2 rK22 T22_4_2 (by decide)

theorem hcardT22_4_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK22)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK22 ⟨4, by decide⟩ R22_2 hpxR22_2 hcardq22_2 (by decide)).symm

/-- **Cell (22, 4) twin (q=2).** -/
theorem cell22_4_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK22) e = true)
    (h : ↥(reps (⟨4, by decide⟩ : Fin 148))) :
    species (reps (⟨4, by decide⟩ : Fin 148)) h (basisElt (reps rK22) (charOfVec2 rK22 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK22 e (h : Coordinate 2) T22_4_2 i :=
  species_entry_eq_sum rK22 ⟨4, by decide⟩ e heK h T22_4_2 hfix22_4_2 hinj22_4_2 hcardT22_4_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨4, by decide⟩) (reps rK22) (T22_4_2 i) (hfix22_4_2 i) h)

/-! ### Cell (22, 12) twin -/

def T22_12_2 : Fin 125 → Coordinate 2 := fun i => T22_12list.getD i.val (0,0,0,0,0)

theorem hfix22_12_2 : ∀ i, ((T22_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK22)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK22) :=
  repsFix_of_siftB2 rK22 ⟨12, by decide⟩ T22_12_2 (by decide)

theorem hinj22_12_2 : Function.Injective
    (fun i => ((T22_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK22)) :=
  repsInj_of_reduceAux2 rK22 T22_12_2 (by decide)

theorem hcardT22_12_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK22)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK22 ⟨12, by decide⟩ R22_2 hpxR22_2 hcardq22_2 (by decide)).symm

/-- **Cell (22, 12) twin (q=2).** -/
theorem cell22_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK22) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK22) (charOfVec2 rK22 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK22 e (h : Coordinate 2) T22_12_2 i :=
  species_entry_eq_sum rK22 ⟨12, by decide⟩ e heK h T22_12_2 hfix22_12_2 hinj22_12_2 hcardT22_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK22) (T22_12_2 i) (hfix22_12_2 i) h)

/-! ### Cell (22, 22) twin -/

def T22_22_2 : Fin 25 → Coordinate 2 := fun i => T22_22list.getD i.val (0,0,0,0,0)

theorem hfix22_22_2 : ∀ i, ((T22_22_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK22)
    ∈ fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK22) :=
  repsFix_of_siftB2 rK22 ⟨22, by decide⟩ T22_22_2 (by decide)

theorem hinj22_22_2 : Function.Injective
    (fun i => ((T22_22_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK22)) :=
  repsInj_of_reduceAux2 rK22 T22_22_2 (by decide)

theorem hcardT22_22_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK22)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK22 ⟨22, by decide⟩ R22_2 hpxR22_2 hcardq22_2 (by decide)).symm

/-- **Cell (22, 22) twin (q=2).** -/
theorem cell22_22_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK22) e = true)
    (h : ↥(reps (⟨22, by decide⟩ : Fin 148))) :
    species (reps (⟨22, by decide⟩ : Fin 148)) h (basisElt (reps rK22) (charOfVec2 rK22 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK22 e (h : Coordinate 2) T22_22_2 i :=
  species_entry_eq_sum rK22 ⟨22, by decide⟩ e heK h T22_22_2 hfix22_22_2 hinj22_22_2 hcardT22_22_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨22, by decide⟩) (reps rK22) (T22_22_2 i) (hfix22_22_2 i) h)

end Q2

end LeanDring.P5Presentation
