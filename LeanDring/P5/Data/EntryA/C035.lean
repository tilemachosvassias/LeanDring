/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, A-block data (rK = 47): certified per-cell species-entry instantiations, both twins.

Emit-embed-decide loop for order-25 A-block class `rK = 47` (`|G/K| = 125`).
All nonzero `H`-columns (`|gH| ≤ 2`, `t⁻¹Ht ⊆ K`).  Full 125-coset transversal
`R47` and each `H`-fixed sub-transversal `T47_rH` embedded as kernel data and
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

def rK47 : Fin 148 := ⟨47, by decide⟩

def R47list : List Coordinates := [(0,1,1,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0)]
def R47 : Fin 125 → Coordinate 1 := fun i => R47list.getD i.val (0,0,0,0,0)

theorem hpxR47 : Function.Injective (fun i => reduceAux 1 (basisAt rK47) (R47 i)) := by decide
theorem hcardq47 : Nat.card (Coordinate 1 ⧸ reps rK47) = 125 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (47, 0): |T| = 125 -/

def T47_0list : List Coordinates := [(0,1,1,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0)]
def T47_0 : Fin 125 → Coordinate 1 := fun i => T47_0list.getD i.val (0,0,0,0,0)

theorem hfix47_0 : ∀ i, ((T47_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK47)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47) :=
  repsFix_of_siftB rK47 ⟨0, by decide⟩ T47_0 (by decide)

theorem hinj47_0 : Function.Injective
    (fun i => ((T47_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK47)) :=
  repsInj_of_reduceAux rK47 T47_0 (by decide)

theorem hcardT47_0 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK47 ⟨0, by decide⟩ R47 hpxR47 hcardq47 (by decide)).symm

/-- **Cell (47, 0).** -/
theorem cell47_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK47) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK47) (charOfVec rK47 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK47 e (h : Coordinate 1) T47_0 i :=
  species_entry_eq_sum rK47 ⟨0, by decide⟩ e heK h T47_0 hfix47_0 hinj47_0 hcardT47_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK47) (T47_0 i) (hfix47_0 i) h)

/-! ## Cell (47, 12): |T| = 125 -/

def T47_12list : List Coordinates := [(0,1,1,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0)]
def T47_12 : Fin 125 → Coordinate 1 := fun i => T47_12list.getD i.val (0,0,0,0,0)

theorem hfix47_12 : ∀ i, ((T47_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK47)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47) :=
  repsFix_of_siftB rK47 ⟨12, by decide⟩ T47_12 (by decide)

theorem hinj47_12 : Function.Injective
    (fun i => ((T47_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK47)) :=
  repsInj_of_reduceAux rK47 T47_12 (by decide)

theorem hcardT47_12 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK47 ⟨12, by decide⟩ R47 hpxR47 hcardq47 (by decide)).symm

/-- **Cell (47, 12).** -/
theorem cell47_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK47) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK47) (charOfVec rK47 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK47 e (h : Coordinate 1) T47_12 i :=
  species_entry_eq_sum rK47 ⟨12, by decide⟩ e heK h T47_12 hfix47_12 hinj47_12 hcardT47_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK47) (T47_12 i) (hfix47_12 i) h)

/-! ## Cell (47, 47): |T| = 25 -/

def T47_47list : List Coordinates := [(0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0)]
def T47_47 : Fin 25 → Coordinate 1 := fun i => T47_47list.getD i.val (0,0,0,0,0)

theorem hfix47_47 : ∀ i, ((T47_47 i : Coordinate 1) : Coordinate 1 ⧸ reps rK47)
    ∈ fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47) :=
  repsFix_of_siftB rK47 ⟨47, by decide⟩ T47_47 (by decide)

theorem hinj47_47 : Function.Injective
    (fun i => ((T47_47 i : Coordinate 1) : Coordinate 1 ⧸ reps rK47)) :=
  repsInj_of_reduceAux rK47 T47_47 (by decide)

theorem hcardT47_47 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK47 ⟨47, by decide⟩ R47 hpxR47 hcardq47 (by decide)).symm

/-- **Cell (47, 47).** -/
theorem cell47_47 (e : List (ZMod 25)) (heK : charOK (basisAt rK47) e = true)
    (h : ↥(reps (⟨47, by decide⟩ : Fin 148))) :
    species (reps (⟨47, by decide⟩ : Fin 148)) h (basisElt (reps rK47) (charOfVec rK47 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK47 e (h : Coordinate 1) T47_47 i :=
  species_entry_eq_sum rK47 ⟨47, by decide⟩ e heK h T47_47 hfix47_47 hinj47_47 hcardT47_47
    (fun i => conj_mem_of_fixedPoints (reps ⟨47, by decide⟩) (reps rK47) (T47_47 i) (hfix47_47 i) h)

namespace Q2

def R47_2 : Fin 125 → Coordinate 2 := fun i => R47list.getD i.val (0,0,0,0,0)
theorem hpxR47_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK47) (R47_2 i)) := by decide
theorem hcardq47_2 : Nat.card (Coordinate 2 ⧸ reps rK47) = 125 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (47, 0) twin -/

def T47_0_2 : Fin 125 → Coordinate 2 := fun i => T47_0list.getD i.val (0,0,0,0,0)

theorem hfix47_0_2 : ∀ i, ((T47_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK47)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK47) :=
  repsFix_of_siftB2 rK47 ⟨0, by decide⟩ T47_0_2 (by decide)

theorem hinj47_0_2 : Function.Injective
    (fun i => ((T47_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK47)) :=
  repsInj_of_reduceAux2 rK47 T47_0_2 (by decide)

theorem hcardT47_0_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK47)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK47 ⟨0, by decide⟩ R47_2 hpxR47_2 hcardq47_2 (by decide)).symm

/-- **Cell (47, 0) twin (q=2).** -/
theorem cell47_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK47) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK47) (charOfVec2 rK47 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK47 e (h : Coordinate 2) T47_0_2 i :=
  species_entry_eq_sum rK47 ⟨0, by decide⟩ e heK h T47_0_2 hfix47_0_2 hinj47_0_2 hcardT47_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK47) (T47_0_2 i) (hfix47_0_2 i) h)

/-! ### Cell (47, 12) twin -/

def T47_12_2 : Fin 125 → Coordinate 2 := fun i => T47_12list.getD i.val (0,0,0,0,0)

theorem hfix47_12_2 : ∀ i, ((T47_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK47)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK47) :=
  repsFix_of_siftB2 rK47 ⟨12, by decide⟩ T47_12_2 (by decide)

theorem hinj47_12_2 : Function.Injective
    (fun i => ((T47_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK47)) :=
  repsInj_of_reduceAux2 rK47 T47_12_2 (by decide)

theorem hcardT47_12_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK47)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK47 ⟨12, by decide⟩ R47_2 hpxR47_2 hcardq47_2 (by decide)).symm

/-- **Cell (47, 12) twin (q=2).** -/
theorem cell47_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK47) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK47) (charOfVec2 rK47 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK47 e (h : Coordinate 2) T47_12_2 i :=
  species_entry_eq_sum rK47 ⟨12, by decide⟩ e heK h T47_12_2 hfix47_12_2 hinj47_12_2 hcardT47_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK47) (T47_12_2 i) (hfix47_12_2 i) h)

/-! ### Cell (47, 47) twin -/

def T47_47_2 : Fin 25 → Coordinate 2 := fun i => T47_47list.getD i.val (0,0,0,0,0)

theorem hfix47_47_2 : ∀ i, ((T47_47_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK47)
    ∈ fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK47) :=
  repsFix_of_siftB2 rK47 ⟨47, by decide⟩ T47_47_2 (by decide)

theorem hinj47_47_2 : Function.Injective
    (fun i => ((T47_47_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK47)) :=
  repsInj_of_reduceAux2 rK47 T47_47_2 (by decide)

theorem hcardT47_47_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK47)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK47 ⟨47, by decide⟩ R47_2 hpxR47_2 hcardq47_2 (by decide)).symm

/-- **Cell (47, 47) twin (q=2).** -/
theorem cell47_47_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK47) e = true)
    (h : ↥(reps (⟨47, by decide⟩ : Fin 148))) :
    species (reps (⟨47, by decide⟩ : Fin 148)) h (basisElt (reps rK47) (charOfVec2 rK47 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK47 e (h : Coordinate 2) T47_47_2 i :=
  species_entry_eq_sum rK47 ⟨47, by decide⟩ e heK h T47_47_2 hfix47_47_2 hinj47_47_2 hcardT47_47_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨47, by decide⟩) (reps rK47) (T47_47_2 i) (hfix47_47_2 i) h)

end Q2

end LeanDring.P5Presentation
