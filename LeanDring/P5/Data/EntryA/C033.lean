/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, A-block data (rK = 45): certified per-cell species-entry instantiations, both twins.

Emit-embed-decide loop for order-25 A-block class `rK = 45` (`|G/K| = 125`).
All nonzero `H`-columns (`|gH| ≤ 2`, `t⁻¹Ht ⊆ K`).  Full 125-coset transversal
`R45` and each `H`-fixed sub-transversal `T45_rH` embedded as kernel data and
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

def rK45 : Fin 148 := ⟨45, by decide⟩

def R45list : List Coordinates := [(0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,1,0,0)]
def R45 : Fin 125 → Coordinate 1 := fun i => R45list.getD i.val (0,0,0,0,0)

theorem hpxR45 : Function.Injective (fun i => reduceAux 1 (basisAt rK45) (R45 i)) := by decide
theorem hcardq45 : Nat.card (Coordinate 1 ⧸ reps rK45) = 125 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (45, 0): |T| = 125 -/

def T45_0list : List Coordinates := [(0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,1,0,0)]
def T45_0 : Fin 125 → Coordinate 1 := fun i => T45_0list.getD i.val (0,0,0,0,0)

theorem hfix45_0 : ∀ i, ((T45_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK45)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45) :=
  repsFix_of_siftB rK45 ⟨0, by decide⟩ T45_0 (by decide)

theorem hinj45_0 : Function.Injective
    (fun i => ((T45_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK45)) :=
  repsInj_of_reduceAux rK45 T45_0 (by decide)

theorem hcardT45_0 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK45 ⟨0, by decide⟩ R45 hpxR45 hcardq45 (by decide)).symm

/-- **Cell (45, 0).** -/
theorem cell45_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK45) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK45) (charOfVec rK45 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK45 e (h : Coordinate 1) T45_0 i :=
  species_entry_eq_sum rK45 ⟨0, by decide⟩ e heK h T45_0 hfix45_0 hinj45_0 hcardT45_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK45) (T45_0 i) (hfix45_0 i) h)

/-! ## Cell (45, 12): |T| = 125 -/

def T45_12list : List Coordinates := [(0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,1,0,0)]
def T45_12 : Fin 125 → Coordinate 1 := fun i => T45_12list.getD i.val (0,0,0,0,0)

theorem hfix45_12 : ∀ i, ((T45_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK45)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45) :=
  repsFix_of_siftB rK45 ⟨12, by decide⟩ T45_12 (by decide)

theorem hinj45_12 : Function.Injective
    (fun i => ((T45_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK45)) :=
  repsInj_of_reduceAux rK45 T45_12 (by decide)

theorem hcardT45_12 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK45 ⟨12, by decide⟩ R45 hpxR45 hcardq45 (by decide)).symm

/-- **Cell (45, 12).** -/
theorem cell45_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK45) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK45) (charOfVec rK45 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK45 e (h : Coordinate 1) T45_12 i :=
  species_entry_eq_sum rK45 ⟨12, by decide⟩ e heK h T45_12 hfix45_12 hinj45_12 hcardT45_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK45) (T45_12 i) (hfix45_12 i) h)

/-! ## Cell (45, 45): |T| = 25 -/

def T45_45list : List Coordinates := [(0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0)]
def T45_45 : Fin 25 → Coordinate 1 := fun i => T45_45list.getD i.val (0,0,0,0,0)

theorem hfix45_45 : ∀ i, ((T45_45 i : Coordinate 1) : Coordinate 1 ⧸ reps rK45)
    ∈ fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45) :=
  repsFix_of_siftB rK45 ⟨45, by decide⟩ T45_45 (by decide)

theorem hinj45_45 : Function.Injective
    (fun i => ((T45_45 i : Coordinate 1) : Coordinate 1 ⧸ reps rK45)) :=
  repsInj_of_reduceAux rK45 T45_45 (by decide)

theorem hcardT45_45 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK45 ⟨45, by decide⟩ R45 hpxR45 hcardq45 (by decide)).symm

/-- **Cell (45, 45).** -/
theorem cell45_45 (e : List (ZMod 25)) (heK : charOK (basisAt rK45) e = true)
    (h : ↥(reps (⟨45, by decide⟩ : Fin 148))) :
    species (reps (⟨45, by decide⟩ : Fin 148)) h (basisElt (reps rK45) (charOfVec rK45 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK45 e (h : Coordinate 1) T45_45 i :=
  species_entry_eq_sum rK45 ⟨45, by decide⟩ e heK h T45_45 hfix45_45 hinj45_45 hcardT45_45
    (fun i => conj_mem_of_fixedPoints (reps ⟨45, by decide⟩) (reps rK45) (T45_45 i) (hfix45_45 i) h)

namespace Q2

def R45_2 : Fin 125 → Coordinate 2 := fun i => R45list.getD i.val (0,0,0,0,0)
theorem hpxR45_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK45) (R45_2 i)) := by decide
theorem hcardq45_2 : Nat.card (Coordinate 2 ⧸ reps rK45) = 125 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (45, 0) twin -/

def T45_0_2 : Fin 125 → Coordinate 2 := fun i => T45_0list.getD i.val (0,0,0,0,0)

theorem hfix45_0_2 : ∀ i, ((T45_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK45)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK45) :=
  repsFix_of_siftB2 rK45 ⟨0, by decide⟩ T45_0_2 (by decide)

theorem hinj45_0_2 : Function.Injective
    (fun i => ((T45_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK45)) :=
  repsInj_of_reduceAux2 rK45 T45_0_2 (by decide)

theorem hcardT45_0_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK45)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK45 ⟨0, by decide⟩ R45_2 hpxR45_2 hcardq45_2 (by decide)).symm

/-- **Cell (45, 0) twin (q=2).** -/
theorem cell45_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK45) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK45) (charOfVec2 rK45 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK45 e (h : Coordinate 2) T45_0_2 i :=
  species_entry_eq_sum rK45 ⟨0, by decide⟩ e heK h T45_0_2 hfix45_0_2 hinj45_0_2 hcardT45_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK45) (T45_0_2 i) (hfix45_0_2 i) h)

/-! ### Cell (45, 12) twin -/

def T45_12_2 : Fin 125 → Coordinate 2 := fun i => T45_12list.getD i.val (0,0,0,0,0)

theorem hfix45_12_2 : ∀ i, ((T45_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK45)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK45) :=
  repsFix_of_siftB2 rK45 ⟨12, by decide⟩ T45_12_2 (by decide)

theorem hinj45_12_2 : Function.Injective
    (fun i => ((T45_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK45)) :=
  repsInj_of_reduceAux2 rK45 T45_12_2 (by decide)

theorem hcardT45_12_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK45)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK45 ⟨12, by decide⟩ R45_2 hpxR45_2 hcardq45_2 (by decide)).symm

/-- **Cell (45, 12) twin (q=2).** -/
theorem cell45_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK45) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK45) (charOfVec2 rK45 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK45 e (h : Coordinate 2) T45_12_2 i :=
  species_entry_eq_sum rK45 ⟨12, by decide⟩ e heK h T45_12_2 hfix45_12_2 hinj45_12_2 hcardT45_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK45) (T45_12_2 i) (hfix45_12_2 i) h)

/-! ### Cell (45, 45) twin -/

def T45_45_2 : Fin 25 → Coordinate 2 := fun i => T45_45list.getD i.val (0,0,0,0,0)

theorem hfix45_45_2 : ∀ i, ((T45_45_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK45)
    ∈ fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK45) :=
  repsFix_of_siftB2 rK45 ⟨45, by decide⟩ T45_45_2 (by decide)

theorem hinj45_45_2 : Function.Injective
    (fun i => ((T45_45_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK45)) :=
  repsInj_of_reduceAux2 rK45 T45_45_2 (by decide)

theorem hcardT45_45_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK45)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK45 ⟨45, by decide⟩ R45_2 hpxR45_2 hcardq45_2 (by decide)).symm

/-- **Cell (45, 45) twin (q=2).** -/
theorem cell45_45_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK45) e = true)
    (h : ↥(reps (⟨45, by decide⟩ : Fin 148))) :
    species (reps (⟨45, by decide⟩ : Fin 148)) h (basisElt (reps rK45) (charOfVec2 rK45 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK45 e (h : Coordinate 2) T45_45_2 i :=
  species_entry_eq_sum rK45 ⟨45, by decide⟩ e heK h T45_45_2 hfix45_45_2 hinj45_45_2 hcardT45_45_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨45, by decide⟩) (reps rK45) (T45_45_2 i) (hfix45_45_2 i) h)

end Q2

end LeanDring.P5Presentation
