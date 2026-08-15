/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, A-block data (rK = 30): certified per-cell species-entry instantiations, both twins.

Emit-embed-decide loop for order-25 A-block class `rK = 30` (`|G/K| = 125`).
All nonzero `H`-columns (`|gH| ≤ 2`, `t⁻¹Ht ⊆ K`).  Full 125-coset transversal
`R30` and each `H`-fixed sub-transversal `T30_rH` embedded as kernel data and
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

def rK30 : Fin 148 := ⟨30, by decide⟩

def R30list : List Coordinates := [(0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,2,0,0)]
def R30 : Fin 125 → Coordinate 1 := fun i => R30list.getD i.val (0,0,0,0,0)

theorem hpxR30 : Function.Injective (fun i => reduceAux 1 (basisAt rK30) (R30 i)) := by decide
theorem hcardq30 : Nat.card (Coordinate 1 ⧸ reps rK30) = 125 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (30, 0): |T| = 125 -/

def T30_0list : List Coordinates := [(0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,2,0,0)]
def T30_0 : Fin 125 → Coordinate 1 := fun i => T30_0list.getD i.val (0,0,0,0,0)

theorem hfix30_0 : ∀ i, ((T30_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK30)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30) :=
  repsFix_of_siftB rK30 ⟨0, by decide⟩ T30_0 (by decide)

theorem hinj30_0 : Function.Injective
    (fun i => ((T30_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK30)) :=
  repsInj_of_reduceAux rK30 T30_0 (by decide)

theorem hcardT30_0 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK30 ⟨0, by decide⟩ R30 hpxR30 hcardq30 (by decide)).symm

/-- **Cell (30, 0).** -/
theorem cell30_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK30) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK30) (charOfVec rK30 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK30 e (h : Coordinate 1) T30_0 i :=
  species_entry_eq_sum rK30 ⟨0, by decide⟩ e heK h T30_0 hfix30_0 hinj30_0 hcardT30_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK30) (T30_0 i) (hfix30_0 i) h)

/-! ## Cell (30, 12): |T| = 125 -/

def T30_12list : List Coordinates := [(0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,2,0,0)]
def T30_12 : Fin 125 → Coordinate 1 := fun i => T30_12list.getD i.val (0,0,0,0,0)

theorem hfix30_12 : ∀ i, ((T30_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK30)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30) :=
  repsFix_of_siftB rK30 ⟨12, by decide⟩ T30_12 (by decide)

theorem hinj30_12 : Function.Injective
    (fun i => ((T30_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK30)) :=
  repsInj_of_reduceAux rK30 T30_12 (by decide)

theorem hcardT30_12 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK30 ⟨12, by decide⟩ R30 hpxR30 hcardq30 (by decide)).symm

/-- **Cell (30, 12).** -/
theorem cell30_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK30) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK30) (charOfVec rK30 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK30 e (h : Coordinate 1) T30_12 i :=
  species_entry_eq_sum rK30 ⟨12, by decide⟩ e heK h T30_12 hfix30_12 hinj30_12 hcardT30_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK30) (T30_12 i) (hfix30_12 i) h)

/-! ## Cell (30, 30): |T| = 25 -/

def T30_30list : List Coordinates := [(0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0)]
def T30_30 : Fin 25 → Coordinate 1 := fun i => T30_30list.getD i.val (0,0,0,0,0)

theorem hfix30_30 : ∀ i, ((T30_30 i : Coordinate 1) : Coordinate 1 ⧸ reps rK30)
    ∈ fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30) :=
  repsFix_of_siftB rK30 ⟨30, by decide⟩ T30_30 (by decide)

theorem hinj30_30 : Function.Injective
    (fun i => ((T30_30 i : Coordinate 1) : Coordinate 1 ⧸ reps rK30)) :=
  repsInj_of_reduceAux rK30 T30_30 (by decide)

theorem hcardT30_30 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK30 ⟨30, by decide⟩ R30 hpxR30 hcardq30 (by decide)).symm

/-- **Cell (30, 30).** -/
theorem cell30_30 (e : List (ZMod 25)) (heK : charOK (basisAt rK30) e = true)
    (h : ↥(reps (⟨30, by decide⟩ : Fin 148))) :
    species (reps (⟨30, by decide⟩ : Fin 148)) h (basisElt (reps rK30) (charOfVec rK30 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK30 e (h : Coordinate 1) T30_30 i :=
  species_entry_eq_sum rK30 ⟨30, by decide⟩ e heK h T30_30 hfix30_30 hinj30_30 hcardT30_30
    (fun i => conj_mem_of_fixedPoints (reps ⟨30, by decide⟩) (reps rK30) (T30_30 i) (hfix30_30 i) h)

namespace Q2

def R30_2 : Fin 125 → Coordinate 2 := fun i => R30list.getD i.val (0,0,0,0,0)
theorem hpxR30_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK30) (R30_2 i)) := by decide
theorem hcardq30_2 : Nat.card (Coordinate 2 ⧸ reps rK30) = 125 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (30, 0) twin -/

def T30_0_2 : Fin 125 → Coordinate 2 := fun i => T30_0list.getD i.val (0,0,0,0,0)

theorem hfix30_0_2 : ∀ i, ((T30_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK30)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK30) :=
  repsFix_of_siftB2 rK30 ⟨0, by decide⟩ T30_0_2 (by decide)

theorem hinj30_0_2 : Function.Injective
    (fun i => ((T30_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK30)) :=
  repsInj_of_reduceAux2 rK30 T30_0_2 (by decide)

theorem hcardT30_0_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK30)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK30 ⟨0, by decide⟩ R30_2 hpxR30_2 hcardq30_2 (by decide)).symm

/-- **Cell (30, 0) twin (q=2).** -/
theorem cell30_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK30) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK30) (charOfVec2 rK30 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK30 e (h : Coordinate 2) T30_0_2 i :=
  species_entry_eq_sum rK30 ⟨0, by decide⟩ e heK h T30_0_2 hfix30_0_2 hinj30_0_2 hcardT30_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK30) (T30_0_2 i) (hfix30_0_2 i) h)

/-! ### Cell (30, 12) twin -/

def T30_12_2 : Fin 125 → Coordinate 2 := fun i => T30_12list.getD i.val (0,0,0,0,0)

theorem hfix30_12_2 : ∀ i, ((T30_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK30)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK30) :=
  repsFix_of_siftB2 rK30 ⟨12, by decide⟩ T30_12_2 (by decide)

theorem hinj30_12_2 : Function.Injective
    (fun i => ((T30_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK30)) :=
  repsInj_of_reduceAux2 rK30 T30_12_2 (by decide)

theorem hcardT30_12_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK30)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK30 ⟨12, by decide⟩ R30_2 hpxR30_2 hcardq30_2 (by decide)).symm

/-- **Cell (30, 12) twin (q=2).** -/
theorem cell30_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK30) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK30) (charOfVec2 rK30 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK30 e (h : Coordinate 2) T30_12_2 i :=
  species_entry_eq_sum rK30 ⟨12, by decide⟩ e heK h T30_12_2 hfix30_12_2 hinj30_12_2 hcardT30_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK30) (T30_12_2 i) (hfix30_12_2 i) h)

/-! ### Cell (30, 30) twin -/

def T30_30_2 : Fin 25 → Coordinate 2 := fun i => T30_30list.getD i.val (0,0,0,0,0)

theorem hfix30_30_2 : ∀ i, ((T30_30_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK30)
    ∈ fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK30) :=
  repsFix_of_siftB2 rK30 ⟨30, by decide⟩ T30_30_2 (by decide)

theorem hinj30_30_2 : Function.Injective
    (fun i => ((T30_30_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK30)) :=
  repsInj_of_reduceAux2 rK30 T30_30_2 (by decide)

theorem hcardT30_30_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK30)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK30 ⟨30, by decide⟩ R30_2 hpxR30_2 hcardq30_2 (by decide)).symm

/-- **Cell (30, 30) twin (q=2).** -/
theorem cell30_30_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK30) e = true)
    (h : ↥(reps (⟨30, by decide⟩ : Fin 148))) :
    species (reps (⟨30, by decide⟩ : Fin 148)) h (basisElt (reps rK30) (charOfVec2 rK30 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK30 e (h : Coordinate 2) T30_30_2 i :=
  species_entry_eq_sum rK30 ⟨30, by decide⟩ e heK h T30_30_2 hfix30_30_2 hinj30_30_2 hcardT30_30_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨30, by decide⟩) (reps rK30) (T30_30_2 i) (hfix30_30_2 i) h)

end Q2

end LeanDring.P5Presentation
