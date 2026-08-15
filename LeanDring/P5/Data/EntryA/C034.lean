/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, A-block data (rK = 46): certified per-cell species-entry instantiations, both twins.

Emit-embed-decide loop for order-25 A-block class `rK = 46` (`|G/K| = 125`).
All nonzero `H`-columns (`|gH| ≤ 2`, `t⁻¹Ht ⊆ K`).  Full 125-coset transversal
`R46` and each `H`-fixed sub-transversal `T46_rH` embedded as kernel data and
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

def rK46 : Fin 148 := ⟨46, by decide⟩

def R46list : List Coordinates := [(0,3,3,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0)]
def R46 : Fin 125 → Coordinate 1 := fun i => R46list.getD i.val (0,0,0,0,0)

theorem hpxR46 : Function.Injective (fun i => reduceAux 1 (basisAt rK46) (R46 i)) := by decide
theorem hcardq46 : Nat.card (Coordinate 1 ⧸ reps rK46) = 125 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (46, 0): |T| = 125 -/

def T46_0list : List Coordinates := [(0,3,3,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0)]
def T46_0 : Fin 125 → Coordinate 1 := fun i => T46_0list.getD i.val (0,0,0,0,0)

theorem hfix46_0 : ∀ i, ((T46_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK46)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46) :=
  repsFix_of_siftB rK46 ⟨0, by decide⟩ T46_0 (by decide)

theorem hinj46_0 : Function.Injective
    (fun i => ((T46_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK46)) :=
  repsInj_of_reduceAux rK46 T46_0 (by decide)

theorem hcardT46_0 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK46 ⟨0, by decide⟩ R46 hpxR46 hcardq46 (by decide)).symm

/-- **Cell (46, 0).** -/
theorem cell46_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK46) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK46) (charOfVec rK46 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK46 e (h : Coordinate 1) T46_0 i :=
  species_entry_eq_sum rK46 ⟨0, by decide⟩ e heK h T46_0 hfix46_0 hinj46_0 hcardT46_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK46) (T46_0 i) (hfix46_0 i) h)

/-! ## Cell (46, 12): |T| = 125 -/

def T46_12list : List Coordinates := [(0,3,3,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0)]
def T46_12 : Fin 125 → Coordinate 1 := fun i => T46_12list.getD i.val (0,0,0,0,0)

theorem hfix46_12 : ∀ i, ((T46_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK46)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46) :=
  repsFix_of_siftB rK46 ⟨12, by decide⟩ T46_12 (by decide)

theorem hinj46_12 : Function.Injective
    (fun i => ((T46_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK46)) :=
  repsInj_of_reduceAux rK46 T46_12 (by decide)

theorem hcardT46_12 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK46 ⟨12, by decide⟩ R46 hpxR46 hcardq46 (by decide)).symm

/-- **Cell (46, 12).** -/
theorem cell46_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK46) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK46) (charOfVec rK46 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK46 e (h : Coordinate 1) T46_12 i :=
  species_entry_eq_sum rK46 ⟨12, by decide⟩ e heK h T46_12 hfix46_12 hinj46_12 hcardT46_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK46) (T46_12 i) (hfix46_12 i) h)

/-! ## Cell (46, 46): |T| = 25 -/

def T46_46list : List Coordinates := [(0,0,3,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0)]
def T46_46 : Fin 25 → Coordinate 1 := fun i => T46_46list.getD i.val (0,0,0,0,0)

theorem hfix46_46 : ∀ i, ((T46_46 i : Coordinate 1) : Coordinate 1 ⧸ reps rK46)
    ∈ fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46) :=
  repsFix_of_siftB rK46 ⟨46, by decide⟩ T46_46 (by decide)

theorem hinj46_46 : Function.Injective
    (fun i => ((T46_46 i : Coordinate 1) : Coordinate 1 ⧸ reps rK46)) :=
  repsInj_of_reduceAux rK46 T46_46 (by decide)

theorem hcardT46_46 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK46 ⟨46, by decide⟩ R46 hpxR46 hcardq46 (by decide)).symm

/-- **Cell (46, 46).** -/
theorem cell46_46 (e : List (ZMod 25)) (heK : charOK (basisAt rK46) e = true)
    (h : ↥(reps (⟨46, by decide⟩ : Fin 148))) :
    species (reps (⟨46, by decide⟩ : Fin 148)) h (basisElt (reps rK46) (charOfVec rK46 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK46 e (h : Coordinate 1) T46_46 i :=
  species_entry_eq_sum rK46 ⟨46, by decide⟩ e heK h T46_46 hfix46_46 hinj46_46 hcardT46_46
    (fun i => conj_mem_of_fixedPoints (reps ⟨46, by decide⟩) (reps rK46) (T46_46 i) (hfix46_46 i) h)

namespace Q2

def R46_2 : Fin 125 → Coordinate 2 := fun i => R46list.getD i.val (0,0,0,0,0)
theorem hpxR46_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK46) (R46_2 i)) := by decide
theorem hcardq46_2 : Nat.card (Coordinate 2 ⧸ reps rK46) = 125 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (46, 0) twin -/

def T46_0_2 : Fin 125 → Coordinate 2 := fun i => T46_0list.getD i.val (0,0,0,0,0)

theorem hfix46_0_2 : ∀ i, ((T46_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK46)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK46) :=
  repsFix_of_siftB2 rK46 ⟨0, by decide⟩ T46_0_2 (by decide)

theorem hinj46_0_2 : Function.Injective
    (fun i => ((T46_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK46)) :=
  repsInj_of_reduceAux2 rK46 T46_0_2 (by decide)

theorem hcardT46_0_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK46)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK46 ⟨0, by decide⟩ R46_2 hpxR46_2 hcardq46_2 (by decide)).symm

/-- **Cell (46, 0) twin (q=2).** -/
theorem cell46_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK46) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK46) (charOfVec2 rK46 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK46 e (h : Coordinate 2) T46_0_2 i :=
  species_entry_eq_sum rK46 ⟨0, by decide⟩ e heK h T46_0_2 hfix46_0_2 hinj46_0_2 hcardT46_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK46) (T46_0_2 i) (hfix46_0_2 i) h)

/-! ### Cell (46, 12) twin -/

def T46_12_2 : Fin 125 → Coordinate 2 := fun i => T46_12list.getD i.val (0,0,0,0,0)

theorem hfix46_12_2 : ∀ i, ((T46_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK46)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK46) :=
  repsFix_of_siftB2 rK46 ⟨12, by decide⟩ T46_12_2 (by decide)

theorem hinj46_12_2 : Function.Injective
    (fun i => ((T46_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK46)) :=
  repsInj_of_reduceAux2 rK46 T46_12_2 (by decide)

theorem hcardT46_12_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK46)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK46 ⟨12, by decide⟩ R46_2 hpxR46_2 hcardq46_2 (by decide)).symm

/-- **Cell (46, 12) twin (q=2).** -/
theorem cell46_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK46) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK46) (charOfVec2 rK46 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK46 e (h : Coordinate 2) T46_12_2 i :=
  species_entry_eq_sum rK46 ⟨12, by decide⟩ e heK h T46_12_2 hfix46_12_2 hinj46_12_2 hcardT46_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK46) (T46_12_2 i) (hfix46_12_2 i) h)

/-! ### Cell (46, 46) twin -/

def T46_46_2 : Fin 25 → Coordinate 2 := fun i => T46_46list.getD i.val (0,0,0,0,0)

theorem hfix46_46_2 : ∀ i, ((T46_46_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK46)
    ∈ fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK46) :=
  repsFix_of_siftB2 rK46 ⟨46, by decide⟩ T46_46_2 (by decide)

theorem hinj46_46_2 : Function.Injective
    (fun i => ((T46_46_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK46)) :=
  repsInj_of_reduceAux2 rK46 T46_46_2 (by decide)

theorem hcardT46_46_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK46)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK46 ⟨46, by decide⟩ R46_2 hpxR46_2 hcardq46_2 (by decide)).symm

/-- **Cell (46, 46) twin (q=2).** -/
theorem cell46_46_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK46) e = true)
    (h : ↥(reps (⟨46, by decide⟩ : Fin 148))) :
    species (reps (⟨46, by decide⟩ : Fin 148)) h (basisElt (reps rK46) (charOfVec2 rK46 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK46 e (h : Coordinate 2) T46_46_2 i :=
  species_entry_eq_sum rK46 ⟨46, by decide⟩ e heK h T46_46_2 hfix46_46_2 hinj46_46_2 hcardT46_46_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨46, by decide⟩) (reps rK46) (T46_46_2 i) (hfix46_46_2 i) h)

end Q2

end LeanDring.P5Presentation
