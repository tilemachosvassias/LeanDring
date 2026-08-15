/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, A-block data (rK = 32): certified per-cell species-entry instantiations, both twins.

Emit-embed-decide loop for order-25 A-block class `rK = 32` (`|G/K| = 125`).
All nonzero `H`-columns (`|gH| ≤ 2`, `t⁻¹Ht ⊆ K`).  Full 125-coset transversal
`R32` and each `H`-fixed sub-transversal `T32_rH` embedded as kernel data and
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

def rK32 : Fin 148 := ⟨32, by decide⟩

def R32list : List Coordinates := [(0,1,4,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0)]
def R32 : Fin 125 → Coordinate 1 := fun i => R32list.getD i.val (0,0,0,0,0)

theorem hpxR32 : Function.Injective (fun i => reduceAux 1 (basisAt rK32) (R32 i)) := by decide
theorem hcardq32 : Nat.card (Coordinate 1 ⧸ reps rK32) = 125 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (32, 0): |T| = 125 -/

def T32_0list : List Coordinates := [(0,1,4,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0)]
def T32_0 : Fin 125 → Coordinate 1 := fun i => T32_0list.getD i.val (0,0,0,0,0)

theorem hfix32_0 : ∀ i, ((T32_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK32)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32) :=
  repsFix_of_siftB rK32 ⟨0, by decide⟩ T32_0 (by decide)

theorem hinj32_0 : Function.Injective
    (fun i => ((T32_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK32)) :=
  repsInj_of_reduceAux rK32 T32_0 (by decide)

theorem hcardT32_0 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK32 ⟨0, by decide⟩ R32 hpxR32 hcardq32 (by decide)).symm

/-- **Cell (32, 0).** -/
theorem cell32_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK32) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK32) (charOfVec rK32 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK32 e (h : Coordinate 1) T32_0 i :=
  species_entry_eq_sum rK32 ⟨0, by decide⟩ e heK h T32_0 hfix32_0 hinj32_0 hcardT32_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK32) (T32_0 i) (hfix32_0 i) h)

/-! ## Cell (32, 12): |T| = 125 -/

def T32_12list : List Coordinates := [(0,1,4,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,2,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0)]
def T32_12 : Fin 125 → Coordinate 1 := fun i => T32_12list.getD i.val (0,0,0,0,0)

theorem hfix32_12 : ∀ i, ((T32_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK32)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32) :=
  repsFix_of_siftB rK32 ⟨12, by decide⟩ T32_12 (by decide)

theorem hinj32_12 : Function.Injective
    (fun i => ((T32_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK32)) :=
  repsInj_of_reduceAux rK32 T32_12 (by decide)

theorem hcardT32_12 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK32 ⟨12, by decide⟩ R32 hpxR32 hcardq32 (by decide)).symm

/-- **Cell (32, 12).** -/
theorem cell32_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK32) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK32) (charOfVec rK32 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK32 e (h : Coordinate 1) T32_12 i :=
  species_entry_eq_sum rK32 ⟨12, by decide⟩ e heK h T32_12 hfix32_12 hinj32_12 hcardT32_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK32) (T32_12 i) (hfix32_12 i) h)

/-! ## Cell (32, 32): |T| = 25 -/

def T32_32list : List Coordinates := [(0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0)]
def T32_32 : Fin 25 → Coordinate 1 := fun i => T32_32list.getD i.val (0,0,0,0,0)

theorem hfix32_32 : ∀ i, ((T32_32 i : Coordinate 1) : Coordinate 1 ⧸ reps rK32)
    ∈ fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32) :=
  repsFix_of_siftB rK32 ⟨32, by decide⟩ T32_32 (by decide)

theorem hinj32_32 : Function.Injective
    (fun i => ((T32_32 i : Coordinate 1) : Coordinate 1 ⧸ reps rK32)) :=
  repsInj_of_reduceAux rK32 T32_32 (by decide)

theorem hcardT32_32 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK32 ⟨32, by decide⟩ R32 hpxR32 hcardq32 (by decide)).symm

/-- **Cell (32, 32).** -/
theorem cell32_32 (e : List (ZMod 25)) (heK : charOK (basisAt rK32) e = true)
    (h : ↥(reps (⟨32, by decide⟩ : Fin 148))) :
    species (reps (⟨32, by decide⟩ : Fin 148)) h (basisElt (reps rK32) (charOfVec rK32 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK32 e (h : Coordinate 1) T32_32 i :=
  species_entry_eq_sum rK32 ⟨32, by decide⟩ e heK h T32_32 hfix32_32 hinj32_32 hcardT32_32
    (fun i => conj_mem_of_fixedPoints (reps ⟨32, by decide⟩) (reps rK32) (T32_32 i) (hfix32_32 i) h)

namespace Q2

def R32_2 : Fin 125 → Coordinate 2 := fun i => R32list.getD i.val (0,0,0,0,0)
theorem hpxR32_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK32) (R32_2 i)) := by decide
theorem hcardq32_2 : Nat.card (Coordinate 2 ⧸ reps rK32) = 125 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (32, 0) twin -/

def T32_0_2 : Fin 125 → Coordinate 2 := fun i => T32_0list.getD i.val (0,0,0,0,0)

theorem hfix32_0_2 : ∀ i, ((T32_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK32)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK32) :=
  repsFix_of_siftB2 rK32 ⟨0, by decide⟩ T32_0_2 (by decide)

theorem hinj32_0_2 : Function.Injective
    (fun i => ((T32_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK32)) :=
  repsInj_of_reduceAux2 rK32 T32_0_2 (by decide)

theorem hcardT32_0_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK32)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK32 ⟨0, by decide⟩ R32_2 hpxR32_2 hcardq32_2 (by decide)).symm

/-- **Cell (32, 0) twin (q=2).** -/
theorem cell32_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK32) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK32) (charOfVec2 rK32 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK32 e (h : Coordinate 2) T32_0_2 i :=
  species_entry_eq_sum rK32 ⟨0, by decide⟩ e heK h T32_0_2 hfix32_0_2 hinj32_0_2 hcardT32_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK32) (T32_0_2 i) (hfix32_0_2 i) h)

/-! ### Cell (32, 12) twin -/

def T32_12_2 : Fin 125 → Coordinate 2 := fun i => T32_12list.getD i.val (0,0,0,0,0)

theorem hfix32_12_2 : ∀ i, ((T32_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK32)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK32) :=
  repsFix_of_siftB2 rK32 ⟨12, by decide⟩ T32_12_2 (by decide)

theorem hinj32_12_2 : Function.Injective
    (fun i => ((T32_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK32)) :=
  repsInj_of_reduceAux2 rK32 T32_12_2 (by decide)

theorem hcardT32_12_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK32)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK32 ⟨12, by decide⟩ R32_2 hpxR32_2 hcardq32_2 (by decide)).symm

/-- **Cell (32, 12) twin (q=2).** -/
theorem cell32_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK32) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK32) (charOfVec2 rK32 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK32 e (h : Coordinate 2) T32_12_2 i :=
  species_entry_eq_sum rK32 ⟨12, by decide⟩ e heK h T32_12_2 hfix32_12_2 hinj32_12_2 hcardT32_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK32) (T32_12_2 i) (hfix32_12_2 i) h)

/-! ### Cell (32, 32) twin -/

def T32_32_2 : Fin 25 → Coordinate 2 := fun i => T32_32list.getD i.val (0,0,0,0,0)

theorem hfix32_32_2 : ∀ i, ((T32_32_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK32)
    ∈ fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK32) :=
  repsFix_of_siftB2 rK32 ⟨32, by decide⟩ T32_32_2 (by decide)

theorem hinj32_32_2 : Function.Injective
    (fun i => ((T32_32_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK32)) :=
  repsInj_of_reduceAux2 rK32 T32_32_2 (by decide)

theorem hcardT32_32_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK32)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK32 ⟨32, by decide⟩ R32_2 hpxR32_2 hcardq32_2 (by decide)).symm

/-- **Cell (32, 32) twin (q=2).** -/
theorem cell32_32_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK32) e = true)
    (h : ↥(reps (⟨32, by decide⟩ : Fin 148))) :
    species (reps (⟨32, by decide⟩ : Fin 148)) h (basisElt (reps rK32) (charOfVec2 rK32 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK32 e (h : Coordinate 2) T32_32_2 i :=
  species_entry_eq_sum rK32 ⟨32, by decide⟩ e heK h T32_32_2 hfix32_32_2 hinj32_32_2 hcardT32_32_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨32, by decide⟩) (reps rK32) (T32_32_2 i) (hfix32_32_2 i) h)

end Q2

end LeanDring.P5Presentation
