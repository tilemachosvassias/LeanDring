/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, A-block data (rK = 25): certified per-cell species-entry instantiations, both twins.

Emit-embed-decide loop for order-25 A-block class `rK = 25` (`|G/K| = 125`).
All nonzero `H`-columns (`|gH| ≤ 2`, `t⁻¹Ht ⊆ K`).  Full 125-coset transversal
`R25` and each `H`-fixed sub-transversal `T25_rH` embedded as kernel data and
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

def rK25 : Fin 148 := ⟨25, by decide⟩

def R25list : List Coordinates := [(0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (1,0,0,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,1,0,3,0), (1,1,0,4,0), (1,1,0,0,0), (1,1,0,1,0), (1,1,0,2,0), (1,2,0,3,0), (1,2,0,4,0), (1,2,0,0,0), (1,2,0,1,0), (1,2,0,2,0), (1,3,0,3,0), (1,3,0,4,0), (1,3,0,0,0), (1,3,0,1,0), (1,3,0,2,0), (1,4,0,3,0), (1,4,0,4,0), (1,4,0,0,0), (1,4,0,1,0), (1,4,0,2,0), (2,0,0,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,1,0,3,0), (2,1,0,4,0), (2,1,0,0,0), (2,1,0,1,0), (2,1,0,2,0), (2,2,0,3,0), (2,2,0,4,0), (2,2,0,0,0), (2,2,0,1,0), (2,2,0,2,0), (2,3,0,3,0), (2,3,0,4,0), (2,3,0,0,0), (2,3,0,1,0), (2,3,0,2,0), (2,4,0,3,0), (2,4,0,4,0), (2,4,0,0,0), (2,4,0,1,0), (2,4,0,2,0), (3,0,0,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,1,0,3,0), (3,1,0,4,0), (3,1,0,0,0), (3,1,0,1,0), (3,1,0,2,0), (3,2,0,3,0), (3,2,0,4,0), (3,2,0,0,0), (3,2,0,1,0), (3,2,0,2,0), (3,3,0,3,0), (3,3,0,4,0), (3,3,0,0,0), (3,3,0,1,0), (3,3,0,2,0), (3,4,0,3,0), (3,4,0,4,0), (3,4,0,0,0), (3,4,0,1,0), (3,4,0,2,0), (4,0,0,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,1,0,3,0), (4,1,0,4,0), (4,1,0,0,0), (4,1,0,1,0), (4,1,0,2,0), (4,2,0,3,0), (4,2,0,4,0), (4,2,0,0,0), (4,2,0,1,0), (4,2,0,2,0), (4,3,0,3,0), (4,3,0,4,0), (4,3,0,0,0), (4,3,0,1,0), (4,3,0,2,0), (4,4,0,3,0), (4,4,0,4,0), (4,4,0,0,0), (4,4,0,1,0), (4,4,0,2,0)]
def R25 : Fin 125 → Coordinate 1 := fun i => R25list.getD i.val (0,0,0,0,0)

theorem hpxR25 : Function.Injective (fun i => reduceAux 1 (basisAt rK25) (R25 i)) := by decide
theorem hcardq25 : Nat.card (Coordinate 1 ⧸ reps rK25) = 125 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (25, 0): |T| = 125 -/

def T25_0list : List Coordinates := [(0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (1,0,0,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,1,0,3,0), (1,1,0,4,0), (1,1,0,0,0), (1,1,0,1,0), (1,1,0,2,0), (1,2,0,3,0), (1,2,0,4,0), (1,2,0,0,0), (1,2,0,1,0), (1,2,0,2,0), (1,3,0,3,0), (1,3,0,4,0), (1,3,0,0,0), (1,3,0,1,0), (1,3,0,2,0), (1,4,0,3,0), (1,4,0,4,0), (1,4,0,0,0), (1,4,0,1,0), (1,4,0,2,0), (2,0,0,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,1,0,3,0), (2,1,0,4,0), (2,1,0,0,0), (2,1,0,1,0), (2,1,0,2,0), (2,2,0,3,0), (2,2,0,4,0), (2,2,0,0,0), (2,2,0,1,0), (2,2,0,2,0), (2,3,0,3,0), (2,3,0,4,0), (2,3,0,0,0), (2,3,0,1,0), (2,3,0,2,0), (2,4,0,3,0), (2,4,0,4,0), (2,4,0,0,0), (2,4,0,1,0), (2,4,0,2,0), (3,0,0,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,1,0,3,0), (3,1,0,4,0), (3,1,0,0,0), (3,1,0,1,0), (3,1,0,2,0), (3,2,0,3,0), (3,2,0,4,0), (3,2,0,0,0), (3,2,0,1,0), (3,2,0,2,0), (3,3,0,3,0), (3,3,0,4,0), (3,3,0,0,0), (3,3,0,1,0), (3,3,0,2,0), (3,4,0,3,0), (3,4,0,4,0), (3,4,0,0,0), (3,4,0,1,0), (3,4,0,2,0), (4,0,0,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,1,0,3,0), (4,1,0,4,0), (4,1,0,0,0), (4,1,0,1,0), (4,1,0,2,0), (4,2,0,3,0), (4,2,0,4,0), (4,2,0,0,0), (4,2,0,1,0), (4,2,0,2,0), (4,3,0,3,0), (4,3,0,4,0), (4,3,0,0,0), (4,3,0,1,0), (4,3,0,2,0), (4,4,0,3,0), (4,4,0,4,0), (4,4,0,0,0), (4,4,0,1,0), (4,4,0,2,0)]
def T25_0 : Fin 125 → Coordinate 1 := fun i => T25_0list.getD i.val (0,0,0,0,0)

theorem hfix25_0 : ∀ i, ((T25_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK25)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25) :=
  repsFix_of_siftB rK25 ⟨0, by decide⟩ T25_0 (by decide)

theorem hinj25_0 : Function.Injective
    (fun i => ((T25_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK25)) :=
  repsInj_of_reduceAux rK25 T25_0 (by decide)

theorem hcardT25_0 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK25 ⟨0, by decide⟩ R25 hpxR25 hcardq25 (by decide)).symm

/-- **Cell (25, 0).** -/
theorem cell25_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK25) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK25) (charOfVec rK25 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK25 e (h : Coordinate 1) T25_0 i :=
  species_entry_eq_sum rK25 ⟨0, by decide⟩ e heK h T25_0 hfix25_0 hinj25_0 hcardT25_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK25) (T25_0 i) (hfix25_0 i) h)

/-! ## Cell (25, 7): |T| = 125 -/

def T25_7list : List Coordinates := [(0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (1,0,0,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,1,0,3,0), (1,1,0,4,0), (1,1,0,0,0), (1,1,0,1,0), (1,1,0,2,0), (1,2,0,3,0), (1,2,0,4,0), (1,2,0,0,0), (1,2,0,1,0), (1,2,0,2,0), (1,3,0,3,0), (1,3,0,4,0), (1,3,0,0,0), (1,3,0,1,0), (1,3,0,2,0), (1,4,0,3,0), (1,4,0,4,0), (1,4,0,0,0), (1,4,0,1,0), (1,4,0,2,0), (2,0,0,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,1,0,3,0), (2,1,0,4,0), (2,1,0,0,0), (2,1,0,1,0), (2,1,0,2,0), (2,2,0,3,0), (2,2,0,4,0), (2,2,0,0,0), (2,2,0,1,0), (2,2,0,2,0), (2,3,0,3,0), (2,3,0,4,0), (2,3,0,0,0), (2,3,0,1,0), (2,3,0,2,0), (2,4,0,3,0), (2,4,0,4,0), (2,4,0,0,0), (2,4,0,1,0), (2,4,0,2,0), (3,0,0,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,1,0,3,0), (3,1,0,4,0), (3,1,0,0,0), (3,1,0,1,0), (3,1,0,2,0), (3,2,0,3,0), (3,2,0,4,0), (3,2,0,0,0), (3,2,0,1,0), (3,2,0,2,0), (3,3,0,3,0), (3,3,0,4,0), (3,3,0,0,0), (3,3,0,1,0), (3,3,0,2,0), (3,4,0,3,0), (3,4,0,4,0), (3,4,0,0,0), (3,4,0,1,0), (3,4,0,2,0), (4,0,0,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,1,0,3,0), (4,1,0,4,0), (4,1,0,0,0), (4,1,0,1,0), (4,1,0,2,0), (4,2,0,3,0), (4,2,0,4,0), (4,2,0,0,0), (4,2,0,1,0), (4,2,0,2,0), (4,3,0,3,0), (4,3,0,4,0), (4,3,0,0,0), (4,3,0,1,0), (4,3,0,2,0), (4,4,0,3,0), (4,4,0,4,0), (4,4,0,0,0), (4,4,0,1,0), (4,4,0,2,0)]
def T25_7 : Fin 125 → Coordinate 1 := fun i => T25_7list.getD i.val (0,0,0,0,0)

theorem hfix25_7 : ∀ i, ((T25_7 i : Coordinate 1) : Coordinate 1 ⧸ reps rK25)
    ∈ fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25) :=
  repsFix_of_siftB rK25 ⟨7, by decide⟩ T25_7 (by decide)

theorem hinj25_7 : Function.Injective
    (fun i => ((T25_7 i : Coordinate 1) : Coordinate 1 ⧸ reps rK25)) :=
  repsInj_of_reduceAux rK25 T25_7 (by decide)

theorem hcardT25_7 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK25 ⟨7, by decide⟩ R25 hpxR25 hcardq25 (by decide)).symm

/-- **Cell (25, 7).** -/
theorem cell25_7 (e : List (ZMod 25)) (heK : charOK (basisAt rK25) e = true)
    (h : ↥(reps (⟨7, by decide⟩ : Fin 148))) :
    species (reps (⟨7, by decide⟩ : Fin 148)) h (basisElt (reps rK25) (charOfVec rK25 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK25 e (h : Coordinate 1) T25_7 i :=
  species_entry_eq_sum rK25 ⟨7, by decide⟩ e heK h T25_7 hfix25_7 hinj25_7 hcardT25_7
    (fun i => conj_mem_of_fixedPoints (reps ⟨7, by decide⟩) (reps rK25) (T25_7 i) (hfix25_7 i) h)

/-! ## Cell (25, 12): |T| = 125 -/

def T25_12list : List Coordinates := [(0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (1,0,0,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,1,0,3,0), (1,1,0,4,0), (1,1,0,0,0), (1,1,0,1,0), (1,1,0,2,0), (1,2,0,3,0), (1,2,0,4,0), (1,2,0,0,0), (1,2,0,1,0), (1,2,0,2,0), (1,3,0,3,0), (1,3,0,4,0), (1,3,0,0,0), (1,3,0,1,0), (1,3,0,2,0), (1,4,0,3,0), (1,4,0,4,0), (1,4,0,0,0), (1,4,0,1,0), (1,4,0,2,0), (2,0,0,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,1,0,3,0), (2,1,0,4,0), (2,1,0,0,0), (2,1,0,1,0), (2,1,0,2,0), (2,2,0,3,0), (2,2,0,4,0), (2,2,0,0,0), (2,2,0,1,0), (2,2,0,2,0), (2,3,0,3,0), (2,3,0,4,0), (2,3,0,0,0), (2,3,0,1,0), (2,3,0,2,0), (2,4,0,3,0), (2,4,0,4,0), (2,4,0,0,0), (2,4,0,1,0), (2,4,0,2,0), (3,0,0,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,1,0,3,0), (3,1,0,4,0), (3,1,0,0,0), (3,1,0,1,0), (3,1,0,2,0), (3,2,0,3,0), (3,2,0,4,0), (3,2,0,0,0), (3,2,0,1,0), (3,2,0,2,0), (3,3,0,3,0), (3,3,0,4,0), (3,3,0,0,0), (3,3,0,1,0), (3,3,0,2,0), (3,4,0,3,0), (3,4,0,4,0), (3,4,0,0,0), (3,4,0,1,0), (3,4,0,2,0), (4,0,0,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,1,0,3,0), (4,1,0,4,0), (4,1,0,0,0), (4,1,0,1,0), (4,1,0,2,0), (4,2,0,3,0), (4,2,0,4,0), (4,2,0,0,0), (4,2,0,1,0), (4,2,0,2,0), (4,3,0,3,0), (4,3,0,4,0), (4,3,0,0,0), (4,3,0,1,0), (4,3,0,2,0), (4,4,0,3,0), (4,4,0,4,0), (4,4,0,0,0), (4,4,0,1,0), (4,4,0,2,0)]
def T25_12 : Fin 125 → Coordinate 1 := fun i => T25_12list.getD i.val (0,0,0,0,0)

theorem hfix25_12 : ∀ i, ((T25_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK25)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25) :=
  repsFix_of_siftB rK25 ⟨12, by decide⟩ T25_12 (by decide)

theorem hinj25_12 : Function.Injective
    (fun i => ((T25_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK25)) :=
  repsInj_of_reduceAux rK25 T25_12 (by decide)

theorem hcardT25_12 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK25 ⟨12, by decide⟩ R25 hpxR25 hcardq25 (by decide)).symm

/-- **Cell (25, 12).** -/
theorem cell25_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK25) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK25) (charOfVec rK25 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK25 e (h : Coordinate 1) T25_12 i :=
  species_entry_eq_sum rK25 ⟨12, by decide⟩ e heK h T25_12 hfix25_12 hinj25_12 hcardT25_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK25) (T25_12 i) (hfix25_12 i) h)

/-! ## Cell (25, 25): |T| = 125 -/

def T25_25list : List Coordinates := [(0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (1,0,0,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,1,0,3,0), (1,1,0,4,0), (1,1,0,0,0), (1,1,0,1,0), (1,1,0,2,0), (1,2,0,3,0), (1,2,0,4,0), (1,2,0,0,0), (1,2,0,1,0), (1,2,0,2,0), (1,3,0,3,0), (1,3,0,4,0), (1,3,0,0,0), (1,3,0,1,0), (1,3,0,2,0), (1,4,0,3,0), (1,4,0,4,0), (1,4,0,0,0), (1,4,0,1,0), (1,4,0,2,0), (2,0,0,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,1,0,3,0), (2,1,0,4,0), (2,1,0,0,0), (2,1,0,1,0), (2,1,0,2,0), (2,2,0,3,0), (2,2,0,4,0), (2,2,0,0,0), (2,2,0,1,0), (2,2,0,2,0), (2,3,0,3,0), (2,3,0,4,0), (2,3,0,0,0), (2,3,0,1,0), (2,3,0,2,0), (2,4,0,3,0), (2,4,0,4,0), (2,4,0,0,0), (2,4,0,1,0), (2,4,0,2,0), (3,0,0,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,1,0,3,0), (3,1,0,4,0), (3,1,0,0,0), (3,1,0,1,0), (3,1,0,2,0), (3,2,0,3,0), (3,2,0,4,0), (3,2,0,0,0), (3,2,0,1,0), (3,2,0,2,0), (3,3,0,3,0), (3,3,0,4,0), (3,3,0,0,0), (3,3,0,1,0), (3,3,0,2,0), (3,4,0,3,0), (3,4,0,4,0), (3,4,0,0,0), (3,4,0,1,0), (3,4,0,2,0), (4,0,0,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,1,0,3,0), (4,1,0,4,0), (4,1,0,0,0), (4,1,0,1,0), (4,1,0,2,0), (4,2,0,3,0), (4,2,0,4,0), (4,2,0,0,0), (4,2,0,1,0), (4,2,0,2,0), (4,3,0,3,0), (4,3,0,4,0), (4,3,0,0,0), (4,3,0,1,0), (4,3,0,2,0), (4,4,0,3,0), (4,4,0,4,0), (4,4,0,0,0), (4,4,0,1,0), (4,4,0,2,0)]
def T25_25 : Fin 125 → Coordinate 1 := fun i => T25_25list.getD i.val (0,0,0,0,0)

theorem hfix25_25 : ∀ i, ((T25_25 i : Coordinate 1) : Coordinate 1 ⧸ reps rK25)
    ∈ fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25) :=
  repsFix_of_siftB rK25 ⟨25, by decide⟩ T25_25 (by decide)

theorem hinj25_25 : Function.Injective
    (fun i => ((T25_25 i : Coordinate 1) : Coordinate 1 ⧸ reps rK25)) :=
  repsInj_of_reduceAux rK25 T25_25 (by decide)

theorem hcardT25_25 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK25 ⟨25, by decide⟩ R25 hpxR25 hcardq25 (by decide)).symm

/-- **Cell (25, 25).** -/
theorem cell25_25 (e : List (ZMod 25)) (heK : charOK (basisAt rK25) e = true)
    (h : ↥(reps (⟨25, by decide⟩ : Fin 148))) :
    species (reps (⟨25, by decide⟩ : Fin 148)) h (basisElt (reps rK25) (charOfVec rK25 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK25 e (h : Coordinate 1) T25_25 i :=
  species_entry_eq_sum rK25 ⟨25, by decide⟩ e heK h T25_25 hfix25_25 hinj25_25 hcardT25_25
    (fun i => conj_mem_of_fixedPoints (reps ⟨25, by decide⟩) (reps rK25) (T25_25 i) (hfix25_25 i) h)

namespace Q2

def R25_2 : Fin 125 → Coordinate 2 := fun i => R25list.getD i.val (0,0,0,0,0)
theorem hpxR25_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK25) (R25_2 i)) := by decide
theorem hcardq25_2 : Nat.card (Coordinate 2 ⧸ reps rK25) = 125 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (25, 0) twin -/

def T25_0_2 : Fin 125 → Coordinate 2 := fun i => T25_0list.getD i.val (0,0,0,0,0)

theorem hfix25_0_2 : ∀ i, ((T25_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK25)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK25) :=
  repsFix_of_siftB2 rK25 ⟨0, by decide⟩ T25_0_2 (by decide)

theorem hinj25_0_2 : Function.Injective
    (fun i => ((T25_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK25)) :=
  repsInj_of_reduceAux2 rK25 T25_0_2 (by decide)

theorem hcardT25_0_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK25)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK25 ⟨0, by decide⟩ R25_2 hpxR25_2 hcardq25_2 (by decide)).symm

/-- **Cell (25, 0) twin (q=2).** -/
theorem cell25_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK25) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK25) (charOfVec2 rK25 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK25 e (h : Coordinate 2) T25_0_2 i :=
  species_entry_eq_sum rK25 ⟨0, by decide⟩ e heK h T25_0_2 hfix25_0_2 hinj25_0_2 hcardT25_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK25) (T25_0_2 i) (hfix25_0_2 i) h)

/-! ### Cell (25, 7) twin -/

def T25_7_2 : Fin 125 → Coordinate 2 := fun i => T25_7list.getD i.val (0,0,0,0,0)

theorem hfix25_7_2 : ∀ i, ((T25_7_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK25)
    ∈ fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK25) :=
  repsFix_of_siftB2 rK25 ⟨7, by decide⟩ T25_7_2 (by decide)

theorem hinj25_7_2 : Function.Injective
    (fun i => ((T25_7_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK25)) :=
  repsInj_of_reduceAux2 rK25 T25_7_2 (by decide)

theorem hcardT25_7_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK25)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK25 ⟨7, by decide⟩ R25_2 hpxR25_2 hcardq25_2 (by decide)).symm

/-- **Cell (25, 7) twin (q=2).** -/
theorem cell25_7_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK25) e = true)
    (h : ↥(reps (⟨7, by decide⟩ : Fin 148))) :
    species (reps (⟨7, by decide⟩ : Fin 148)) h (basisElt (reps rK25) (charOfVec2 rK25 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK25 e (h : Coordinate 2) T25_7_2 i :=
  species_entry_eq_sum rK25 ⟨7, by decide⟩ e heK h T25_7_2 hfix25_7_2 hinj25_7_2 hcardT25_7_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨7, by decide⟩) (reps rK25) (T25_7_2 i) (hfix25_7_2 i) h)

/-! ### Cell (25, 12) twin -/

def T25_12_2 : Fin 125 → Coordinate 2 := fun i => T25_12list.getD i.val (0,0,0,0,0)

theorem hfix25_12_2 : ∀ i, ((T25_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK25)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK25) :=
  repsFix_of_siftB2 rK25 ⟨12, by decide⟩ T25_12_2 (by decide)

theorem hinj25_12_2 : Function.Injective
    (fun i => ((T25_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK25)) :=
  repsInj_of_reduceAux2 rK25 T25_12_2 (by decide)

theorem hcardT25_12_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK25)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK25 ⟨12, by decide⟩ R25_2 hpxR25_2 hcardq25_2 (by decide)).symm

/-- **Cell (25, 12) twin (q=2).** -/
theorem cell25_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK25) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK25) (charOfVec2 rK25 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK25 e (h : Coordinate 2) T25_12_2 i :=
  species_entry_eq_sum rK25 ⟨12, by decide⟩ e heK h T25_12_2 hfix25_12_2 hinj25_12_2 hcardT25_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK25) (T25_12_2 i) (hfix25_12_2 i) h)

/-! ### Cell (25, 25) twin -/

def T25_25_2 : Fin 125 → Coordinate 2 := fun i => T25_25list.getD i.val (0,0,0,0,0)

theorem hfix25_25_2 : ∀ i, ((T25_25_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK25)
    ∈ fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK25) :=
  repsFix_of_siftB2 rK25 ⟨25, by decide⟩ T25_25_2 (by decide)

theorem hinj25_25_2 : Function.Injective
    (fun i => ((T25_25_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK25)) :=
  repsInj_of_reduceAux2 rK25 T25_25_2 (by decide)

theorem hcardT25_25_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK25)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK25 ⟨25, by decide⟩ R25_2 hpxR25_2 hcardq25_2 (by decide)).symm

/-- **Cell (25, 25) twin (q=2).** -/
theorem cell25_25_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK25) e = true)
    (h : ↥(reps (⟨25, by decide⟩ : Fin 148))) :
    species (reps (⟨25, by decide⟩ : Fin 148)) h (basisElt (reps rK25) (charOfVec2 rK25 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK25 e (h : Coordinate 2) T25_25_2 i :=
  species_entry_eq_sum rK25 ⟨25, by decide⟩ e heK h T25_25_2 hfix25_25_2 hinj25_25_2 hcardT25_25_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨25, by decide⟩) (reps rK25) (T25_25_2 i) (hfix25_25_2 i) h)

end Q2

end LeanDring.P5Presentation
