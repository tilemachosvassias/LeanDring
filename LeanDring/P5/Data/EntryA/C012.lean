/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, A-block data (rK = 24): certified per-cell species-entry instantiations, both twins.

Emit-embed-decide loop for order-25 A-block class `rK = 24` (`|G/K| = 125`).
All nonzero `H`-columns (`|gH| ≤ 2`, `t⁻¹Ht ⊆ K`).  Full 125-coset transversal
`R24` and each `H`-fixed sub-transversal `T24_rH` embedded as kernel data and
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

def rK24 : Fin 148 := ⟨24, by decide⟩

def R24list : List Coordinates := [(0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,1,0,2,0), (1,1,0,3,0), (1,1,0,4,0), (1,1,0,0,0), (1,1,0,1,0), (1,2,0,2,0), (1,2,0,3,0), (1,2,0,4,0), (1,2,0,0,0), (1,2,0,1,0), (1,3,0,2,0), (1,3,0,3,0), (1,3,0,4,0), (1,3,0,0,0), (1,3,0,1,0), (1,4,0,2,0), (1,4,0,3,0), (1,4,0,4,0), (1,4,0,0,0), (1,4,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,1,0,2,0), (2,1,0,3,0), (2,1,0,4,0), (2,1,0,0,0), (2,1,0,1,0), (2,2,0,2,0), (2,2,0,3,0), (2,2,0,4,0), (2,2,0,0,0), (2,2,0,1,0), (2,3,0,2,0), (2,3,0,3,0), (2,3,0,4,0), (2,3,0,0,0), (2,3,0,1,0), (2,4,0,2,0), (2,4,0,3,0), (2,4,0,4,0), (2,4,0,0,0), (2,4,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,1,0,2,0), (3,1,0,3,0), (3,1,0,4,0), (3,1,0,0,0), (3,1,0,1,0), (3,2,0,2,0), (3,2,0,3,0), (3,2,0,4,0), (3,2,0,0,0), (3,2,0,1,0), (3,3,0,2,0), (3,3,0,3,0), (3,3,0,4,0), (3,3,0,0,0), (3,3,0,1,0), (3,4,0,2,0), (3,4,0,3,0), (3,4,0,4,0), (3,4,0,0,0), (3,4,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,1,0,2,0), (4,1,0,3,0), (4,1,0,4,0), (4,1,0,0,0), (4,1,0,1,0), (4,2,0,2,0), (4,2,0,3,0), (4,2,0,4,0), (4,2,0,0,0), (4,2,0,1,0), (4,3,0,2,0), (4,3,0,3,0), (4,3,0,4,0), (4,3,0,0,0), (4,3,0,1,0), (4,4,0,2,0), (4,4,0,3,0), (4,4,0,4,0), (4,4,0,0,0), (4,4,0,1,0)]
def R24 : Fin 125 → Coordinate 1 := fun i => R24list.getD i.val (0,0,0,0,0)

theorem hpxR24 : Function.Injective (fun i => reduceAux 1 (basisAt rK24) (R24 i)) := by decide
theorem hcardq24 : Nat.card (Coordinate 1 ⧸ reps rK24) = 125 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (24, 0): |T| = 125 -/

def T24_0list : List Coordinates := [(0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,1,0,2,0), (1,1,0,3,0), (1,1,0,4,0), (1,1,0,0,0), (1,1,0,1,0), (1,2,0,2,0), (1,2,0,3,0), (1,2,0,4,0), (1,2,0,0,0), (1,2,0,1,0), (1,3,0,2,0), (1,3,0,3,0), (1,3,0,4,0), (1,3,0,0,0), (1,3,0,1,0), (1,4,0,2,0), (1,4,0,3,0), (1,4,0,4,0), (1,4,0,0,0), (1,4,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,1,0,2,0), (2,1,0,3,0), (2,1,0,4,0), (2,1,0,0,0), (2,1,0,1,0), (2,2,0,2,0), (2,2,0,3,0), (2,2,0,4,0), (2,2,0,0,0), (2,2,0,1,0), (2,3,0,2,0), (2,3,0,3,0), (2,3,0,4,0), (2,3,0,0,0), (2,3,0,1,0), (2,4,0,2,0), (2,4,0,3,0), (2,4,0,4,0), (2,4,0,0,0), (2,4,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,1,0,2,0), (3,1,0,3,0), (3,1,0,4,0), (3,1,0,0,0), (3,1,0,1,0), (3,2,0,2,0), (3,2,0,3,0), (3,2,0,4,0), (3,2,0,0,0), (3,2,0,1,0), (3,3,0,2,0), (3,3,0,3,0), (3,3,0,4,0), (3,3,0,0,0), (3,3,0,1,0), (3,4,0,2,0), (3,4,0,3,0), (3,4,0,4,0), (3,4,0,0,0), (3,4,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,1,0,2,0), (4,1,0,3,0), (4,1,0,4,0), (4,1,0,0,0), (4,1,0,1,0), (4,2,0,2,0), (4,2,0,3,0), (4,2,0,4,0), (4,2,0,0,0), (4,2,0,1,0), (4,3,0,2,0), (4,3,0,3,0), (4,3,0,4,0), (4,3,0,0,0), (4,3,0,1,0), (4,4,0,2,0), (4,4,0,3,0), (4,4,0,4,0), (4,4,0,0,0), (4,4,0,1,0)]
def T24_0 : Fin 125 → Coordinate 1 := fun i => T24_0list.getD i.val (0,0,0,0,0)

theorem hfix24_0 : ∀ i, ((T24_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK24)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24) :=
  repsFix_of_siftB rK24 ⟨0, by decide⟩ T24_0 (by decide)

theorem hinj24_0 : Function.Injective
    (fun i => ((T24_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK24)) :=
  repsInj_of_reduceAux rK24 T24_0 (by decide)

theorem hcardT24_0 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK24 ⟨0, by decide⟩ R24 hpxR24 hcardq24 (by decide)).symm

/-- **Cell (24, 0).** -/
theorem cell24_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK24) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK24) (charOfVec rK24 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK24 e (h : Coordinate 1) T24_0 i :=
  species_entry_eq_sum rK24 ⟨0, by decide⟩ e heK h T24_0 hfix24_0 hinj24_0 hcardT24_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK24) (T24_0 i) (hfix24_0 i) h)

/-! ## Cell (24, 6): |T| = 125 -/

def T24_6list : List Coordinates := [(0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,1,0,2,0), (1,1,0,3,0), (1,1,0,4,0), (1,1,0,0,0), (1,1,0,1,0), (1,2,0,2,0), (1,2,0,3,0), (1,2,0,4,0), (1,2,0,0,0), (1,2,0,1,0), (1,3,0,2,0), (1,3,0,3,0), (1,3,0,4,0), (1,3,0,0,0), (1,3,0,1,0), (1,4,0,2,0), (1,4,0,3,0), (1,4,0,4,0), (1,4,0,0,0), (1,4,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,1,0,2,0), (2,1,0,3,0), (2,1,0,4,0), (2,1,0,0,0), (2,1,0,1,0), (2,2,0,2,0), (2,2,0,3,0), (2,2,0,4,0), (2,2,0,0,0), (2,2,0,1,0), (2,3,0,2,0), (2,3,0,3,0), (2,3,0,4,0), (2,3,0,0,0), (2,3,0,1,0), (2,4,0,2,0), (2,4,0,3,0), (2,4,0,4,0), (2,4,0,0,0), (2,4,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,1,0,2,0), (3,1,0,3,0), (3,1,0,4,0), (3,1,0,0,0), (3,1,0,1,0), (3,2,0,2,0), (3,2,0,3,0), (3,2,0,4,0), (3,2,0,0,0), (3,2,0,1,0), (3,3,0,2,0), (3,3,0,3,0), (3,3,0,4,0), (3,3,0,0,0), (3,3,0,1,0), (3,4,0,2,0), (3,4,0,3,0), (3,4,0,4,0), (3,4,0,0,0), (3,4,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,1,0,2,0), (4,1,0,3,0), (4,1,0,4,0), (4,1,0,0,0), (4,1,0,1,0), (4,2,0,2,0), (4,2,0,3,0), (4,2,0,4,0), (4,2,0,0,0), (4,2,0,1,0), (4,3,0,2,0), (4,3,0,3,0), (4,3,0,4,0), (4,3,0,0,0), (4,3,0,1,0), (4,4,0,2,0), (4,4,0,3,0), (4,4,0,4,0), (4,4,0,0,0), (4,4,0,1,0)]
def T24_6 : Fin 125 → Coordinate 1 := fun i => T24_6list.getD i.val (0,0,0,0,0)

theorem hfix24_6 : ∀ i, ((T24_6 i : Coordinate 1) : Coordinate 1 ⧸ reps rK24)
    ∈ fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24) :=
  repsFix_of_siftB rK24 ⟨6, by decide⟩ T24_6 (by decide)

theorem hinj24_6 : Function.Injective
    (fun i => ((T24_6 i : Coordinate 1) : Coordinate 1 ⧸ reps rK24)) :=
  repsInj_of_reduceAux rK24 T24_6 (by decide)

theorem hcardT24_6 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK24 ⟨6, by decide⟩ R24 hpxR24 hcardq24 (by decide)).symm

/-- **Cell (24, 6).** -/
theorem cell24_6 (e : List (ZMod 25)) (heK : charOK (basisAt rK24) e = true)
    (h : ↥(reps (⟨6, by decide⟩ : Fin 148))) :
    species (reps (⟨6, by decide⟩ : Fin 148)) h (basisElt (reps rK24) (charOfVec rK24 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK24 e (h : Coordinate 1) T24_6 i :=
  species_entry_eq_sum rK24 ⟨6, by decide⟩ e heK h T24_6 hfix24_6 hinj24_6 hcardT24_6
    (fun i => conj_mem_of_fixedPoints (reps ⟨6, by decide⟩) (reps rK24) (T24_6 i) (hfix24_6 i) h)

/-! ## Cell (24, 12): |T| = 125 -/

def T24_12list : List Coordinates := [(0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,1,0,2,0), (1,1,0,3,0), (1,1,0,4,0), (1,1,0,0,0), (1,1,0,1,0), (1,2,0,2,0), (1,2,0,3,0), (1,2,0,4,0), (1,2,0,0,0), (1,2,0,1,0), (1,3,0,2,0), (1,3,0,3,0), (1,3,0,4,0), (1,3,0,0,0), (1,3,0,1,0), (1,4,0,2,0), (1,4,0,3,0), (1,4,0,4,0), (1,4,0,0,0), (1,4,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,1,0,2,0), (2,1,0,3,0), (2,1,0,4,0), (2,1,0,0,0), (2,1,0,1,0), (2,2,0,2,0), (2,2,0,3,0), (2,2,0,4,0), (2,2,0,0,0), (2,2,0,1,0), (2,3,0,2,0), (2,3,0,3,0), (2,3,0,4,0), (2,3,0,0,0), (2,3,0,1,0), (2,4,0,2,0), (2,4,0,3,0), (2,4,0,4,0), (2,4,0,0,0), (2,4,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,1,0,2,0), (3,1,0,3,0), (3,1,0,4,0), (3,1,0,0,0), (3,1,0,1,0), (3,2,0,2,0), (3,2,0,3,0), (3,2,0,4,0), (3,2,0,0,0), (3,2,0,1,0), (3,3,0,2,0), (3,3,0,3,0), (3,3,0,4,0), (3,3,0,0,0), (3,3,0,1,0), (3,4,0,2,0), (3,4,0,3,0), (3,4,0,4,0), (3,4,0,0,0), (3,4,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,1,0,2,0), (4,1,0,3,0), (4,1,0,4,0), (4,1,0,0,0), (4,1,0,1,0), (4,2,0,2,0), (4,2,0,3,0), (4,2,0,4,0), (4,2,0,0,0), (4,2,0,1,0), (4,3,0,2,0), (4,3,0,3,0), (4,3,0,4,0), (4,3,0,0,0), (4,3,0,1,0), (4,4,0,2,0), (4,4,0,3,0), (4,4,0,4,0), (4,4,0,0,0), (4,4,0,1,0)]
def T24_12 : Fin 125 → Coordinate 1 := fun i => T24_12list.getD i.val (0,0,0,0,0)

theorem hfix24_12 : ∀ i, ((T24_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK24)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24) :=
  repsFix_of_siftB rK24 ⟨12, by decide⟩ T24_12 (by decide)

theorem hinj24_12 : Function.Injective
    (fun i => ((T24_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK24)) :=
  repsInj_of_reduceAux rK24 T24_12 (by decide)

theorem hcardT24_12 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK24 ⟨12, by decide⟩ R24 hpxR24 hcardq24 (by decide)).symm

/-- **Cell (24, 12).** -/
theorem cell24_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK24) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK24) (charOfVec rK24 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK24 e (h : Coordinate 1) T24_12 i :=
  species_entry_eq_sum rK24 ⟨12, by decide⟩ e heK h T24_12 hfix24_12 hinj24_12 hcardT24_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK24) (T24_12 i) (hfix24_12 i) h)

/-! ## Cell (24, 24): |T| = 125 -/

def T24_24list : List Coordinates := [(0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,1,0,2,0), (1,1,0,3,0), (1,1,0,4,0), (1,1,0,0,0), (1,1,0,1,0), (1,2,0,2,0), (1,2,0,3,0), (1,2,0,4,0), (1,2,0,0,0), (1,2,0,1,0), (1,3,0,2,0), (1,3,0,3,0), (1,3,0,4,0), (1,3,0,0,0), (1,3,0,1,0), (1,4,0,2,0), (1,4,0,3,0), (1,4,0,4,0), (1,4,0,0,0), (1,4,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,1,0,2,0), (2,1,0,3,0), (2,1,0,4,0), (2,1,0,0,0), (2,1,0,1,0), (2,2,0,2,0), (2,2,0,3,0), (2,2,0,4,0), (2,2,0,0,0), (2,2,0,1,0), (2,3,0,2,0), (2,3,0,3,0), (2,3,0,4,0), (2,3,0,0,0), (2,3,0,1,0), (2,4,0,2,0), (2,4,0,3,0), (2,4,0,4,0), (2,4,0,0,0), (2,4,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,1,0,2,0), (3,1,0,3,0), (3,1,0,4,0), (3,1,0,0,0), (3,1,0,1,0), (3,2,0,2,0), (3,2,0,3,0), (3,2,0,4,0), (3,2,0,0,0), (3,2,0,1,0), (3,3,0,2,0), (3,3,0,3,0), (3,3,0,4,0), (3,3,0,0,0), (3,3,0,1,0), (3,4,0,2,0), (3,4,0,3,0), (3,4,0,4,0), (3,4,0,0,0), (3,4,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,1,0,2,0), (4,1,0,3,0), (4,1,0,4,0), (4,1,0,0,0), (4,1,0,1,0), (4,2,0,2,0), (4,2,0,3,0), (4,2,0,4,0), (4,2,0,0,0), (4,2,0,1,0), (4,3,0,2,0), (4,3,0,3,0), (4,3,0,4,0), (4,3,0,0,0), (4,3,0,1,0), (4,4,0,2,0), (4,4,0,3,0), (4,4,0,4,0), (4,4,0,0,0), (4,4,0,1,0)]
def T24_24 : Fin 125 → Coordinate 1 := fun i => T24_24list.getD i.val (0,0,0,0,0)

theorem hfix24_24 : ∀ i, ((T24_24 i : Coordinate 1) : Coordinate 1 ⧸ reps rK24)
    ∈ fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24) :=
  repsFix_of_siftB rK24 ⟨24, by decide⟩ T24_24 (by decide)

theorem hinj24_24 : Function.Injective
    (fun i => ((T24_24 i : Coordinate 1) : Coordinate 1 ⧸ reps rK24)) :=
  repsInj_of_reduceAux rK24 T24_24 (by decide)

theorem hcardT24_24 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK24 ⟨24, by decide⟩ R24 hpxR24 hcardq24 (by decide)).symm

/-- **Cell (24, 24).** -/
theorem cell24_24 (e : List (ZMod 25)) (heK : charOK (basisAt rK24) e = true)
    (h : ↥(reps (⟨24, by decide⟩ : Fin 148))) :
    species (reps (⟨24, by decide⟩ : Fin 148)) h (basisElt (reps rK24) (charOfVec rK24 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK24 e (h : Coordinate 1) T24_24 i :=
  species_entry_eq_sum rK24 ⟨24, by decide⟩ e heK h T24_24 hfix24_24 hinj24_24 hcardT24_24
    (fun i => conj_mem_of_fixedPoints (reps ⟨24, by decide⟩) (reps rK24) (T24_24 i) (hfix24_24 i) h)

namespace Q2

def R24_2 : Fin 125 → Coordinate 2 := fun i => R24list.getD i.val (0,0,0,0,0)
theorem hpxR24_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK24) (R24_2 i)) := by decide
theorem hcardq24_2 : Nat.card (Coordinate 2 ⧸ reps rK24) = 125 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (24, 0) twin -/

def T24_0_2 : Fin 125 → Coordinate 2 := fun i => T24_0list.getD i.val (0,0,0,0,0)

theorem hfix24_0_2 : ∀ i, ((T24_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK24)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK24) :=
  repsFix_of_siftB2 rK24 ⟨0, by decide⟩ T24_0_2 (by decide)

theorem hinj24_0_2 : Function.Injective
    (fun i => ((T24_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK24)) :=
  repsInj_of_reduceAux2 rK24 T24_0_2 (by decide)

theorem hcardT24_0_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK24)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK24 ⟨0, by decide⟩ R24_2 hpxR24_2 hcardq24_2 (by decide)).symm

/-- **Cell (24, 0) twin (q=2).** -/
theorem cell24_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK24) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK24) (charOfVec2 rK24 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK24 e (h : Coordinate 2) T24_0_2 i :=
  species_entry_eq_sum rK24 ⟨0, by decide⟩ e heK h T24_0_2 hfix24_0_2 hinj24_0_2 hcardT24_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK24) (T24_0_2 i) (hfix24_0_2 i) h)

/-! ### Cell (24, 6) twin -/

def T24_6_2 : Fin 125 → Coordinate 2 := fun i => T24_6list.getD i.val (0,0,0,0,0)

theorem hfix24_6_2 : ∀ i, ((T24_6_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK24)
    ∈ fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK24) :=
  repsFix_of_siftB2 rK24 ⟨6, by decide⟩ T24_6_2 (by decide)

theorem hinj24_6_2 : Function.Injective
    (fun i => ((T24_6_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK24)) :=
  repsInj_of_reduceAux2 rK24 T24_6_2 (by decide)

theorem hcardT24_6_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK24)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK24 ⟨6, by decide⟩ R24_2 hpxR24_2 hcardq24_2 (by decide)).symm

/-- **Cell (24, 6) twin (q=2).** -/
theorem cell24_6_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK24) e = true)
    (h : ↥(reps (⟨6, by decide⟩ : Fin 148))) :
    species (reps (⟨6, by decide⟩ : Fin 148)) h (basisElt (reps rK24) (charOfVec2 rK24 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK24 e (h : Coordinate 2) T24_6_2 i :=
  species_entry_eq_sum rK24 ⟨6, by decide⟩ e heK h T24_6_2 hfix24_6_2 hinj24_6_2 hcardT24_6_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨6, by decide⟩) (reps rK24) (T24_6_2 i) (hfix24_6_2 i) h)

/-! ### Cell (24, 12) twin -/

def T24_12_2 : Fin 125 → Coordinate 2 := fun i => T24_12list.getD i.val (0,0,0,0,0)

theorem hfix24_12_2 : ∀ i, ((T24_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK24)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK24) :=
  repsFix_of_siftB2 rK24 ⟨12, by decide⟩ T24_12_2 (by decide)

theorem hinj24_12_2 : Function.Injective
    (fun i => ((T24_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK24)) :=
  repsInj_of_reduceAux2 rK24 T24_12_2 (by decide)

theorem hcardT24_12_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK24)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK24 ⟨12, by decide⟩ R24_2 hpxR24_2 hcardq24_2 (by decide)).symm

/-- **Cell (24, 12) twin (q=2).** -/
theorem cell24_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK24) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK24) (charOfVec2 rK24 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK24 e (h : Coordinate 2) T24_12_2 i :=
  species_entry_eq_sum rK24 ⟨12, by decide⟩ e heK h T24_12_2 hfix24_12_2 hinj24_12_2 hcardT24_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK24) (T24_12_2 i) (hfix24_12_2 i) h)

/-! ### Cell (24, 24) twin -/

def T24_24_2 : Fin 125 → Coordinate 2 := fun i => T24_24list.getD i.val (0,0,0,0,0)

theorem hfix24_24_2 : ∀ i, ((T24_24_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK24)
    ∈ fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK24) :=
  repsFix_of_siftB2 rK24 ⟨24, by decide⟩ T24_24_2 (by decide)

theorem hinj24_24_2 : Function.Injective
    (fun i => ((T24_24_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK24)) :=
  repsInj_of_reduceAux2 rK24 T24_24_2 (by decide)

theorem hcardT24_24_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK24)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK24 ⟨24, by decide⟩ R24_2 hpxR24_2 hcardq24_2 (by decide)).symm

/-- **Cell (24, 24) twin (q=2).** -/
theorem cell24_24_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK24) e = true)
    (h : ↥(reps (⟨24, by decide⟩ : Fin 148))) :
    species (reps (⟨24, by decide⟩ : Fin 148)) h (basisElt (reps rK24) (charOfVec2 rK24 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK24 e (h : Coordinate 2) T24_24_2 i :=
  species_entry_eq_sum rK24 ⟨24, by decide⟩ e heK h T24_24_2 hfix24_24_2 hinj24_24_2 hcardT24_24_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨24, by decide⟩) (reps rK24) (T24_24_2 i) (hfix24_24_2 i) h)

end Q2

end LeanDring.P5Presentation
