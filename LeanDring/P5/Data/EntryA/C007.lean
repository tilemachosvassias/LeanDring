/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, A-block data (rK = 19): certified per-cell species-entry instantiations, both twins.

Emit-embed-decide loop for order-25 A-block class `rK = 19` (`|G/K| = 125`).
All nonzero `H`-columns (`|gH| ≤ 2`, `t⁻¹Ht ⊆ K`).  Full 125-coset transversal
`R19` and each `H`-fixed sub-transversal `T19_rH` embedded as kernel data and
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

def rK19 : Fin 148 := ⟨19, by decide⟩

def R19list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,1,0,4,0), (1,1,0,0,0), (1,1,0,1,0), (1,1,0,2,0), (1,1,0,3,0), (1,2,0,4,0), (1,2,0,0,0), (1,2,0,1,0), (1,2,0,2,0), (1,2,0,3,0), (1,3,0,4,0), (1,3,0,0,0), (1,3,0,1,0), (1,3,0,2,0), (1,3,0,3,0), (1,4,0,4,0), (1,4,0,0,0), (1,4,0,1,0), (1,4,0,2,0), (1,4,0,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,1,0,4,0), (2,1,0,0,0), (2,1,0,1,0), (2,1,0,2,0), (2,1,0,3,0), (2,2,0,4,0), (2,2,0,0,0), (2,2,0,1,0), (2,2,0,2,0), (2,2,0,3,0), (2,3,0,4,0), (2,3,0,0,0), (2,3,0,1,0), (2,3,0,2,0), (2,3,0,3,0), (2,4,0,4,0), (2,4,0,0,0), (2,4,0,1,0), (2,4,0,2,0), (2,4,0,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,1,0,4,0), (3,1,0,0,0), (3,1,0,1,0), (3,1,0,2,0), (3,1,0,3,0), (3,2,0,4,0), (3,2,0,0,0), (3,2,0,1,0), (3,2,0,2,0), (3,2,0,3,0), (3,3,0,4,0), (3,3,0,0,0), (3,3,0,1,0), (3,3,0,2,0), (3,3,0,3,0), (3,4,0,4,0), (3,4,0,0,0), (3,4,0,1,0), (3,4,0,2,0), (3,4,0,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,1,0,4,0), (4,1,0,0,0), (4,1,0,1,0), (4,1,0,2,0), (4,1,0,3,0), (4,2,0,4,0), (4,2,0,0,0), (4,2,0,1,0), (4,2,0,2,0), (4,2,0,3,0), (4,3,0,4,0), (4,3,0,0,0), (4,3,0,1,0), (4,3,0,2,0), (4,3,0,3,0), (4,4,0,4,0), (4,4,0,0,0), (4,4,0,1,0), (4,4,0,2,0), (4,4,0,3,0)]
def R19 : Fin 125 → Coordinate 1 := fun i => R19list.getD i.val (0,0,0,0,0)

theorem hpxR19 : Function.Injective (fun i => reduceAux 1 (basisAt rK19) (R19 i)) := by decide
theorem hcardq19 : Nat.card (Coordinate 1 ⧸ reps rK19) = 125 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (19, 0): |T| = 125 -/

def T19_0list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,1,0,4,0), (1,1,0,0,0), (1,1,0,1,0), (1,1,0,2,0), (1,1,0,3,0), (1,2,0,4,0), (1,2,0,0,0), (1,2,0,1,0), (1,2,0,2,0), (1,2,0,3,0), (1,3,0,4,0), (1,3,0,0,0), (1,3,0,1,0), (1,3,0,2,0), (1,3,0,3,0), (1,4,0,4,0), (1,4,0,0,0), (1,4,0,1,0), (1,4,0,2,0), (1,4,0,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,1,0,4,0), (2,1,0,0,0), (2,1,0,1,0), (2,1,0,2,0), (2,1,0,3,0), (2,2,0,4,0), (2,2,0,0,0), (2,2,0,1,0), (2,2,0,2,0), (2,2,0,3,0), (2,3,0,4,0), (2,3,0,0,0), (2,3,0,1,0), (2,3,0,2,0), (2,3,0,3,0), (2,4,0,4,0), (2,4,0,0,0), (2,4,0,1,0), (2,4,0,2,0), (2,4,0,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,1,0,4,0), (3,1,0,0,0), (3,1,0,1,0), (3,1,0,2,0), (3,1,0,3,0), (3,2,0,4,0), (3,2,0,0,0), (3,2,0,1,0), (3,2,0,2,0), (3,2,0,3,0), (3,3,0,4,0), (3,3,0,0,0), (3,3,0,1,0), (3,3,0,2,0), (3,3,0,3,0), (3,4,0,4,0), (3,4,0,0,0), (3,4,0,1,0), (3,4,0,2,0), (3,4,0,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,1,0,4,0), (4,1,0,0,0), (4,1,0,1,0), (4,1,0,2,0), (4,1,0,3,0), (4,2,0,4,0), (4,2,0,0,0), (4,2,0,1,0), (4,2,0,2,0), (4,2,0,3,0), (4,3,0,4,0), (4,3,0,0,0), (4,3,0,1,0), (4,3,0,2,0), (4,3,0,3,0), (4,4,0,4,0), (4,4,0,0,0), (4,4,0,1,0), (4,4,0,2,0), (4,4,0,3,0)]
def T19_0 : Fin 125 → Coordinate 1 := fun i => T19_0list.getD i.val (0,0,0,0,0)

theorem hfix19_0 : ∀ i, ((T19_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK19)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19) :=
  repsFix_of_siftB rK19 ⟨0, by decide⟩ T19_0 (by decide)

theorem hinj19_0 : Function.Injective
    (fun i => ((T19_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK19)) :=
  repsInj_of_reduceAux rK19 T19_0 (by decide)

theorem hcardT19_0 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK19 ⟨0, by decide⟩ R19 hpxR19 hcardq19 (by decide)).symm

/-- **Cell (19, 0).** -/
theorem cell19_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK19) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK19) (charOfVec rK19 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK19 e (h : Coordinate 1) T19_0 i :=
  species_entry_eq_sum rK19 ⟨0, by decide⟩ e heK h T19_0 hfix19_0 hinj19_0 hcardT19_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK19) (T19_0 i) (hfix19_0 i) h)

/-! ## Cell (19, 1): |T| = 125 -/

def T19_1list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,1,0,4,0), (1,1,0,0,0), (1,1,0,1,0), (1,1,0,2,0), (1,1,0,3,0), (1,2,0,4,0), (1,2,0,0,0), (1,2,0,1,0), (1,2,0,2,0), (1,2,0,3,0), (1,3,0,4,0), (1,3,0,0,0), (1,3,0,1,0), (1,3,0,2,0), (1,3,0,3,0), (1,4,0,4,0), (1,4,0,0,0), (1,4,0,1,0), (1,4,0,2,0), (1,4,0,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,1,0,4,0), (2,1,0,0,0), (2,1,0,1,0), (2,1,0,2,0), (2,1,0,3,0), (2,2,0,4,0), (2,2,0,0,0), (2,2,0,1,0), (2,2,0,2,0), (2,2,0,3,0), (2,3,0,4,0), (2,3,0,0,0), (2,3,0,1,0), (2,3,0,2,0), (2,3,0,3,0), (2,4,0,4,0), (2,4,0,0,0), (2,4,0,1,0), (2,4,0,2,0), (2,4,0,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,1,0,4,0), (3,1,0,0,0), (3,1,0,1,0), (3,1,0,2,0), (3,1,0,3,0), (3,2,0,4,0), (3,2,0,0,0), (3,2,0,1,0), (3,2,0,2,0), (3,2,0,3,0), (3,3,0,4,0), (3,3,0,0,0), (3,3,0,1,0), (3,3,0,2,0), (3,3,0,3,0), (3,4,0,4,0), (3,4,0,0,0), (3,4,0,1,0), (3,4,0,2,0), (3,4,0,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,1,0,4,0), (4,1,0,0,0), (4,1,0,1,0), (4,1,0,2,0), (4,1,0,3,0), (4,2,0,4,0), (4,2,0,0,0), (4,2,0,1,0), (4,2,0,2,0), (4,2,0,3,0), (4,3,0,4,0), (4,3,0,0,0), (4,3,0,1,0), (4,3,0,2,0), (4,3,0,3,0), (4,4,0,4,0), (4,4,0,0,0), (4,4,0,1,0), (4,4,0,2,0), (4,4,0,3,0)]
def T19_1 : Fin 125 → Coordinate 1 := fun i => T19_1list.getD i.val (0,0,0,0,0)

theorem hfix19_1 : ∀ i, ((T19_1 i : Coordinate 1) : Coordinate 1 ⧸ reps rK19)
    ∈ fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19) :=
  repsFix_of_siftB rK19 ⟨1, by decide⟩ T19_1 (by decide)

theorem hinj19_1 : Function.Injective
    (fun i => ((T19_1 i : Coordinate 1) : Coordinate 1 ⧸ reps rK19)) :=
  repsInj_of_reduceAux rK19 T19_1 (by decide)

theorem hcardT19_1 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK19 ⟨1, by decide⟩ R19 hpxR19 hcardq19 (by decide)).symm

/-- **Cell (19, 1).** -/
theorem cell19_1 (e : List (ZMod 25)) (heK : charOK (basisAt rK19) e = true)
    (h : ↥(reps (⟨1, by decide⟩ : Fin 148))) :
    species (reps (⟨1, by decide⟩ : Fin 148)) h (basisElt (reps rK19) (charOfVec rK19 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK19 e (h : Coordinate 1) T19_1 i :=
  species_entry_eq_sum rK19 ⟨1, by decide⟩ e heK h T19_1 hfix19_1 hinj19_1 hcardT19_1
    (fun i => conj_mem_of_fixedPoints (reps ⟨1, by decide⟩) (reps rK19) (T19_1 i) (hfix19_1 i) h)

/-! ## Cell (19, 12): |T| = 125 -/

def T19_12list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,1,0,4,0), (1,1,0,0,0), (1,1,0,1,0), (1,1,0,2,0), (1,1,0,3,0), (1,2,0,4,0), (1,2,0,0,0), (1,2,0,1,0), (1,2,0,2,0), (1,2,0,3,0), (1,3,0,4,0), (1,3,0,0,0), (1,3,0,1,0), (1,3,0,2,0), (1,3,0,3,0), (1,4,0,4,0), (1,4,0,0,0), (1,4,0,1,0), (1,4,0,2,0), (1,4,0,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,1,0,4,0), (2,1,0,0,0), (2,1,0,1,0), (2,1,0,2,0), (2,1,0,3,0), (2,2,0,4,0), (2,2,0,0,0), (2,2,0,1,0), (2,2,0,2,0), (2,2,0,3,0), (2,3,0,4,0), (2,3,0,0,0), (2,3,0,1,0), (2,3,0,2,0), (2,3,0,3,0), (2,4,0,4,0), (2,4,0,0,0), (2,4,0,1,0), (2,4,0,2,0), (2,4,0,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,1,0,4,0), (3,1,0,0,0), (3,1,0,1,0), (3,1,0,2,0), (3,1,0,3,0), (3,2,0,4,0), (3,2,0,0,0), (3,2,0,1,0), (3,2,0,2,0), (3,2,0,3,0), (3,3,0,4,0), (3,3,0,0,0), (3,3,0,1,0), (3,3,0,2,0), (3,3,0,3,0), (3,4,0,4,0), (3,4,0,0,0), (3,4,0,1,0), (3,4,0,2,0), (3,4,0,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,1,0,4,0), (4,1,0,0,0), (4,1,0,1,0), (4,1,0,2,0), (4,1,0,3,0), (4,2,0,4,0), (4,2,0,0,0), (4,2,0,1,0), (4,2,0,2,0), (4,2,0,3,0), (4,3,0,4,0), (4,3,0,0,0), (4,3,0,1,0), (4,3,0,2,0), (4,3,0,3,0), (4,4,0,4,0), (4,4,0,0,0), (4,4,0,1,0), (4,4,0,2,0), (4,4,0,3,0)]
def T19_12 : Fin 125 → Coordinate 1 := fun i => T19_12list.getD i.val (0,0,0,0,0)

theorem hfix19_12 : ∀ i, ((T19_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK19)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19) :=
  repsFix_of_siftB rK19 ⟨12, by decide⟩ T19_12 (by decide)

theorem hinj19_12 : Function.Injective
    (fun i => ((T19_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK19)) :=
  repsInj_of_reduceAux rK19 T19_12 (by decide)

theorem hcardT19_12 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK19 ⟨12, by decide⟩ R19 hpxR19 hcardq19 (by decide)).symm

/-- **Cell (19, 12).** -/
theorem cell19_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK19) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK19) (charOfVec rK19 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK19 e (h : Coordinate 1) T19_12 i :=
  species_entry_eq_sum rK19 ⟨12, by decide⟩ e heK h T19_12 hfix19_12 hinj19_12 hcardT19_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK19) (T19_12 i) (hfix19_12 i) h)

/-! ## Cell (19, 19): |T| = 125 -/

def T19_19list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,1,0,4,0), (1,1,0,0,0), (1,1,0,1,0), (1,1,0,2,0), (1,1,0,3,0), (1,2,0,4,0), (1,2,0,0,0), (1,2,0,1,0), (1,2,0,2,0), (1,2,0,3,0), (1,3,0,4,0), (1,3,0,0,0), (1,3,0,1,0), (1,3,0,2,0), (1,3,0,3,0), (1,4,0,4,0), (1,4,0,0,0), (1,4,0,1,0), (1,4,0,2,0), (1,4,0,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,1,0,4,0), (2,1,0,0,0), (2,1,0,1,0), (2,1,0,2,0), (2,1,0,3,0), (2,2,0,4,0), (2,2,0,0,0), (2,2,0,1,0), (2,2,0,2,0), (2,2,0,3,0), (2,3,0,4,0), (2,3,0,0,0), (2,3,0,1,0), (2,3,0,2,0), (2,3,0,3,0), (2,4,0,4,0), (2,4,0,0,0), (2,4,0,1,0), (2,4,0,2,0), (2,4,0,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,1,0,4,0), (3,1,0,0,0), (3,1,0,1,0), (3,1,0,2,0), (3,1,0,3,0), (3,2,0,4,0), (3,2,0,0,0), (3,2,0,1,0), (3,2,0,2,0), (3,2,0,3,0), (3,3,0,4,0), (3,3,0,0,0), (3,3,0,1,0), (3,3,0,2,0), (3,3,0,3,0), (3,4,0,4,0), (3,4,0,0,0), (3,4,0,1,0), (3,4,0,2,0), (3,4,0,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,1,0,4,0), (4,1,0,0,0), (4,1,0,1,0), (4,1,0,2,0), (4,1,0,3,0), (4,2,0,4,0), (4,2,0,0,0), (4,2,0,1,0), (4,2,0,2,0), (4,2,0,3,0), (4,3,0,4,0), (4,3,0,0,0), (4,3,0,1,0), (4,3,0,2,0), (4,3,0,3,0), (4,4,0,4,0), (4,4,0,0,0), (4,4,0,1,0), (4,4,0,2,0), (4,4,0,3,0)]
def T19_19 : Fin 125 → Coordinate 1 := fun i => T19_19list.getD i.val (0,0,0,0,0)

theorem hfix19_19 : ∀ i, ((T19_19 i : Coordinate 1) : Coordinate 1 ⧸ reps rK19)
    ∈ fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19) :=
  repsFix_of_siftB rK19 ⟨19, by decide⟩ T19_19 (by decide)

theorem hinj19_19 : Function.Injective
    (fun i => ((T19_19 i : Coordinate 1) : Coordinate 1 ⧸ reps rK19)) :=
  repsInj_of_reduceAux rK19 T19_19 (by decide)

theorem hcardT19_19 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK19 ⟨19, by decide⟩ R19 hpxR19 hcardq19 (by decide)).symm

/-- **Cell (19, 19).** -/
theorem cell19_19 (e : List (ZMod 25)) (heK : charOK (basisAt rK19) e = true)
    (h : ↥(reps (⟨19, by decide⟩ : Fin 148))) :
    species (reps (⟨19, by decide⟩ : Fin 148)) h (basisElt (reps rK19) (charOfVec rK19 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK19 e (h : Coordinate 1) T19_19 i :=
  species_entry_eq_sum rK19 ⟨19, by decide⟩ e heK h T19_19 hfix19_19 hinj19_19 hcardT19_19
    (fun i => conj_mem_of_fixedPoints (reps ⟨19, by decide⟩) (reps rK19) (T19_19 i) (hfix19_19 i) h)

namespace Q2

def R19_2 : Fin 125 → Coordinate 2 := fun i => R19list.getD i.val (0,0,0,0,0)
theorem hpxR19_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK19) (R19_2 i)) := by decide
theorem hcardq19_2 : Nat.card (Coordinate 2 ⧸ reps rK19) = 125 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (19, 0) twin -/

def T19_0_2 : Fin 125 → Coordinate 2 := fun i => T19_0list.getD i.val (0,0,0,0,0)

theorem hfix19_0_2 : ∀ i, ((T19_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK19)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK19) :=
  repsFix_of_siftB2 rK19 ⟨0, by decide⟩ T19_0_2 (by decide)

theorem hinj19_0_2 : Function.Injective
    (fun i => ((T19_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK19)) :=
  repsInj_of_reduceAux2 rK19 T19_0_2 (by decide)

theorem hcardT19_0_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK19)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK19 ⟨0, by decide⟩ R19_2 hpxR19_2 hcardq19_2 (by decide)).symm

/-- **Cell (19, 0) twin (q=2).** -/
theorem cell19_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK19) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK19) (charOfVec2 rK19 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK19 e (h : Coordinate 2) T19_0_2 i :=
  species_entry_eq_sum rK19 ⟨0, by decide⟩ e heK h T19_0_2 hfix19_0_2 hinj19_0_2 hcardT19_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK19) (T19_0_2 i) (hfix19_0_2 i) h)

/-! ### Cell (19, 1) twin -/

def T19_1_2 : Fin 125 → Coordinate 2 := fun i => T19_1list.getD i.val (0,0,0,0,0)

theorem hfix19_1_2 : ∀ i, ((T19_1_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK19)
    ∈ fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK19) :=
  repsFix_of_siftB2 rK19 ⟨1, by decide⟩ T19_1_2 (by decide)

theorem hinj19_1_2 : Function.Injective
    (fun i => ((T19_1_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK19)) :=
  repsInj_of_reduceAux2 rK19 T19_1_2 (by decide)

theorem hcardT19_1_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK19)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK19 ⟨1, by decide⟩ R19_2 hpxR19_2 hcardq19_2 (by decide)).symm

/-- **Cell (19, 1) twin (q=2).** -/
theorem cell19_1_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK19) e = true)
    (h : ↥(reps (⟨1, by decide⟩ : Fin 148))) :
    species (reps (⟨1, by decide⟩ : Fin 148)) h (basisElt (reps rK19) (charOfVec2 rK19 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK19 e (h : Coordinate 2) T19_1_2 i :=
  species_entry_eq_sum rK19 ⟨1, by decide⟩ e heK h T19_1_2 hfix19_1_2 hinj19_1_2 hcardT19_1_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨1, by decide⟩) (reps rK19) (T19_1_2 i) (hfix19_1_2 i) h)

/-! ### Cell (19, 12) twin -/

def T19_12_2 : Fin 125 → Coordinate 2 := fun i => T19_12list.getD i.val (0,0,0,0,0)

theorem hfix19_12_2 : ∀ i, ((T19_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK19)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK19) :=
  repsFix_of_siftB2 rK19 ⟨12, by decide⟩ T19_12_2 (by decide)

theorem hinj19_12_2 : Function.Injective
    (fun i => ((T19_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK19)) :=
  repsInj_of_reduceAux2 rK19 T19_12_2 (by decide)

theorem hcardT19_12_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK19)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK19 ⟨12, by decide⟩ R19_2 hpxR19_2 hcardq19_2 (by decide)).symm

/-- **Cell (19, 12) twin (q=2).** -/
theorem cell19_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK19) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK19) (charOfVec2 rK19 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK19 e (h : Coordinate 2) T19_12_2 i :=
  species_entry_eq_sum rK19 ⟨12, by decide⟩ e heK h T19_12_2 hfix19_12_2 hinj19_12_2 hcardT19_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK19) (T19_12_2 i) (hfix19_12_2 i) h)

/-! ### Cell (19, 19) twin -/

def T19_19_2 : Fin 125 → Coordinate 2 := fun i => T19_19list.getD i.val (0,0,0,0,0)

theorem hfix19_19_2 : ∀ i, ((T19_19_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK19)
    ∈ fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK19) :=
  repsFix_of_siftB2 rK19 ⟨19, by decide⟩ T19_19_2 (by decide)

theorem hinj19_19_2 : Function.Injective
    (fun i => ((T19_19_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK19)) :=
  repsInj_of_reduceAux2 rK19 T19_19_2 (by decide)

theorem hcardT19_19_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK19)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK19 ⟨19, by decide⟩ R19_2 hpxR19_2 hcardq19_2 (by decide)).symm

/-- **Cell (19, 19) twin (q=2).** -/
theorem cell19_19_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK19) e = true)
    (h : ↥(reps (⟨19, by decide⟩ : Fin 148))) :
    species (reps (⟨19, by decide⟩ : Fin 148)) h (basisElt (reps rK19) (charOfVec2 rK19 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK19 e (h : Coordinate 2) T19_19_2 i :=
  species_entry_eq_sum rK19 ⟨19, by decide⟩ e heK h T19_19_2 hfix19_19_2 hinj19_19_2 hcardT19_19_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨19, by decide⟩) (reps rK19) (T19_19_2 i) (hfix19_19_2 i) h)

end Q2

end LeanDring.P5Presentation
