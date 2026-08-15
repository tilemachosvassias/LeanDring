/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, A-block data (rK = 54): certified per-cell species-entry instantiations, both twins.

Emit-embed-decide loop for order-25 A-block class `rK = 54` (`|G/K| = 125`).
All nonzero `H`-columns (`|gH| ≤ 2`, `t⁻¹Ht ⊆ K`).  Full 125-coset transversal
`R54` and each `H`-fixed sub-transversal `T54_rH` embedded as kernel data and
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

def rK54 : Fin 148 := ⟨54, by decide⟩

def R54list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,4,2,0)]
def R54 : Fin 125 → Coordinate 1 := fun i => R54list.getD i.val (0,0,0,0,0)

theorem hpxR54 : Function.Injective (fun i => reduceAux 1 (basisAt rK54) (R54 i)) := by decide
theorem hcardq54 : Nat.card (Coordinate 1 ⧸ reps rK54) = 125 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (54, 0): |T| = 125 -/

def T54_0list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,4,2,0)]
def T54_0 : Fin 125 → Coordinate 1 := fun i => T54_0list.getD i.val (0,0,0,0,0)

theorem hfix54_0 : ∀ i, ((T54_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK54)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54) :=
  repsFix_of_siftB rK54 ⟨0, by decide⟩ T54_0 (by decide)

theorem hinj54_0 : Function.Injective
    (fun i => ((T54_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK54)) :=
  repsInj_of_reduceAux rK54 T54_0 (by decide)

theorem hcardT54_0 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK54 ⟨0, by decide⟩ R54 hpxR54 hcardq54 (by decide)).symm

/-- **Cell (54, 0).** -/
theorem cell54_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK54) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK54) (charOfVec rK54 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK54 e (h : Coordinate 1) T54_0 i :=
  species_entry_eq_sum rK54 ⟨0, by decide⟩ e heK h T54_0 hfix54_0 hinj54_0 hcardT54_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK54) (T54_0 i) (hfix54_0 i) h)

/-! ## Cell (54, 11): |T| = 25 -/

def T54_11list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0)]
def T54_11 : Fin 25 → Coordinate 1 := fun i => T54_11list.getD i.val (0,0,0,0,0)

theorem hfix54_11 : ∀ i, ((T54_11 i : Coordinate 1) : Coordinate 1 ⧸ reps rK54)
    ∈ fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54) :=
  repsFix_of_siftB rK54 ⟨11, by decide⟩ T54_11 (by decide)

theorem hinj54_11 : Function.Injective
    (fun i => ((T54_11 i : Coordinate 1) : Coordinate 1 ⧸ reps rK54)) :=
  repsInj_of_reduceAux rK54 T54_11 (by decide)

theorem hcardT54_11 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK54 ⟨11, by decide⟩ R54 hpxR54 hcardq54 (by decide)).symm

/-- **Cell (54, 11).** -/
theorem cell54_11 (e : List (ZMod 25)) (heK : charOK (basisAt rK54) e = true)
    (h : ↥(reps (⟨11, by decide⟩ : Fin 148))) :
    species (reps (⟨11, by decide⟩ : Fin 148)) h (basisElt (reps rK54) (charOfVec rK54 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK54 e (h : Coordinate 1) T54_11 i :=
  species_entry_eq_sum rK54 ⟨11, by decide⟩ e heK h T54_11 hfix54_11 hinj54_11 hcardT54_11
    (fun i => conj_mem_of_fixedPoints (reps ⟨11, by decide⟩) (reps rK54) (T54_11 i) (hfix54_11 i) h)

/-! ## Cell (54, 12): |T| = 125 -/

def T54_12list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,2,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,4,2,0)]
def T54_12 : Fin 125 → Coordinate 1 := fun i => T54_12list.getD i.val (0,0,0,0,0)

theorem hfix54_12 : ∀ i, ((T54_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK54)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54) :=
  repsFix_of_siftB rK54 ⟨12, by decide⟩ T54_12 (by decide)

theorem hinj54_12 : Function.Injective
    (fun i => ((T54_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK54)) :=
  repsInj_of_reduceAux rK54 T54_12 (by decide)

theorem hcardT54_12 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK54 ⟨12, by decide⟩ R54 hpxR54 hcardq54 (by decide)).symm

/-- **Cell (54, 12).** -/
theorem cell54_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK54) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK54) (charOfVec rK54 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK54 e (h : Coordinate 1) T54_12 i :=
  species_entry_eq_sum rK54 ⟨12, by decide⟩ e heK h T54_12 hfix54_12 hinj54_12 hcardT54_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK54) (T54_12 i) (hfix54_12 i) h)

/-! ## Cell (54, 54): |T| = 25 -/

def T54_54list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0)]
def T54_54 : Fin 25 → Coordinate 1 := fun i => T54_54list.getD i.val (0,0,0,0,0)

theorem hfix54_54 : ∀ i, ((T54_54 i : Coordinate 1) : Coordinate 1 ⧸ reps rK54)
    ∈ fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54) :=
  repsFix_of_siftB rK54 ⟨54, by decide⟩ T54_54 (by decide)

theorem hinj54_54 : Function.Injective
    (fun i => ((T54_54 i : Coordinate 1) : Coordinate 1 ⧸ reps rK54)) :=
  repsInj_of_reduceAux rK54 T54_54 (by decide)

theorem hcardT54_54 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK54 ⟨54, by decide⟩ R54 hpxR54 hcardq54 (by decide)).symm

/-- **Cell (54, 54).** -/
theorem cell54_54 (e : List (ZMod 25)) (heK : charOK (basisAt rK54) e = true)
    (h : ↥(reps (⟨54, by decide⟩ : Fin 148))) :
    species (reps (⟨54, by decide⟩ : Fin 148)) h (basisElt (reps rK54) (charOfVec rK54 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK54 e (h : Coordinate 1) T54_54 i :=
  species_entry_eq_sum rK54 ⟨54, by decide⟩ e heK h T54_54 hfix54_54 hinj54_54 hcardT54_54
    (fun i => conj_mem_of_fixedPoints (reps ⟨54, by decide⟩) (reps rK54) (T54_54 i) (hfix54_54 i) h)

namespace Q2

def R54_2 : Fin 125 → Coordinate 2 := fun i => R54list.getD i.val (0,0,0,0,0)
theorem hpxR54_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK54) (R54_2 i)) := by decide
theorem hcardq54_2 : Nat.card (Coordinate 2 ⧸ reps rK54) = 125 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (54, 0) twin -/

def T54_0_2 : Fin 125 → Coordinate 2 := fun i => T54_0list.getD i.val (0,0,0,0,0)

theorem hfix54_0_2 : ∀ i, ((T54_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK54)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK54) :=
  repsFix_of_siftB2 rK54 ⟨0, by decide⟩ T54_0_2 (by decide)

theorem hinj54_0_2 : Function.Injective
    (fun i => ((T54_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK54)) :=
  repsInj_of_reduceAux2 rK54 T54_0_2 (by decide)

theorem hcardT54_0_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK54)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK54 ⟨0, by decide⟩ R54_2 hpxR54_2 hcardq54_2 (by decide)).symm

/-- **Cell (54, 0) twin (q=2).** -/
theorem cell54_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK54) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK54) (charOfVec2 rK54 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK54 e (h : Coordinate 2) T54_0_2 i :=
  species_entry_eq_sum rK54 ⟨0, by decide⟩ e heK h T54_0_2 hfix54_0_2 hinj54_0_2 hcardT54_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK54) (T54_0_2 i) (hfix54_0_2 i) h)

/-! ### Cell (54, 11) twin -/

def T54_11_2 : Fin 25 → Coordinate 2 := fun i => T54_11list.getD i.val (0,0,0,0,0)

theorem hfix54_11_2 : ∀ i, ((T54_11_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK54)
    ∈ fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK54) :=
  repsFix_of_siftB2 rK54 ⟨11, by decide⟩ T54_11_2 (by decide)

theorem hinj54_11_2 : Function.Injective
    (fun i => ((T54_11_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK54)) :=
  repsInj_of_reduceAux2 rK54 T54_11_2 (by decide)

theorem hcardT54_11_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK54)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK54 ⟨11, by decide⟩ R54_2 hpxR54_2 hcardq54_2 (by decide)).symm

/-- **Cell (54, 11) twin (q=2).** -/
theorem cell54_11_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK54) e = true)
    (h : ↥(reps (⟨11, by decide⟩ : Fin 148))) :
    species (reps (⟨11, by decide⟩ : Fin 148)) h (basisElt (reps rK54) (charOfVec2 rK54 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK54 e (h : Coordinate 2) T54_11_2 i :=
  species_entry_eq_sum rK54 ⟨11, by decide⟩ e heK h T54_11_2 hfix54_11_2 hinj54_11_2 hcardT54_11_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨11, by decide⟩) (reps rK54) (T54_11_2 i) (hfix54_11_2 i) h)

/-! ### Cell (54, 12) twin -/

def T54_12_2 : Fin 125 → Coordinate 2 := fun i => T54_12list.getD i.val (0,0,0,0,0)

theorem hfix54_12_2 : ∀ i, ((T54_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK54)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK54) :=
  repsFix_of_siftB2 rK54 ⟨12, by decide⟩ T54_12_2 (by decide)

theorem hinj54_12_2 : Function.Injective
    (fun i => ((T54_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK54)) :=
  repsInj_of_reduceAux2 rK54 T54_12_2 (by decide)

theorem hcardT54_12_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK54)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK54 ⟨12, by decide⟩ R54_2 hpxR54_2 hcardq54_2 (by decide)).symm

/-- **Cell (54, 12) twin (q=2).** -/
theorem cell54_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK54) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK54) (charOfVec2 rK54 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK54 e (h : Coordinate 2) T54_12_2 i :=
  species_entry_eq_sum rK54 ⟨12, by decide⟩ e heK h T54_12_2 hfix54_12_2 hinj54_12_2 hcardT54_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK54) (T54_12_2 i) (hfix54_12_2 i) h)

/-! ### Cell (54, 54) twin -/

def T54_54_2 : Fin 25 → Coordinate 2 := fun i => T54_54list.getD i.val (0,0,0,0,0)

theorem hfix54_54_2 : ∀ i, ((T54_54_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK54)
    ∈ fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK54) :=
  repsFix_of_siftB2 rK54 ⟨54, by decide⟩ T54_54_2 (by decide)

theorem hinj54_54_2 : Function.Injective
    (fun i => ((T54_54_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK54)) :=
  repsInj_of_reduceAux2 rK54 T54_54_2 (by decide)

theorem hcardT54_54_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK54)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK54 ⟨54, by decide⟩ R54_2 hpxR54_2 hcardq54_2 (by decide)).symm

/-- **Cell (54, 54) twin (q=2).** -/
theorem cell54_54_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK54) e = true)
    (h : ↥(reps (⟨54, by decide⟩ : Fin 148))) :
    species (reps (⟨54, by decide⟩ : Fin 148)) h (basisElt (reps rK54) (charOfVec2 rK54 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK54 e (h : Coordinate 2) T54_54_2 i :=
  species_entry_eq_sum rK54 ⟨54, by decide⟩ e heK h T54_54_2 hfix54_54_2 hinj54_54_2 hcardT54_54_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨54, by decide⟩) (reps rK54) (T54_54_2 i) (hfix54_54_2 i) h)

end Q2

end LeanDring.P5Presentation
