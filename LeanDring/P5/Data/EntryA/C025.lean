/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, A-block data (rK = 37): certified per-cell species-entry instantiations, both twins.

Emit-embed-decide loop for order-25 A-block class `rK = 37` (`|G/K| = 125`).
All nonzero `H`-columns (`|gH| ≤ 2`, `t⁻¹Ht ⊆ K`).  Full 125-coset transversal
`R37` and each `H`-fixed sub-transversal `T37_rH` embedded as kernel data and
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

def rK37 : Fin 148 := ⟨37, by decide⟩

def R37list : List Coordinates := [(0,1,2,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0)]
def R37 : Fin 125 → Coordinate 1 := fun i => R37list.getD i.val (0,0,0,0,0)

theorem hpxR37 : Function.Injective (fun i => reduceAux 1 (basisAt rK37) (R37 i)) := by decide
theorem hcardq37 : Nat.card (Coordinate 1 ⧸ reps rK37) = 125 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (37, 0): |T| = 125 -/

def T37_0list : List Coordinates := [(0,1,2,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0)]
def T37_0 : Fin 125 → Coordinate 1 := fun i => T37_0list.getD i.val (0,0,0,0,0)

theorem hfix37_0 : ∀ i, ((T37_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK37)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37) :=
  repsFix_of_siftB rK37 ⟨0, by decide⟩ T37_0 (by decide)

theorem hinj37_0 : Function.Injective
    (fun i => ((T37_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK37)) :=
  repsInj_of_reduceAux rK37 T37_0 (by decide)

theorem hcardT37_0 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK37 ⟨0, by decide⟩ R37 hpxR37 hcardq37 (by decide)).symm

/-- **Cell (37, 0).** -/
theorem cell37_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK37) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK37) (charOfVec rK37 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK37 e (h : Coordinate 1) T37_0 i :=
  species_entry_eq_sum rK37 ⟨0, by decide⟩ e heK h T37_0 hfix37_0 hinj37_0 hcardT37_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK37) (T37_0 i) (hfix37_0 i) h)

/-! ## Cell (37, 12): |T| = 125 -/

def T37_12list : List Coordinates := [(0,1,2,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,3,4,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,4,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,1,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,2,2,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,3,0,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,4,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,1,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,3,2,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,3,1,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,4,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,1,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,4,2,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,3,2,0), (0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,4,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,1,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0)]
def T37_12 : Fin 125 → Coordinate 1 := fun i => T37_12list.getD i.val (0,0,0,0,0)

theorem hfix37_12 : ∀ i, ((T37_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK37)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37) :=
  repsFix_of_siftB rK37 ⟨12, by decide⟩ T37_12 (by decide)

theorem hinj37_12 : Function.Injective
    (fun i => ((T37_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK37)) :=
  repsInj_of_reduceAux rK37 T37_12 (by decide)

theorem hcardT37_12 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK37 ⟨12, by decide⟩ R37 hpxR37 hcardq37 (by decide)).symm

/-- **Cell (37, 12).** -/
theorem cell37_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK37) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK37) (charOfVec rK37 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK37 e (h : Coordinate 1) T37_12 i :=
  species_entry_eq_sum rK37 ⟨12, by decide⟩ e heK h T37_12 hfix37_12 hinj37_12 hcardT37_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK37) (T37_12 i) (hfix37_12 i) h)

/-! ## Cell (37, 37): |T| = 25 -/

def T37_37list : List Coordinates := [(0,0,2,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,3,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,4,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,1,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0)]
def T37_37 : Fin 25 → Coordinate 1 := fun i => T37_37list.getD i.val (0,0,0,0,0)

theorem hfix37_37 : ∀ i, ((T37_37 i : Coordinate 1) : Coordinate 1 ⧸ reps rK37)
    ∈ fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37) :=
  repsFix_of_siftB rK37 ⟨37, by decide⟩ T37_37 (by decide)

theorem hinj37_37 : Function.Injective
    (fun i => ((T37_37 i : Coordinate 1) : Coordinate 1 ⧸ reps rK37)) :=
  repsInj_of_reduceAux rK37 T37_37 (by decide)

theorem hcardT37_37 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK37 ⟨37, by decide⟩ R37 hpxR37 hcardq37 (by decide)).symm

/-- **Cell (37, 37).** -/
theorem cell37_37 (e : List (ZMod 25)) (heK : charOK (basisAt rK37) e = true)
    (h : ↥(reps (⟨37, by decide⟩ : Fin 148))) :
    species (reps (⟨37, by decide⟩ : Fin 148)) h (basisElt (reps rK37) (charOfVec rK37 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK37 e (h : Coordinate 1) T37_37 i :=
  species_entry_eq_sum rK37 ⟨37, by decide⟩ e heK h T37_37 hfix37_37 hinj37_37 hcardT37_37
    (fun i => conj_mem_of_fixedPoints (reps ⟨37, by decide⟩) (reps rK37) (T37_37 i) (hfix37_37 i) h)

namespace Q2

def R37_2 : Fin 125 → Coordinate 2 := fun i => R37list.getD i.val (0,0,0,0,0)
theorem hpxR37_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK37) (R37_2 i)) := by decide
theorem hcardq37_2 : Nat.card (Coordinate 2 ⧸ reps rK37) = 125 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (37, 0) twin -/

def T37_0_2 : Fin 125 → Coordinate 2 := fun i => T37_0list.getD i.val (0,0,0,0,0)

theorem hfix37_0_2 : ∀ i, ((T37_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK37)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK37) :=
  repsFix_of_siftB2 rK37 ⟨0, by decide⟩ T37_0_2 (by decide)

theorem hinj37_0_2 : Function.Injective
    (fun i => ((T37_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK37)) :=
  repsInj_of_reduceAux2 rK37 T37_0_2 (by decide)

theorem hcardT37_0_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK37)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK37 ⟨0, by decide⟩ R37_2 hpxR37_2 hcardq37_2 (by decide)).symm

/-- **Cell (37, 0) twin (q=2).** -/
theorem cell37_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK37) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK37) (charOfVec2 rK37 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK37 e (h : Coordinate 2) T37_0_2 i :=
  species_entry_eq_sum rK37 ⟨0, by decide⟩ e heK h T37_0_2 hfix37_0_2 hinj37_0_2 hcardT37_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK37) (T37_0_2 i) (hfix37_0_2 i) h)

/-! ### Cell (37, 12) twin -/

def T37_12_2 : Fin 125 → Coordinate 2 := fun i => T37_12list.getD i.val (0,0,0,0,0)

theorem hfix37_12_2 : ∀ i, ((T37_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK37)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK37) :=
  repsFix_of_siftB2 rK37 ⟨12, by decide⟩ T37_12_2 (by decide)

theorem hinj37_12_2 : Function.Injective
    (fun i => ((T37_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK37)) :=
  repsInj_of_reduceAux2 rK37 T37_12_2 (by decide)

theorem hcardT37_12_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK37)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK37 ⟨12, by decide⟩ R37_2 hpxR37_2 hcardq37_2 (by decide)).symm

/-- **Cell (37, 12) twin (q=2).** -/
theorem cell37_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK37) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK37) (charOfVec2 rK37 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK37 e (h : Coordinate 2) T37_12_2 i :=
  species_entry_eq_sum rK37 ⟨12, by decide⟩ e heK h T37_12_2 hfix37_12_2 hinj37_12_2 hcardT37_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK37) (T37_12_2 i) (hfix37_12_2 i) h)

/-! ### Cell (37, 37) twin -/

def T37_37_2 : Fin 25 → Coordinate 2 := fun i => T37_37list.getD i.val (0,0,0,0,0)

theorem hfix37_37_2 : ∀ i, ((T37_37_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK37)
    ∈ fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK37) :=
  repsFix_of_siftB2 rK37 ⟨37, by decide⟩ T37_37_2 (by decide)

theorem hinj37_37_2 : Function.Injective
    (fun i => ((T37_37_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK37)) :=
  repsInj_of_reduceAux2 rK37 T37_37_2 (by decide)

theorem hcardT37_37_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK37)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK37 ⟨37, by decide⟩ R37_2 hpxR37_2 hcardq37_2 (by decide)).symm

/-- **Cell (37, 37) twin (q=2).** -/
theorem cell37_37_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK37) e = true)
    (h : ↥(reps (⟨37, by decide⟩ : Fin 148))) :
    species (reps (⟨37, by decide⟩ : Fin 148)) h (basisElt (reps rK37) (charOfVec2 rK37 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK37 e (h : Coordinate 2) T37_37_2 i :=
  species_entry_eq_sum rK37 ⟨37, by decide⟩ e heK h T37_37_2 hfix37_37_2 hinj37_37_2 hcardT37_37_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨37, by decide⟩) (reps rK37) (T37_37_2 i) (hfix37_37_2 i) h)

end Q2

end LeanDring.P5Presentation
