/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, A-block data (rK = 38): certified per-cell species-entry instantiations, both twins.

Emit-embed-decide loop for order-25 A-block class `rK = 38` (`|G/K| = 125`).
All nonzero `H`-columns (`|gH| ≤ 2`, `t⁻¹Ht ⊆ K`).  Full 125-coset transversal
`R38` and each `H`-fixed sub-transversal `T38_rH` embedded as kernel data and
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

def rK38 : Fin 148 := ⟨38, by decide⟩

def R38list : List Coordinates := [(0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (1,0,3,4,0), (1,0,3,0,0), (1,0,3,1,0), (1,0,3,2,0), (1,0,3,3,0), (1,0,4,4,0), (1,0,4,0,0), (1,0,4,1,0), (1,0,4,2,0), (1,0,4,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,0,1,4,0), (1,0,1,0,0), (1,0,1,1,0), (1,0,1,2,0), (1,0,1,3,0), (1,0,2,4,0), (1,0,2,0,0), (1,0,2,1,0), (1,0,2,2,0), (1,0,2,3,0), (2,0,3,4,0), (2,0,3,0,0), (2,0,3,1,0), (2,0,3,2,0), (2,0,3,3,0), (2,0,4,4,0), (2,0,4,0,0), (2,0,4,1,0), (2,0,4,2,0), (2,0,4,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,0,1,4,0), (2,0,1,0,0), (2,0,1,1,0), (2,0,1,2,0), (2,0,1,3,0), (2,0,2,4,0), (2,0,2,0,0), (2,0,2,1,0), (2,0,2,2,0), (2,0,2,3,0), (3,0,3,4,0), (3,0,3,0,0), (3,0,3,1,0), (3,0,3,2,0), (3,0,3,3,0), (3,0,4,4,0), (3,0,4,0,0), (3,0,4,1,0), (3,0,4,2,0), (3,0,4,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,0,1,4,0), (3,0,1,0,0), (3,0,1,1,0), (3,0,1,2,0), (3,0,1,3,0), (3,0,2,4,0), (3,0,2,0,0), (3,0,2,1,0), (3,0,2,2,0), (3,0,2,3,0), (4,0,3,4,0), (4,0,3,0,0), (4,0,3,1,0), (4,0,3,2,0), (4,0,3,3,0), (4,0,4,4,0), (4,0,4,0,0), (4,0,4,1,0), (4,0,4,2,0), (4,0,4,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,0,1,4,0), (4,0,1,0,0), (4,0,1,1,0), (4,0,1,2,0), (4,0,1,3,0), (4,0,2,4,0), (4,0,2,0,0), (4,0,2,1,0), (4,0,2,2,0), (4,0,2,3,0)]
def R38 : Fin 125 → Coordinate 1 := fun i => R38list.getD i.val (0,0,0,0,0)

theorem hpxR38 : Function.Injective (fun i => reduceAux 1 (basisAt rK38) (R38 i)) := by decide
theorem hcardq38 : Nat.card (Coordinate 1 ⧸ reps rK38) = 125 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (38, 0): |T| = 125 -/

def T38_0list : List Coordinates := [(0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (1,0,3,4,0), (1,0,3,0,0), (1,0,3,1,0), (1,0,3,2,0), (1,0,3,3,0), (1,0,4,4,0), (1,0,4,0,0), (1,0,4,1,0), (1,0,4,2,0), (1,0,4,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,0,1,4,0), (1,0,1,0,0), (1,0,1,1,0), (1,0,1,2,0), (1,0,1,3,0), (1,0,2,4,0), (1,0,2,0,0), (1,0,2,1,0), (1,0,2,2,0), (1,0,2,3,0), (2,0,3,4,0), (2,0,3,0,0), (2,0,3,1,0), (2,0,3,2,0), (2,0,3,3,0), (2,0,4,4,0), (2,0,4,0,0), (2,0,4,1,0), (2,0,4,2,0), (2,0,4,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,0,1,4,0), (2,0,1,0,0), (2,0,1,1,0), (2,0,1,2,0), (2,0,1,3,0), (2,0,2,4,0), (2,0,2,0,0), (2,0,2,1,0), (2,0,2,2,0), (2,0,2,3,0), (3,0,3,4,0), (3,0,3,0,0), (3,0,3,1,0), (3,0,3,2,0), (3,0,3,3,0), (3,0,4,4,0), (3,0,4,0,0), (3,0,4,1,0), (3,0,4,2,0), (3,0,4,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,0,1,4,0), (3,0,1,0,0), (3,0,1,1,0), (3,0,1,2,0), (3,0,1,3,0), (3,0,2,4,0), (3,0,2,0,0), (3,0,2,1,0), (3,0,2,2,0), (3,0,2,3,0), (4,0,3,4,0), (4,0,3,0,0), (4,0,3,1,0), (4,0,3,2,0), (4,0,3,3,0), (4,0,4,4,0), (4,0,4,0,0), (4,0,4,1,0), (4,0,4,2,0), (4,0,4,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,0,1,4,0), (4,0,1,0,0), (4,0,1,1,0), (4,0,1,2,0), (4,0,1,3,0), (4,0,2,4,0), (4,0,2,0,0), (4,0,2,1,0), (4,0,2,2,0), (4,0,2,3,0)]
def T38_0 : Fin 125 → Coordinate 1 := fun i => T38_0list.getD i.val (0,0,0,0,0)

theorem hfix38_0 : ∀ i, ((T38_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK38)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38) :=
  repsFix_of_siftB rK38 ⟨0, by decide⟩ T38_0 (by decide)

theorem hinj38_0 : Function.Injective
    (fun i => ((T38_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK38)) :=
  repsInj_of_reduceAux rK38 T38_0 (by decide)

theorem hcardT38_0 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK38 ⟨0, by decide⟩ R38 hpxR38 hcardq38 (by decide)).symm

/-- **Cell (38, 0).** -/
theorem cell38_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK38) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK38) (charOfVec rK38 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK38 e (h : Coordinate 1) T38_0 i :=
  species_entry_eq_sum rK38 ⟨0, by decide⟩ e heK h T38_0 hfix38_0 hinj38_0 hcardT38_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK38) (T38_0 i) (hfix38_0 i) h)

/-! ## Cell (38, 12): |T| = 125 -/

def T38_12list : List Coordinates := [(0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (1,0,3,4,0), (1,0,3,0,0), (1,0,3,1,0), (1,0,3,2,0), (1,0,3,3,0), (1,0,4,4,0), (1,0,4,0,0), (1,0,4,1,0), (1,0,4,2,0), (1,0,4,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,0,1,4,0), (1,0,1,0,0), (1,0,1,1,0), (1,0,1,2,0), (1,0,1,3,0), (1,0,2,4,0), (1,0,2,0,0), (1,0,2,1,0), (1,0,2,2,0), (1,0,2,3,0), (2,0,3,4,0), (2,0,3,0,0), (2,0,3,1,0), (2,0,3,2,0), (2,0,3,3,0), (2,0,4,4,0), (2,0,4,0,0), (2,0,4,1,0), (2,0,4,2,0), (2,0,4,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,0,1,4,0), (2,0,1,0,0), (2,0,1,1,0), (2,0,1,2,0), (2,0,1,3,0), (2,0,2,4,0), (2,0,2,0,0), (2,0,2,1,0), (2,0,2,2,0), (2,0,2,3,0), (3,0,3,4,0), (3,0,3,0,0), (3,0,3,1,0), (3,0,3,2,0), (3,0,3,3,0), (3,0,4,4,0), (3,0,4,0,0), (3,0,4,1,0), (3,0,4,2,0), (3,0,4,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,0,1,4,0), (3,0,1,0,0), (3,0,1,1,0), (3,0,1,2,0), (3,0,1,3,0), (3,0,2,4,0), (3,0,2,0,0), (3,0,2,1,0), (3,0,2,2,0), (3,0,2,3,0), (4,0,3,4,0), (4,0,3,0,0), (4,0,3,1,0), (4,0,3,2,0), (4,0,3,3,0), (4,0,4,4,0), (4,0,4,0,0), (4,0,4,1,0), (4,0,4,2,0), (4,0,4,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,0,1,4,0), (4,0,1,0,0), (4,0,1,1,0), (4,0,1,2,0), (4,0,1,3,0), (4,0,2,4,0), (4,0,2,0,0), (4,0,2,1,0), (4,0,2,2,0), (4,0,2,3,0)]
def T38_12 : Fin 125 → Coordinate 1 := fun i => T38_12list.getD i.val (0,0,0,0,0)

theorem hfix38_12 : ∀ i, ((T38_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK38)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38) :=
  repsFix_of_siftB rK38 ⟨12, by decide⟩ T38_12 (by decide)

theorem hinj38_12 : Function.Injective
    (fun i => ((T38_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK38)) :=
  repsInj_of_reduceAux rK38 T38_12 (by decide)

theorem hcardT38_12 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK38 ⟨12, by decide⟩ R38 hpxR38 hcardq38 (by decide)).symm

/-- **Cell (38, 12).** -/
theorem cell38_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK38) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK38) (charOfVec rK38 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK38 e (h : Coordinate 1) T38_12 i :=
  species_entry_eq_sum rK38 ⟨12, by decide⟩ e heK h T38_12 hfix38_12 hinj38_12 hcardT38_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK38) (T38_12 i) (hfix38_12 i) h)

/-! ## Cell (38, 38): |T| = 25 -/

def T38_38list : List Coordinates := [(0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0)]
def T38_38 : Fin 25 → Coordinate 1 := fun i => T38_38list.getD i.val (0,0,0,0,0)

theorem hfix38_38 : ∀ i, ((T38_38 i : Coordinate 1) : Coordinate 1 ⧸ reps rK38)
    ∈ fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38) :=
  repsFix_of_siftB rK38 ⟨38, by decide⟩ T38_38 (by decide)

theorem hinj38_38 : Function.Injective
    (fun i => ((T38_38 i : Coordinate 1) : Coordinate 1 ⧸ reps rK38)) :=
  repsInj_of_reduceAux rK38 T38_38 (by decide)

theorem hcardT38_38 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK38 ⟨38, by decide⟩ R38 hpxR38 hcardq38 (by decide)).symm

/-- **Cell (38, 38).** -/
theorem cell38_38 (e : List (ZMod 25)) (heK : charOK (basisAt rK38) e = true)
    (h : ↥(reps (⟨38, by decide⟩ : Fin 148))) :
    species (reps (⟨38, by decide⟩ : Fin 148)) h (basisElt (reps rK38) (charOfVec rK38 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK38 e (h : Coordinate 1) T38_38 i :=
  species_entry_eq_sum rK38 ⟨38, by decide⟩ e heK h T38_38 hfix38_38 hinj38_38 hcardT38_38
    (fun i => conj_mem_of_fixedPoints (reps ⟨38, by decide⟩) (reps rK38) (T38_38 i) (hfix38_38 i) h)

namespace Q2

def R38_2 : Fin 125 → Coordinate 2 := fun i => R38list.getD i.val (0,0,0,0,0)
theorem hpxR38_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK38) (R38_2 i)) := by decide
theorem hcardq38_2 : Nat.card (Coordinate 2 ⧸ reps rK38) = 125 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (38, 0) twin -/

def T38_0_2 : Fin 125 → Coordinate 2 := fun i => T38_0list.getD i.val (0,0,0,0,0)

theorem hfix38_0_2 : ∀ i, ((T38_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK38)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK38) :=
  repsFix_of_siftB2 rK38 ⟨0, by decide⟩ T38_0_2 (by decide)

theorem hinj38_0_2 : Function.Injective
    (fun i => ((T38_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK38)) :=
  repsInj_of_reduceAux2 rK38 T38_0_2 (by decide)

theorem hcardT38_0_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK38)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK38 ⟨0, by decide⟩ R38_2 hpxR38_2 hcardq38_2 (by decide)).symm

/-- **Cell (38, 0) twin (q=2).** -/
theorem cell38_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK38) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK38) (charOfVec2 rK38 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK38 e (h : Coordinate 2) T38_0_2 i :=
  species_entry_eq_sum rK38 ⟨0, by decide⟩ e heK h T38_0_2 hfix38_0_2 hinj38_0_2 hcardT38_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK38) (T38_0_2 i) (hfix38_0_2 i) h)

/-! ### Cell (38, 12) twin -/

def T38_12_2 : Fin 125 → Coordinate 2 := fun i => T38_12list.getD i.val (0,0,0,0,0)

theorem hfix38_12_2 : ∀ i, ((T38_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK38)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK38) :=
  repsFix_of_siftB2 rK38 ⟨12, by decide⟩ T38_12_2 (by decide)

theorem hinj38_12_2 : Function.Injective
    (fun i => ((T38_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK38)) :=
  repsInj_of_reduceAux2 rK38 T38_12_2 (by decide)

theorem hcardT38_12_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK38)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK38 ⟨12, by decide⟩ R38_2 hpxR38_2 hcardq38_2 (by decide)).symm

/-- **Cell (38, 12) twin (q=2).** -/
theorem cell38_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK38) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK38) (charOfVec2 rK38 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK38 e (h : Coordinate 2) T38_12_2 i :=
  species_entry_eq_sum rK38 ⟨12, by decide⟩ e heK h T38_12_2 hfix38_12_2 hinj38_12_2 hcardT38_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK38) (T38_12_2 i) (hfix38_12_2 i) h)

/-! ### Cell (38, 38) twin -/

def T38_38_2 : Fin 25 → Coordinate 2 := fun i => T38_38list.getD i.val (0,0,0,0,0)

theorem hfix38_38_2 : ∀ i, ((T38_38_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK38)
    ∈ fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK38) :=
  repsFix_of_siftB2 rK38 ⟨38, by decide⟩ T38_38_2 (by decide)

theorem hinj38_38_2 : Function.Injective
    (fun i => ((T38_38_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK38)) :=
  repsInj_of_reduceAux2 rK38 T38_38_2 (by decide)

theorem hcardT38_38_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK38)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK38 ⟨38, by decide⟩ R38_2 hpxR38_2 hcardq38_2 (by decide)).symm

/-- **Cell (38, 38) twin (q=2).** -/
theorem cell38_38_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK38) e = true)
    (h : ↥(reps (⟨38, by decide⟩ : Fin 148))) :
    species (reps (⟨38, by decide⟩ : Fin 148)) h (basisElt (reps rK38) (charOfVec2 rK38 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK38 e (h : Coordinate 2) T38_38_2 i :=
  species_entry_eq_sum rK38 ⟨38, by decide⟩ e heK h T38_38_2 hfix38_38_2 hinj38_38_2 hcardT38_38_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨38, by decide⟩) (reps rK38) (T38_38_2 i) (hfix38_38_2 i) h)

end Q2

end LeanDring.P5Presentation
