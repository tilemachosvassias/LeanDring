/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, A-block data (rK = 43): certified per-cell species-entry instantiations, both twins.

Emit-embed-decide loop for order-25 A-block class `rK = 43` (`|G/K| = 125`).
All nonzero `H`-columns (`|gH| ≤ 2`, `t⁻¹Ht ⊆ K`).  Full 125-coset transversal
`R43` and each `H`-fixed sub-transversal `T43_rH` embedded as kernel data and
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

def rK43 : Fin 148 := ⟨43, by decide⟩

def R43list : List Coordinates := [(0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (1,0,1,4,0), (1,0,1,0,0), (1,0,1,1,0), (1,0,1,2,0), (1,0,1,3,0), (1,0,2,4,0), (1,0,2,0,0), (1,0,2,1,0), (1,0,2,2,0), (1,0,2,3,0), (1,0,3,4,0), (1,0,3,0,0), (1,0,3,1,0), (1,0,3,2,0), (1,0,3,3,0), (1,0,4,4,0), (1,0,4,0,0), (1,0,4,1,0), (1,0,4,2,0), (1,0,4,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (2,0,1,4,0), (2,0,1,0,0), (2,0,1,1,0), (2,0,1,2,0), (2,0,1,3,0), (2,0,2,4,0), (2,0,2,0,0), (2,0,2,1,0), (2,0,2,2,0), (2,0,2,3,0), (2,0,3,4,0), (2,0,3,0,0), (2,0,3,1,0), (2,0,3,2,0), (2,0,3,3,0), (2,0,4,4,0), (2,0,4,0,0), (2,0,4,1,0), (2,0,4,2,0), (2,0,4,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (3,0,1,4,0), (3,0,1,0,0), (3,0,1,1,0), (3,0,1,2,0), (3,0,1,3,0), (3,0,2,4,0), (3,0,2,0,0), (3,0,2,1,0), (3,0,2,2,0), (3,0,2,3,0), (3,0,3,4,0), (3,0,3,0,0), (3,0,3,1,0), (3,0,3,2,0), (3,0,3,3,0), (3,0,4,4,0), (3,0,4,0,0), (3,0,4,1,0), (3,0,4,2,0), (3,0,4,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (4,0,1,4,0), (4,0,1,0,0), (4,0,1,1,0), (4,0,1,2,0), (4,0,1,3,0), (4,0,2,4,0), (4,0,2,0,0), (4,0,2,1,0), (4,0,2,2,0), (4,0,2,3,0), (4,0,3,4,0), (4,0,3,0,0), (4,0,3,1,0), (4,0,3,2,0), (4,0,3,3,0), (4,0,4,4,0), (4,0,4,0,0), (4,0,4,1,0), (4,0,4,2,0), (4,0,4,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0)]
def R43 : Fin 125 → Coordinate 1 := fun i => R43list.getD i.val (0,0,0,0,0)

theorem hpxR43 : Function.Injective (fun i => reduceAux 1 (basisAt rK43) (R43 i)) := by decide
theorem hcardq43 : Nat.card (Coordinate 1 ⧸ reps rK43) = 125 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (43, 0): |T| = 125 -/

def T43_0list : List Coordinates := [(0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (1,0,1,4,0), (1,0,1,0,0), (1,0,1,1,0), (1,0,1,2,0), (1,0,1,3,0), (1,0,2,4,0), (1,0,2,0,0), (1,0,2,1,0), (1,0,2,2,0), (1,0,2,3,0), (1,0,3,4,0), (1,0,3,0,0), (1,0,3,1,0), (1,0,3,2,0), (1,0,3,3,0), (1,0,4,4,0), (1,0,4,0,0), (1,0,4,1,0), (1,0,4,2,0), (1,0,4,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (2,0,1,4,0), (2,0,1,0,0), (2,0,1,1,0), (2,0,1,2,0), (2,0,1,3,0), (2,0,2,4,0), (2,0,2,0,0), (2,0,2,1,0), (2,0,2,2,0), (2,0,2,3,0), (2,0,3,4,0), (2,0,3,0,0), (2,0,3,1,0), (2,0,3,2,0), (2,0,3,3,0), (2,0,4,4,0), (2,0,4,0,0), (2,0,4,1,0), (2,0,4,2,0), (2,0,4,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (3,0,1,4,0), (3,0,1,0,0), (3,0,1,1,0), (3,0,1,2,0), (3,0,1,3,0), (3,0,2,4,0), (3,0,2,0,0), (3,0,2,1,0), (3,0,2,2,0), (3,0,2,3,0), (3,0,3,4,0), (3,0,3,0,0), (3,0,3,1,0), (3,0,3,2,0), (3,0,3,3,0), (3,0,4,4,0), (3,0,4,0,0), (3,0,4,1,0), (3,0,4,2,0), (3,0,4,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (4,0,1,4,0), (4,0,1,0,0), (4,0,1,1,0), (4,0,1,2,0), (4,0,1,3,0), (4,0,2,4,0), (4,0,2,0,0), (4,0,2,1,0), (4,0,2,2,0), (4,0,2,3,0), (4,0,3,4,0), (4,0,3,0,0), (4,0,3,1,0), (4,0,3,2,0), (4,0,3,3,0), (4,0,4,4,0), (4,0,4,0,0), (4,0,4,1,0), (4,0,4,2,0), (4,0,4,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0)]
def T43_0 : Fin 125 → Coordinate 1 := fun i => T43_0list.getD i.val (0,0,0,0,0)

theorem hfix43_0 : ∀ i, ((T43_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK43)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43) :=
  repsFix_of_siftB rK43 ⟨0, by decide⟩ T43_0 (by decide)

theorem hinj43_0 : Function.Injective
    (fun i => ((T43_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK43)) :=
  repsInj_of_reduceAux rK43 T43_0 (by decide)

theorem hcardT43_0 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK43 ⟨0, by decide⟩ R43 hpxR43 hcardq43 (by decide)).symm

/-- **Cell (43, 0).** -/
theorem cell43_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK43) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK43) (charOfVec rK43 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK43 e (h : Coordinate 1) T43_0 i :=
  species_entry_eq_sum rK43 ⟨0, by decide⟩ e heK h T43_0 hfix43_0 hinj43_0 hcardT43_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK43) (T43_0 i) (hfix43_0 i) h)

/-! ## Cell (43, 12): |T| = 125 -/

def T43_12list : List Coordinates := [(0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (1,0,1,4,0), (1,0,1,0,0), (1,0,1,1,0), (1,0,1,2,0), (1,0,1,3,0), (1,0,2,4,0), (1,0,2,0,0), (1,0,2,1,0), (1,0,2,2,0), (1,0,2,3,0), (1,0,3,4,0), (1,0,3,0,0), (1,0,3,1,0), (1,0,3,2,0), (1,0,3,3,0), (1,0,4,4,0), (1,0,4,0,0), (1,0,4,1,0), (1,0,4,2,0), (1,0,4,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (2,0,1,4,0), (2,0,1,0,0), (2,0,1,1,0), (2,0,1,2,0), (2,0,1,3,0), (2,0,2,4,0), (2,0,2,0,0), (2,0,2,1,0), (2,0,2,2,0), (2,0,2,3,0), (2,0,3,4,0), (2,0,3,0,0), (2,0,3,1,0), (2,0,3,2,0), (2,0,3,3,0), (2,0,4,4,0), (2,0,4,0,0), (2,0,4,1,0), (2,0,4,2,0), (2,0,4,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (3,0,1,4,0), (3,0,1,0,0), (3,0,1,1,0), (3,0,1,2,0), (3,0,1,3,0), (3,0,2,4,0), (3,0,2,0,0), (3,0,2,1,0), (3,0,2,2,0), (3,0,2,3,0), (3,0,3,4,0), (3,0,3,0,0), (3,0,3,1,0), (3,0,3,2,0), (3,0,3,3,0), (3,0,4,4,0), (3,0,4,0,0), (3,0,4,1,0), (3,0,4,2,0), (3,0,4,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (4,0,1,4,0), (4,0,1,0,0), (4,0,1,1,0), (4,0,1,2,0), (4,0,1,3,0), (4,0,2,4,0), (4,0,2,0,0), (4,0,2,1,0), (4,0,2,2,0), (4,0,2,3,0), (4,0,3,4,0), (4,0,3,0,0), (4,0,3,1,0), (4,0,3,2,0), (4,0,3,3,0), (4,0,4,4,0), (4,0,4,0,0), (4,0,4,1,0), (4,0,4,2,0), (4,0,4,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0)]
def T43_12 : Fin 125 → Coordinate 1 := fun i => T43_12list.getD i.val (0,0,0,0,0)

theorem hfix43_12 : ∀ i, ((T43_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK43)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43) :=
  repsFix_of_siftB rK43 ⟨12, by decide⟩ T43_12 (by decide)

theorem hinj43_12 : Function.Injective
    (fun i => ((T43_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK43)) :=
  repsInj_of_reduceAux rK43 T43_12 (by decide)

theorem hcardT43_12 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK43 ⟨12, by decide⟩ R43 hpxR43 hcardq43 (by decide)).symm

/-- **Cell (43, 12).** -/
theorem cell43_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK43) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK43) (charOfVec rK43 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK43 e (h : Coordinate 1) T43_12 i :=
  species_entry_eq_sum rK43 ⟨12, by decide⟩ e heK h T43_12 hfix43_12 hinj43_12 hcardT43_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK43) (T43_12 i) (hfix43_12 i) h)

/-! ## Cell (43, 43): |T| = 25 -/

def T43_43list : List Coordinates := [(0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0)]
def T43_43 : Fin 25 → Coordinate 1 := fun i => T43_43list.getD i.val (0,0,0,0,0)

theorem hfix43_43 : ∀ i, ((T43_43 i : Coordinate 1) : Coordinate 1 ⧸ reps rK43)
    ∈ fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43) :=
  repsFix_of_siftB rK43 ⟨43, by decide⟩ T43_43 (by decide)

theorem hinj43_43 : Function.Injective
    (fun i => ((T43_43 i : Coordinate 1) : Coordinate 1 ⧸ reps rK43)) :=
  repsInj_of_reduceAux rK43 T43_43 (by decide)

theorem hcardT43_43 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK43 ⟨43, by decide⟩ R43 hpxR43 hcardq43 (by decide)).symm

/-- **Cell (43, 43).** -/
theorem cell43_43 (e : List (ZMod 25)) (heK : charOK (basisAt rK43) e = true)
    (h : ↥(reps (⟨43, by decide⟩ : Fin 148))) :
    species (reps (⟨43, by decide⟩ : Fin 148)) h (basisElt (reps rK43) (charOfVec rK43 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK43 e (h : Coordinate 1) T43_43 i :=
  species_entry_eq_sum rK43 ⟨43, by decide⟩ e heK h T43_43 hfix43_43 hinj43_43 hcardT43_43
    (fun i => conj_mem_of_fixedPoints (reps ⟨43, by decide⟩) (reps rK43) (T43_43 i) (hfix43_43 i) h)

namespace Q2

def R43_2 : Fin 125 → Coordinate 2 := fun i => R43list.getD i.val (0,0,0,0,0)
theorem hpxR43_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK43) (R43_2 i)) := by decide
theorem hcardq43_2 : Nat.card (Coordinate 2 ⧸ reps rK43) = 125 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (43, 0) twin -/

def T43_0_2 : Fin 125 → Coordinate 2 := fun i => T43_0list.getD i.val (0,0,0,0,0)

theorem hfix43_0_2 : ∀ i, ((T43_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK43)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK43) :=
  repsFix_of_siftB2 rK43 ⟨0, by decide⟩ T43_0_2 (by decide)

theorem hinj43_0_2 : Function.Injective
    (fun i => ((T43_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK43)) :=
  repsInj_of_reduceAux2 rK43 T43_0_2 (by decide)

theorem hcardT43_0_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK43)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK43 ⟨0, by decide⟩ R43_2 hpxR43_2 hcardq43_2 (by decide)).symm

/-- **Cell (43, 0) twin (q=2).** -/
theorem cell43_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK43) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK43) (charOfVec2 rK43 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK43 e (h : Coordinate 2) T43_0_2 i :=
  species_entry_eq_sum rK43 ⟨0, by decide⟩ e heK h T43_0_2 hfix43_0_2 hinj43_0_2 hcardT43_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK43) (T43_0_2 i) (hfix43_0_2 i) h)

/-! ### Cell (43, 12) twin -/

def T43_12_2 : Fin 125 → Coordinate 2 := fun i => T43_12list.getD i.val (0,0,0,0,0)

theorem hfix43_12_2 : ∀ i, ((T43_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK43)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK43) :=
  repsFix_of_siftB2 rK43 ⟨12, by decide⟩ T43_12_2 (by decide)

theorem hinj43_12_2 : Function.Injective
    (fun i => ((T43_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK43)) :=
  repsInj_of_reduceAux2 rK43 T43_12_2 (by decide)

theorem hcardT43_12_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK43)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK43 ⟨12, by decide⟩ R43_2 hpxR43_2 hcardq43_2 (by decide)).symm

/-- **Cell (43, 12) twin (q=2).** -/
theorem cell43_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK43) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK43) (charOfVec2 rK43 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK43 e (h : Coordinate 2) T43_12_2 i :=
  species_entry_eq_sum rK43 ⟨12, by decide⟩ e heK h T43_12_2 hfix43_12_2 hinj43_12_2 hcardT43_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK43) (T43_12_2 i) (hfix43_12_2 i) h)

/-! ### Cell (43, 43) twin -/

def T43_43_2 : Fin 25 → Coordinate 2 := fun i => T43_43list.getD i.val (0,0,0,0,0)

theorem hfix43_43_2 : ∀ i, ((T43_43_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK43)
    ∈ fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK43) :=
  repsFix_of_siftB2 rK43 ⟨43, by decide⟩ T43_43_2 (by decide)

theorem hinj43_43_2 : Function.Injective
    (fun i => ((T43_43_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK43)) :=
  repsInj_of_reduceAux2 rK43 T43_43_2 (by decide)

theorem hcardT43_43_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK43)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK43 ⟨43, by decide⟩ R43_2 hpxR43_2 hcardq43_2 (by decide)).symm

/-- **Cell (43, 43) twin (q=2).** -/
theorem cell43_43_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK43) e = true)
    (h : ↥(reps (⟨43, by decide⟩ : Fin 148))) :
    species (reps (⟨43, by decide⟩ : Fin 148)) h (basisElt (reps rK43) (charOfVec2 rK43 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK43 e (h : Coordinate 2) T43_43_2 i :=
  species_entry_eq_sum rK43 ⟨43, by decide⟩ e heK h T43_43_2 hfix43_43_2 hinj43_43_2 hcardT43_43_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨43, by decide⟩) (reps rK43) (T43_43_2 i) (hfix43_43_2 i) h)

end Q2

end LeanDring.P5Presentation
