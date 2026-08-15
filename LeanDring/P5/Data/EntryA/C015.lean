/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, A-block data (rK = 27): certified per-cell species-entry instantiations, both twins.

Emit-embed-decide loop for order-25 A-block class `rK = 27` (`|G/K| = 125`).
All nonzero `H`-columns (`|gH| ≤ 2`, `t⁻¹Ht ⊆ K`).  Full 125-coset transversal
`R27` and each `H`-fixed sub-transversal `T27_rH` embedded as kernel data and
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

def rK27 : Fin 148 := ⟨27, by decide⟩

def R27list : List Coordinates := [(0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,0,0,4,0), (1,1,0,0,0), (1,1,0,1,0), (1,1,0,2,0), (1,1,0,3,0), (1,1,0,4,0), (1,2,0,0,0), (1,2,0,1,0), (1,2,0,2,0), (1,2,0,3,0), (1,2,0,4,0), (1,3,0,0,0), (1,3,0,1,0), (1,3,0,2,0), (1,3,0,3,0), (1,3,0,4,0), (1,4,0,0,0), (1,4,0,1,0), (1,4,0,2,0), (1,4,0,3,0), (1,4,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,0,0,4,0), (2,1,0,0,0), (2,1,0,1,0), (2,1,0,2,0), (2,1,0,3,0), (2,1,0,4,0), (2,2,0,0,0), (2,2,0,1,0), (2,2,0,2,0), (2,2,0,3,0), (2,2,0,4,0), (2,3,0,0,0), (2,3,0,1,0), (2,3,0,2,0), (2,3,0,3,0), (2,3,0,4,0), (2,4,0,0,0), (2,4,0,1,0), (2,4,0,2,0), (2,4,0,3,0), (2,4,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,0,0,4,0), (3,1,0,0,0), (3,1,0,1,0), (3,1,0,2,0), (3,1,0,3,0), (3,1,0,4,0), (3,2,0,0,0), (3,2,0,1,0), (3,2,0,2,0), (3,2,0,3,0), (3,2,0,4,0), (3,3,0,0,0), (3,3,0,1,0), (3,3,0,2,0), (3,3,0,3,0), (3,3,0,4,0), (3,4,0,0,0), (3,4,0,1,0), (3,4,0,2,0), (3,4,0,3,0), (3,4,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,0,0,4,0), (4,1,0,0,0), (4,1,0,1,0), (4,1,0,2,0), (4,1,0,3,0), (4,1,0,4,0), (4,2,0,0,0), (4,2,0,1,0), (4,2,0,2,0), (4,2,0,3,0), (4,2,0,4,0), (4,3,0,0,0), (4,3,0,1,0), (4,3,0,2,0), (4,3,0,3,0), (4,3,0,4,0), (4,4,0,0,0), (4,4,0,1,0), (4,4,0,2,0), (4,4,0,3,0), (4,4,0,4,0)]
def R27 : Fin 125 → Coordinate 1 := fun i => R27list.getD i.val (0,0,0,0,0)

theorem hpxR27 : Function.Injective (fun i => reduceAux 1 (basisAt rK27) (R27 i)) := by decide
theorem hcardq27 : Nat.card (Coordinate 1 ⧸ reps rK27) = 125 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (27, 0): |T| = 125 -/

def T27_0list : List Coordinates := [(0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,0,0,4,0), (1,1,0,0,0), (1,1,0,1,0), (1,1,0,2,0), (1,1,0,3,0), (1,1,0,4,0), (1,2,0,0,0), (1,2,0,1,0), (1,2,0,2,0), (1,2,0,3,0), (1,2,0,4,0), (1,3,0,0,0), (1,3,0,1,0), (1,3,0,2,0), (1,3,0,3,0), (1,3,0,4,0), (1,4,0,0,0), (1,4,0,1,0), (1,4,0,2,0), (1,4,0,3,0), (1,4,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,0,0,4,0), (2,1,0,0,0), (2,1,0,1,0), (2,1,0,2,0), (2,1,0,3,0), (2,1,0,4,0), (2,2,0,0,0), (2,2,0,1,0), (2,2,0,2,0), (2,2,0,3,0), (2,2,0,4,0), (2,3,0,0,0), (2,3,0,1,0), (2,3,0,2,0), (2,3,0,3,0), (2,3,0,4,0), (2,4,0,0,0), (2,4,0,1,0), (2,4,0,2,0), (2,4,0,3,0), (2,4,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,0,0,4,0), (3,1,0,0,0), (3,1,0,1,0), (3,1,0,2,0), (3,1,0,3,0), (3,1,0,4,0), (3,2,0,0,0), (3,2,0,1,0), (3,2,0,2,0), (3,2,0,3,0), (3,2,0,4,0), (3,3,0,0,0), (3,3,0,1,0), (3,3,0,2,0), (3,3,0,3,0), (3,3,0,4,0), (3,4,0,0,0), (3,4,0,1,0), (3,4,0,2,0), (3,4,0,3,0), (3,4,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,0,0,4,0), (4,1,0,0,0), (4,1,0,1,0), (4,1,0,2,0), (4,1,0,3,0), (4,1,0,4,0), (4,2,0,0,0), (4,2,0,1,0), (4,2,0,2,0), (4,2,0,3,0), (4,2,0,4,0), (4,3,0,0,0), (4,3,0,1,0), (4,3,0,2,0), (4,3,0,3,0), (4,3,0,4,0), (4,4,0,0,0), (4,4,0,1,0), (4,4,0,2,0), (4,4,0,3,0), (4,4,0,4,0)]
def T27_0 : Fin 125 → Coordinate 1 := fun i => T27_0list.getD i.val (0,0,0,0,0)

theorem hfix27_0 : ∀ i, ((T27_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK27)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27) :=
  repsFix_of_siftB rK27 ⟨0, by decide⟩ T27_0 (by decide)

theorem hinj27_0 : Function.Injective
    (fun i => ((T27_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK27)) :=
  repsInj_of_reduceAux rK27 T27_0 (by decide)

theorem hcardT27_0 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK27 ⟨0, by decide⟩ R27 hpxR27 hcardq27 (by decide)).symm

/-- **Cell (27, 0).** -/
theorem cell27_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK27) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK27) (charOfVec rK27 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK27 e (h : Coordinate 1) T27_0 i :=
  species_entry_eq_sum rK27 ⟨0, by decide⟩ e heK h T27_0 hfix27_0 hinj27_0 hcardT27_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK27) (T27_0 i) (hfix27_0 i) h)

/-! ## Cell (27, 9): |T| = 125 -/

def T27_9list : List Coordinates := [(0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,0,0,4,0), (1,1,0,0,0), (1,1,0,1,0), (1,1,0,2,0), (1,1,0,3,0), (1,1,0,4,0), (1,2,0,0,0), (1,2,0,1,0), (1,2,0,2,0), (1,2,0,3,0), (1,2,0,4,0), (1,3,0,0,0), (1,3,0,1,0), (1,3,0,2,0), (1,3,0,3,0), (1,3,0,4,0), (1,4,0,0,0), (1,4,0,1,0), (1,4,0,2,0), (1,4,0,3,0), (1,4,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,0,0,4,0), (2,1,0,0,0), (2,1,0,1,0), (2,1,0,2,0), (2,1,0,3,0), (2,1,0,4,0), (2,2,0,0,0), (2,2,0,1,0), (2,2,0,2,0), (2,2,0,3,0), (2,2,0,4,0), (2,3,0,0,0), (2,3,0,1,0), (2,3,0,2,0), (2,3,0,3,0), (2,3,0,4,0), (2,4,0,0,0), (2,4,0,1,0), (2,4,0,2,0), (2,4,0,3,0), (2,4,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,0,0,4,0), (3,1,0,0,0), (3,1,0,1,0), (3,1,0,2,0), (3,1,0,3,0), (3,1,0,4,0), (3,2,0,0,0), (3,2,0,1,0), (3,2,0,2,0), (3,2,0,3,0), (3,2,0,4,0), (3,3,0,0,0), (3,3,0,1,0), (3,3,0,2,0), (3,3,0,3,0), (3,3,0,4,0), (3,4,0,0,0), (3,4,0,1,0), (3,4,0,2,0), (3,4,0,3,0), (3,4,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,0,0,4,0), (4,1,0,0,0), (4,1,0,1,0), (4,1,0,2,0), (4,1,0,3,0), (4,1,0,4,0), (4,2,0,0,0), (4,2,0,1,0), (4,2,0,2,0), (4,2,0,3,0), (4,2,0,4,0), (4,3,0,0,0), (4,3,0,1,0), (4,3,0,2,0), (4,3,0,3,0), (4,3,0,4,0), (4,4,0,0,0), (4,4,0,1,0), (4,4,0,2,0), (4,4,0,3,0), (4,4,0,4,0)]
def T27_9 : Fin 125 → Coordinate 1 := fun i => T27_9list.getD i.val (0,0,0,0,0)

theorem hfix27_9 : ∀ i, ((T27_9 i : Coordinate 1) : Coordinate 1 ⧸ reps rK27)
    ∈ fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27) :=
  repsFix_of_siftB rK27 ⟨9, by decide⟩ T27_9 (by decide)

theorem hinj27_9 : Function.Injective
    (fun i => ((T27_9 i : Coordinate 1) : Coordinate 1 ⧸ reps rK27)) :=
  repsInj_of_reduceAux rK27 T27_9 (by decide)

theorem hcardT27_9 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK27 ⟨9, by decide⟩ R27 hpxR27 hcardq27 (by decide)).symm

/-- **Cell (27, 9).** -/
theorem cell27_9 (e : List (ZMod 25)) (heK : charOK (basisAt rK27) e = true)
    (h : ↥(reps (⟨9, by decide⟩ : Fin 148))) :
    species (reps (⟨9, by decide⟩ : Fin 148)) h (basisElt (reps rK27) (charOfVec rK27 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK27 e (h : Coordinate 1) T27_9 i :=
  species_entry_eq_sum rK27 ⟨9, by decide⟩ e heK h T27_9 hfix27_9 hinj27_9 hcardT27_9
    (fun i => conj_mem_of_fixedPoints (reps ⟨9, by decide⟩) (reps rK27) (T27_9 i) (hfix27_9 i) h)

/-! ## Cell (27, 12): |T| = 125 -/

def T27_12list : List Coordinates := [(0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,0,0,4,0), (1,1,0,0,0), (1,1,0,1,0), (1,1,0,2,0), (1,1,0,3,0), (1,1,0,4,0), (1,2,0,0,0), (1,2,0,1,0), (1,2,0,2,0), (1,2,0,3,0), (1,2,0,4,0), (1,3,0,0,0), (1,3,0,1,0), (1,3,0,2,0), (1,3,0,3,0), (1,3,0,4,0), (1,4,0,0,0), (1,4,0,1,0), (1,4,0,2,0), (1,4,0,3,0), (1,4,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,0,0,4,0), (2,1,0,0,0), (2,1,0,1,0), (2,1,0,2,0), (2,1,0,3,0), (2,1,0,4,0), (2,2,0,0,0), (2,2,0,1,0), (2,2,0,2,0), (2,2,0,3,0), (2,2,0,4,0), (2,3,0,0,0), (2,3,0,1,0), (2,3,0,2,0), (2,3,0,3,0), (2,3,0,4,0), (2,4,0,0,0), (2,4,0,1,0), (2,4,0,2,0), (2,4,0,3,0), (2,4,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,0,0,4,0), (3,1,0,0,0), (3,1,0,1,0), (3,1,0,2,0), (3,1,0,3,0), (3,1,0,4,0), (3,2,0,0,0), (3,2,0,1,0), (3,2,0,2,0), (3,2,0,3,0), (3,2,0,4,0), (3,3,0,0,0), (3,3,0,1,0), (3,3,0,2,0), (3,3,0,3,0), (3,3,0,4,0), (3,4,0,0,0), (3,4,0,1,0), (3,4,0,2,0), (3,4,0,3,0), (3,4,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,0,0,4,0), (4,1,0,0,0), (4,1,0,1,0), (4,1,0,2,0), (4,1,0,3,0), (4,1,0,4,0), (4,2,0,0,0), (4,2,0,1,0), (4,2,0,2,0), (4,2,0,3,0), (4,2,0,4,0), (4,3,0,0,0), (4,3,0,1,0), (4,3,0,2,0), (4,3,0,3,0), (4,3,0,4,0), (4,4,0,0,0), (4,4,0,1,0), (4,4,0,2,0), (4,4,0,3,0), (4,4,0,4,0)]
def T27_12 : Fin 125 → Coordinate 1 := fun i => T27_12list.getD i.val (0,0,0,0,0)

theorem hfix27_12 : ∀ i, ((T27_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK27)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27) :=
  repsFix_of_siftB rK27 ⟨12, by decide⟩ T27_12 (by decide)

theorem hinj27_12 : Function.Injective
    (fun i => ((T27_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK27)) :=
  repsInj_of_reduceAux rK27 T27_12 (by decide)

theorem hcardT27_12 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK27 ⟨12, by decide⟩ R27 hpxR27 hcardq27 (by decide)).symm

/-- **Cell (27, 12).** -/
theorem cell27_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK27) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK27) (charOfVec rK27 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK27 e (h : Coordinate 1) T27_12 i :=
  species_entry_eq_sum rK27 ⟨12, by decide⟩ e heK h T27_12 hfix27_12 hinj27_12 hcardT27_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK27) (T27_12 i) (hfix27_12 i) h)

/-! ## Cell (27, 27): |T| = 125 -/

def T27_27list : List Coordinates := [(0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (1,0,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,0,0,4,0), (1,1,0,0,0), (1,1,0,1,0), (1,1,0,2,0), (1,1,0,3,0), (1,1,0,4,0), (1,2,0,0,0), (1,2,0,1,0), (1,2,0,2,0), (1,2,0,3,0), (1,2,0,4,0), (1,3,0,0,0), (1,3,0,1,0), (1,3,0,2,0), (1,3,0,3,0), (1,3,0,4,0), (1,4,0,0,0), (1,4,0,1,0), (1,4,0,2,0), (1,4,0,3,0), (1,4,0,4,0), (2,0,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,0,0,4,0), (2,1,0,0,0), (2,1,0,1,0), (2,1,0,2,0), (2,1,0,3,0), (2,1,0,4,0), (2,2,0,0,0), (2,2,0,1,0), (2,2,0,2,0), (2,2,0,3,0), (2,2,0,4,0), (2,3,0,0,0), (2,3,0,1,0), (2,3,0,2,0), (2,3,0,3,0), (2,3,0,4,0), (2,4,0,0,0), (2,4,0,1,0), (2,4,0,2,0), (2,4,0,3,0), (2,4,0,4,0), (3,0,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,0,0,4,0), (3,1,0,0,0), (3,1,0,1,0), (3,1,0,2,0), (3,1,0,3,0), (3,1,0,4,0), (3,2,0,0,0), (3,2,0,1,0), (3,2,0,2,0), (3,2,0,3,0), (3,2,0,4,0), (3,3,0,0,0), (3,3,0,1,0), (3,3,0,2,0), (3,3,0,3,0), (3,3,0,4,0), (3,4,0,0,0), (3,4,0,1,0), (3,4,0,2,0), (3,4,0,3,0), (3,4,0,4,0), (4,0,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,0,0,4,0), (4,1,0,0,0), (4,1,0,1,0), (4,1,0,2,0), (4,1,0,3,0), (4,1,0,4,0), (4,2,0,0,0), (4,2,0,1,0), (4,2,0,2,0), (4,2,0,3,0), (4,2,0,4,0), (4,3,0,0,0), (4,3,0,1,0), (4,3,0,2,0), (4,3,0,3,0), (4,3,0,4,0), (4,4,0,0,0), (4,4,0,1,0), (4,4,0,2,0), (4,4,0,3,0), (4,4,0,4,0)]
def T27_27 : Fin 125 → Coordinate 1 := fun i => T27_27list.getD i.val (0,0,0,0,0)

theorem hfix27_27 : ∀ i, ((T27_27 i : Coordinate 1) : Coordinate 1 ⧸ reps rK27)
    ∈ fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27) :=
  repsFix_of_siftB rK27 ⟨27, by decide⟩ T27_27 (by decide)

theorem hinj27_27 : Function.Injective
    (fun i => ((T27_27 i : Coordinate 1) : Coordinate 1 ⧸ reps rK27)) :=
  repsInj_of_reduceAux rK27 T27_27 (by decide)

theorem hcardT27_27 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK27 ⟨27, by decide⟩ R27 hpxR27 hcardq27 (by decide)).symm

/-- **Cell (27, 27).** -/
theorem cell27_27 (e : List (ZMod 25)) (heK : charOK (basisAt rK27) e = true)
    (h : ↥(reps (⟨27, by decide⟩ : Fin 148))) :
    species (reps (⟨27, by decide⟩ : Fin 148)) h (basisElt (reps rK27) (charOfVec rK27 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK27 e (h : Coordinate 1) T27_27 i :=
  species_entry_eq_sum rK27 ⟨27, by decide⟩ e heK h T27_27 hfix27_27 hinj27_27 hcardT27_27
    (fun i => conj_mem_of_fixedPoints (reps ⟨27, by decide⟩) (reps rK27) (T27_27 i) (hfix27_27 i) h)

namespace Q2

def R27_2 : Fin 125 → Coordinate 2 := fun i => R27list.getD i.val (0,0,0,0,0)
theorem hpxR27_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK27) (R27_2 i)) := by decide
theorem hcardq27_2 : Nat.card (Coordinate 2 ⧸ reps rK27) = 125 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (27, 0) twin -/

def T27_0_2 : Fin 125 → Coordinate 2 := fun i => T27_0list.getD i.val (0,0,0,0,0)

theorem hfix27_0_2 : ∀ i, ((T27_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK27)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK27) :=
  repsFix_of_siftB2 rK27 ⟨0, by decide⟩ T27_0_2 (by decide)

theorem hinj27_0_2 : Function.Injective
    (fun i => ((T27_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK27)) :=
  repsInj_of_reduceAux2 rK27 T27_0_2 (by decide)

theorem hcardT27_0_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK27)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK27 ⟨0, by decide⟩ R27_2 hpxR27_2 hcardq27_2 (by decide)).symm

/-- **Cell (27, 0) twin (q=2).** -/
theorem cell27_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK27) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK27) (charOfVec2 rK27 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK27 e (h : Coordinate 2) T27_0_2 i :=
  species_entry_eq_sum rK27 ⟨0, by decide⟩ e heK h T27_0_2 hfix27_0_2 hinj27_0_2 hcardT27_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK27) (T27_0_2 i) (hfix27_0_2 i) h)

/-! ### Cell (27, 9) twin -/

def T27_9_2 : Fin 125 → Coordinate 2 := fun i => T27_9list.getD i.val (0,0,0,0,0)

theorem hfix27_9_2 : ∀ i, ((T27_9_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK27)
    ∈ fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK27) :=
  repsFix_of_siftB2 rK27 ⟨9, by decide⟩ T27_9_2 (by decide)

theorem hinj27_9_2 : Function.Injective
    (fun i => ((T27_9_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK27)) :=
  repsInj_of_reduceAux2 rK27 T27_9_2 (by decide)

theorem hcardT27_9_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK27)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK27 ⟨9, by decide⟩ R27_2 hpxR27_2 hcardq27_2 (by decide)).symm

/-- **Cell (27, 9) twin (q=2).** -/
theorem cell27_9_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK27) e = true)
    (h : ↥(reps (⟨9, by decide⟩ : Fin 148))) :
    species (reps (⟨9, by decide⟩ : Fin 148)) h (basisElt (reps rK27) (charOfVec2 rK27 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK27 e (h : Coordinate 2) T27_9_2 i :=
  species_entry_eq_sum rK27 ⟨9, by decide⟩ e heK h T27_9_2 hfix27_9_2 hinj27_9_2 hcardT27_9_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨9, by decide⟩) (reps rK27) (T27_9_2 i) (hfix27_9_2 i) h)

/-! ### Cell (27, 12) twin -/

def T27_12_2 : Fin 125 → Coordinate 2 := fun i => T27_12list.getD i.val (0,0,0,0,0)

theorem hfix27_12_2 : ∀ i, ((T27_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK27)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK27) :=
  repsFix_of_siftB2 rK27 ⟨12, by decide⟩ T27_12_2 (by decide)

theorem hinj27_12_2 : Function.Injective
    (fun i => ((T27_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK27)) :=
  repsInj_of_reduceAux2 rK27 T27_12_2 (by decide)

theorem hcardT27_12_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK27)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK27 ⟨12, by decide⟩ R27_2 hpxR27_2 hcardq27_2 (by decide)).symm

/-- **Cell (27, 12) twin (q=2).** -/
theorem cell27_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK27) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK27) (charOfVec2 rK27 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK27 e (h : Coordinate 2) T27_12_2 i :=
  species_entry_eq_sum rK27 ⟨12, by decide⟩ e heK h T27_12_2 hfix27_12_2 hinj27_12_2 hcardT27_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK27) (T27_12_2 i) (hfix27_12_2 i) h)

/-! ### Cell (27, 27) twin -/

def T27_27_2 : Fin 125 → Coordinate 2 := fun i => T27_27list.getD i.val (0,0,0,0,0)

theorem hfix27_27_2 : ∀ i, ((T27_27_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK27)
    ∈ fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK27) :=
  repsFix_of_siftB2 rK27 ⟨27, by decide⟩ T27_27_2 (by decide)

theorem hinj27_27_2 : Function.Injective
    (fun i => ((T27_27_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK27)) :=
  repsInj_of_reduceAux2 rK27 T27_27_2 (by decide)

theorem hcardT27_27_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK27)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK27 ⟨27, by decide⟩ R27_2 hpxR27_2 hcardq27_2 (by decide)).symm

/-- **Cell (27, 27) twin (q=2).** -/
theorem cell27_27_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK27) e = true)
    (h : ↥(reps (⟨27, by decide⟩ : Fin 148))) :
    species (reps (⟨27, by decide⟩ : Fin 148)) h (basisElt (reps rK27) (charOfVec2 rK27 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK27 e (h : Coordinate 2) T27_27_2 i :=
  species_entry_eq_sum rK27 ⟨27, by decide⟩ e heK h T27_27_2 hfix27_27_2 hinj27_27_2 hcardT27_27_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨27, by decide⟩) (reps rK27) (T27_27_2 i) (hfix27_27_2 i) h)

end Q2

end LeanDring.P5Presentation
