/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, A-block data (rK = 53): certified per-cell species-entry instantiations, both twins.

Emit-embed-decide loop for order-25 A-block class `rK = 53` (`|G/K| = 125`).
All nonzero `H`-columns (`|gH| ≤ 2`, `t⁻¹Ht ⊆ K`).  Full 125-coset transversal
`R53` and each `H`-fixed sub-transversal `T53_rH` embedded as kernel data and
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

def rK53 : Fin 148 := ⟨53, by decide⟩

def R53list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (1,0,0,0,0), (1,0,1,0,0), (1,0,2,0,0), (1,0,3,0,0), (1,0,4,0,0), (1,1,0,0,0), (1,1,1,0,0), (1,1,2,0,0), (1,1,3,0,0), (1,1,4,0,0), (1,2,0,0,0), (1,2,1,0,0), (1,2,2,0,0), (1,2,3,0,0), (1,2,4,0,0), (1,3,0,0,0), (1,3,1,0,0), (1,3,2,0,0), (1,3,3,0,0), (1,3,4,0,0), (1,4,0,0,0), (1,4,1,0,0), (1,4,2,0,0), (1,4,3,0,0), (1,4,4,0,0), (2,0,0,0,0), (2,0,1,0,0), (2,0,2,0,0), (2,0,3,0,0), (2,0,4,0,0), (2,1,0,0,0), (2,1,1,0,0), (2,1,2,0,0), (2,1,3,0,0), (2,1,4,0,0), (2,2,0,0,0), (2,2,1,0,0), (2,2,2,0,0), (2,2,3,0,0), (2,2,4,0,0), (2,3,0,0,0), (2,3,1,0,0), (2,3,2,0,0), (2,3,3,0,0), (2,3,4,0,0), (2,4,0,0,0), (2,4,1,0,0), (2,4,2,0,0), (2,4,3,0,0), (2,4,4,0,0), (3,0,0,0,0), (3,0,1,0,0), (3,0,2,0,0), (3,0,3,0,0), (3,0,4,0,0), (3,1,0,0,0), (3,1,1,0,0), (3,1,2,0,0), (3,1,3,0,0), (3,1,4,0,0), (3,2,0,0,0), (3,2,1,0,0), (3,2,2,0,0), (3,2,3,0,0), (3,2,4,0,0), (3,3,0,0,0), (3,3,1,0,0), (3,3,2,0,0), (3,3,3,0,0), (3,3,4,0,0), (3,4,0,0,0), (3,4,1,0,0), (3,4,2,0,0), (3,4,3,0,0), (3,4,4,0,0), (4,0,0,0,0), (4,0,1,0,0), (4,0,2,0,0), (4,0,3,0,0), (4,0,4,0,0), (4,1,0,0,0), (4,1,1,0,0), (4,1,2,0,0), (4,1,3,0,0), (4,1,4,0,0), (4,2,0,0,0), (4,2,1,0,0), (4,2,2,0,0), (4,2,3,0,0), (4,2,4,0,0), (4,3,0,0,0), (4,3,1,0,0), (4,3,2,0,0), (4,3,3,0,0), (4,3,4,0,0), (4,4,0,0,0), (4,4,1,0,0), (4,4,2,0,0), (4,4,3,0,0), (4,4,4,0,0)]
def R53 : Fin 125 → Coordinate 1 := fun i => R53list.getD i.val (0,0,0,0,0)

theorem hpxR53 : Function.Injective (fun i => reduceAux 1 (basisAt rK53) (R53 i)) := by decide
theorem hcardq53 : Nat.card (Coordinate 1 ⧸ reps rK53) = 125 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (53, 0): |T| = 125 -/

def T53_0list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (1,0,0,0,0), (1,0,1,0,0), (1,0,2,0,0), (1,0,3,0,0), (1,0,4,0,0), (1,1,0,0,0), (1,1,1,0,0), (1,1,2,0,0), (1,1,3,0,0), (1,1,4,0,0), (1,2,0,0,0), (1,2,1,0,0), (1,2,2,0,0), (1,2,3,0,0), (1,2,4,0,0), (1,3,0,0,0), (1,3,1,0,0), (1,3,2,0,0), (1,3,3,0,0), (1,3,4,0,0), (1,4,0,0,0), (1,4,1,0,0), (1,4,2,0,0), (1,4,3,0,0), (1,4,4,0,0), (2,0,0,0,0), (2,0,1,0,0), (2,0,2,0,0), (2,0,3,0,0), (2,0,4,0,0), (2,1,0,0,0), (2,1,1,0,0), (2,1,2,0,0), (2,1,3,0,0), (2,1,4,0,0), (2,2,0,0,0), (2,2,1,0,0), (2,2,2,0,0), (2,2,3,0,0), (2,2,4,0,0), (2,3,0,0,0), (2,3,1,0,0), (2,3,2,0,0), (2,3,3,0,0), (2,3,4,0,0), (2,4,0,0,0), (2,4,1,0,0), (2,4,2,0,0), (2,4,3,0,0), (2,4,4,0,0), (3,0,0,0,0), (3,0,1,0,0), (3,0,2,0,0), (3,0,3,0,0), (3,0,4,0,0), (3,1,0,0,0), (3,1,1,0,0), (3,1,2,0,0), (3,1,3,0,0), (3,1,4,0,0), (3,2,0,0,0), (3,2,1,0,0), (3,2,2,0,0), (3,2,3,0,0), (3,2,4,0,0), (3,3,0,0,0), (3,3,1,0,0), (3,3,2,0,0), (3,3,3,0,0), (3,3,4,0,0), (3,4,0,0,0), (3,4,1,0,0), (3,4,2,0,0), (3,4,3,0,0), (3,4,4,0,0), (4,0,0,0,0), (4,0,1,0,0), (4,0,2,0,0), (4,0,3,0,0), (4,0,4,0,0), (4,1,0,0,0), (4,1,1,0,0), (4,1,2,0,0), (4,1,3,0,0), (4,1,4,0,0), (4,2,0,0,0), (4,2,1,0,0), (4,2,2,0,0), (4,2,3,0,0), (4,2,4,0,0), (4,3,0,0,0), (4,3,1,0,0), (4,3,2,0,0), (4,3,3,0,0), (4,3,4,0,0), (4,4,0,0,0), (4,4,1,0,0), (4,4,2,0,0), (4,4,3,0,0), (4,4,4,0,0)]
def T53_0 : Fin 125 → Coordinate 1 := fun i => T53_0list.getD i.val (0,0,0,0,0)

theorem hfix53_0 : ∀ i, ((T53_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK53)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53) :=
  repsFix_of_siftB rK53 ⟨0, by decide⟩ T53_0 (by decide)

theorem hinj53_0 : Function.Injective
    (fun i => ((T53_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK53)) :=
  repsInj_of_reduceAux rK53 T53_0 (by decide)

theorem hcardT53_0 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK53 ⟨0, by decide⟩ R53 hpxR53 hcardq53 (by decide)).symm

/-- **Cell (53, 0).** -/
theorem cell53_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK53) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK53) (charOfVec rK53 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK53 e (h : Coordinate 1) T53_0 i :=
  species_entry_eq_sum rK53 ⟨0, by decide⟩ e heK h T53_0 hfix53_0 hinj53_0 hcardT53_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK53) (T53_0 i) (hfix53_0 i) h)

/-! ## Cell (53, 10): |T| = 125 -/

def T53_10list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (1,0,0,0,0), (1,0,1,0,0), (1,0,2,0,0), (1,0,3,0,0), (1,0,4,0,0), (1,1,0,0,0), (1,1,1,0,0), (1,1,2,0,0), (1,1,3,0,0), (1,1,4,0,0), (1,2,0,0,0), (1,2,1,0,0), (1,2,2,0,0), (1,2,3,0,0), (1,2,4,0,0), (1,3,0,0,0), (1,3,1,0,0), (1,3,2,0,0), (1,3,3,0,0), (1,3,4,0,0), (1,4,0,0,0), (1,4,1,0,0), (1,4,2,0,0), (1,4,3,0,0), (1,4,4,0,0), (2,0,0,0,0), (2,0,1,0,0), (2,0,2,0,0), (2,0,3,0,0), (2,0,4,0,0), (2,1,0,0,0), (2,1,1,0,0), (2,1,2,0,0), (2,1,3,0,0), (2,1,4,0,0), (2,2,0,0,0), (2,2,1,0,0), (2,2,2,0,0), (2,2,3,0,0), (2,2,4,0,0), (2,3,0,0,0), (2,3,1,0,0), (2,3,2,0,0), (2,3,3,0,0), (2,3,4,0,0), (2,4,0,0,0), (2,4,1,0,0), (2,4,2,0,0), (2,4,3,0,0), (2,4,4,0,0), (3,0,0,0,0), (3,0,1,0,0), (3,0,2,0,0), (3,0,3,0,0), (3,0,4,0,0), (3,1,0,0,0), (3,1,1,0,0), (3,1,2,0,0), (3,1,3,0,0), (3,1,4,0,0), (3,2,0,0,0), (3,2,1,0,0), (3,2,2,0,0), (3,2,3,0,0), (3,2,4,0,0), (3,3,0,0,0), (3,3,1,0,0), (3,3,2,0,0), (3,3,3,0,0), (3,3,4,0,0), (3,4,0,0,0), (3,4,1,0,0), (3,4,2,0,0), (3,4,3,0,0), (3,4,4,0,0), (4,0,0,0,0), (4,0,1,0,0), (4,0,2,0,0), (4,0,3,0,0), (4,0,4,0,0), (4,1,0,0,0), (4,1,1,0,0), (4,1,2,0,0), (4,1,3,0,0), (4,1,4,0,0), (4,2,0,0,0), (4,2,1,0,0), (4,2,2,0,0), (4,2,3,0,0), (4,2,4,0,0), (4,3,0,0,0), (4,3,1,0,0), (4,3,2,0,0), (4,3,3,0,0), (4,3,4,0,0), (4,4,0,0,0), (4,4,1,0,0), (4,4,2,0,0), (4,4,3,0,0), (4,4,4,0,0)]
def T53_10 : Fin 125 → Coordinate 1 := fun i => T53_10list.getD i.val (0,0,0,0,0)

theorem hfix53_10 : ∀ i, ((T53_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK53)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53) :=
  repsFix_of_siftB rK53 ⟨10, by decide⟩ T53_10 (by decide)

theorem hinj53_10 : Function.Injective
    (fun i => ((T53_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK53)) :=
  repsInj_of_reduceAux rK53 T53_10 (by decide)

theorem hcardT53_10 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK53 ⟨10, by decide⟩ R53 hpxR53 hcardq53 (by decide)).symm

/-- **Cell (53, 10).** -/
theorem cell53_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK53) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK53) (charOfVec rK53 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK53 e (h : Coordinate 1) T53_10 i :=
  species_entry_eq_sum rK53 ⟨10, by decide⟩ e heK h T53_10 hfix53_10 hinj53_10 hcardT53_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK53) (T53_10 i) (hfix53_10 i) h)

/-! ## Cell (53, 12): |T| = 125 -/

def T53_12list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (1,0,0,0,0), (1,0,1,0,0), (1,0,2,0,0), (1,0,3,0,0), (1,0,4,0,0), (1,1,0,0,0), (1,1,1,0,0), (1,1,2,0,0), (1,1,3,0,0), (1,1,4,0,0), (1,2,0,0,0), (1,2,1,0,0), (1,2,2,0,0), (1,2,3,0,0), (1,2,4,0,0), (1,3,0,0,0), (1,3,1,0,0), (1,3,2,0,0), (1,3,3,0,0), (1,3,4,0,0), (1,4,0,0,0), (1,4,1,0,0), (1,4,2,0,0), (1,4,3,0,0), (1,4,4,0,0), (2,0,0,0,0), (2,0,1,0,0), (2,0,2,0,0), (2,0,3,0,0), (2,0,4,0,0), (2,1,0,0,0), (2,1,1,0,0), (2,1,2,0,0), (2,1,3,0,0), (2,1,4,0,0), (2,2,0,0,0), (2,2,1,0,0), (2,2,2,0,0), (2,2,3,0,0), (2,2,4,0,0), (2,3,0,0,0), (2,3,1,0,0), (2,3,2,0,0), (2,3,3,0,0), (2,3,4,0,0), (2,4,0,0,0), (2,4,1,0,0), (2,4,2,0,0), (2,4,3,0,0), (2,4,4,0,0), (3,0,0,0,0), (3,0,1,0,0), (3,0,2,0,0), (3,0,3,0,0), (3,0,4,0,0), (3,1,0,0,0), (3,1,1,0,0), (3,1,2,0,0), (3,1,3,0,0), (3,1,4,0,0), (3,2,0,0,0), (3,2,1,0,0), (3,2,2,0,0), (3,2,3,0,0), (3,2,4,0,0), (3,3,0,0,0), (3,3,1,0,0), (3,3,2,0,0), (3,3,3,0,0), (3,3,4,0,0), (3,4,0,0,0), (3,4,1,0,0), (3,4,2,0,0), (3,4,3,0,0), (3,4,4,0,0), (4,0,0,0,0), (4,0,1,0,0), (4,0,2,0,0), (4,0,3,0,0), (4,0,4,0,0), (4,1,0,0,0), (4,1,1,0,0), (4,1,2,0,0), (4,1,3,0,0), (4,1,4,0,0), (4,2,0,0,0), (4,2,1,0,0), (4,2,2,0,0), (4,2,3,0,0), (4,2,4,0,0), (4,3,0,0,0), (4,3,1,0,0), (4,3,2,0,0), (4,3,3,0,0), (4,3,4,0,0), (4,4,0,0,0), (4,4,1,0,0), (4,4,2,0,0), (4,4,3,0,0), (4,4,4,0,0)]
def T53_12 : Fin 125 → Coordinate 1 := fun i => T53_12list.getD i.val (0,0,0,0,0)

theorem hfix53_12 : ∀ i, ((T53_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK53)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53) :=
  repsFix_of_siftB rK53 ⟨12, by decide⟩ T53_12 (by decide)

theorem hinj53_12 : Function.Injective
    (fun i => ((T53_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK53)) :=
  repsInj_of_reduceAux rK53 T53_12 (by decide)

theorem hcardT53_12 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK53 ⟨12, by decide⟩ R53 hpxR53 hcardq53 (by decide)).symm

/-- **Cell (53, 12).** -/
theorem cell53_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK53) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK53) (charOfVec rK53 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK53 e (h : Coordinate 1) T53_12 i :=
  species_entry_eq_sum rK53 ⟨12, by decide⟩ e heK h T53_12 hfix53_12 hinj53_12 hcardT53_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK53) (T53_12 i) (hfix53_12 i) h)

/-! ## Cell (53, 53): |T| = 125 -/

def T53_53list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (1,0,0,0,0), (1,0,1,0,0), (1,0,2,0,0), (1,0,3,0,0), (1,0,4,0,0), (1,1,0,0,0), (1,1,1,0,0), (1,1,2,0,0), (1,1,3,0,0), (1,1,4,0,0), (1,2,0,0,0), (1,2,1,0,0), (1,2,2,0,0), (1,2,3,0,0), (1,2,4,0,0), (1,3,0,0,0), (1,3,1,0,0), (1,3,2,0,0), (1,3,3,0,0), (1,3,4,0,0), (1,4,0,0,0), (1,4,1,0,0), (1,4,2,0,0), (1,4,3,0,0), (1,4,4,0,0), (2,0,0,0,0), (2,0,1,0,0), (2,0,2,0,0), (2,0,3,0,0), (2,0,4,0,0), (2,1,0,0,0), (2,1,1,0,0), (2,1,2,0,0), (2,1,3,0,0), (2,1,4,0,0), (2,2,0,0,0), (2,2,1,0,0), (2,2,2,0,0), (2,2,3,0,0), (2,2,4,0,0), (2,3,0,0,0), (2,3,1,0,0), (2,3,2,0,0), (2,3,3,0,0), (2,3,4,0,0), (2,4,0,0,0), (2,4,1,0,0), (2,4,2,0,0), (2,4,3,0,0), (2,4,4,0,0), (3,0,0,0,0), (3,0,1,0,0), (3,0,2,0,0), (3,0,3,0,0), (3,0,4,0,0), (3,1,0,0,0), (3,1,1,0,0), (3,1,2,0,0), (3,1,3,0,0), (3,1,4,0,0), (3,2,0,0,0), (3,2,1,0,0), (3,2,2,0,0), (3,2,3,0,0), (3,2,4,0,0), (3,3,0,0,0), (3,3,1,0,0), (3,3,2,0,0), (3,3,3,0,0), (3,3,4,0,0), (3,4,0,0,0), (3,4,1,0,0), (3,4,2,0,0), (3,4,3,0,0), (3,4,4,0,0), (4,0,0,0,0), (4,0,1,0,0), (4,0,2,0,0), (4,0,3,0,0), (4,0,4,0,0), (4,1,0,0,0), (4,1,1,0,0), (4,1,2,0,0), (4,1,3,0,0), (4,1,4,0,0), (4,2,0,0,0), (4,2,1,0,0), (4,2,2,0,0), (4,2,3,0,0), (4,2,4,0,0), (4,3,0,0,0), (4,3,1,0,0), (4,3,2,0,0), (4,3,3,0,0), (4,3,4,0,0), (4,4,0,0,0), (4,4,1,0,0), (4,4,2,0,0), (4,4,3,0,0), (4,4,4,0,0)]
def T53_53 : Fin 125 → Coordinate 1 := fun i => T53_53list.getD i.val (0,0,0,0,0)

theorem hfix53_53 : ∀ i, ((T53_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK53)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53) :=
  repsFix_of_siftB rK53 ⟨53, by decide⟩ T53_53 (by decide)

theorem hinj53_53 : Function.Injective
    (fun i => ((T53_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK53)) :=
  repsInj_of_reduceAux rK53 T53_53 (by decide)

theorem hcardT53_53 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK53 ⟨53, by decide⟩ R53 hpxR53 hcardq53 (by decide)).symm

/-- **Cell (53, 53).** -/
theorem cell53_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK53) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK53) (charOfVec rK53 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK53 e (h : Coordinate 1) T53_53 i :=
  species_entry_eq_sum rK53 ⟨53, by decide⟩ e heK h T53_53 hfix53_53 hinj53_53 hcardT53_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK53) (T53_53 i) (hfix53_53 i) h)

namespace Q2

def R53_2 : Fin 125 → Coordinate 2 := fun i => R53list.getD i.val (0,0,0,0,0)
theorem hpxR53_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK53) (R53_2 i)) := by decide
theorem hcardq53_2 : Nat.card (Coordinate 2 ⧸ reps rK53) = 125 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (53, 0) twin -/

def T53_0_2 : Fin 125 → Coordinate 2 := fun i => T53_0list.getD i.val (0,0,0,0,0)

theorem hfix53_0_2 : ∀ i, ((T53_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK53)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK53) :=
  repsFix_of_siftB2 rK53 ⟨0, by decide⟩ T53_0_2 (by decide)

theorem hinj53_0_2 : Function.Injective
    (fun i => ((T53_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK53)) :=
  repsInj_of_reduceAux2 rK53 T53_0_2 (by decide)

theorem hcardT53_0_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK53)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK53 ⟨0, by decide⟩ R53_2 hpxR53_2 hcardq53_2 (by decide)).symm

/-- **Cell (53, 0) twin (q=2).** -/
theorem cell53_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK53) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK53) (charOfVec2 rK53 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK53 e (h : Coordinate 2) T53_0_2 i :=
  species_entry_eq_sum rK53 ⟨0, by decide⟩ e heK h T53_0_2 hfix53_0_2 hinj53_0_2 hcardT53_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK53) (T53_0_2 i) (hfix53_0_2 i) h)

/-! ### Cell (53, 10) twin -/

def T53_10_2 : Fin 125 → Coordinate 2 := fun i => T53_10list.getD i.val (0,0,0,0,0)

theorem hfix53_10_2 : ∀ i, ((T53_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK53)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK53) :=
  repsFix_of_siftB2 rK53 ⟨10, by decide⟩ T53_10_2 (by decide)

theorem hinj53_10_2 : Function.Injective
    (fun i => ((T53_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK53)) :=
  repsInj_of_reduceAux2 rK53 T53_10_2 (by decide)

theorem hcardT53_10_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK53)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK53 ⟨10, by decide⟩ R53_2 hpxR53_2 hcardq53_2 (by decide)).symm

/-- **Cell (53, 10) twin (q=2).** -/
theorem cell53_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK53) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK53) (charOfVec2 rK53 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK53 e (h : Coordinate 2) T53_10_2 i :=
  species_entry_eq_sum rK53 ⟨10, by decide⟩ e heK h T53_10_2 hfix53_10_2 hinj53_10_2 hcardT53_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK53) (T53_10_2 i) (hfix53_10_2 i) h)

/-! ### Cell (53, 12) twin -/

def T53_12_2 : Fin 125 → Coordinate 2 := fun i => T53_12list.getD i.val (0,0,0,0,0)

theorem hfix53_12_2 : ∀ i, ((T53_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK53)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK53) :=
  repsFix_of_siftB2 rK53 ⟨12, by decide⟩ T53_12_2 (by decide)

theorem hinj53_12_2 : Function.Injective
    (fun i => ((T53_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK53)) :=
  repsInj_of_reduceAux2 rK53 T53_12_2 (by decide)

theorem hcardT53_12_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK53)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK53 ⟨12, by decide⟩ R53_2 hpxR53_2 hcardq53_2 (by decide)).symm

/-- **Cell (53, 12) twin (q=2).** -/
theorem cell53_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK53) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK53) (charOfVec2 rK53 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK53 e (h : Coordinate 2) T53_12_2 i :=
  species_entry_eq_sum rK53 ⟨12, by decide⟩ e heK h T53_12_2 hfix53_12_2 hinj53_12_2 hcardT53_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK53) (T53_12_2 i) (hfix53_12_2 i) h)

/-! ### Cell (53, 53) twin -/

def T53_53_2 : Fin 125 → Coordinate 2 := fun i => T53_53list.getD i.val (0,0,0,0,0)

theorem hfix53_53_2 : ∀ i, ((T53_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK53)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK53) :=
  repsFix_of_siftB2 rK53 ⟨53, by decide⟩ T53_53_2 (by decide)

theorem hinj53_53_2 : Function.Injective
    (fun i => ((T53_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK53)) :=
  repsInj_of_reduceAux2 rK53 T53_53_2 (by decide)

theorem hcardT53_53_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK53)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK53 ⟨53, by decide⟩ R53_2 hpxR53_2 hcardq53_2 (by decide)).symm

/-- **Cell (53, 53) twin (q=2).** -/
theorem cell53_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK53) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK53) (charOfVec2 rK53 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK53 e (h : Coordinate 2) T53_53_2 i :=
  species_entry_eq_sum rK53 ⟨53, by decide⟩ e heK h T53_53_2 hfix53_53_2 hinj53_53_2 hcardT53_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK53) (T53_53_2 i) (hfix53_53_2 i) h)

end Q2

end LeanDring.P5Presentation
