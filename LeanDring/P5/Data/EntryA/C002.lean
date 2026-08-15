/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, A-block data (rK = 14): diagonal (H = K) species-entry cell, both twins.

Emit-embed-decide loop for order-25 A-block class `rK = 14`, diagonal column
`H = K` (`|T| = 5`).  Same recipe as `LeanDring/P5/Data/EntryA/C001.lean`.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false
set_option linter.style.setOption false

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

def rK14 : Fin 148 := ⟨14, by decide⟩

def R14list : List Coordinates := [(0,0,0,4,3), (0,0,0,4,4), (0,0,0,4,0), (0,0,0,4,1), (0,0,0,4,2), (0,0,0,0,4), (0,0,0,0,0), (0,0,0,0,1), (0,0,0,0,2), (0,0,0,0,3), (0,0,0,1,0), (0,0,0,1,1), (0,0,0,1,2), (0,0,0,1,3), (0,0,0,1,4), (0,0,0,2,1), (0,0,0,2,2), (0,0,0,2,3), (0,0,0,2,4), (0,0,0,2,0), (0,0,0,3,2), (0,0,0,3,3), (0,0,0,3,4), (0,0,0,3,0), (0,0,0,3,1), (0,1,0,0,3), (0,1,0,0,4), (0,1,0,0,0), (0,1,0,0,1), (0,1,0,0,2), (0,1,0,1,4), (0,1,0,1,0), (0,1,0,1,1), (0,1,0,1,2), (0,1,0,1,3), (0,1,0,2,0), (0,1,0,2,1), (0,1,0,2,2), (0,1,0,2,3), (0,1,0,2,4), (0,1,0,3,1), (0,1,0,3,2), (0,1,0,3,3), (0,1,0,3,4), (0,1,0,3,0), (0,1,0,4,2), (0,1,0,4,3), (0,1,0,4,4), (0,1,0,4,0), (0,1,0,4,1), (0,2,0,1,3), (0,2,0,1,4), (0,2,0,1,0), (0,2,0,1,1), (0,2,0,1,2), (0,2,0,2,4), (0,2,0,2,0), (0,2,0,2,1), (0,2,0,2,2), (0,2,0,2,3), (0,2,0,3,0), (0,2,0,3,1), (0,2,0,3,2), (0,2,0,3,3), (0,2,0,3,4), (0,2,0,4,1), (0,2,0,4,2), (0,2,0,4,3), (0,2,0,4,4), (0,2,0,4,0), (0,2,0,0,2), (0,2,0,0,3), (0,2,0,0,4), (0,2,0,0,0), (0,2,0,0,1), (0,3,0,2,3), (0,3,0,2,4), (0,3,0,2,0), (0,3,0,2,1), (0,3,0,2,2), (0,3,0,3,4), (0,3,0,3,0), (0,3,0,3,1), (0,3,0,3,2), (0,3,0,3,3), (0,3,0,4,0), (0,3,0,4,1), (0,3,0,4,2), (0,3,0,4,3), (0,3,0,4,4), (0,3,0,0,1), (0,3,0,0,2), (0,3,0,0,3), (0,3,0,0,4), (0,3,0,0,0), (0,3,0,1,2), (0,3,0,1,3), (0,3,0,1,4), (0,3,0,1,0), (0,3,0,1,1), (0,4,0,3,3), (0,4,0,3,4), (0,4,0,3,0), (0,4,0,3,1), (0,4,0,3,2), (0,4,0,4,4), (0,4,0,4,0), (0,4,0,4,1), (0,4,0,4,2), (0,4,0,4,3), (0,4,0,0,0), (0,4,0,0,1), (0,4,0,0,2), (0,4,0,0,3), (0,4,0,0,4), (0,4,0,1,1), (0,4,0,1,2), (0,4,0,1,3), (0,4,0,1,4), (0,4,0,1,0), (0,4,0,2,2), (0,4,0,2,3), (0,4,0,2,4), (0,4,0,2,0), (0,4,0,2,1)]
def R14 : Fin 125 → Coordinate 1 := fun i => R14list.getD i.val (0,0,0,0,0)
def T14_list : List Coordinates := [(0,0,0,0,4), (0,0,0,0,0), (0,0,0,0,1), (0,0,0,0,2), (0,0,0,0,3)]
def T14 : Fin 5 → Coordinate 1 := fun i => T14_list.getD i.val (0,0,0,0,0)

theorem hpxR14 : Function.Injective (fun i => reduceAux 1 (basisAt rK14) (R14 i)) := by decide
theorem hcardq14 : Nat.card (Coordinate 1 ⧸ reps rK14) = 125 := by
  rw [card_quotient_reps]; decide

theorem hfix14 : ∀ i, ((T14 i : Coordinate 1) : Coordinate 1 ⧸ reps rK14)
    ∈ fixedPoints (reps rK14) (Coordinate 1 ⧸ reps rK14) :=
  repsFix_of_siftB rK14 rK14 T14 (by decide)
theorem hinj14 : Function.Injective
    (fun i => ((T14 i : Coordinate 1) : Coordinate 1 ⧸ reps rK14)) :=
  repsInj_of_reduceAux rK14 T14 (by decide)
theorem hcardT14 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps rK14) (Coordinate 1 ⧸ reps rK14)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK14 rK14 R14 hpxR14 hcardq14 (by decide)).symm

/-- **Cell (14, 14).** -/
theorem cell14_diag (e : List (ZMod 25)) (heK : charOK (basisAt rK14) e = true)
    (h : ↥(reps rK14)) :
    species (reps rK14) h (basisElt (reps rK14) (charOfVec rK14 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK14 e (h : Coordinate 1) T14 i :=
  species_entry_eq_sum rK14 rK14 e heK h T14 hfix14 hinj14 hcardT14
    (fun i => conj_mem_of_fixedPoints (reps rK14) (reps rK14) (T14 i) (hfix14 i) h)

namespace Q2

def R14_2 : Fin 125 → Coordinate 2 := fun i => R14list.getD i.val (0,0,0,0,0)
def T14_2 : Fin 5 → Coordinate 2 := fun i => T14_list.getD i.val (0,0,0,0,0)

theorem hpxR14_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK14) (R14_2 i)) := by decide
theorem hcardq14_2 : Nat.card (Coordinate 2 ⧸ reps rK14) = 125 := by
  rw [card_quotient_reps2]; decide

theorem hfix14_2 : ∀ i, ((T14_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK14)
    ∈ fixedPoints (reps rK14) (Coordinate 2 ⧸ reps rK14) :=
  repsFix_of_siftB2 rK14 rK14 T14_2 (by decide)
theorem hinj14_2 : Function.Injective
    (fun i => ((T14_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK14)) :=
  repsInj_of_reduceAux2 rK14 T14_2 (by decide)
theorem hcardT14_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps rK14) (Coordinate 2 ⧸ reps rK14)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK14 rK14 R14_2 hpxR14_2 hcardq14_2 (by decide)).symm

/-- **Cell (14, 14) twin (q=2).** -/
theorem cell14_diag_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK14) e = true)
    (h : ↥(reps rK14)) :
    species (reps rK14) h (basisElt (reps rK14) (charOfVec2 rK14 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK14 e (h : Coordinate 2) T14_2 i :=
  species_entry_eq_sum rK14 rK14 e heK h T14_2 hfix14_2 hinj14_2 hcardT14_2
    (fun i => conj_mem_of_fixedPoints (reps rK14) (reps rK14) (T14_2 i) (hfix14_2 i) h)

end Q2

end LeanDring.P5Presentation
