/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, A-block data (rK = 15): diagonal (H = K) species-entry cell, both twins.

Emit-embed-decide loop for order-25 A-block class `rK = 15`, diagonal column
`H = K` (`|T| = 5`).  Same recipe as `LeanDring/P5/Data/EntryA/C001.lean`.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false
set_option linter.style.setOption false

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

def rK15 : Fin 148 := ⟨15, by decide⟩

def R15list : List Coordinates := [(0,0,0,4,2), (0,0,0,4,3), (0,0,0,4,4), (0,0,0,4,0), (0,0,0,4,1), (0,0,0,0,3), (0,0,0,0,4), (0,0,0,0,0), (0,0,0,0,1), (0,0,0,0,2), (0,0,0,1,4), (0,0,0,1,0), (0,0,0,1,1), (0,0,0,1,2), (0,0,0,1,3), (0,0,0,2,0), (0,0,0,2,1), (0,0,0,2,2), (0,0,0,2,3), (0,0,0,2,4), (0,0,0,3,1), (0,0,0,3,2), (0,0,0,3,3), (0,0,0,3,4), (0,0,0,3,0), (0,1,0,0,2), (0,1,0,0,3), (0,1,0,0,4), (0,1,0,0,0), (0,1,0,0,1), (0,1,0,1,3), (0,1,0,1,4), (0,1,0,1,0), (0,1,0,1,1), (0,1,0,1,2), (0,1,0,2,4), (0,1,0,2,0), (0,1,0,2,1), (0,1,0,2,2), (0,1,0,2,3), (0,1,0,3,0), (0,1,0,3,1), (0,1,0,3,2), (0,1,0,3,3), (0,1,0,3,4), (0,1,0,4,1), (0,1,0,4,2), (0,1,0,4,3), (0,1,0,4,4), (0,1,0,4,0), (0,2,0,1,2), (0,2,0,1,3), (0,2,0,1,4), (0,2,0,1,0), (0,2,0,1,1), (0,2,0,2,3), (0,2,0,2,4), (0,2,0,2,0), (0,2,0,2,1), (0,2,0,2,2), (0,2,0,3,4), (0,2,0,3,0), (0,2,0,3,1), (0,2,0,3,2), (0,2,0,3,3), (0,2,0,4,0), (0,2,0,4,1), (0,2,0,4,2), (0,2,0,4,3), (0,2,0,4,4), (0,2,0,0,1), (0,2,0,0,2), (0,2,0,0,3), (0,2,0,0,4), (0,2,0,0,0), (0,3,0,2,2), (0,3,0,2,3), (0,3,0,2,4), (0,3,0,2,0), (0,3,0,2,1), (0,3,0,3,3), (0,3,0,3,4), (0,3,0,3,0), (0,3,0,3,1), (0,3,0,3,2), (0,3,0,4,4), (0,3,0,4,0), (0,3,0,4,1), (0,3,0,4,2), (0,3,0,4,3), (0,3,0,0,0), (0,3,0,0,1), (0,3,0,0,2), (0,3,0,0,3), (0,3,0,0,4), (0,3,0,1,1), (0,3,0,1,2), (0,3,0,1,3), (0,3,0,1,4), (0,3,0,1,0), (0,4,0,3,2), (0,4,0,3,3), (0,4,0,3,4), (0,4,0,3,0), (0,4,0,3,1), (0,4,0,4,3), (0,4,0,4,4), (0,4,0,4,0), (0,4,0,4,1), (0,4,0,4,2), (0,4,0,0,4), (0,4,0,0,0), (0,4,0,0,1), (0,4,0,0,2), (0,4,0,0,3), (0,4,0,1,0), (0,4,0,1,1), (0,4,0,1,2), (0,4,0,1,3), (0,4,0,1,4), (0,4,0,2,1), (0,4,0,2,2), (0,4,0,2,3), (0,4,0,2,4), (0,4,0,2,0)]
def R15 : Fin 125 → Coordinate 1 := fun i => R15list.getD i.val (0,0,0,0,0)
def T15_list : List Coordinates := [(0,0,0,0,3), (0,0,0,0,4), (0,0,0,0,0), (0,0,0,0,1), (0,0,0,0,2)]
def T15 : Fin 5 → Coordinate 1 := fun i => T15_list.getD i.val (0,0,0,0,0)

theorem hpxR15 : Function.Injective (fun i => reduceAux 1 (basisAt rK15) (R15 i)) := by decide
theorem hcardq15 : Nat.card (Coordinate 1 ⧸ reps rK15) = 125 := by
  rw [card_quotient_reps]; decide

theorem hfix15 : ∀ i, ((T15 i : Coordinate 1) : Coordinate 1 ⧸ reps rK15)
    ∈ fixedPoints (reps rK15) (Coordinate 1 ⧸ reps rK15) :=
  repsFix_of_siftB rK15 rK15 T15 (by decide)
theorem hinj15 : Function.Injective
    (fun i => ((T15 i : Coordinate 1) : Coordinate 1 ⧸ reps rK15)) :=
  repsInj_of_reduceAux rK15 T15 (by decide)
theorem hcardT15 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps rK15) (Coordinate 1 ⧸ reps rK15)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK15 rK15 R15 hpxR15 hcardq15 (by decide)).symm

/-- **Cell (15, 15).** -/
theorem cell15_diag (e : List (ZMod 25)) (heK : charOK (basisAt rK15) e = true)
    (h : ↥(reps rK15)) :
    species (reps rK15) h (basisElt (reps rK15) (charOfVec rK15 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK15 e (h : Coordinate 1) T15 i :=
  species_entry_eq_sum rK15 rK15 e heK h T15 hfix15 hinj15 hcardT15
    (fun i => conj_mem_of_fixedPoints (reps rK15) (reps rK15) (T15 i) (hfix15 i) h)

namespace Q2

def R15_2 : Fin 125 → Coordinate 2 := fun i => R15list.getD i.val (0,0,0,0,0)
def T15_2 : Fin 5 → Coordinate 2 := fun i => T15_list.getD i.val (0,0,0,0,0)

theorem hpxR15_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK15) (R15_2 i)) := by decide
theorem hcardq15_2 : Nat.card (Coordinate 2 ⧸ reps rK15) = 125 := by
  rw [card_quotient_reps2]; decide

theorem hfix15_2 : ∀ i, ((T15_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK15)
    ∈ fixedPoints (reps rK15) (Coordinate 2 ⧸ reps rK15) :=
  repsFix_of_siftB2 rK15 rK15 T15_2 (by decide)
theorem hinj15_2 : Function.Injective
    (fun i => ((T15_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK15)) :=
  repsInj_of_reduceAux2 rK15 T15_2 (by decide)
theorem hcardT15_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps rK15) (Coordinate 2 ⧸ reps rK15)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK15 rK15 R15_2 hpxR15_2 hcardq15_2 (by decide)).symm

/-- **Cell (15, 15) twin (q=2).** -/
theorem cell15_diag_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK15) e = true)
    (h : ↥(reps rK15)) :
    species (reps rK15) h (basisElt (reps rK15) (charOfVec2 rK15 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK15 e (h : Coordinate 2) T15_2 i :=
  species_entry_eq_sum rK15 rK15 e heK h T15_2 hfix15_2 hinj15_2 hcardT15_2
    (fun i => conj_mem_of_fixedPoints (reps rK15) (reps rK15) (T15_2 i) (hfix15_2 i) h)

end Q2

end LeanDring.P5Presentation
