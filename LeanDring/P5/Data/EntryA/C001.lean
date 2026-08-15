/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, A-block data (rK = 13): certified per-cell species-entry instantiations

The emit-embed-decide loop landed for the order-25 A-block class `rK = 13`
(`|G/K| = 125`), q=1.  The full 125-coset transversal `R13` and the `H`-fixed
sub-transversals `T13_rH` are embedded as kernel data; injectivity
(`reduceAux`-proxy), fixedness (`siftB`), and the fixed-point count (filter over
`R13`) are discharged by `decide` and fed through the `LeanDring/P5/Certificate/SpeciesTable/EntryTransA.lean` adapters to
produce, per cell, a species-entry-as-power-sum theorem parametric in the certified
character `e` and the column element `h`.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false
set_option linter.style.setOption false

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

def rK13 : Fin 148 := ⟨13, by decide⟩

/-- Full 125-element coset transversal of `reps 13`. -/
def R13list : List Coordinates := [(0,0,0,0,4), (0,0,0,0,0), (0,0,0,0,1), (0,0,0,0,2), (0,0,0,0,3), (0,1,0,0,4), (0,1,0,0,0), (0,1,0,0,1), (0,1,0,0,2), (0,1,0,0,3), (0,2,0,0,4), (0,2,0,0,0), (0,2,0,0,1), (0,2,0,0,2), (0,2,0,0,3), (0,3,0,0,4), (0,3,0,0,0), (0,3,0,0,1), (0,3,0,0,2), (0,3,0,0,3), (0,4,0,0,4), (0,4,0,0,0), (0,4,0,0,1), (0,4,0,0,2), (0,4,0,0,3), (1,0,0,0,4), (1,0,0,0,0), (1,0,0,0,1), (1,0,0,0,2), (1,0,0,0,3), (1,1,0,0,4), (1,1,0,0,0), (1,1,0,0,1), (1,1,0,0,2), (1,1,0,0,3), (1,2,0,0,4), (1,2,0,0,0), (1,2,0,0,1), (1,2,0,0,2), (1,2,0,0,3), (1,3,0,0,4), (1,3,0,0,0), (1,3,0,0,1), (1,3,0,0,2), (1,3,0,0,3), (1,4,0,0,4), (1,4,0,0,0), (1,4,0,0,1), (1,4,0,0,2), (1,4,0,0,3), (2,0,0,0,4), (2,0,0,0,0), (2,0,0,0,1), (2,0,0,0,2), (2,0,0,0,3), (2,1,0,0,4), (2,1,0,0,0), (2,1,0,0,1), (2,1,0,0,2), (2,1,0,0,3), (2,2,0,0,4), (2,2,0,0,0), (2,2,0,0,1), (2,2,0,0,2), (2,2,0,0,3), (2,3,0,0,4), (2,3,0,0,0), (2,3,0,0,1), (2,3,0,0,2), (2,3,0,0,3), (2,4,0,0,4), (2,4,0,0,0), (2,4,0,0,1), (2,4,0,0,2), (2,4,0,0,3), (3,0,0,0,4), (3,0,0,0,0), (3,0,0,0,1), (3,0,0,0,2), (3,0,0,0,3), (3,1,0,0,4), (3,1,0,0,0), (3,1,0,0,1), (3,1,0,0,2), (3,1,0,0,3), (3,2,0,0,4), (3,2,0,0,0), (3,2,0,0,1), (3,2,0,0,2), (3,2,0,0,3), (3,3,0,0,4), (3,3,0,0,0), (3,3,0,0,1), (3,3,0,0,2), (3,3,0,0,3), (3,4,0,0,4), (3,4,0,0,0), (3,4,0,0,1), (3,4,0,0,2), (3,4,0,0,3), (4,0,0,0,4), (4,0,0,0,0), (4,0,0,0,1), (4,0,0,0,2), (4,0,0,0,3), (4,1,0,0,4), (4,1,0,0,0), (4,1,0,0,1), (4,1,0,0,2), (4,1,0,0,3), (4,2,0,0,4), (4,2,0,0,0), (4,2,0,0,1), (4,2,0,0,2), (4,2,0,0,3), (4,3,0,0,4), (4,3,0,0,0), (4,3,0,0,1), (4,3,0,0,2), (4,3,0,0,3), (4,4,0,0,4), (4,4,0,0,0), (4,4,0,0,1), (4,4,0,0,2), (4,4,0,0,3)]
def R13 : Fin 125 → Coordinate 1 := fun i => R13list.getD i.val (0,0,0,0,0)

/-- `reduceAux`-proxy injectivity of the full transversal — the one heavy per-`rK`
`decide` (125^2 canonical-form compares). -/
theorem hpxR13 : Function.Injective (fun i => reduceAux 1 (basisAt rK13) (R13 i)) := by decide

/-- `|G/reps 13| = 125`. -/
theorem hcardq13 : Nat.card (Coordinate 1 ⧸ reps rK13) = 125 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (13, 1): order-5 column, |T| = 25 -/

def T13_1list : List Coordinates := [(0,0,0,0,4), (0,0,0,0,0), (0,0,0,0,1), (0,0,0,0,2), (0,0,0,0,3), (1,1,0,0,4), (1,1,0,0,0), (1,1,0,0,1), (1,1,0,0,2), (1,1,0,0,3), (2,2,0,0,4), (2,2,0,0,0), (2,2,0,0,1), (2,2,0,0,2), (2,2,0,0,3), (3,3,0,0,4), (3,3,0,0,0), (3,3,0,0,1), (3,3,0,0,2), (3,3,0,0,3), (4,4,0,0,4), (4,4,0,0,0), (4,4,0,0,1), (4,4,0,0,2), (4,4,0,0,3)]
def T13_1 : Fin 25 → Coordinate 1 := fun i => T13_1list.getD i.val (0,0,0,0,0)

theorem hfix13_1 : ∀ i, ((T13_1 i : Coordinate 1) : Coordinate 1 ⧸ reps rK13)
    ∈ MulAction.fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13) :=
  repsFix_of_siftB rK13 ⟨1, by decide⟩ T13_1 (by decide)

theorem hinj13_1 : Function.Injective
    (fun i => ((T13_1 i : Coordinate 1) : Coordinate 1 ⧸ reps rK13)) :=
  repsInj_of_reduceAux rK13 T13_1 (by decide)

theorem hcardT13_1 : Fintype.card (Fin 25)
    = Fintype.card (MulAction.fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK13 ⟨1, by decide⟩ R13 hpxR13 hcardq13 (by decide)).symm

/-- **Cell (13, 1).** The species entry as a power sum over the 25-element
`H`-fixed transversal, for any certified character `e` and column element
`h ∈ reps 1`. -/
theorem cell13_1 (e : List (ZMod 25)) (heK : charOK (basisAt rK13) e = true)
    (h : ↥(reps (⟨1, by decide⟩ : Fin 148))) :
    species (reps (⟨1, by decide⟩ : Fin 148)) h (basisElt (reps rK13) (charOfVec rK13 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK13 e (h : Coordinate 1) T13_1 i :=
  species_entry_eq_sum rK13 ⟨1, by decide⟩ e heK h T13_1 hfix13_1 hinj13_1 hcardT13_1
    (fun i => conj_mem_of_fixedPoints (reps ⟨1, by decide⟩) (reps rK13) (T13_1 i) (hfix13_1 i) h)

/-! ## Cell (13, 13): order-25 column (H = K), |T| = 5 -/

def T13_13list : List Coordinates := [(0,0,0,0,4), (0,0,0,0,0), (0,0,0,0,1), (0,0,0,0,2), (0,0,0,0,3)]
def T13_13 : Fin 5 → Coordinate 1 := fun i => T13_13list.getD i.val (0,0,0,0,0)

theorem hfix13_13 : ∀ i, ((T13_13 i : Coordinate 1) : Coordinate 1 ⧸ reps rK13)
    ∈ MulAction.fixedPoints (reps rK13) (Coordinate 1 ⧸ reps rK13) :=
  repsFix_of_siftB rK13 rK13 T13_13 (by decide)

theorem hinj13_13 : Function.Injective
    (fun i => ((T13_13 i : Coordinate 1) : Coordinate 1 ⧸ reps rK13)) :=
  repsInj_of_reduceAux rK13 T13_13 (by decide)

theorem hcardT13_13 : Fintype.card (Fin 5)
    = Fintype.card (MulAction.fixedPoints (reps rK13) (Coordinate 1 ⧸ reps rK13)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK13 rK13 R13 hpxR13 hcardq13 (by decide)).symm

/-- **Cell (13, 13).** `H = K`; |T| = 5. -/
theorem cell13_13 (e : List (ZMod 25)) (heK : charOK (basisAt rK13) e = true)
    (h : ↥(reps rK13)) :
    species (reps rK13) h (basisElt (reps rK13) (charOfVec rK13 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK13 e (h : Coordinate 1) T13_13 i :=
  species_entry_eq_sum rK13 rK13 e heK h T13_13 hfix13_13 hinj13_13 hcardT13_13
    (fun i => conj_mem_of_fixedPoints (reps rK13) (reps rK13) (T13_13 i) (hfix13_13 i) h)

/-! ## q=2 twin cells (rK = 13); transversal data coincides with q=1 -/

namespace Q2

def R13_2 : Fin 125 → Coordinate 2 := fun i => R13list.getD i.val (0,0,0,0,0)
def T13_1_2 : Fin 25 → Coordinate 2 := fun i => T13_1list.getD i.val (0,0,0,0,0)
def T13_13_2 : Fin 5 → Coordinate 2 := fun i => T13_13list.getD i.val (0,0,0,0,0)

theorem hpxR13_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK13) (R13_2 i)) := by decide

theorem hcardq13_2 : Nat.card (Coordinate 2 ⧸ reps rK13) = 125 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (13, 1) twin -/

theorem hfix13_1_2 : ∀ i, ((T13_1_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK13)
    ∈ fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK13) :=
  repsFix_of_siftB2 rK13 ⟨1, by decide⟩ T13_1_2 (by decide)

theorem hinj13_1_2 : Function.Injective
    (fun i => ((T13_1_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK13)) :=
  repsInj_of_reduceAux2 rK13 T13_1_2 (by decide)

theorem hcardT13_1_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK13)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK13 ⟨1, by decide⟩ R13_2 hpxR13_2 hcardq13_2 (by decide)).symm

/-- **Cell (13, 1) twin (q=2).** -/
theorem cell13_1_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK13) e = true)
    (h : ↥(reps (⟨1, by decide⟩ : Fin 148))) :
    species (reps (⟨1, by decide⟩ : Fin 148)) h (basisElt (reps rK13) (charOfVec2 rK13 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK13 e (h : Coordinate 2) T13_1_2 i :=
  species_entry_eq_sum rK13 ⟨1, by decide⟩ e heK h T13_1_2 hfix13_1_2 hinj13_1_2 hcardT13_1_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨1, by decide⟩) (reps rK13) (T13_1_2 i) (hfix13_1_2 i) h)

/-! ### Cell (13, 13) twin -/

theorem hfix13_13_2 : ∀ i, ((T13_13_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK13)
    ∈ fixedPoints (reps rK13) (Coordinate 2 ⧸ reps rK13) :=
  repsFix_of_siftB2 rK13 rK13 T13_13_2 (by decide)

theorem hinj13_13_2 : Function.Injective
    (fun i => ((T13_13_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK13)) :=
  repsInj_of_reduceAux2 rK13 T13_13_2 (by decide)

theorem hcardT13_13_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps rK13) (Coordinate 2 ⧸ reps rK13)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK13 rK13 R13_2 hpxR13_2 hcardq13_2 (by decide)).symm

/-- **Cell (13, 13) twin (q=2).** -/
theorem cell13_13_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK13) e = true)
    (h : ↥(reps rK13)) :
    species (reps rK13) h (basisElt (reps rK13) (charOfVec2 rK13 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK13 e (h : Coordinate 2) T13_13_2 i :=
  species_entry_eq_sum rK13 rK13 e heK h T13_13_2 hfix13_13_2 hinj13_13_2 hcardT13_13_2
    (fun i => conj_mem_of_fixedPoints (reps rK13) (reps rK13) (T13_13_2 i) (hfix13_13_2 i) h)

end Q2

end LeanDring.P5Presentation
