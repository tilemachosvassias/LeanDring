/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, A-block data (rK = 34): certified per-cell species-entry instantiations, both twins.

Emit-embed-decide loop for order-25 A-block class `rK = 34` (`|G/K| = 125`).
All nonzero `H`-columns (`|gH| ≤ 2`, `t⁻¹Ht ⊆ K`).  Full 125-coset transversal
`R34` and each `H`-fixed sub-transversal `T34_rH` embedded as kernel data and
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

def rK34 : Fin 148 := ⟨34, by decide⟩

def R34list : List Coordinates := [(0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,2,1,0)]
def R34 : Fin 125 → Coordinate 1 := fun i => R34list.getD i.val (0,0,0,0,0)

theorem hpxR34 : Function.Injective (fun i => reduceAux 1 (basisAt rK34) (R34 i)) := by decide
theorem hcardq34 : Nat.card (Coordinate 1 ⧸ reps rK34) = 125 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (34, 0): |T| = 125 -/

def T34_0list : List Coordinates := [(0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,2,1,0)]
def T34_0 : Fin 125 → Coordinate 1 := fun i => T34_0list.getD i.val (0,0,0,0,0)

theorem hfix34_0 : ∀ i, ((T34_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK34)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34) :=
  repsFix_of_siftB rK34 ⟨0, by decide⟩ T34_0 (by decide)

theorem hinj34_0 : Function.Injective
    (fun i => ((T34_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK34)) :=
  repsInj_of_reduceAux rK34 T34_0 (by decide)

theorem hcardT34_0 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK34 ⟨0, by decide⟩ R34 hpxR34 hcardq34 (by decide)).symm

/-- **Cell (34, 0).** -/
theorem cell34_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK34) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK34) (charOfVec rK34 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK34 e (h : Coordinate 1) T34_0 i :=
  species_entry_eq_sum rK34 ⟨0, by decide⟩ e heK h T34_0 hfix34_0 hinj34_0 hcardT34_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK34) (T34_0 i) (hfix34_0 i) h)

/-! ## Cell (34, 12): |T| = 125 -/

def T34_12list : List Coordinates := [(0,4,3,3,0), (0,4,3,4,0), (0,4,3,0,0), (0,4,3,1,0), (0,4,3,2,0), (0,4,4,3,0), (0,4,4,4,0), (0,4,4,0,0), (0,4,4,1,0), (0,4,4,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,1,3,0), (0,4,1,4,0), (0,4,1,0,0), (0,4,1,1,0), (0,4,1,2,0), (0,4,2,3,0), (0,4,2,4,0), (0,4,2,0,0), (0,4,2,1,0), (0,4,2,2,0), (0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0), (0,1,3,0,0), (0,1,3,1,0), (0,1,3,2,0), (0,1,3,3,0), (0,1,3,4,0), (0,1,4,0,0), (0,1,4,1,0), (0,1,4,2,0), (0,1,4,3,0), (0,1,4,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0), (0,1,1,3,0), (0,1,1,4,0), (0,1,2,0,0), (0,1,2,1,0), (0,1,2,2,0), (0,1,2,3,0), (0,1,2,4,0), (0,2,3,1,0), (0,2,3,2,0), (0,2,3,3,0), (0,2,3,4,0), (0,2,3,0,0), (0,2,4,1,0), (0,2,4,2,0), (0,2,4,3,0), (0,2,4,4,0), (0,2,4,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,1,1,0), (0,2,1,2,0), (0,2,1,3,0), (0,2,1,4,0), (0,2,1,0,0), (0,2,2,1,0), (0,2,2,2,0), (0,2,2,3,0), (0,2,2,4,0), (0,2,2,0,0), (0,3,3,2,0), (0,3,3,3,0), (0,3,3,4,0), (0,3,3,0,0), (0,3,3,1,0), (0,3,4,2,0), (0,3,4,3,0), (0,3,4,4,0), (0,3,4,0,0), (0,3,4,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,1,2,0), (0,3,1,3,0), (0,3,1,4,0), (0,3,1,0,0), (0,3,1,1,0), (0,3,2,2,0), (0,3,2,3,0), (0,3,2,4,0), (0,3,2,0,0), (0,3,2,1,0)]
def T34_12 : Fin 125 → Coordinate 1 := fun i => T34_12list.getD i.val (0,0,0,0,0)

theorem hfix34_12 : ∀ i, ((T34_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK34)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34) :=
  repsFix_of_siftB rK34 ⟨12, by decide⟩ T34_12 (by decide)

theorem hinj34_12 : Function.Injective
    (fun i => ((T34_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK34)) :=
  repsInj_of_reduceAux rK34 T34_12 (by decide)

theorem hcardT34_12 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK34 ⟨12, by decide⟩ R34 hpxR34 hcardq34 (by decide)).symm

/-- **Cell (34, 12).** -/
theorem cell34_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK34) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK34) (charOfVec rK34 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK34 e (h : Coordinate 1) T34_12 i :=
  species_entry_eq_sum rK34 ⟨12, by decide⟩ e heK h T34_12 hfix34_12 hinj34_12 hcardT34_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK34) (T34_12 i) (hfix34_12 i) h)

/-! ## Cell (34, 34): |T| = 25 -/

def T34_34list : List Coordinates := [(0,0,3,4,0), (0,0,3,0,0), (0,0,3,1,0), (0,0,3,2,0), (0,0,3,3,0), (0,0,4,4,0), (0,0,4,0,0), (0,0,4,1,0), (0,0,4,2,0), (0,0,4,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,1,4,0), (0,0,1,0,0), (0,0,1,1,0), (0,0,1,2,0), (0,0,1,3,0), (0,0,2,4,0), (0,0,2,0,0), (0,0,2,1,0), (0,0,2,2,0), (0,0,2,3,0)]
def T34_34 : Fin 25 → Coordinate 1 := fun i => T34_34list.getD i.val (0,0,0,0,0)

theorem hfix34_34 : ∀ i, ((T34_34 i : Coordinate 1) : Coordinate 1 ⧸ reps rK34)
    ∈ fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34) :=
  repsFix_of_siftB rK34 ⟨34, by decide⟩ T34_34 (by decide)

theorem hinj34_34 : Function.Injective
    (fun i => ((T34_34 i : Coordinate 1) : Coordinate 1 ⧸ reps rK34)) :=
  repsInj_of_reduceAux rK34 T34_34 (by decide)

theorem hcardT34_34 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK34 ⟨34, by decide⟩ R34 hpxR34 hcardq34 (by decide)).symm

/-- **Cell (34, 34).** -/
theorem cell34_34 (e : List (ZMod 25)) (heK : charOK (basisAt rK34) e = true)
    (h : ↥(reps (⟨34, by decide⟩ : Fin 148))) :
    species (reps (⟨34, by decide⟩ : Fin 148)) h (basisElt (reps rK34) (charOfVec rK34 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK34 e (h : Coordinate 1) T34_34 i :=
  species_entry_eq_sum rK34 ⟨34, by decide⟩ e heK h T34_34 hfix34_34 hinj34_34 hcardT34_34
    (fun i => conj_mem_of_fixedPoints (reps ⟨34, by decide⟩) (reps rK34) (T34_34 i) (hfix34_34 i) h)

namespace Q2

def R34_2 : Fin 125 → Coordinate 2 := fun i => R34list.getD i.val (0,0,0,0,0)
theorem hpxR34_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK34) (R34_2 i)) := by decide
theorem hcardq34_2 : Nat.card (Coordinate 2 ⧸ reps rK34) = 125 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (34, 0) twin -/

def T34_0_2 : Fin 125 → Coordinate 2 := fun i => T34_0list.getD i.val (0,0,0,0,0)

theorem hfix34_0_2 : ∀ i, ((T34_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK34)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK34) :=
  repsFix_of_siftB2 rK34 ⟨0, by decide⟩ T34_0_2 (by decide)

theorem hinj34_0_2 : Function.Injective
    (fun i => ((T34_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK34)) :=
  repsInj_of_reduceAux2 rK34 T34_0_2 (by decide)

theorem hcardT34_0_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK34)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK34 ⟨0, by decide⟩ R34_2 hpxR34_2 hcardq34_2 (by decide)).symm

/-- **Cell (34, 0) twin (q=2).** -/
theorem cell34_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK34) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK34) (charOfVec2 rK34 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK34 e (h : Coordinate 2) T34_0_2 i :=
  species_entry_eq_sum rK34 ⟨0, by decide⟩ e heK h T34_0_2 hfix34_0_2 hinj34_0_2 hcardT34_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK34) (T34_0_2 i) (hfix34_0_2 i) h)

/-! ### Cell (34, 12) twin -/

def T34_12_2 : Fin 125 → Coordinate 2 := fun i => T34_12list.getD i.val (0,0,0,0,0)

theorem hfix34_12_2 : ∀ i, ((T34_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK34)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK34) :=
  repsFix_of_siftB2 rK34 ⟨12, by decide⟩ T34_12_2 (by decide)

theorem hinj34_12_2 : Function.Injective
    (fun i => ((T34_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK34)) :=
  repsInj_of_reduceAux2 rK34 T34_12_2 (by decide)

theorem hcardT34_12_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK34)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK34 ⟨12, by decide⟩ R34_2 hpxR34_2 hcardq34_2 (by decide)).symm

/-- **Cell (34, 12) twin (q=2).** -/
theorem cell34_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK34) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK34) (charOfVec2 rK34 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK34 e (h : Coordinate 2) T34_12_2 i :=
  species_entry_eq_sum rK34 ⟨12, by decide⟩ e heK h T34_12_2 hfix34_12_2 hinj34_12_2 hcardT34_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK34) (T34_12_2 i) (hfix34_12_2 i) h)

/-! ### Cell (34, 34) twin -/

def T34_34_2 : Fin 25 → Coordinate 2 := fun i => T34_34list.getD i.val (0,0,0,0,0)

theorem hfix34_34_2 : ∀ i, ((T34_34_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK34)
    ∈ fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK34) :=
  repsFix_of_siftB2 rK34 ⟨34, by decide⟩ T34_34_2 (by decide)

theorem hinj34_34_2 : Function.Injective
    (fun i => ((T34_34_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK34)) :=
  repsInj_of_reduceAux2 rK34 T34_34_2 (by decide)

theorem hcardT34_34_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK34)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK34 ⟨34, by decide⟩ R34_2 hpxR34_2 hcardq34_2 (by decide)).symm

/-- **Cell (34, 34) twin (q=2).** -/
theorem cell34_34_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK34) e = true)
    (h : ↥(reps (⟨34, by decide⟩ : Fin 148))) :
    species (reps (⟨34, by decide⟩ : Fin 148)) h (basisElt (reps rK34) (charOfVec2 rK34 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK34 e (h : Coordinate 2) T34_34_2 i :=
  species_entry_eq_sum rK34 ⟨34, by decide⟩ e heK h T34_34_2 hfix34_34_2 hinj34_34_2 hcardT34_34_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨34, by decide⟩) (reps rK34) (T34_34_2 i) (hfix34_34_2 i) h)

end Q2

end LeanDring.P5Presentation
