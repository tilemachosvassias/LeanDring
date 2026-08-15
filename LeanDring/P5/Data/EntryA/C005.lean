/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, A-block data (rK = 17): certified per-cell species-entry instantiations, both twins.

Emit-embed-decide loop for order-25 A-block class `rK = 17` (`|G/K| = 125`).
All nonzero `H`-columns (`|gH| ≤ 2`, `t⁻¹Ht ⊆ K`).  Full 125-coset transversal
`R17` and each `H`-fixed sub-transversal `T17_rH` embedded as kernel data and
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

def rK17 : Fin 148 := ⟨17, by decide⟩

def R17list : List Coordinates := [(0,0,0,4,0), (0,0,0,4,1), (0,0,0,4,2), (0,0,0,4,3), (0,0,0,4,4), (0,0,0,0,1), (0,0,0,0,2), (0,0,0,0,3), (0,0,0,0,4), (0,0,0,0,0), (0,0,0,1,2), (0,0,0,1,3), (0,0,0,1,4), (0,0,0,1,0), (0,0,0,1,1), (0,0,0,2,3), (0,0,0,2,4), (0,0,0,2,0), (0,0,0,2,1), (0,0,0,2,2), (0,0,0,3,4), (0,0,0,3,0), (0,0,0,3,1), (0,0,0,3,2), (0,0,0,3,3), (0,1,0,0,0), (0,1,0,0,1), (0,1,0,0,2), (0,1,0,0,3), (0,1,0,0,4), (0,1,0,1,1), (0,1,0,1,2), (0,1,0,1,3), (0,1,0,1,4), (0,1,0,1,0), (0,1,0,2,2), (0,1,0,2,3), (0,1,0,2,4), (0,1,0,2,0), (0,1,0,2,1), (0,1,0,3,3), (0,1,0,3,4), (0,1,0,3,0), (0,1,0,3,1), (0,1,0,3,2), (0,1,0,4,4), (0,1,0,4,0), (0,1,0,4,1), (0,1,0,4,2), (0,1,0,4,3), (0,2,0,1,0), (0,2,0,1,1), (0,2,0,1,2), (0,2,0,1,3), (0,2,0,1,4), (0,2,0,2,1), (0,2,0,2,2), (0,2,0,2,3), (0,2,0,2,4), (0,2,0,2,0), (0,2,0,3,2), (0,2,0,3,3), (0,2,0,3,4), (0,2,0,3,0), (0,2,0,3,1), (0,2,0,4,3), (0,2,0,4,4), (0,2,0,4,0), (0,2,0,4,1), (0,2,0,4,2), (0,2,0,0,4), (0,2,0,0,0), (0,2,0,0,1), (0,2,0,0,2), (0,2,0,0,3), (0,3,0,2,0), (0,3,0,2,1), (0,3,0,2,2), (0,3,0,2,3), (0,3,0,2,4), (0,3,0,3,1), (0,3,0,3,2), (0,3,0,3,3), (0,3,0,3,4), (0,3,0,3,0), (0,3,0,4,2), (0,3,0,4,3), (0,3,0,4,4), (0,3,0,4,0), (0,3,0,4,1), (0,3,0,0,3), (0,3,0,0,4), (0,3,0,0,0), (0,3,0,0,1), (0,3,0,0,2), (0,3,0,1,4), (0,3,0,1,0), (0,3,0,1,1), (0,3,0,1,2), (0,3,0,1,3), (0,4,0,3,0), (0,4,0,3,1), (0,4,0,3,2), (0,4,0,3,3), (0,4,0,3,4), (0,4,0,4,1), (0,4,0,4,2), (0,4,0,4,3), (0,4,0,4,4), (0,4,0,4,0), (0,4,0,0,2), (0,4,0,0,3), (0,4,0,0,4), (0,4,0,0,0), (0,4,0,0,1), (0,4,0,1,3), (0,4,0,1,4), (0,4,0,1,0), (0,4,0,1,1), (0,4,0,1,2), (0,4,0,2,4), (0,4,0,2,0), (0,4,0,2,1), (0,4,0,2,2), (0,4,0,2,3)]
def R17 : Fin 125 → Coordinate 1 := fun i => R17list.getD i.val (0,0,0,0,0)

theorem hpxR17 : Function.Injective (fun i => reduceAux 1 (basisAt rK17) (R17 i)) := by decide
theorem hcardq17 : Nat.card (Coordinate 1 ⧸ reps rK17) = 125 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (17, 0): |T| = 125 -/

def T17_0list : List Coordinates := [(0,0,0,4,0), (0,0,0,4,1), (0,0,0,4,2), (0,0,0,4,3), (0,0,0,4,4), (0,0,0,0,1), (0,0,0,0,2), (0,0,0,0,3), (0,0,0,0,4), (0,0,0,0,0), (0,0,0,1,2), (0,0,0,1,3), (0,0,0,1,4), (0,0,0,1,0), (0,0,0,1,1), (0,0,0,2,3), (0,0,0,2,4), (0,0,0,2,0), (0,0,0,2,1), (0,0,0,2,2), (0,0,0,3,4), (0,0,0,3,0), (0,0,0,3,1), (0,0,0,3,2), (0,0,0,3,3), (0,1,0,0,0), (0,1,0,0,1), (0,1,0,0,2), (0,1,0,0,3), (0,1,0,0,4), (0,1,0,1,1), (0,1,0,1,2), (0,1,0,1,3), (0,1,0,1,4), (0,1,0,1,0), (0,1,0,2,2), (0,1,0,2,3), (0,1,0,2,4), (0,1,0,2,0), (0,1,0,2,1), (0,1,0,3,3), (0,1,0,3,4), (0,1,0,3,0), (0,1,0,3,1), (0,1,0,3,2), (0,1,0,4,4), (0,1,0,4,0), (0,1,0,4,1), (0,1,0,4,2), (0,1,0,4,3), (0,2,0,1,0), (0,2,0,1,1), (0,2,0,1,2), (0,2,0,1,3), (0,2,0,1,4), (0,2,0,2,1), (0,2,0,2,2), (0,2,0,2,3), (0,2,0,2,4), (0,2,0,2,0), (0,2,0,3,2), (0,2,0,3,3), (0,2,0,3,4), (0,2,0,3,0), (0,2,0,3,1), (0,2,0,4,3), (0,2,0,4,4), (0,2,0,4,0), (0,2,0,4,1), (0,2,0,4,2), (0,2,0,0,4), (0,2,0,0,0), (0,2,0,0,1), (0,2,0,0,2), (0,2,0,0,3), (0,3,0,2,0), (0,3,0,2,1), (0,3,0,2,2), (0,3,0,2,3), (0,3,0,2,4), (0,3,0,3,1), (0,3,0,3,2), (0,3,0,3,3), (0,3,0,3,4), (0,3,0,3,0), (0,3,0,4,2), (0,3,0,4,3), (0,3,0,4,4), (0,3,0,4,0), (0,3,0,4,1), (0,3,0,0,3), (0,3,0,0,4), (0,3,0,0,0), (0,3,0,0,1), (0,3,0,0,2), (0,3,0,1,4), (0,3,0,1,0), (0,3,0,1,1), (0,3,0,1,2), (0,3,0,1,3), (0,4,0,3,0), (0,4,0,3,1), (0,4,0,3,2), (0,4,0,3,3), (0,4,0,3,4), (0,4,0,4,1), (0,4,0,4,2), (0,4,0,4,3), (0,4,0,4,4), (0,4,0,4,0), (0,4,0,0,2), (0,4,0,0,3), (0,4,0,0,4), (0,4,0,0,0), (0,4,0,0,1), (0,4,0,1,3), (0,4,0,1,4), (0,4,0,1,0), (0,4,0,1,1), (0,4,0,1,2), (0,4,0,2,4), (0,4,0,2,0), (0,4,0,2,1), (0,4,0,2,2), (0,4,0,2,3)]
def T17_0 : Fin 125 → Coordinate 1 := fun i => T17_0list.getD i.val (0,0,0,0,0)

theorem hfix17_0 : ∀ i, ((T17_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK17)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17) :=
  repsFix_of_siftB rK17 ⟨0, by decide⟩ T17_0 (by decide)

theorem hinj17_0 : Function.Injective
    (fun i => ((T17_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK17)) :=
  repsInj_of_reduceAux rK17 T17_0 (by decide)

theorem hcardT17_0 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK17 ⟨0, by decide⟩ R17 hpxR17 hcardq17 (by decide)).symm

/-- **Cell (17, 0).** -/
theorem cell17_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK17) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK17) (charOfVec rK17 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK17 e (h : Coordinate 1) T17_0 i :=
  species_entry_eq_sum rK17 ⟨0, by decide⟩ e heK h T17_0 hfix17_0 hinj17_0 hcardT17_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK17) (T17_0 i) (hfix17_0 i) h)

/-! ## Cell (17, 2): |T| = 5 -/

def T17_2list : List Coordinates := [(0,2,0,2,1), (0,2,0,2,2), (0,2,0,2,3), (0,2,0,2,4), (0,2,0,2,0)]
def T17_2 : Fin 5 → Coordinate 1 := fun i => T17_2list.getD i.val (0,0,0,0,0)

theorem hfix17_2 : ∀ i, ((T17_2 i : Coordinate 1) : Coordinate 1 ⧸ reps rK17)
    ∈ fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17) :=
  repsFix_of_siftB rK17 ⟨2, by decide⟩ T17_2 (by decide)

theorem hinj17_2 : Function.Injective
    (fun i => ((T17_2 i : Coordinate 1) : Coordinate 1 ⧸ reps rK17)) :=
  repsInj_of_reduceAux rK17 T17_2 (by decide)

theorem hcardT17_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK17 ⟨2, by decide⟩ R17 hpxR17 hcardq17 (by decide)).symm

/-- **Cell (17, 2).** -/
theorem cell17_2 (e : List (ZMod 25)) (heK : charOK (basisAt rK17) e = true)
    (h : ↥(reps (⟨2, by decide⟩ : Fin 148))) :
    species (reps (⟨2, by decide⟩ : Fin 148)) h (basisElt (reps rK17) (charOfVec rK17 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK17 e (h : Coordinate 1) T17_2 i :=
  species_entry_eq_sum rK17 ⟨2, by decide⟩ e heK h T17_2 hfix17_2 hinj17_2 hcardT17_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨2, by decide⟩) (reps rK17) (T17_2 i) (hfix17_2 i) h)

/-! ## Cell (17, 3): |T| = 5 -/

def T17_3list : List Coordinates := [(0,4,0,2,4), (0,4,0,2,0), (0,4,0,2,1), (0,4,0,2,2), (0,4,0,2,3)]
def T17_3 : Fin 5 → Coordinate 1 := fun i => T17_3list.getD i.val (0,0,0,0,0)

theorem hfix17_3 : ∀ i, ((T17_3 i : Coordinate 1) : Coordinate 1 ⧸ reps rK17)
    ∈ fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17) :=
  repsFix_of_siftB rK17 ⟨3, by decide⟩ T17_3 (by decide)

theorem hinj17_3 : Function.Injective
    (fun i => ((T17_3 i : Coordinate 1) : Coordinate 1 ⧸ reps rK17)) :=
  repsInj_of_reduceAux rK17 T17_3 (by decide)

theorem hcardT17_3 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK17 ⟨3, by decide⟩ R17 hpxR17 hcardq17 (by decide)).symm

/-- **Cell (17, 3).** -/
theorem cell17_3 (e : List (ZMod 25)) (heK : charOK (basisAt rK17) e = true)
    (h : ↥(reps (⟨3, by decide⟩ : Fin 148))) :
    species (reps (⟨3, by decide⟩ : Fin 148)) h (basisElt (reps rK17) (charOfVec rK17 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK17 e (h : Coordinate 1) T17_3 i :=
  species_entry_eq_sum rK17 ⟨3, by decide⟩ e heK h T17_3 hfix17_3 hinj17_3 hcardT17_3
    (fun i => conj_mem_of_fixedPoints (reps ⟨3, by decide⟩) (reps rK17) (T17_3 i) (hfix17_3 i) h)

/-! ## Cell (17, 4): |T| = 5 -/

def T17_4list : List Coordinates := [(0,3,0,3,1), (0,3,0,3,2), (0,3,0,3,3), (0,3,0,3,4), (0,3,0,3,0)]
def T17_4 : Fin 5 → Coordinate 1 := fun i => T17_4list.getD i.val (0,0,0,0,0)

theorem hfix17_4 : ∀ i, ((T17_4 i : Coordinate 1) : Coordinate 1 ⧸ reps rK17)
    ∈ fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17) :=
  repsFix_of_siftB rK17 ⟨4, by decide⟩ T17_4 (by decide)

theorem hinj17_4 : Function.Injective
    (fun i => ((T17_4 i : Coordinate 1) : Coordinate 1 ⧸ reps rK17)) :=
  repsInj_of_reduceAux rK17 T17_4 (by decide)

theorem hcardT17_4 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK17 ⟨4, by decide⟩ R17 hpxR17 hcardq17 (by decide)).symm

/-- **Cell (17, 4).** -/
theorem cell17_4 (e : List (ZMod 25)) (heK : charOK (basisAt rK17) e = true)
    (h : ↥(reps (⟨4, by decide⟩ : Fin 148))) :
    species (reps (⟨4, by decide⟩ : Fin 148)) h (basisElt (reps rK17) (charOfVec rK17 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK17 e (h : Coordinate 1) T17_4 i :=
  species_entry_eq_sum rK17 ⟨4, by decide⟩ e heK h T17_4 hfix17_4 hinj17_4 hcardT17_4
    (fun i => conj_mem_of_fixedPoints (reps ⟨4, by decide⟩) (reps rK17) (T17_4 i) (hfix17_4 i) h)

/-! ## Cell (17, 5): |T| = 5 -/

def T17_5list : List Coordinates := [(0,0,0,4,0), (0,0,0,4,1), (0,0,0,4,2), (0,0,0,4,3), (0,0,0,4,4)]
def T17_5 : Fin 5 → Coordinate 1 := fun i => T17_5list.getD i.val (0,0,0,0,0)

theorem hfix17_5 : ∀ i, ((T17_5 i : Coordinate 1) : Coordinate 1 ⧸ reps rK17)
    ∈ fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17) :=
  repsFix_of_siftB rK17 ⟨5, by decide⟩ T17_5 (by decide)

theorem hinj17_5 : Function.Injective
    (fun i => ((T17_5 i : Coordinate 1) : Coordinate 1 ⧸ reps rK17)) :=
  repsInj_of_reduceAux rK17 T17_5 (by decide)

theorem hcardT17_5 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK17 ⟨5, by decide⟩ R17 hpxR17 hcardq17 (by decide)).symm

/-- **Cell (17, 5).** -/
theorem cell17_5 (e : List (ZMod 25)) (heK : charOK (basisAt rK17) e = true)
    (h : ↥(reps (⟨5, by decide⟩ : Fin 148))) :
    species (reps (⟨5, by decide⟩ : Fin 148)) h (basisElt (reps rK17) (charOfVec rK17 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK17 e (h : Coordinate 1) T17_5 i :=
  species_entry_eq_sum rK17 ⟨5, by decide⟩ e heK h T17_5 hfix17_5 hinj17_5 hcardT17_5
    (fun i => conj_mem_of_fixedPoints (reps ⟨5, by decide⟩) (reps rK17) (T17_5 i) (hfix17_5 i) h)

/-! ## Cell (17, 9): |T| = 25 -/

def T17_9list : List Coordinates := [(0,3,0,2,0), (0,3,0,2,1), (0,3,0,2,2), (0,3,0,2,3), (0,3,0,2,4), (0,3,0,3,1), (0,3,0,3,2), (0,3,0,3,3), (0,3,0,3,4), (0,3,0,3,0), (0,3,0,4,2), (0,3,0,4,3), (0,3,0,4,4), (0,3,0,4,0), (0,3,0,4,1), (0,3,0,0,3), (0,3,0,0,4), (0,3,0,0,0), (0,3,0,0,1), (0,3,0,0,2), (0,3,0,1,4), (0,3,0,1,0), (0,3,0,1,1), (0,3,0,1,2), (0,3,0,1,3)]
def T17_9 : Fin 25 → Coordinate 1 := fun i => T17_9list.getD i.val (0,0,0,0,0)

theorem hfix17_9 : ∀ i, ((T17_9 i : Coordinate 1) : Coordinate 1 ⧸ reps rK17)
    ∈ fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17) :=
  repsFix_of_siftB rK17 ⟨9, by decide⟩ T17_9 (by decide)

theorem hinj17_9 : Function.Injective
    (fun i => ((T17_9 i : Coordinate 1) : Coordinate 1 ⧸ reps rK17)) :=
  repsInj_of_reduceAux rK17 T17_9 (by decide)

theorem hcardT17_9 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK17 ⟨9, by decide⟩ R17 hpxR17 hcardq17 (by decide)).symm

/-- **Cell (17, 9).** -/
theorem cell17_9 (e : List (ZMod 25)) (heK : charOK (basisAt rK17) e = true)
    (h : ↥(reps (⟨9, by decide⟩ : Fin 148))) :
    species (reps (⟨9, by decide⟩ : Fin 148)) h (basisElt (reps rK17) (charOfVec rK17 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK17 e (h : Coordinate 1) T17_9 i :=
  species_entry_eq_sum rK17 ⟨9, by decide⟩ e heK h T17_9 hfix17_9 hinj17_9 hcardT17_9
    (fun i => conj_mem_of_fixedPoints (reps ⟨9, by decide⟩) (reps rK17) (T17_9 i) (hfix17_9 i) h)

/-! ## Cell (17, 11): |T| = 5 -/

def T17_11list : List Coordinates := [(0,0,0,0,1), (0,0,0,0,2), (0,0,0,0,3), (0,0,0,0,4), (0,0,0,0,0)]
def T17_11 : Fin 5 → Coordinate 1 := fun i => T17_11list.getD i.val (0,0,0,0,0)

theorem hfix17_11 : ∀ i, ((T17_11 i : Coordinate 1) : Coordinate 1 ⧸ reps rK17)
    ∈ fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17) :=
  repsFix_of_siftB rK17 ⟨11, by decide⟩ T17_11 (by decide)

theorem hinj17_11 : Function.Injective
    (fun i => ((T17_11 i : Coordinate 1) : Coordinate 1 ⧸ reps rK17)) :=
  repsInj_of_reduceAux rK17 T17_11 (by decide)

theorem hcardT17_11 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK17 ⟨11, by decide⟩ R17 hpxR17 hcardq17 (by decide)).symm

/-- **Cell (17, 11).** -/
theorem cell17_11 (e : List (ZMod 25)) (heK : charOK (basisAt rK17) e = true)
    (h : ↥(reps (⟨11, by decide⟩ : Fin 148))) :
    species (reps (⟨11, by decide⟩ : Fin 148)) h (basisElt (reps rK17) (charOfVec rK17 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK17 e (h : Coordinate 1) T17_11 i :=
  species_entry_eq_sum rK17 ⟨11, by decide⟩ e heK h T17_11 hfix17_11 hinj17_11 hcardT17_11
    (fun i => conj_mem_of_fixedPoints (reps ⟨11, by decide⟩) (reps rK17) (T17_11 i) (hfix17_11 i) h)

/-! ## Cell (17, 17): |T| = 5 -/

def T17_17list : List Coordinates := [(0,0,0,0,1), (0,0,0,0,2), (0,0,0,0,3), (0,0,0,0,4), (0,0,0,0,0)]
def T17_17 : Fin 5 → Coordinate 1 := fun i => T17_17list.getD i.val (0,0,0,0,0)

theorem hfix17_17 : ∀ i, ((T17_17 i : Coordinate 1) : Coordinate 1 ⧸ reps rK17)
    ∈ fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17) :=
  repsFix_of_siftB rK17 ⟨17, by decide⟩ T17_17 (by decide)

theorem hinj17_17 : Function.Injective
    (fun i => ((T17_17 i : Coordinate 1) : Coordinate 1 ⧸ reps rK17)) :=
  repsInj_of_reduceAux rK17 T17_17 (by decide)

theorem hcardT17_17 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK17 ⟨17, by decide⟩ R17 hpxR17 hcardq17 (by decide)).symm

/-- **Cell (17, 17).** -/
theorem cell17_17 (e : List (ZMod 25)) (heK : charOK (basisAt rK17) e = true)
    (h : ↥(reps (⟨17, by decide⟩ : Fin 148))) :
    species (reps (⟨17, by decide⟩ : Fin 148)) h (basisElt (reps rK17) (charOfVec rK17 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK17 e (h : Coordinate 1) T17_17 i :=
  species_entry_eq_sum rK17 ⟨17, by decide⟩ e heK h T17_17 hfix17_17 hinj17_17 hcardT17_17
    (fun i => conj_mem_of_fixedPoints (reps ⟨17, by decide⟩) (reps rK17) (T17_17 i) (hfix17_17 i) h)

namespace Q2

def R17_2 : Fin 125 → Coordinate 2 := fun i => R17list.getD i.val (0,0,0,0,0)
theorem hpxR17_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK17) (R17_2 i)) := by decide
theorem hcardq17_2 : Nat.card (Coordinate 2 ⧸ reps rK17) = 125 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (17, 0) twin -/

def T17_0_2 : Fin 125 → Coordinate 2 := fun i => T17_0list.getD i.val (0,0,0,0,0)

theorem hfix17_0_2 : ∀ i, ((T17_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK17)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK17) :=
  repsFix_of_siftB2 rK17 ⟨0, by decide⟩ T17_0_2 (by decide)

theorem hinj17_0_2 : Function.Injective
    (fun i => ((T17_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK17)) :=
  repsInj_of_reduceAux2 rK17 T17_0_2 (by decide)

theorem hcardT17_0_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK17)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK17 ⟨0, by decide⟩ R17_2 hpxR17_2 hcardq17_2 (by decide)).symm

/-- **Cell (17, 0) twin (q=2).** -/
theorem cell17_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK17) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK17) (charOfVec2 rK17 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK17 e (h : Coordinate 2) T17_0_2 i :=
  species_entry_eq_sum rK17 ⟨0, by decide⟩ e heK h T17_0_2 hfix17_0_2 hinj17_0_2 hcardT17_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK17) (T17_0_2 i) (hfix17_0_2 i) h)

/-! ### Cell (17, 2) twin -/

def T17_2_2 : Fin 5 → Coordinate 2 := fun i => T17_2list.getD i.val (0,0,0,0,0)

theorem hfix17_2_2 : ∀ i, ((T17_2_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK17)
    ∈ fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK17) :=
  repsFix_of_siftB2 rK17 ⟨2, by decide⟩ T17_2_2 (by decide)

theorem hinj17_2_2 : Function.Injective
    (fun i => ((T17_2_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK17)) :=
  repsInj_of_reduceAux2 rK17 T17_2_2 (by decide)

theorem hcardT17_2_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK17)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK17 ⟨2, by decide⟩ R17_2 hpxR17_2 hcardq17_2 (by decide)).symm

/-- **Cell (17, 2) twin (q=2).** -/
theorem cell17_2_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK17) e = true)
    (h : ↥(reps (⟨2, by decide⟩ : Fin 148))) :
    species (reps (⟨2, by decide⟩ : Fin 148)) h (basisElt (reps rK17) (charOfVec2 rK17 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK17 e (h : Coordinate 2) T17_2_2 i :=
  species_entry_eq_sum rK17 ⟨2, by decide⟩ e heK h T17_2_2 hfix17_2_2 hinj17_2_2 hcardT17_2_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨2, by decide⟩) (reps rK17) (T17_2_2 i) (hfix17_2_2 i) h)

/-! ### Cell (17, 3) twin -/

def T17_3_2 : Fin 5 → Coordinate 2 := fun i => T17_3list.getD i.val (0,0,0,0,0)

theorem hfix17_3_2 : ∀ i, ((T17_3_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK17)
    ∈ fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK17) :=
  repsFix_of_siftB2 rK17 ⟨3, by decide⟩ T17_3_2 (by decide)

theorem hinj17_3_2 : Function.Injective
    (fun i => ((T17_3_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK17)) :=
  repsInj_of_reduceAux2 rK17 T17_3_2 (by decide)

theorem hcardT17_3_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK17)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK17 ⟨3, by decide⟩ R17_2 hpxR17_2 hcardq17_2 (by decide)).symm

/-- **Cell (17, 3) twin (q=2).** -/
theorem cell17_3_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK17) e = true)
    (h : ↥(reps (⟨3, by decide⟩ : Fin 148))) :
    species (reps (⟨3, by decide⟩ : Fin 148)) h (basisElt (reps rK17) (charOfVec2 rK17 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK17 e (h : Coordinate 2) T17_3_2 i :=
  species_entry_eq_sum rK17 ⟨3, by decide⟩ e heK h T17_3_2 hfix17_3_2 hinj17_3_2 hcardT17_3_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨3, by decide⟩) (reps rK17) (T17_3_2 i) (hfix17_3_2 i) h)

/-! ### Cell (17, 4) twin -/

def T17_4_2 : Fin 5 → Coordinate 2 := fun i => T17_4list.getD i.val (0,0,0,0,0)

theorem hfix17_4_2 : ∀ i, ((T17_4_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK17)
    ∈ fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK17) :=
  repsFix_of_siftB2 rK17 ⟨4, by decide⟩ T17_4_2 (by decide)

theorem hinj17_4_2 : Function.Injective
    (fun i => ((T17_4_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK17)) :=
  repsInj_of_reduceAux2 rK17 T17_4_2 (by decide)

theorem hcardT17_4_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK17)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK17 ⟨4, by decide⟩ R17_2 hpxR17_2 hcardq17_2 (by decide)).symm

/-- **Cell (17, 4) twin (q=2).** -/
theorem cell17_4_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK17) e = true)
    (h : ↥(reps (⟨4, by decide⟩ : Fin 148))) :
    species (reps (⟨4, by decide⟩ : Fin 148)) h (basisElt (reps rK17) (charOfVec2 rK17 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK17 e (h : Coordinate 2) T17_4_2 i :=
  species_entry_eq_sum rK17 ⟨4, by decide⟩ e heK h T17_4_2 hfix17_4_2 hinj17_4_2 hcardT17_4_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨4, by decide⟩) (reps rK17) (T17_4_2 i) (hfix17_4_2 i) h)

/-! ### Cell (17, 5) twin -/

def T17_5_2 : Fin 5 → Coordinate 2 := fun i => T17_5list.getD i.val (0,0,0,0,0)

theorem hfix17_5_2 : ∀ i, ((T17_5_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK17)
    ∈ fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK17) :=
  repsFix_of_siftB2 rK17 ⟨5, by decide⟩ T17_5_2 (by decide)

theorem hinj17_5_2 : Function.Injective
    (fun i => ((T17_5_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK17)) :=
  repsInj_of_reduceAux2 rK17 T17_5_2 (by decide)

theorem hcardT17_5_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK17)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK17 ⟨5, by decide⟩ R17_2 hpxR17_2 hcardq17_2 (by decide)).symm

/-- **Cell (17, 5) twin (q=2).** -/
theorem cell17_5_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK17) e = true)
    (h : ↥(reps (⟨5, by decide⟩ : Fin 148))) :
    species (reps (⟨5, by decide⟩ : Fin 148)) h (basisElt (reps rK17) (charOfVec2 rK17 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK17 e (h : Coordinate 2) T17_5_2 i :=
  species_entry_eq_sum rK17 ⟨5, by decide⟩ e heK h T17_5_2 hfix17_5_2 hinj17_5_2 hcardT17_5_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨5, by decide⟩) (reps rK17) (T17_5_2 i) (hfix17_5_2 i) h)

/-! ### Cell (17, 9) twin -/

def T17_9_2 : Fin 25 → Coordinate 2 := fun i => T17_9list.getD i.val (0,0,0,0,0)

theorem hfix17_9_2 : ∀ i, ((T17_9_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK17)
    ∈ fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK17) :=
  repsFix_of_siftB2 rK17 ⟨9, by decide⟩ T17_9_2 (by decide)

theorem hinj17_9_2 : Function.Injective
    (fun i => ((T17_9_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK17)) :=
  repsInj_of_reduceAux2 rK17 T17_9_2 (by decide)

theorem hcardT17_9_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK17)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK17 ⟨9, by decide⟩ R17_2 hpxR17_2 hcardq17_2 (by decide)).symm

/-- **Cell (17, 9) twin (q=2).** -/
theorem cell17_9_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK17) e = true)
    (h : ↥(reps (⟨9, by decide⟩ : Fin 148))) :
    species (reps (⟨9, by decide⟩ : Fin 148)) h (basisElt (reps rK17) (charOfVec2 rK17 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK17 e (h : Coordinate 2) T17_9_2 i :=
  species_entry_eq_sum rK17 ⟨9, by decide⟩ e heK h T17_9_2 hfix17_9_2 hinj17_9_2 hcardT17_9_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨9, by decide⟩) (reps rK17) (T17_9_2 i) (hfix17_9_2 i) h)

/-! ### Cell (17, 11) twin -/

def T17_11_2 : Fin 5 → Coordinate 2 := fun i => T17_11list.getD i.val (0,0,0,0,0)

theorem hfix17_11_2 : ∀ i, ((T17_11_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK17)
    ∈ fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK17) :=
  repsFix_of_siftB2 rK17 ⟨11, by decide⟩ T17_11_2 (by decide)

theorem hinj17_11_2 : Function.Injective
    (fun i => ((T17_11_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK17)) :=
  repsInj_of_reduceAux2 rK17 T17_11_2 (by decide)

theorem hcardT17_11_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK17)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK17 ⟨11, by decide⟩ R17_2 hpxR17_2 hcardq17_2 (by decide)).symm

/-- **Cell (17, 11) twin (q=2).** -/
theorem cell17_11_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK17) e = true)
    (h : ↥(reps (⟨11, by decide⟩ : Fin 148))) :
    species (reps (⟨11, by decide⟩ : Fin 148)) h (basisElt (reps rK17) (charOfVec2 rK17 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK17 e (h : Coordinate 2) T17_11_2 i :=
  species_entry_eq_sum rK17 ⟨11, by decide⟩ e heK h T17_11_2 hfix17_11_2 hinj17_11_2 hcardT17_11_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨11, by decide⟩) (reps rK17) (T17_11_2 i) (hfix17_11_2 i) h)

/-! ### Cell (17, 17) twin -/

def T17_17_2 : Fin 5 → Coordinate 2 := fun i => T17_17list.getD i.val (0,0,0,0,0)

theorem hfix17_17_2 : ∀ i, ((T17_17_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK17)
    ∈ fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK17) :=
  repsFix_of_siftB2 rK17 ⟨17, by decide⟩ T17_17_2 (by decide)

theorem hinj17_17_2 : Function.Injective
    (fun i => ((T17_17_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK17)) :=
  repsInj_of_reduceAux2 rK17 T17_17_2 (by decide)

theorem hcardT17_17_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK17)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK17 ⟨17, by decide⟩ R17_2 hpxR17_2 hcardq17_2 (by decide)).symm

/-- **Cell (17, 17) twin (q=2).** -/
theorem cell17_17_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK17) e = true)
    (h : ↥(reps (⟨17, by decide⟩ : Fin 148))) :
    species (reps (⟨17, by decide⟩ : Fin 148)) h (basisElt (reps rK17) (charOfVec2 rK17 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK17 e (h : Coordinate 2) T17_17_2 i :=
  species_entry_eq_sum rK17 ⟨17, by decide⟩ e heK h T17_17_2 hfix17_17_2 hinj17_17_2 hcardT17_17_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨17, by decide⟩) (reps rK17) (T17_17_2 i) (hfix17_17_2 i) h)

end Q2

end LeanDring.P5Presentation
