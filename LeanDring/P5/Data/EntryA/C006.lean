/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, A-block data (rK = 18): certified per-cell species-entry instantiations, both twins.

Emit-embed-decide loop for order-25 A-block class `rK = 18` (`|G/K| = 125`).
All nonzero `H`-columns (`|gH| ≤ 2`, `t⁻¹Ht ⊆ K`).  Full 125-coset transversal
`R18` and each `H`-fixed sub-transversal `T18_rH` embedded as kernel data and
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

def rK18 : Fin 148 := ⟨18, by decide⟩

def R18list : List Coordinates := [(0,0,0,4,4), (0,0,0,4,0), (0,0,0,4,1), (0,0,0,4,2), (0,0,0,4,3), (0,0,0,0,0), (0,0,0,0,1), (0,0,0,0,2), (0,0,0,0,3), (0,0,0,0,4), (0,0,0,1,1), (0,0,0,1,2), (0,0,0,1,3), (0,0,0,1,4), (0,0,0,1,0), (0,0,0,2,2), (0,0,0,2,3), (0,0,0,2,4), (0,0,0,2,0), (0,0,0,2,1), (0,0,0,3,3), (0,0,0,3,4), (0,0,0,3,0), (0,0,0,3,1), (0,0,0,3,2), (0,1,0,0,4), (0,1,0,0,0), (0,1,0,0,1), (0,1,0,0,2), (0,1,0,0,3), (0,1,0,1,0), (0,1,0,1,1), (0,1,0,1,2), (0,1,0,1,3), (0,1,0,1,4), (0,1,0,2,1), (0,1,0,2,2), (0,1,0,2,3), (0,1,0,2,4), (0,1,0,2,0), (0,1,0,3,2), (0,1,0,3,3), (0,1,0,3,4), (0,1,0,3,0), (0,1,0,3,1), (0,1,0,4,3), (0,1,0,4,4), (0,1,0,4,0), (0,1,0,4,1), (0,1,0,4,2), (0,2,0,1,4), (0,2,0,1,0), (0,2,0,1,1), (0,2,0,1,2), (0,2,0,1,3), (0,2,0,2,0), (0,2,0,2,1), (0,2,0,2,2), (0,2,0,2,3), (0,2,0,2,4), (0,2,0,3,1), (0,2,0,3,2), (0,2,0,3,3), (0,2,0,3,4), (0,2,0,3,0), (0,2,0,4,2), (0,2,0,4,3), (0,2,0,4,4), (0,2,0,4,0), (0,2,0,4,1), (0,2,0,0,3), (0,2,0,0,4), (0,2,0,0,0), (0,2,0,0,1), (0,2,0,0,2), (0,3,0,2,4), (0,3,0,2,0), (0,3,0,2,1), (0,3,0,2,2), (0,3,0,2,3), (0,3,0,3,0), (0,3,0,3,1), (0,3,0,3,2), (0,3,0,3,3), (0,3,0,3,4), (0,3,0,4,1), (0,3,0,4,2), (0,3,0,4,3), (0,3,0,4,4), (0,3,0,4,0), (0,3,0,0,2), (0,3,0,0,3), (0,3,0,0,4), (0,3,0,0,0), (0,3,0,0,1), (0,3,0,1,3), (0,3,0,1,4), (0,3,0,1,0), (0,3,0,1,1), (0,3,0,1,2), (0,4,0,3,4), (0,4,0,3,0), (0,4,0,3,1), (0,4,0,3,2), (0,4,0,3,3), (0,4,0,4,0), (0,4,0,4,1), (0,4,0,4,2), (0,4,0,4,3), (0,4,0,4,4), (0,4,0,0,1), (0,4,0,0,2), (0,4,0,0,3), (0,4,0,0,4), (0,4,0,0,0), (0,4,0,1,2), (0,4,0,1,3), (0,4,0,1,4), (0,4,0,1,0), (0,4,0,1,1), (0,4,0,2,3), (0,4,0,2,4), (0,4,0,2,0), (0,4,0,2,1), (0,4,0,2,2)]
def R18 : Fin 125 → Coordinate 1 := fun i => R18list.getD i.val (0,0,0,0,0)

theorem hpxR18 : Function.Injective (fun i => reduceAux 1 (basisAt rK18) (R18 i)) := by decide
theorem hcardq18 : Nat.card (Coordinate 1 ⧸ reps rK18) = 125 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (18, 0): |T| = 125 -/

def T18_0list : List Coordinates := [(0,0,0,4,4), (0,0,0,4,0), (0,0,0,4,1), (0,0,0,4,2), (0,0,0,4,3), (0,0,0,0,0), (0,0,0,0,1), (0,0,0,0,2), (0,0,0,0,3), (0,0,0,0,4), (0,0,0,1,1), (0,0,0,1,2), (0,0,0,1,3), (0,0,0,1,4), (0,0,0,1,0), (0,0,0,2,2), (0,0,0,2,3), (0,0,0,2,4), (0,0,0,2,0), (0,0,0,2,1), (0,0,0,3,3), (0,0,0,3,4), (0,0,0,3,0), (0,0,0,3,1), (0,0,0,3,2), (0,1,0,0,4), (0,1,0,0,0), (0,1,0,0,1), (0,1,0,0,2), (0,1,0,0,3), (0,1,0,1,0), (0,1,0,1,1), (0,1,0,1,2), (0,1,0,1,3), (0,1,0,1,4), (0,1,0,2,1), (0,1,0,2,2), (0,1,0,2,3), (0,1,0,2,4), (0,1,0,2,0), (0,1,0,3,2), (0,1,0,3,3), (0,1,0,3,4), (0,1,0,3,0), (0,1,0,3,1), (0,1,0,4,3), (0,1,0,4,4), (0,1,0,4,0), (0,1,0,4,1), (0,1,0,4,2), (0,2,0,1,4), (0,2,0,1,0), (0,2,0,1,1), (0,2,0,1,2), (0,2,0,1,3), (0,2,0,2,0), (0,2,0,2,1), (0,2,0,2,2), (0,2,0,2,3), (0,2,0,2,4), (0,2,0,3,1), (0,2,0,3,2), (0,2,0,3,3), (0,2,0,3,4), (0,2,0,3,0), (0,2,0,4,2), (0,2,0,4,3), (0,2,0,4,4), (0,2,0,4,0), (0,2,0,4,1), (0,2,0,0,3), (0,2,0,0,4), (0,2,0,0,0), (0,2,0,0,1), (0,2,0,0,2), (0,3,0,2,4), (0,3,0,2,0), (0,3,0,2,1), (0,3,0,2,2), (0,3,0,2,3), (0,3,0,3,0), (0,3,0,3,1), (0,3,0,3,2), (0,3,0,3,3), (0,3,0,3,4), (0,3,0,4,1), (0,3,0,4,2), (0,3,0,4,3), (0,3,0,4,4), (0,3,0,4,0), (0,3,0,0,2), (0,3,0,0,3), (0,3,0,0,4), (0,3,0,0,0), (0,3,0,0,1), (0,3,0,1,3), (0,3,0,1,4), (0,3,0,1,0), (0,3,0,1,1), (0,3,0,1,2), (0,4,0,3,4), (0,4,0,3,0), (0,4,0,3,1), (0,4,0,3,2), (0,4,0,3,3), (0,4,0,4,0), (0,4,0,4,1), (0,4,0,4,2), (0,4,0,4,3), (0,4,0,4,4), (0,4,0,0,1), (0,4,0,0,2), (0,4,0,0,3), (0,4,0,0,4), (0,4,0,0,0), (0,4,0,1,2), (0,4,0,1,3), (0,4,0,1,4), (0,4,0,1,0), (0,4,0,1,1), (0,4,0,2,3), (0,4,0,2,4), (0,4,0,2,0), (0,4,0,2,1), (0,4,0,2,2)]
def T18_0 : Fin 125 → Coordinate 1 := fun i => T18_0list.getD i.val (0,0,0,0,0)

theorem hfix18_0 : ∀ i, ((T18_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK18)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18) :=
  repsFix_of_siftB rK18 ⟨0, by decide⟩ T18_0 (by decide)

theorem hinj18_0 : Function.Injective
    (fun i => ((T18_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK18)) :=
  repsInj_of_reduceAux rK18 T18_0 (by decide)

theorem hcardT18_0 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK18 ⟨0, by decide⟩ R18 hpxR18 hcardq18 (by decide)).symm

/-- **Cell (18, 0).** -/
theorem cell18_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK18) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK18) (charOfVec rK18 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK18 e (h : Coordinate 1) T18_0 i :=
  species_entry_eq_sum rK18 ⟨0, by decide⟩ e heK h T18_0 hfix18_0 hinj18_0 hcardT18_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK18) (T18_0 i) (hfix18_0 i) h)

/-! ## Cell (18, 2): |T| = 5 -/

def T18_2list : List Coordinates := [(0,2,0,1,4), (0,2,0,1,0), (0,2,0,1,1), (0,2,0,1,2), (0,2,0,1,3)]
def T18_2 : Fin 5 → Coordinate 1 := fun i => T18_2list.getD i.val (0,0,0,0,0)

theorem hfix18_2 : ∀ i, ((T18_2 i : Coordinate 1) : Coordinate 1 ⧸ reps rK18)
    ∈ fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18) :=
  repsFix_of_siftB rK18 ⟨2, by decide⟩ T18_2 (by decide)

theorem hinj18_2 : Function.Injective
    (fun i => ((T18_2 i : Coordinate 1) : Coordinate 1 ⧸ reps rK18)) :=
  repsInj_of_reduceAux rK18 T18_2 (by decide)

theorem hcardT18_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK18 ⟨2, by decide⟩ R18 hpxR18 hcardq18 (by decide)).symm

/-- **Cell (18, 2).** -/
theorem cell18_2 (e : List (ZMod 25)) (heK : charOK (basisAt rK18) e = true)
    (h : ↥(reps (⟨2, by decide⟩ : Fin 148))) :
    species (reps (⟨2, by decide⟩ : Fin 148)) h (basisElt (reps rK18) (charOfVec rK18 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK18 e (h : Coordinate 1) T18_2 i :=
  species_entry_eq_sum rK18 ⟨2, by decide⟩ e heK h T18_2 hfix18_2 hinj18_2 hcardT18_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨2, by decide⟩) (reps rK18) (T18_2 i) (hfix18_2 i) h)

/-! ## Cell (18, 3): |T| = 5 -/

def T18_3list : List Coordinates := [(0,4,0,4,0), (0,4,0,4,1), (0,4,0,4,2), (0,4,0,4,3), (0,4,0,4,4)]
def T18_3 : Fin 5 → Coordinate 1 := fun i => T18_3list.getD i.val (0,0,0,0,0)

theorem hfix18_3 : ∀ i, ((T18_3 i : Coordinate 1) : Coordinate 1 ⧸ reps rK18)
    ∈ fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18) :=
  repsFix_of_siftB rK18 ⟨3, by decide⟩ T18_3 (by decide)

theorem hinj18_3 : Function.Injective
    (fun i => ((T18_3 i : Coordinate 1) : Coordinate 1 ⧸ reps rK18)) :=
  repsInj_of_reduceAux rK18 T18_3 (by decide)

theorem hcardT18_3 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK18 ⟨3, by decide⟩ R18 hpxR18 hcardq18 (by decide)).symm

/-- **Cell (18, 3).** -/
theorem cell18_3 (e : List (ZMod 25)) (heK : charOK (basisAt rK18) e = true)
    (h : ↥(reps (⟨3, by decide⟩ : Fin 148))) :
    species (reps (⟨3, by decide⟩ : Fin 148)) h (basisElt (reps rK18) (charOfVec rK18 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK18 e (h : Coordinate 1) T18_3 i :=
  species_entry_eq_sum rK18 ⟨3, by decide⟩ e heK h T18_3 hfix18_3 hinj18_3 hcardT18_3
    (fun i => conj_mem_of_fixedPoints (reps ⟨3, by decide⟩) (reps rK18) (T18_3 i) (hfix18_3 i) h)

/-! ## Cell (18, 4): |T| = 5 -/

def T18_4list : List Coordinates := [(0,3,0,1,3), (0,3,0,1,4), (0,3,0,1,0), (0,3,0,1,1), (0,3,0,1,2)]
def T18_4 : Fin 5 → Coordinate 1 := fun i => T18_4list.getD i.val (0,0,0,0,0)

theorem hfix18_4 : ∀ i, ((T18_4 i : Coordinate 1) : Coordinate 1 ⧸ reps rK18)
    ∈ fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18) :=
  repsFix_of_siftB rK18 ⟨4, by decide⟩ T18_4 (by decide)

theorem hinj18_4 : Function.Injective
    (fun i => ((T18_4 i : Coordinate 1) : Coordinate 1 ⧸ reps rK18)) :=
  repsInj_of_reduceAux rK18 T18_4 (by decide)

theorem hcardT18_4 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK18 ⟨4, by decide⟩ R18 hpxR18 hcardq18 (by decide)).symm

/-- **Cell (18, 4).** -/
theorem cell18_4 (e : List (ZMod 25)) (heK : charOK (basisAt rK18) e = true)
    (h : ↥(reps (⟨4, by decide⟩ : Fin 148))) :
    species (reps (⟨4, by decide⟩ : Fin 148)) h (basisElt (reps rK18) (charOfVec rK18 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK18 e (h : Coordinate 1) T18_4 i :=
  species_entry_eq_sum rK18 ⟨4, by decide⟩ e heK h T18_4 hfix18_4 hinj18_4 hcardT18_4
    (fun i => conj_mem_of_fixedPoints (reps ⟨4, by decide⟩) (reps rK18) (T18_4 i) (hfix18_4 i) h)

/-! ## Cell (18, 5): |T| = 5 -/

def T18_5list : List Coordinates := [(0,0,0,0,0), (0,0,0,0,1), (0,0,0,0,2), (0,0,0,0,3), (0,0,0,0,4)]
def T18_5 : Fin 5 → Coordinate 1 := fun i => T18_5list.getD i.val (0,0,0,0,0)

theorem hfix18_5 : ∀ i, ((T18_5 i : Coordinate 1) : Coordinate 1 ⧸ reps rK18)
    ∈ fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18) :=
  repsFix_of_siftB rK18 ⟨5, by decide⟩ T18_5 (by decide)

theorem hinj18_5 : Function.Injective
    (fun i => ((T18_5 i : Coordinate 1) : Coordinate 1 ⧸ reps rK18)) :=
  repsInj_of_reduceAux rK18 T18_5 (by decide)

theorem hcardT18_5 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK18 ⟨5, by decide⟩ R18 hpxR18 hcardq18 (by decide)).symm

/-- **Cell (18, 5).** -/
theorem cell18_5 (e : List (ZMod 25)) (heK : charOK (basisAt rK18) e = true)
    (h : ↥(reps (⟨5, by decide⟩ : Fin 148))) :
    species (reps (⟨5, by decide⟩ : Fin 148)) h (basisElt (reps rK18) (charOfVec rK18 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK18 e (h : Coordinate 1) T18_5 i :=
  species_entry_eq_sum rK18 ⟨5, by decide⟩ e heK h T18_5 hfix18_5 hinj18_5 hcardT18_5
    (fun i => conj_mem_of_fixedPoints (reps ⟨5, by decide⟩) (reps rK18) (T18_5 i) (hfix18_5 i) h)

/-! ## Cell (18, 9): |T| = 25 -/

def T18_9list : List Coordinates := [(0,2,0,1,4), (0,2,0,1,0), (0,2,0,1,1), (0,2,0,1,2), (0,2,0,1,3), (0,2,0,2,0), (0,2,0,2,1), (0,2,0,2,2), (0,2,0,2,3), (0,2,0,2,4), (0,2,0,3,1), (0,2,0,3,2), (0,2,0,3,3), (0,2,0,3,4), (0,2,0,3,0), (0,2,0,4,2), (0,2,0,4,3), (0,2,0,4,4), (0,2,0,4,0), (0,2,0,4,1), (0,2,0,0,3), (0,2,0,0,4), (0,2,0,0,0), (0,2,0,0,1), (0,2,0,0,2)]
def T18_9 : Fin 25 → Coordinate 1 := fun i => T18_9list.getD i.val (0,0,0,0,0)

theorem hfix18_9 : ∀ i, ((T18_9 i : Coordinate 1) : Coordinate 1 ⧸ reps rK18)
    ∈ fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18) :=
  repsFix_of_siftB rK18 ⟨9, by decide⟩ T18_9 (by decide)

theorem hinj18_9 : Function.Injective
    (fun i => ((T18_9 i : Coordinate 1) : Coordinate 1 ⧸ reps rK18)) :=
  repsInj_of_reduceAux rK18 T18_9 (by decide)

theorem hcardT18_9 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK18 ⟨9, by decide⟩ R18 hpxR18 hcardq18 (by decide)).symm

/-- **Cell (18, 9).** -/
theorem cell18_9 (e : List (ZMod 25)) (heK : charOK (basisAt rK18) e = true)
    (h : ↥(reps (⟨9, by decide⟩ : Fin 148))) :
    species (reps (⟨9, by decide⟩ : Fin 148)) h (basisElt (reps rK18) (charOfVec rK18 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK18 e (h : Coordinate 1) T18_9 i :=
  species_entry_eq_sum rK18 ⟨9, by decide⟩ e heK h T18_9 hfix18_9 hinj18_9 hcardT18_9
    (fun i => conj_mem_of_fixedPoints (reps ⟨9, by decide⟩) (reps rK18) (T18_9 i) (hfix18_9 i) h)

/-! ## Cell (18, 11): |T| = 5 -/

def T18_11list : List Coordinates := [(0,0,0,0,0), (0,0,0,0,1), (0,0,0,0,2), (0,0,0,0,3), (0,0,0,0,4)]
def T18_11 : Fin 5 → Coordinate 1 := fun i => T18_11list.getD i.val (0,0,0,0,0)

theorem hfix18_11 : ∀ i, ((T18_11 i : Coordinate 1) : Coordinate 1 ⧸ reps rK18)
    ∈ fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18) :=
  repsFix_of_siftB rK18 ⟨11, by decide⟩ T18_11 (by decide)

theorem hinj18_11 : Function.Injective
    (fun i => ((T18_11 i : Coordinate 1) : Coordinate 1 ⧸ reps rK18)) :=
  repsInj_of_reduceAux rK18 T18_11 (by decide)

theorem hcardT18_11 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK18 ⟨11, by decide⟩ R18 hpxR18 hcardq18 (by decide)).symm

/-- **Cell (18, 11).** -/
theorem cell18_11 (e : List (ZMod 25)) (heK : charOK (basisAt rK18) e = true)
    (h : ↥(reps (⟨11, by decide⟩ : Fin 148))) :
    species (reps (⟨11, by decide⟩ : Fin 148)) h (basisElt (reps rK18) (charOfVec rK18 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK18 e (h : Coordinate 1) T18_11 i :=
  species_entry_eq_sum rK18 ⟨11, by decide⟩ e heK h T18_11 hfix18_11 hinj18_11 hcardT18_11
    (fun i => conj_mem_of_fixedPoints (reps ⟨11, by decide⟩) (reps rK18) (T18_11 i) (hfix18_11 i) h)

/-! ## Cell (18, 18): |T| = 5 -/

def T18_18list : List Coordinates := [(0,0,0,0,0), (0,0,0,0,1), (0,0,0,0,2), (0,0,0,0,3), (0,0,0,0,4)]
def T18_18 : Fin 5 → Coordinate 1 := fun i => T18_18list.getD i.val (0,0,0,0,0)

theorem hfix18_18 : ∀ i, ((T18_18 i : Coordinate 1) : Coordinate 1 ⧸ reps rK18)
    ∈ fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18) :=
  repsFix_of_siftB rK18 ⟨18, by decide⟩ T18_18 (by decide)

theorem hinj18_18 : Function.Injective
    (fun i => ((T18_18 i : Coordinate 1) : Coordinate 1 ⧸ reps rK18)) :=
  repsInj_of_reduceAux rK18 T18_18 (by decide)

theorem hcardT18_18 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK18 ⟨18, by decide⟩ R18 hpxR18 hcardq18 (by decide)).symm

/-- **Cell (18, 18).** -/
theorem cell18_18 (e : List (ZMod 25)) (heK : charOK (basisAt rK18) e = true)
    (h : ↥(reps (⟨18, by decide⟩ : Fin 148))) :
    species (reps (⟨18, by decide⟩ : Fin 148)) h (basisElt (reps rK18) (charOfVec rK18 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK18 e (h : Coordinate 1) T18_18 i :=
  species_entry_eq_sum rK18 ⟨18, by decide⟩ e heK h T18_18 hfix18_18 hinj18_18 hcardT18_18
    (fun i => conj_mem_of_fixedPoints (reps ⟨18, by decide⟩) (reps rK18) (T18_18 i) (hfix18_18 i) h)

namespace Q2

def R18_2 : Fin 125 → Coordinate 2 := fun i => R18list.getD i.val (0,0,0,0,0)
theorem hpxR18_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK18) (R18_2 i)) := by decide
theorem hcardq18_2 : Nat.card (Coordinate 2 ⧸ reps rK18) = 125 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (18, 0) twin -/

def T18_0_2 : Fin 125 → Coordinate 2 := fun i => T18_0list.getD i.val (0,0,0,0,0)

theorem hfix18_0_2 : ∀ i, ((T18_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK18)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK18) :=
  repsFix_of_siftB2 rK18 ⟨0, by decide⟩ T18_0_2 (by decide)

theorem hinj18_0_2 : Function.Injective
    (fun i => ((T18_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK18)) :=
  repsInj_of_reduceAux2 rK18 T18_0_2 (by decide)

theorem hcardT18_0_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK18)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK18 ⟨0, by decide⟩ R18_2 hpxR18_2 hcardq18_2 (by decide)).symm

/-- **Cell (18, 0) twin (q=2).** -/
theorem cell18_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK18) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK18) (charOfVec2 rK18 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK18 e (h : Coordinate 2) T18_0_2 i :=
  species_entry_eq_sum rK18 ⟨0, by decide⟩ e heK h T18_0_2 hfix18_0_2 hinj18_0_2 hcardT18_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK18) (T18_0_2 i) (hfix18_0_2 i) h)

/-! ### Cell (18, 2) twin -/

def T18_2_2 : Fin 5 → Coordinate 2 := fun i => T18_2list.getD i.val (0,0,0,0,0)

theorem hfix18_2_2 : ∀ i, ((T18_2_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK18)
    ∈ fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK18) :=
  repsFix_of_siftB2 rK18 ⟨2, by decide⟩ T18_2_2 (by decide)

theorem hinj18_2_2 : Function.Injective
    (fun i => ((T18_2_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK18)) :=
  repsInj_of_reduceAux2 rK18 T18_2_2 (by decide)

theorem hcardT18_2_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK18)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK18 ⟨2, by decide⟩ R18_2 hpxR18_2 hcardq18_2 (by decide)).symm

/-- **Cell (18, 2) twin (q=2).** -/
theorem cell18_2_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK18) e = true)
    (h : ↥(reps (⟨2, by decide⟩ : Fin 148))) :
    species (reps (⟨2, by decide⟩ : Fin 148)) h (basisElt (reps rK18) (charOfVec2 rK18 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK18 e (h : Coordinate 2) T18_2_2 i :=
  species_entry_eq_sum rK18 ⟨2, by decide⟩ e heK h T18_2_2 hfix18_2_2 hinj18_2_2 hcardT18_2_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨2, by decide⟩) (reps rK18) (T18_2_2 i) (hfix18_2_2 i) h)

/-! ### Cell (18, 3) twin -/

def T18_3_2 : Fin 5 → Coordinate 2 := fun i => T18_3list.getD i.val (0,0,0,0,0)

theorem hfix18_3_2 : ∀ i, ((T18_3_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK18)
    ∈ fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK18) :=
  repsFix_of_siftB2 rK18 ⟨3, by decide⟩ T18_3_2 (by decide)

theorem hinj18_3_2 : Function.Injective
    (fun i => ((T18_3_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK18)) :=
  repsInj_of_reduceAux2 rK18 T18_3_2 (by decide)

theorem hcardT18_3_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK18)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK18 ⟨3, by decide⟩ R18_2 hpxR18_2 hcardq18_2 (by decide)).symm

/-- **Cell (18, 3) twin (q=2).** -/
theorem cell18_3_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK18) e = true)
    (h : ↥(reps (⟨3, by decide⟩ : Fin 148))) :
    species (reps (⟨3, by decide⟩ : Fin 148)) h (basisElt (reps rK18) (charOfVec2 rK18 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK18 e (h : Coordinate 2) T18_3_2 i :=
  species_entry_eq_sum rK18 ⟨3, by decide⟩ e heK h T18_3_2 hfix18_3_2 hinj18_3_2 hcardT18_3_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨3, by decide⟩) (reps rK18) (T18_3_2 i) (hfix18_3_2 i) h)

/-! ### Cell (18, 4) twin -/

def T18_4_2 : Fin 5 → Coordinate 2 := fun i => T18_4list.getD i.val (0,0,0,0,0)

theorem hfix18_4_2 : ∀ i, ((T18_4_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK18)
    ∈ fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK18) :=
  repsFix_of_siftB2 rK18 ⟨4, by decide⟩ T18_4_2 (by decide)

theorem hinj18_4_2 : Function.Injective
    (fun i => ((T18_4_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK18)) :=
  repsInj_of_reduceAux2 rK18 T18_4_2 (by decide)

theorem hcardT18_4_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK18)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK18 ⟨4, by decide⟩ R18_2 hpxR18_2 hcardq18_2 (by decide)).symm

/-- **Cell (18, 4) twin (q=2).** -/
theorem cell18_4_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK18) e = true)
    (h : ↥(reps (⟨4, by decide⟩ : Fin 148))) :
    species (reps (⟨4, by decide⟩ : Fin 148)) h (basisElt (reps rK18) (charOfVec2 rK18 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK18 e (h : Coordinate 2) T18_4_2 i :=
  species_entry_eq_sum rK18 ⟨4, by decide⟩ e heK h T18_4_2 hfix18_4_2 hinj18_4_2 hcardT18_4_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨4, by decide⟩) (reps rK18) (T18_4_2 i) (hfix18_4_2 i) h)

/-! ### Cell (18, 5) twin -/

def T18_5_2 : Fin 5 → Coordinate 2 := fun i => T18_5list.getD i.val (0,0,0,0,0)

theorem hfix18_5_2 : ∀ i, ((T18_5_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK18)
    ∈ fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK18) :=
  repsFix_of_siftB2 rK18 ⟨5, by decide⟩ T18_5_2 (by decide)

theorem hinj18_5_2 : Function.Injective
    (fun i => ((T18_5_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK18)) :=
  repsInj_of_reduceAux2 rK18 T18_5_2 (by decide)

theorem hcardT18_5_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK18)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK18 ⟨5, by decide⟩ R18_2 hpxR18_2 hcardq18_2 (by decide)).symm

/-- **Cell (18, 5) twin (q=2).** -/
theorem cell18_5_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK18) e = true)
    (h : ↥(reps (⟨5, by decide⟩ : Fin 148))) :
    species (reps (⟨5, by decide⟩ : Fin 148)) h (basisElt (reps rK18) (charOfVec2 rK18 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK18 e (h : Coordinate 2) T18_5_2 i :=
  species_entry_eq_sum rK18 ⟨5, by decide⟩ e heK h T18_5_2 hfix18_5_2 hinj18_5_2 hcardT18_5_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨5, by decide⟩) (reps rK18) (T18_5_2 i) (hfix18_5_2 i) h)

/-! ### Cell (18, 9) twin -/

def T18_9_2 : Fin 25 → Coordinate 2 := fun i => T18_9list.getD i.val (0,0,0,0,0)

theorem hfix18_9_2 : ∀ i, ((T18_9_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK18)
    ∈ fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK18) :=
  repsFix_of_siftB2 rK18 ⟨9, by decide⟩ T18_9_2 (by decide)

theorem hinj18_9_2 : Function.Injective
    (fun i => ((T18_9_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK18)) :=
  repsInj_of_reduceAux2 rK18 T18_9_2 (by decide)

theorem hcardT18_9_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK18)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK18 ⟨9, by decide⟩ R18_2 hpxR18_2 hcardq18_2 (by decide)).symm

/-- **Cell (18, 9) twin (q=2).** -/
theorem cell18_9_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK18) e = true)
    (h : ↥(reps (⟨9, by decide⟩ : Fin 148))) :
    species (reps (⟨9, by decide⟩ : Fin 148)) h (basisElt (reps rK18) (charOfVec2 rK18 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK18 e (h : Coordinate 2) T18_9_2 i :=
  species_entry_eq_sum rK18 ⟨9, by decide⟩ e heK h T18_9_2 hfix18_9_2 hinj18_9_2 hcardT18_9_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨9, by decide⟩) (reps rK18) (T18_9_2 i) (hfix18_9_2 i) h)

/-! ### Cell (18, 11) twin -/

def T18_11_2 : Fin 5 → Coordinate 2 := fun i => T18_11list.getD i.val (0,0,0,0,0)

theorem hfix18_11_2 : ∀ i, ((T18_11_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK18)
    ∈ fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK18) :=
  repsFix_of_siftB2 rK18 ⟨11, by decide⟩ T18_11_2 (by decide)

theorem hinj18_11_2 : Function.Injective
    (fun i => ((T18_11_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK18)) :=
  repsInj_of_reduceAux2 rK18 T18_11_2 (by decide)

theorem hcardT18_11_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK18)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK18 ⟨11, by decide⟩ R18_2 hpxR18_2 hcardq18_2 (by decide)).symm

/-- **Cell (18, 11) twin (q=2).** -/
theorem cell18_11_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK18) e = true)
    (h : ↥(reps (⟨11, by decide⟩ : Fin 148))) :
    species (reps (⟨11, by decide⟩ : Fin 148)) h (basisElt (reps rK18) (charOfVec2 rK18 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK18 e (h : Coordinate 2) T18_11_2 i :=
  species_entry_eq_sum rK18 ⟨11, by decide⟩ e heK h T18_11_2 hfix18_11_2 hinj18_11_2 hcardT18_11_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨11, by decide⟩) (reps rK18) (T18_11_2 i) (hfix18_11_2 i) h)

/-! ### Cell (18, 18) twin -/

def T18_18_2 : Fin 5 → Coordinate 2 := fun i => T18_18list.getD i.val (0,0,0,0,0)

theorem hfix18_18_2 : ∀ i, ((T18_18_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK18)
    ∈ fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK18) :=
  repsFix_of_siftB2 rK18 ⟨18, by decide⟩ T18_18_2 (by decide)

theorem hinj18_18_2 : Function.Injective
    (fun i => ((T18_18_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK18)) :=
  repsInj_of_reduceAux2 rK18 T18_18_2 (by decide)

theorem hcardT18_18_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK18)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK18 ⟨18, by decide⟩ R18_2 hpxR18_2 hcardq18_2 (by decide)).symm

/-- **Cell (18, 18) twin (q=2).** -/
theorem cell18_18_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK18) e = true)
    (h : ↥(reps (⟨18, by decide⟩ : Fin 148))) :
    species (reps (⟨18, by decide⟩ : Fin 148)) h (basisElt (reps rK18) (charOfVec2 rK18 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK18 e (h : Coordinate 2) T18_18_2 i :=
  species_entry_eq_sum rK18 ⟨18, by decide⟩ e heK h T18_18_2 hfix18_18_2 hinj18_18_2 hcardT18_18_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨18, by decide⟩) (reps rK18) (T18_18_2 i) (hfix18_18_2 i) h)

end Q2

end LeanDring.P5Presentation
