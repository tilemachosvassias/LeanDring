/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, A-block data (rK = 16): certified per-cell species-entry instantiations, both twins.

Emit-embed-decide loop for order-25 A-block class `rK = 16` (`|G/K| = 125`).
All nonzero `H`-columns (`|gH| ≤ 2`, `t⁻¹Ht ⊆ K`).  Full 125-coset transversal
`R16` and each `H`-fixed sub-transversal `T16_rH` embedded as kernel data and
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

def rK16 : Fin 148 := ⟨16, by decide⟩

def R16list : List Coordinates := [(0,0,0,4,1), (0,0,0,4,2), (0,0,0,4,3), (0,0,0,4,4), (0,0,0,4,0), (0,0,0,0,2), (0,0,0,0,3), (0,0,0,0,4), (0,0,0,0,0), (0,0,0,0,1), (0,0,0,1,3), (0,0,0,1,4), (0,0,0,1,0), (0,0,0,1,1), (0,0,0,1,2), (0,0,0,2,4), (0,0,0,2,0), (0,0,0,2,1), (0,0,0,2,2), (0,0,0,2,3), (0,0,0,3,0), (0,0,0,3,1), (0,0,0,3,2), (0,0,0,3,3), (0,0,0,3,4), (0,1,0,0,1), (0,1,0,0,2), (0,1,0,0,3), (0,1,0,0,4), (0,1,0,0,0), (0,1,0,1,2), (0,1,0,1,3), (0,1,0,1,4), (0,1,0,1,0), (0,1,0,1,1), (0,1,0,2,3), (0,1,0,2,4), (0,1,0,2,0), (0,1,0,2,1), (0,1,0,2,2), (0,1,0,3,4), (0,1,0,3,0), (0,1,0,3,1), (0,1,0,3,2), (0,1,0,3,3), (0,1,0,4,0), (0,1,0,4,1), (0,1,0,4,2), (0,1,0,4,3), (0,1,0,4,4), (0,2,0,1,1), (0,2,0,1,2), (0,2,0,1,3), (0,2,0,1,4), (0,2,0,1,0), (0,2,0,2,2), (0,2,0,2,3), (0,2,0,2,4), (0,2,0,2,0), (0,2,0,2,1), (0,2,0,3,3), (0,2,0,3,4), (0,2,0,3,0), (0,2,0,3,1), (0,2,0,3,2), (0,2,0,4,4), (0,2,0,4,0), (0,2,0,4,1), (0,2,0,4,2), (0,2,0,4,3), (0,2,0,0,0), (0,2,0,0,1), (0,2,0,0,2), (0,2,0,0,3), (0,2,0,0,4), (0,3,0,2,1), (0,3,0,2,2), (0,3,0,2,3), (0,3,0,2,4), (0,3,0,2,0), (0,3,0,3,2), (0,3,0,3,3), (0,3,0,3,4), (0,3,0,3,0), (0,3,0,3,1), (0,3,0,4,3), (0,3,0,4,4), (0,3,0,4,0), (0,3,0,4,1), (0,3,0,4,2), (0,3,0,0,4), (0,3,0,0,0), (0,3,0,0,1), (0,3,0,0,2), (0,3,0,0,3), (0,3,0,1,0), (0,3,0,1,1), (0,3,0,1,2), (0,3,0,1,3), (0,3,0,1,4), (0,4,0,3,1), (0,4,0,3,2), (0,4,0,3,3), (0,4,0,3,4), (0,4,0,3,0), (0,4,0,4,2), (0,4,0,4,3), (0,4,0,4,4), (0,4,0,4,0), (0,4,0,4,1), (0,4,0,0,3), (0,4,0,0,4), (0,4,0,0,0), (0,4,0,0,1), (0,4,0,0,2), (0,4,0,1,4), (0,4,0,1,0), (0,4,0,1,1), (0,4,0,1,2), (0,4,0,1,3), (0,4,0,2,0), (0,4,0,2,1), (0,4,0,2,2), (0,4,0,2,3), (0,4,0,2,4)]
def R16 : Fin 125 → Coordinate 1 := fun i => R16list.getD i.val (0,0,0,0,0)

theorem hpxR16 : Function.Injective (fun i => reduceAux 1 (basisAt rK16) (R16 i)) := by decide
theorem hcardq16 : Nat.card (Coordinate 1 ⧸ reps rK16) = 125 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (16, 0): |T| = 125 -/

def T16_0list : List Coordinates := [(0,0,0,4,1), (0,0,0,4,2), (0,0,0,4,3), (0,0,0,4,4), (0,0,0,4,0), (0,0,0,0,2), (0,0,0,0,3), (0,0,0,0,4), (0,0,0,0,0), (0,0,0,0,1), (0,0,0,1,3), (0,0,0,1,4), (0,0,0,1,0), (0,0,0,1,1), (0,0,0,1,2), (0,0,0,2,4), (0,0,0,2,0), (0,0,0,2,1), (0,0,0,2,2), (0,0,0,2,3), (0,0,0,3,0), (0,0,0,3,1), (0,0,0,3,2), (0,0,0,3,3), (0,0,0,3,4), (0,1,0,0,1), (0,1,0,0,2), (0,1,0,0,3), (0,1,0,0,4), (0,1,0,0,0), (0,1,0,1,2), (0,1,0,1,3), (0,1,0,1,4), (0,1,0,1,0), (0,1,0,1,1), (0,1,0,2,3), (0,1,0,2,4), (0,1,0,2,0), (0,1,0,2,1), (0,1,0,2,2), (0,1,0,3,4), (0,1,0,3,0), (0,1,0,3,1), (0,1,0,3,2), (0,1,0,3,3), (0,1,0,4,0), (0,1,0,4,1), (0,1,0,4,2), (0,1,0,4,3), (0,1,0,4,4), (0,2,0,1,1), (0,2,0,1,2), (0,2,0,1,3), (0,2,0,1,4), (0,2,0,1,0), (0,2,0,2,2), (0,2,0,2,3), (0,2,0,2,4), (0,2,0,2,0), (0,2,0,2,1), (0,2,0,3,3), (0,2,0,3,4), (0,2,0,3,0), (0,2,0,3,1), (0,2,0,3,2), (0,2,0,4,4), (0,2,0,4,0), (0,2,0,4,1), (0,2,0,4,2), (0,2,0,4,3), (0,2,0,0,0), (0,2,0,0,1), (0,2,0,0,2), (0,2,0,0,3), (0,2,0,0,4), (0,3,0,2,1), (0,3,0,2,2), (0,3,0,2,3), (0,3,0,2,4), (0,3,0,2,0), (0,3,0,3,2), (0,3,0,3,3), (0,3,0,3,4), (0,3,0,3,0), (0,3,0,3,1), (0,3,0,4,3), (0,3,0,4,4), (0,3,0,4,0), (0,3,0,4,1), (0,3,0,4,2), (0,3,0,0,4), (0,3,0,0,0), (0,3,0,0,1), (0,3,0,0,2), (0,3,0,0,3), (0,3,0,1,0), (0,3,0,1,1), (0,3,0,1,2), (0,3,0,1,3), (0,3,0,1,4), (0,4,0,3,1), (0,4,0,3,2), (0,4,0,3,3), (0,4,0,3,4), (0,4,0,3,0), (0,4,0,4,2), (0,4,0,4,3), (0,4,0,4,4), (0,4,0,4,0), (0,4,0,4,1), (0,4,0,0,3), (0,4,0,0,4), (0,4,0,0,0), (0,4,0,0,1), (0,4,0,0,2), (0,4,0,1,4), (0,4,0,1,0), (0,4,0,1,1), (0,4,0,1,2), (0,4,0,1,3), (0,4,0,2,0), (0,4,0,2,1), (0,4,0,2,2), (0,4,0,2,3), (0,4,0,2,4)]
def T16_0 : Fin 125 → Coordinate 1 := fun i => T16_0list.getD i.val (0,0,0,0,0)

theorem hfix16_0 : ∀ i, ((T16_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK16)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16) :=
  repsFix_of_siftB rK16 ⟨0, by decide⟩ T16_0 (by decide)

theorem hinj16_0 : Function.Injective
    (fun i => ((T16_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK16)) :=
  repsInj_of_reduceAux rK16 T16_0 (by decide)

theorem hcardT16_0 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK16 ⟨0, by decide⟩ R16 hpxR16 hcardq16 (by decide)).symm

/-- **Cell (16, 0).** -/
theorem cell16_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK16) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK16) (charOfVec rK16 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK16 e (h : Coordinate 1) T16_0 i :=
  species_entry_eq_sum rK16 ⟨0, by decide⟩ e heK h T16_0 hfix16_0 hinj16_0 hcardT16_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK16) (T16_0 i) (hfix16_0 i) h)

/-! ## Cell (16, 2): |T| = 5 -/

def T16_2list : List Coordinates := [(0,2,0,3,3), (0,2,0,3,4), (0,2,0,3,0), (0,2,0,3,1), (0,2,0,3,2)]
def T16_2 : Fin 5 → Coordinate 1 := fun i => T16_2list.getD i.val (0,0,0,0,0)

theorem hfix16_2 : ∀ i, ((T16_2 i : Coordinate 1) : Coordinate 1 ⧸ reps rK16)
    ∈ fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16) :=
  repsFix_of_siftB rK16 ⟨2, by decide⟩ T16_2 (by decide)

theorem hinj16_2 : Function.Injective
    (fun i => ((T16_2 i : Coordinate 1) : Coordinate 1 ⧸ reps rK16)) :=
  repsInj_of_reduceAux rK16 T16_2 (by decide)

theorem hcardT16_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK16 ⟨2, by decide⟩ R16 hpxR16 hcardq16 (by decide)).symm

/-- **Cell (16, 2).** -/
theorem cell16_2 (e : List (ZMod 25)) (heK : charOK (basisAt rK16) e = true)
    (h : ↥(reps (⟨2, by decide⟩ : Fin 148))) :
    species (reps (⟨2, by decide⟩ : Fin 148)) h (basisElt (reps rK16) (charOfVec rK16 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK16 e (h : Coordinate 1) T16_2 i :=
  species_entry_eq_sum rK16 ⟨2, by decide⟩ e heK h T16_2 hfix16_2 hinj16_2 hcardT16_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨2, by decide⟩) (reps rK16) (T16_2 i) (hfix16_2 i) h)

/-! ## Cell (16, 3): |T| = 5 -/

def T16_3list : List Coordinates := [(0,4,0,0,3), (0,4,0,0,4), (0,4,0,0,0), (0,4,0,0,1), (0,4,0,0,2)]
def T16_3 : Fin 5 → Coordinate 1 := fun i => T16_3list.getD i.val (0,0,0,0,0)

theorem hfix16_3 : ∀ i, ((T16_3 i : Coordinate 1) : Coordinate 1 ⧸ reps rK16)
    ∈ fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16) :=
  repsFix_of_siftB rK16 ⟨3, by decide⟩ T16_3 (by decide)

theorem hinj16_3 : Function.Injective
    (fun i => ((T16_3 i : Coordinate 1) : Coordinate 1 ⧸ reps rK16)) :=
  repsInj_of_reduceAux rK16 T16_3 (by decide)

theorem hcardT16_3 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK16 ⟨3, by decide⟩ R16 hpxR16 hcardq16 (by decide)).symm

/-- **Cell (16, 3).** -/
theorem cell16_3 (e : List (ZMod 25)) (heK : charOK (basisAt rK16) e = true)
    (h : ↥(reps (⟨3, by decide⟩ : Fin 148))) :
    species (reps (⟨3, by decide⟩ : Fin 148)) h (basisElt (reps rK16) (charOfVec rK16 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK16 e (h : Coordinate 1) T16_3 i :=
  species_entry_eq_sum rK16 ⟨3, by decide⟩ e heK h T16_3 hfix16_3 hinj16_3 hcardT16_3
    (fun i => conj_mem_of_fixedPoints (reps ⟨3, by decide⟩) (reps rK16) (T16_3 i) (hfix16_3 i) h)

/-! ## Cell (16, 4): |T| = 5 -/

def T16_4list : List Coordinates := [(0,3,0,0,4), (0,3,0,0,0), (0,3,0,0,1), (0,3,0,0,2), (0,3,0,0,3)]
def T16_4 : Fin 5 → Coordinate 1 := fun i => T16_4list.getD i.val (0,0,0,0,0)

theorem hfix16_4 : ∀ i, ((T16_4 i : Coordinate 1) : Coordinate 1 ⧸ reps rK16)
    ∈ fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16) :=
  repsFix_of_siftB rK16 ⟨4, by decide⟩ T16_4 (by decide)

theorem hinj16_4 : Function.Injective
    (fun i => ((T16_4 i : Coordinate 1) : Coordinate 1 ⧸ reps rK16)) :=
  repsInj_of_reduceAux rK16 T16_4 (by decide)

theorem hcardT16_4 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK16 ⟨4, by decide⟩ R16 hpxR16 hcardq16 (by decide)).symm

/-- **Cell (16, 4).** -/
theorem cell16_4 (e : List (ZMod 25)) (heK : charOK (basisAt rK16) e = true)
    (h : ↥(reps (⟨4, by decide⟩ : Fin 148))) :
    species (reps (⟨4, by decide⟩ : Fin 148)) h (basisElt (reps rK16) (charOfVec rK16 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK16 e (h : Coordinate 1) T16_4 i :=
  species_entry_eq_sum rK16 ⟨4, by decide⟩ e heK h T16_4 hfix16_4 hinj16_4 hcardT16_4
    (fun i => conj_mem_of_fixedPoints (reps ⟨4, by decide⟩) (reps rK16) (T16_4 i) (hfix16_4 i) h)

/-! ## Cell (16, 5): |T| = 5 -/

def T16_5list : List Coordinates := [(0,0,0,3,0), (0,0,0,3,1), (0,0,0,3,2), (0,0,0,3,3), (0,0,0,3,4)]
def T16_5 : Fin 5 → Coordinate 1 := fun i => T16_5list.getD i.val (0,0,0,0,0)

theorem hfix16_5 : ∀ i, ((T16_5 i : Coordinate 1) : Coordinate 1 ⧸ reps rK16)
    ∈ fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16) :=
  repsFix_of_siftB rK16 ⟨5, by decide⟩ T16_5 (by decide)

theorem hinj16_5 : Function.Injective
    (fun i => ((T16_5 i : Coordinate 1) : Coordinate 1 ⧸ reps rK16)) :=
  repsInj_of_reduceAux rK16 T16_5 (by decide)

theorem hcardT16_5 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK16 ⟨5, by decide⟩ R16 hpxR16 hcardq16 (by decide)).symm

/-- **Cell (16, 5).** -/
theorem cell16_5 (e : List (ZMod 25)) (heK : charOK (basisAt rK16) e = true)
    (h : ↥(reps (⟨5, by decide⟩ : Fin 148))) :
    species (reps (⟨5, by decide⟩ : Fin 148)) h (basisElt (reps rK16) (charOfVec rK16 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK16 e (h : Coordinate 1) T16_5 i :=
  species_entry_eq_sum rK16 ⟨5, by decide⟩ e heK h T16_5 hfix16_5 hinj16_5 hcardT16_5
    (fun i => conj_mem_of_fixedPoints (reps ⟨5, by decide⟩) (reps rK16) (T16_5 i) (hfix16_5 i) h)

/-! ## Cell (16, 9): |T| = 25 -/

def T16_9list : List Coordinates := [(0,4,0,3,1), (0,4,0,3,2), (0,4,0,3,3), (0,4,0,3,4), (0,4,0,3,0), (0,4,0,4,2), (0,4,0,4,3), (0,4,0,4,4), (0,4,0,4,0), (0,4,0,4,1), (0,4,0,0,3), (0,4,0,0,4), (0,4,0,0,0), (0,4,0,0,1), (0,4,0,0,2), (0,4,0,1,4), (0,4,0,1,0), (0,4,0,1,1), (0,4,0,1,2), (0,4,0,1,3), (0,4,0,2,0), (0,4,0,2,1), (0,4,0,2,2), (0,4,0,2,3), (0,4,0,2,4)]
def T16_9 : Fin 25 → Coordinate 1 := fun i => T16_9list.getD i.val (0,0,0,0,0)

theorem hfix16_9 : ∀ i, ((T16_9 i : Coordinate 1) : Coordinate 1 ⧸ reps rK16)
    ∈ fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16) :=
  repsFix_of_siftB rK16 ⟨9, by decide⟩ T16_9 (by decide)

theorem hinj16_9 : Function.Injective
    (fun i => ((T16_9 i : Coordinate 1) : Coordinate 1 ⧸ reps rK16)) :=
  repsInj_of_reduceAux rK16 T16_9 (by decide)

theorem hcardT16_9 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK16 ⟨9, by decide⟩ R16 hpxR16 hcardq16 (by decide)).symm

/-- **Cell (16, 9).** -/
theorem cell16_9 (e : List (ZMod 25)) (heK : charOK (basisAt rK16) e = true)
    (h : ↥(reps (⟨9, by decide⟩ : Fin 148))) :
    species (reps (⟨9, by decide⟩ : Fin 148)) h (basisElt (reps rK16) (charOfVec rK16 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK16 e (h : Coordinate 1) T16_9 i :=
  species_entry_eq_sum rK16 ⟨9, by decide⟩ e heK h T16_9 hfix16_9 hinj16_9 hcardT16_9
    (fun i => conj_mem_of_fixedPoints (reps ⟨9, by decide⟩) (reps rK16) (T16_9 i) (hfix16_9 i) h)

/-! ## Cell (16, 11): |T| = 5 -/

def T16_11list : List Coordinates := [(0,0,0,0,2), (0,0,0,0,3), (0,0,0,0,4), (0,0,0,0,0), (0,0,0,0,1)]
def T16_11 : Fin 5 → Coordinate 1 := fun i => T16_11list.getD i.val (0,0,0,0,0)

theorem hfix16_11 : ∀ i, ((T16_11 i : Coordinate 1) : Coordinate 1 ⧸ reps rK16)
    ∈ fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16) :=
  repsFix_of_siftB rK16 ⟨11, by decide⟩ T16_11 (by decide)

theorem hinj16_11 : Function.Injective
    (fun i => ((T16_11 i : Coordinate 1) : Coordinate 1 ⧸ reps rK16)) :=
  repsInj_of_reduceAux rK16 T16_11 (by decide)

theorem hcardT16_11 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK16 ⟨11, by decide⟩ R16 hpxR16 hcardq16 (by decide)).symm

/-- **Cell (16, 11).** -/
theorem cell16_11 (e : List (ZMod 25)) (heK : charOK (basisAt rK16) e = true)
    (h : ↥(reps (⟨11, by decide⟩ : Fin 148))) :
    species (reps (⟨11, by decide⟩ : Fin 148)) h (basisElt (reps rK16) (charOfVec rK16 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK16 e (h : Coordinate 1) T16_11 i :=
  species_entry_eq_sum rK16 ⟨11, by decide⟩ e heK h T16_11 hfix16_11 hinj16_11 hcardT16_11
    (fun i => conj_mem_of_fixedPoints (reps ⟨11, by decide⟩) (reps rK16) (T16_11 i) (hfix16_11 i) h)

/-! ## Cell (16, 16): |T| = 5 -/

def T16_16list : List Coordinates := [(0,0,0,0,2), (0,0,0,0,3), (0,0,0,0,4), (0,0,0,0,0), (0,0,0,0,1)]
def T16_16 : Fin 5 → Coordinate 1 := fun i => T16_16list.getD i.val (0,0,0,0,0)

theorem hfix16_16 : ∀ i, ((T16_16 i : Coordinate 1) : Coordinate 1 ⧸ reps rK16)
    ∈ fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16) :=
  repsFix_of_siftB rK16 ⟨16, by decide⟩ T16_16 (by decide)

theorem hinj16_16 : Function.Injective
    (fun i => ((T16_16 i : Coordinate 1) : Coordinate 1 ⧸ reps rK16)) :=
  repsInj_of_reduceAux rK16 T16_16 (by decide)

theorem hcardT16_16 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK16 ⟨16, by decide⟩ R16 hpxR16 hcardq16 (by decide)).symm

/-- **Cell (16, 16).** -/
theorem cell16_16 (e : List (ZMod 25)) (heK : charOK (basisAt rK16) e = true)
    (h : ↥(reps (⟨16, by decide⟩ : Fin 148))) :
    species (reps (⟨16, by decide⟩ : Fin 148)) h (basisElt (reps rK16) (charOfVec rK16 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK16 e (h : Coordinate 1) T16_16 i :=
  species_entry_eq_sum rK16 ⟨16, by decide⟩ e heK h T16_16 hfix16_16 hinj16_16 hcardT16_16
    (fun i => conj_mem_of_fixedPoints (reps ⟨16, by decide⟩) (reps rK16) (T16_16 i) (hfix16_16 i) h)

namespace Q2

def R16_2 : Fin 125 → Coordinate 2 := fun i => R16list.getD i.val (0,0,0,0,0)
theorem hpxR16_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK16) (R16_2 i)) := by decide
theorem hcardq16_2 : Nat.card (Coordinate 2 ⧸ reps rK16) = 125 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (16, 0) twin -/

def T16_0_2 : Fin 125 → Coordinate 2 := fun i => T16_0list.getD i.val (0,0,0,0,0)

theorem hfix16_0_2 : ∀ i, ((T16_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK16)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK16) :=
  repsFix_of_siftB2 rK16 ⟨0, by decide⟩ T16_0_2 (by decide)

theorem hinj16_0_2 : Function.Injective
    (fun i => ((T16_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK16)) :=
  repsInj_of_reduceAux2 rK16 T16_0_2 (by decide)

theorem hcardT16_0_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK16)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK16 ⟨0, by decide⟩ R16_2 hpxR16_2 hcardq16_2 (by decide)).symm

/-- **Cell (16, 0) twin (q=2).** -/
theorem cell16_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK16) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK16) (charOfVec2 rK16 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK16 e (h : Coordinate 2) T16_0_2 i :=
  species_entry_eq_sum rK16 ⟨0, by decide⟩ e heK h T16_0_2 hfix16_0_2 hinj16_0_2 hcardT16_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK16) (T16_0_2 i) (hfix16_0_2 i) h)

/-! ### Cell (16, 2) twin -/

def T16_2_2 : Fin 5 → Coordinate 2 := fun i => T16_2list.getD i.val (0,0,0,0,0)

theorem hfix16_2_2 : ∀ i, ((T16_2_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK16)
    ∈ fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK16) :=
  repsFix_of_siftB2 rK16 ⟨2, by decide⟩ T16_2_2 (by decide)

theorem hinj16_2_2 : Function.Injective
    (fun i => ((T16_2_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK16)) :=
  repsInj_of_reduceAux2 rK16 T16_2_2 (by decide)

theorem hcardT16_2_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK16)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK16 ⟨2, by decide⟩ R16_2 hpxR16_2 hcardq16_2 (by decide)).symm

/-- **Cell (16, 2) twin (q=2).** -/
theorem cell16_2_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK16) e = true)
    (h : ↥(reps (⟨2, by decide⟩ : Fin 148))) :
    species (reps (⟨2, by decide⟩ : Fin 148)) h (basisElt (reps rK16) (charOfVec2 rK16 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK16 e (h : Coordinate 2) T16_2_2 i :=
  species_entry_eq_sum rK16 ⟨2, by decide⟩ e heK h T16_2_2 hfix16_2_2 hinj16_2_2 hcardT16_2_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨2, by decide⟩) (reps rK16) (T16_2_2 i) (hfix16_2_2 i) h)

/-! ### Cell (16, 3) twin -/

def T16_3_2 : Fin 5 → Coordinate 2 := fun i => T16_3list.getD i.val (0,0,0,0,0)

theorem hfix16_3_2 : ∀ i, ((T16_3_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK16)
    ∈ fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK16) :=
  repsFix_of_siftB2 rK16 ⟨3, by decide⟩ T16_3_2 (by decide)

theorem hinj16_3_2 : Function.Injective
    (fun i => ((T16_3_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK16)) :=
  repsInj_of_reduceAux2 rK16 T16_3_2 (by decide)

theorem hcardT16_3_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK16)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK16 ⟨3, by decide⟩ R16_2 hpxR16_2 hcardq16_2 (by decide)).symm

/-- **Cell (16, 3) twin (q=2).** -/
theorem cell16_3_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK16) e = true)
    (h : ↥(reps (⟨3, by decide⟩ : Fin 148))) :
    species (reps (⟨3, by decide⟩ : Fin 148)) h (basisElt (reps rK16) (charOfVec2 rK16 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK16 e (h : Coordinate 2) T16_3_2 i :=
  species_entry_eq_sum rK16 ⟨3, by decide⟩ e heK h T16_3_2 hfix16_3_2 hinj16_3_2 hcardT16_3_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨3, by decide⟩) (reps rK16) (T16_3_2 i) (hfix16_3_2 i) h)

/-! ### Cell (16, 4) twin -/

def T16_4_2 : Fin 5 → Coordinate 2 := fun i => T16_4list.getD i.val (0,0,0,0,0)

theorem hfix16_4_2 : ∀ i, ((T16_4_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK16)
    ∈ fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK16) :=
  repsFix_of_siftB2 rK16 ⟨4, by decide⟩ T16_4_2 (by decide)

theorem hinj16_4_2 : Function.Injective
    (fun i => ((T16_4_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK16)) :=
  repsInj_of_reduceAux2 rK16 T16_4_2 (by decide)

theorem hcardT16_4_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK16)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK16 ⟨4, by decide⟩ R16_2 hpxR16_2 hcardq16_2 (by decide)).symm

/-- **Cell (16, 4) twin (q=2).** -/
theorem cell16_4_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK16) e = true)
    (h : ↥(reps (⟨4, by decide⟩ : Fin 148))) :
    species (reps (⟨4, by decide⟩ : Fin 148)) h (basisElt (reps rK16) (charOfVec2 rK16 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK16 e (h : Coordinate 2) T16_4_2 i :=
  species_entry_eq_sum rK16 ⟨4, by decide⟩ e heK h T16_4_2 hfix16_4_2 hinj16_4_2 hcardT16_4_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨4, by decide⟩) (reps rK16) (T16_4_2 i) (hfix16_4_2 i) h)

/-! ### Cell (16, 5) twin -/

def T16_5_2 : Fin 5 → Coordinate 2 := fun i => T16_5list.getD i.val (0,0,0,0,0)

theorem hfix16_5_2 : ∀ i, ((T16_5_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK16)
    ∈ fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK16) :=
  repsFix_of_siftB2 rK16 ⟨5, by decide⟩ T16_5_2 (by decide)

theorem hinj16_5_2 : Function.Injective
    (fun i => ((T16_5_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK16)) :=
  repsInj_of_reduceAux2 rK16 T16_5_2 (by decide)

theorem hcardT16_5_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK16)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK16 ⟨5, by decide⟩ R16_2 hpxR16_2 hcardq16_2 (by decide)).symm

/-- **Cell (16, 5) twin (q=2).** -/
theorem cell16_5_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK16) e = true)
    (h : ↥(reps (⟨5, by decide⟩ : Fin 148))) :
    species (reps (⟨5, by decide⟩ : Fin 148)) h (basisElt (reps rK16) (charOfVec2 rK16 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK16 e (h : Coordinate 2) T16_5_2 i :=
  species_entry_eq_sum rK16 ⟨5, by decide⟩ e heK h T16_5_2 hfix16_5_2 hinj16_5_2 hcardT16_5_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨5, by decide⟩) (reps rK16) (T16_5_2 i) (hfix16_5_2 i) h)

/-! ### Cell (16, 9) twin -/

def T16_9_2 : Fin 25 → Coordinate 2 := fun i => T16_9list.getD i.val (0,0,0,0,0)

theorem hfix16_9_2 : ∀ i, ((T16_9_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK16)
    ∈ fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK16) :=
  repsFix_of_siftB2 rK16 ⟨9, by decide⟩ T16_9_2 (by decide)

theorem hinj16_9_2 : Function.Injective
    (fun i => ((T16_9_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK16)) :=
  repsInj_of_reduceAux2 rK16 T16_9_2 (by decide)

theorem hcardT16_9_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK16)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK16 ⟨9, by decide⟩ R16_2 hpxR16_2 hcardq16_2 (by decide)).symm

/-- **Cell (16, 9) twin (q=2).** -/
theorem cell16_9_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK16) e = true)
    (h : ↥(reps (⟨9, by decide⟩ : Fin 148))) :
    species (reps (⟨9, by decide⟩ : Fin 148)) h (basisElt (reps rK16) (charOfVec2 rK16 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK16 e (h : Coordinate 2) T16_9_2 i :=
  species_entry_eq_sum rK16 ⟨9, by decide⟩ e heK h T16_9_2 hfix16_9_2 hinj16_9_2 hcardT16_9_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨9, by decide⟩) (reps rK16) (T16_9_2 i) (hfix16_9_2 i) h)

/-! ### Cell (16, 11) twin -/

def T16_11_2 : Fin 5 → Coordinate 2 := fun i => T16_11list.getD i.val (0,0,0,0,0)

theorem hfix16_11_2 : ∀ i, ((T16_11_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK16)
    ∈ fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK16) :=
  repsFix_of_siftB2 rK16 ⟨11, by decide⟩ T16_11_2 (by decide)

theorem hinj16_11_2 : Function.Injective
    (fun i => ((T16_11_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK16)) :=
  repsInj_of_reduceAux2 rK16 T16_11_2 (by decide)

theorem hcardT16_11_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK16)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK16 ⟨11, by decide⟩ R16_2 hpxR16_2 hcardq16_2 (by decide)).symm

/-- **Cell (16, 11) twin (q=2).** -/
theorem cell16_11_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK16) e = true)
    (h : ↥(reps (⟨11, by decide⟩ : Fin 148))) :
    species (reps (⟨11, by decide⟩ : Fin 148)) h (basisElt (reps rK16) (charOfVec2 rK16 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK16 e (h : Coordinate 2) T16_11_2 i :=
  species_entry_eq_sum rK16 ⟨11, by decide⟩ e heK h T16_11_2 hfix16_11_2 hinj16_11_2 hcardT16_11_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨11, by decide⟩) (reps rK16) (T16_11_2 i) (hfix16_11_2 i) h)

/-! ### Cell (16, 16) twin -/

def T16_16_2 : Fin 5 → Coordinate 2 := fun i => T16_16list.getD i.val (0,0,0,0,0)

theorem hfix16_16_2 : ∀ i, ((T16_16_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK16)
    ∈ fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK16) :=
  repsFix_of_siftB2 rK16 ⟨16, by decide⟩ T16_16_2 (by decide)

theorem hinj16_16_2 : Function.Injective
    (fun i => ((T16_16_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK16)) :=
  repsInj_of_reduceAux2 rK16 T16_16_2 (by decide)

theorem hcardT16_16_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK16)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK16 ⟨16, by decide⟩ R16_2 hpxR16_2 hcardq16_2 (by decide)).symm

/-- **Cell (16, 16) twin (q=2).** -/
theorem cell16_16_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK16) e = true)
    (h : ↥(reps (⟨16, by decide⟩ : Fin 148))) :
    species (reps (⟨16, by decide⟩ : Fin 148)) h (basisElt (reps rK16) (charOfVec2 rK16 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK16 e (h : Coordinate 2) T16_16_2 i :=
  species_entry_eq_sum rK16 ⟨16, by decide⟩ e heK h T16_16_2 hfix16_16_2 hinj16_16_2 hcardT16_16_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨16, by decide⟩) (reps rK16) (T16_16_2 i) (hfix16_16_2 i) h)

end Q2

end LeanDring.P5Presentation
