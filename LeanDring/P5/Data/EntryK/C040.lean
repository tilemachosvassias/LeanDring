/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, K-strata data (5^4 stratum, rK 141-141): certified per-cell species-entry instantiations, both
twins.

Covers K-classes 141 (order-5^4 K, |R|=5).  For each nonzero `H`-column
(`(G/K)^H ≠ ∅`), the full coset transversal `R141..` and each `H`-fixed
sub-transversal are embedded as kernel data and re-verified by `decide` through
the `LeanDring/P5/Certificate/SpeciesTable/EntryTransA.lean` adapters, producing a species-entry-as-power-sum theorem
parametric in the certified character `e` and column element `h`.  Transversal
data is SHARED between the twins (`reduceAux` normal forms coincide; verified in
the emitter and re-checked by the q=2 `decide`s).
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false
set_option linter.style.setOption false

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-! # K-class rK = 141  (|G/K| = 5) -/

def rK141 : Fin 148 := ⟨141, by decide⟩

def R141list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0)]
def R141 : Fin 5 → Coordinate 1 := fun i => R141list.getD i.val (0,0,0,0,0)

theorem hpxR141 : Function.Injective (fun i => reduceAux 1 (basisAt rK141) (R141 i)) := by decide
theorem hcardq141 : Nat.card (Coordinate 1 ⧸ reps rK141) = 5 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (141, 0): |T| = 5 -/

def T141_0list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0)]
def T141_0 : Fin 5 → Coordinate 1 := fun i => T141_0list.getD i.val (0,0,0,0,0)

theorem hfix141_0 : ∀ i, ((T141_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141) :=
  repsFix_of_siftB rK141 ⟨0, by decide⟩ T141_0 (by decide)

theorem hinj141_0 : Function.Injective
    (fun i => ((T141_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)) :=
  repsInj_of_reduceAux rK141 T141_0 (by decide)

theorem hcardT141_0 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK141 ⟨0, by decide⟩ R141 hpxR141 hcardq141 (by decide)).symm

/-- **Cell (141, 0).** -/
theorem cell141_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK141) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK141 e (h : Coordinate 1) T141_0 i :=
  species_entry_eq_sum rK141 ⟨0, by decide⟩ e heK h T141_0 hfix141_0 hinj141_0 hcardT141_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK141) (T141_0 i) (hfix141_0 i) h)

/-! ## Cell (141, 1): |T| = 5 -/

def T141_1list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0)]
def T141_1 : Fin 5 → Coordinate 1 := fun i => T141_1list.getD i.val (0,0,0,0,0)

theorem hfix141_1 : ∀ i, ((T141_1 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141) :=
  repsFix_of_siftB rK141 ⟨1, by decide⟩ T141_1 (by decide)

theorem hinj141_1 : Function.Injective
    (fun i => ((T141_1 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)) :=
  repsInj_of_reduceAux rK141 T141_1 (by decide)

theorem hcardT141_1 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK141 ⟨1, by decide⟩ R141 hpxR141 hcardq141 (by decide)).symm

/-- **Cell (141, 1).** -/
theorem cell141_1 (e : List (ZMod 25)) (heK : charOK (basisAt rK141) e = true)
    (h : ↥(reps (⟨1, by decide⟩ : Fin 148))) :
    species (reps (⟨1, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK141 e (h : Coordinate 1) T141_1 i :=
  species_entry_eq_sum rK141 ⟨1, by decide⟩ e heK h T141_1 hfix141_1 hinj141_1 hcardT141_1
    (fun i => conj_mem_of_fixedPoints (reps ⟨1, by decide⟩) (reps rK141) (T141_1 i) (hfix141_1 i) h)

/-! ## Cell (141, 2): |T| = 5 -/

def T141_2list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0)]
def T141_2 : Fin 5 → Coordinate 1 := fun i => T141_2list.getD i.val (0,0,0,0,0)

theorem hfix141_2 : ∀ i, ((T141_2 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141) :=
  repsFix_of_siftB rK141 ⟨2, by decide⟩ T141_2 (by decide)

theorem hinj141_2 : Function.Injective
    (fun i => ((T141_2 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)) :=
  repsInj_of_reduceAux rK141 T141_2 (by decide)

theorem hcardT141_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK141 ⟨2, by decide⟩ R141 hpxR141 hcardq141 (by decide)).symm

/-- **Cell (141, 2).** -/
theorem cell141_2 (e : List (ZMod 25)) (heK : charOK (basisAt rK141) e = true)
    (h : ↥(reps (⟨2, by decide⟩ : Fin 148))) :
    species (reps (⟨2, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK141 e (h : Coordinate 1) T141_2 i :=
  species_entry_eq_sum rK141 ⟨2, by decide⟩ e heK h T141_2 hfix141_2 hinj141_2 hcardT141_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨2, by decide⟩) (reps rK141) (T141_2 i) (hfix141_2 i) h)

/-! ## Cell (141, 3): |T| = 5 -/

def T141_3list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0)]
def T141_3 : Fin 5 → Coordinate 1 := fun i => T141_3list.getD i.val (0,0,0,0,0)

theorem hfix141_3 : ∀ i, ((T141_3 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141) :=
  repsFix_of_siftB rK141 ⟨3, by decide⟩ T141_3 (by decide)

theorem hinj141_3 : Function.Injective
    (fun i => ((T141_3 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)) :=
  repsInj_of_reduceAux rK141 T141_3 (by decide)

theorem hcardT141_3 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK141 ⟨3, by decide⟩ R141 hpxR141 hcardq141 (by decide)).symm

/-- **Cell (141, 3).** -/
theorem cell141_3 (e : List (ZMod 25)) (heK : charOK (basisAt rK141) e = true)
    (h : ↥(reps (⟨3, by decide⟩ : Fin 148))) :
    species (reps (⟨3, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK141 e (h : Coordinate 1) T141_3 i :=
  species_entry_eq_sum rK141 ⟨3, by decide⟩ e heK h T141_3 hfix141_3 hinj141_3 hcardT141_3
    (fun i => conj_mem_of_fixedPoints (reps ⟨3, by decide⟩) (reps rK141) (T141_3 i) (hfix141_3 i) h)

/-! ## Cell (141, 4): |T| = 5 -/

def T141_4list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0)]
def T141_4 : Fin 5 → Coordinate 1 := fun i => T141_4list.getD i.val (0,0,0,0,0)

theorem hfix141_4 : ∀ i, ((T141_4 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141) :=
  repsFix_of_siftB rK141 ⟨4, by decide⟩ T141_4 (by decide)

theorem hinj141_4 : Function.Injective
    (fun i => ((T141_4 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)) :=
  repsInj_of_reduceAux rK141 T141_4 (by decide)

theorem hcardT141_4 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK141 ⟨4, by decide⟩ R141 hpxR141 hcardq141 (by decide)).symm

/-- **Cell (141, 4).** -/
theorem cell141_4 (e : List (ZMod 25)) (heK : charOK (basisAt rK141) e = true)
    (h : ↥(reps (⟨4, by decide⟩ : Fin 148))) :
    species (reps (⟨4, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK141 e (h : Coordinate 1) T141_4 i :=
  species_entry_eq_sum rK141 ⟨4, by decide⟩ e heK h T141_4 hfix141_4 hinj141_4 hcardT141_4
    (fun i => conj_mem_of_fixedPoints (reps ⟨4, by decide⟩) (reps rK141) (T141_4 i) (hfix141_4 i) h)

/-! ## Cell (141, 5): |T| = 5 -/

def T141_5list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0)]
def T141_5 : Fin 5 → Coordinate 1 := fun i => T141_5list.getD i.val (0,0,0,0,0)

theorem hfix141_5 : ∀ i, ((T141_5 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141) :=
  repsFix_of_siftB rK141 ⟨5, by decide⟩ T141_5 (by decide)

theorem hinj141_5 : Function.Injective
    (fun i => ((T141_5 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)) :=
  repsInj_of_reduceAux rK141 T141_5 (by decide)

theorem hcardT141_5 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK141 ⟨5, by decide⟩ R141 hpxR141 hcardq141 (by decide)).symm

/-- **Cell (141, 5).** -/
theorem cell141_5 (e : List (ZMod 25)) (heK : charOK (basisAt rK141) e = true)
    (h : ↥(reps (⟨5, by decide⟩ : Fin 148))) :
    species (reps (⟨5, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK141 e (h : Coordinate 1) T141_5 i :=
  species_entry_eq_sum rK141 ⟨5, by decide⟩ e heK h T141_5 hfix141_5 hinj141_5 hcardT141_5
    (fun i => conj_mem_of_fixedPoints (reps ⟨5, by decide⟩) (reps rK141) (T141_5 i) (hfix141_5 i) h)

/-! ## Cell (141, 6): |T| = 5 -/

def T141_6list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0)]
def T141_6 : Fin 5 → Coordinate 1 := fun i => T141_6list.getD i.val (0,0,0,0,0)

theorem hfix141_6 : ∀ i, ((T141_6 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141) :=
  repsFix_of_siftB rK141 ⟨6, by decide⟩ T141_6 (by decide)

theorem hinj141_6 : Function.Injective
    (fun i => ((T141_6 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)) :=
  repsInj_of_reduceAux rK141 T141_6 (by decide)

theorem hcardT141_6 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK141 ⟨6, by decide⟩ R141 hpxR141 hcardq141 (by decide)).symm

/-- **Cell (141, 6).** -/
theorem cell141_6 (e : List (ZMod 25)) (heK : charOK (basisAt rK141) e = true)
    (h : ↥(reps (⟨6, by decide⟩ : Fin 148))) :
    species (reps (⟨6, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK141 e (h : Coordinate 1) T141_6 i :=
  species_entry_eq_sum rK141 ⟨6, by decide⟩ e heK h T141_6 hfix141_6 hinj141_6 hcardT141_6
    (fun i => conj_mem_of_fixedPoints (reps ⟨6, by decide⟩) (reps rK141) (T141_6 i) (hfix141_6 i) h)

/-! ## Cell (141, 7): |T| = 5 -/

def T141_7list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0)]
def T141_7 : Fin 5 → Coordinate 1 := fun i => T141_7list.getD i.val (0,0,0,0,0)

theorem hfix141_7 : ∀ i, ((T141_7 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141) :=
  repsFix_of_siftB rK141 ⟨7, by decide⟩ T141_7 (by decide)

theorem hinj141_7 : Function.Injective
    (fun i => ((T141_7 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)) :=
  repsInj_of_reduceAux rK141 T141_7 (by decide)

theorem hcardT141_7 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK141 ⟨7, by decide⟩ R141 hpxR141 hcardq141 (by decide)).symm

/-- **Cell (141, 7).** -/
theorem cell141_7 (e : List (ZMod 25)) (heK : charOK (basisAt rK141) e = true)
    (h : ↥(reps (⟨7, by decide⟩ : Fin 148))) :
    species (reps (⟨7, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK141 e (h : Coordinate 1) T141_7 i :=
  species_entry_eq_sum rK141 ⟨7, by decide⟩ e heK h T141_7 hfix141_7 hinj141_7 hcardT141_7
    (fun i => conj_mem_of_fixedPoints (reps ⟨7, by decide⟩) (reps rK141) (T141_7 i) (hfix141_7 i) h)

/-! ## Cell (141, 8): |T| = 5 -/

def T141_8list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0)]
def T141_8 : Fin 5 → Coordinate 1 := fun i => T141_8list.getD i.val (0,0,0,0,0)

theorem hfix141_8 : ∀ i, ((T141_8 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141) :=
  repsFix_of_siftB rK141 ⟨8, by decide⟩ T141_8 (by decide)

theorem hinj141_8 : Function.Injective
    (fun i => ((T141_8 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)) :=
  repsInj_of_reduceAux rK141 T141_8 (by decide)

theorem hcardT141_8 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK141 ⟨8, by decide⟩ R141 hpxR141 hcardq141 (by decide)).symm

/-- **Cell (141, 8).** -/
theorem cell141_8 (e : List (ZMod 25)) (heK : charOK (basisAt rK141) e = true)
    (h : ↥(reps (⟨8, by decide⟩ : Fin 148))) :
    species (reps (⟨8, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK141 e (h : Coordinate 1) T141_8 i :=
  species_entry_eq_sum rK141 ⟨8, by decide⟩ e heK h T141_8 hfix141_8 hinj141_8 hcardT141_8
    (fun i => conj_mem_of_fixedPoints (reps ⟨8, by decide⟩) (reps rK141) (T141_8 i) (hfix141_8 i) h)

/-! ## Cell (141, 9): |T| = 5 -/

def T141_9list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0)]
def T141_9 : Fin 5 → Coordinate 1 := fun i => T141_9list.getD i.val (0,0,0,0,0)

theorem hfix141_9 : ∀ i, ((T141_9 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141) :=
  repsFix_of_siftB rK141 ⟨9, by decide⟩ T141_9 (by decide)

theorem hinj141_9 : Function.Injective
    (fun i => ((T141_9 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)) :=
  repsInj_of_reduceAux rK141 T141_9 (by decide)

theorem hcardT141_9 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK141 ⟨9, by decide⟩ R141 hpxR141 hcardq141 (by decide)).symm

/-- **Cell (141, 9).** -/
theorem cell141_9 (e : List (ZMod 25)) (heK : charOK (basisAt rK141) e = true)
    (h : ↥(reps (⟨9, by decide⟩ : Fin 148))) :
    species (reps (⟨9, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK141 e (h : Coordinate 1) T141_9 i :=
  species_entry_eq_sum rK141 ⟨9, by decide⟩ e heK h T141_9 hfix141_9 hinj141_9 hcardT141_9
    (fun i => conj_mem_of_fixedPoints (reps ⟨9, by decide⟩) (reps rK141) (T141_9 i) (hfix141_9 i) h)

/-! ## Cell (141, 10): |T| = 5 -/

def T141_10list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0)]
def T141_10 : Fin 5 → Coordinate 1 := fun i => T141_10list.getD i.val (0,0,0,0,0)

theorem hfix141_10 : ∀ i, ((T141_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141) :=
  repsFix_of_siftB rK141 ⟨10, by decide⟩ T141_10 (by decide)

theorem hinj141_10 : Function.Injective
    (fun i => ((T141_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)) :=
  repsInj_of_reduceAux rK141 T141_10 (by decide)

theorem hcardT141_10 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK141 ⟨10, by decide⟩ R141 hpxR141 hcardq141 (by decide)).symm

/-- **Cell (141, 10).** -/
theorem cell141_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK141) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK141 e (h : Coordinate 1) T141_10 i :=
  species_entry_eq_sum rK141 ⟨10, by decide⟩ e heK h T141_10 hfix141_10 hinj141_10 hcardT141_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK141) (T141_10 i) (hfix141_10 i) h)

/-! ## Cell (141, 11): |T| = 5 -/

def T141_11list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0)]
def T141_11 : Fin 5 → Coordinate 1 := fun i => T141_11list.getD i.val (0,0,0,0,0)

theorem hfix141_11 : ∀ i, ((T141_11 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141) :=
  repsFix_of_siftB rK141 ⟨11, by decide⟩ T141_11 (by decide)

theorem hinj141_11 : Function.Injective
    (fun i => ((T141_11 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)) :=
  repsInj_of_reduceAux rK141 T141_11 (by decide)

theorem hcardT141_11 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK141 ⟨11, by decide⟩ R141 hpxR141 hcardq141 (by decide)).symm

/-- **Cell (141, 11).** -/
theorem cell141_11 (e : List (ZMod 25)) (heK : charOK (basisAt rK141) e = true)
    (h : ↥(reps (⟨11, by decide⟩ : Fin 148))) :
    species (reps (⟨11, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK141 e (h : Coordinate 1) T141_11 i :=
  species_entry_eq_sum rK141 ⟨11, by decide⟩ e heK h T141_11 hfix141_11 hinj141_11 hcardT141_11
    (fun i => conj_mem_of_fixedPoints (reps ⟨11, by decide⟩) (reps rK141) (T141_11 i) (hfix141_11 i) h)

/-! ## Cell (141, 12): |T| = 5 -/

def T141_12list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0)]
def T141_12 : Fin 5 → Coordinate 1 := fun i => T141_12list.getD i.val (0,0,0,0,0)

theorem hfix141_12 : ∀ i, ((T141_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141) :=
  repsFix_of_siftB rK141 ⟨12, by decide⟩ T141_12 (by decide)

theorem hinj141_12 : Function.Injective
    (fun i => ((T141_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)) :=
  repsInj_of_reduceAux rK141 T141_12 (by decide)

theorem hcardT141_12 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK141 ⟨12, by decide⟩ R141 hpxR141 hcardq141 (by decide)).symm

/-- **Cell (141, 12).** -/
theorem cell141_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK141) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK141 e (h : Coordinate 1) T141_12 i :=
  species_entry_eq_sum rK141 ⟨12, by decide⟩ e heK h T141_12 hfix141_12 hinj141_12 hcardT141_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK141) (T141_12 i) (hfix141_12 i) h)

/-! ## Cell (141, 13): |T| = 5 -/

def T141_13list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0)]
def T141_13 : Fin 5 → Coordinate 1 := fun i => T141_13list.getD i.val (0,0,0,0,0)

theorem hfix141_13 : ∀ i, ((T141_13 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141) :=
  repsFix_of_siftB rK141 ⟨13, by decide⟩ T141_13 (by decide)

theorem hinj141_13 : Function.Injective
    (fun i => ((T141_13 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)) :=
  repsInj_of_reduceAux rK141 T141_13 (by decide)

theorem hcardT141_13 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK141 ⟨13, by decide⟩ R141 hpxR141 hcardq141 (by decide)).symm

/-- **Cell (141, 13).** -/
theorem cell141_13 (e : List (ZMod 25)) (heK : charOK (basisAt rK141) e = true)
    (h : ↥(reps (⟨13, by decide⟩ : Fin 148))) :
    species (reps (⟨13, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK141 e (h : Coordinate 1) T141_13 i :=
  species_entry_eq_sum rK141 ⟨13, by decide⟩ e heK h T141_13 hfix141_13 hinj141_13 hcardT141_13
    (fun i => conj_mem_of_fixedPoints (reps ⟨13, by decide⟩) (reps rK141) (T141_13 i) (hfix141_13 i) h)

/-! ## Cell (141, 14): |T| = 5 -/

def T141_14list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0)]
def T141_14 : Fin 5 → Coordinate 1 := fun i => T141_14list.getD i.val (0,0,0,0,0)

theorem hfix141_14 : ∀ i, ((T141_14 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141) :=
  repsFix_of_siftB rK141 ⟨14, by decide⟩ T141_14 (by decide)

theorem hinj141_14 : Function.Injective
    (fun i => ((T141_14 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)) :=
  repsInj_of_reduceAux rK141 T141_14 (by decide)

theorem hcardT141_14 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK141 ⟨14, by decide⟩ R141 hpxR141 hcardq141 (by decide)).symm

/-- **Cell (141, 14).** -/
theorem cell141_14 (e : List (ZMod 25)) (heK : charOK (basisAt rK141) e = true)
    (h : ↥(reps (⟨14, by decide⟩ : Fin 148))) :
    species (reps (⟨14, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK141 e (h : Coordinate 1) T141_14 i :=
  species_entry_eq_sum rK141 ⟨14, by decide⟩ e heK h T141_14 hfix141_14 hinj141_14 hcardT141_14
    (fun i => conj_mem_of_fixedPoints (reps ⟨14, by decide⟩) (reps rK141) (T141_14 i) (hfix141_14 i) h)

/-! ## Cell (141, 15): |T| = 5 -/

def T141_15list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0)]
def T141_15 : Fin 5 → Coordinate 1 := fun i => T141_15list.getD i.val (0,0,0,0,0)

theorem hfix141_15 : ∀ i, ((T141_15 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141) :=
  repsFix_of_siftB rK141 ⟨15, by decide⟩ T141_15 (by decide)

theorem hinj141_15 : Function.Injective
    (fun i => ((T141_15 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)) :=
  repsInj_of_reduceAux rK141 T141_15 (by decide)

theorem hcardT141_15 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK141 ⟨15, by decide⟩ R141 hpxR141 hcardq141 (by decide)).symm

/-- **Cell (141, 15).** -/
theorem cell141_15 (e : List (ZMod 25)) (heK : charOK (basisAt rK141) e = true)
    (h : ↥(reps (⟨15, by decide⟩ : Fin 148))) :
    species (reps (⟨15, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK141 e (h : Coordinate 1) T141_15 i :=
  species_entry_eq_sum rK141 ⟨15, by decide⟩ e heK h T141_15 hfix141_15 hinj141_15 hcardT141_15
    (fun i => conj_mem_of_fixedPoints (reps ⟨15, by decide⟩) (reps rK141) (T141_15 i) (hfix141_15 i) h)

/-! ## Cell (141, 16): |T| = 5 -/

def T141_16list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0)]
def T141_16 : Fin 5 → Coordinate 1 := fun i => T141_16list.getD i.val (0,0,0,0,0)

theorem hfix141_16 : ∀ i, ((T141_16 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141) :=
  repsFix_of_siftB rK141 ⟨16, by decide⟩ T141_16 (by decide)

theorem hinj141_16 : Function.Injective
    (fun i => ((T141_16 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)) :=
  repsInj_of_reduceAux rK141 T141_16 (by decide)

theorem hcardT141_16 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK141 ⟨16, by decide⟩ R141 hpxR141 hcardq141 (by decide)).symm

/-- **Cell (141, 16).** -/
theorem cell141_16 (e : List (ZMod 25)) (heK : charOK (basisAt rK141) e = true)
    (h : ↥(reps (⟨16, by decide⟩ : Fin 148))) :
    species (reps (⟨16, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK141 e (h : Coordinate 1) T141_16 i :=
  species_entry_eq_sum rK141 ⟨16, by decide⟩ e heK h T141_16 hfix141_16 hinj141_16 hcardT141_16
    (fun i => conj_mem_of_fixedPoints (reps ⟨16, by decide⟩) (reps rK141) (T141_16 i) (hfix141_16 i) h)

/-! ## Cell (141, 17): |T| = 5 -/

def T141_17list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0)]
def T141_17 : Fin 5 → Coordinate 1 := fun i => T141_17list.getD i.val (0,0,0,0,0)

theorem hfix141_17 : ∀ i, ((T141_17 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141) :=
  repsFix_of_siftB rK141 ⟨17, by decide⟩ T141_17 (by decide)

theorem hinj141_17 : Function.Injective
    (fun i => ((T141_17 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)) :=
  repsInj_of_reduceAux rK141 T141_17 (by decide)

theorem hcardT141_17 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK141 ⟨17, by decide⟩ R141 hpxR141 hcardq141 (by decide)).symm

/-- **Cell (141, 17).** -/
theorem cell141_17 (e : List (ZMod 25)) (heK : charOK (basisAt rK141) e = true)
    (h : ↥(reps (⟨17, by decide⟩ : Fin 148))) :
    species (reps (⟨17, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK141 e (h : Coordinate 1) T141_17 i :=
  species_entry_eq_sum rK141 ⟨17, by decide⟩ e heK h T141_17 hfix141_17 hinj141_17 hcardT141_17
    (fun i => conj_mem_of_fixedPoints (reps ⟨17, by decide⟩) (reps rK141) (T141_17 i) (hfix141_17 i) h)

/-! ## Cell (141, 18): |T| = 5 -/

def T141_18list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0)]
def T141_18 : Fin 5 → Coordinate 1 := fun i => T141_18list.getD i.val (0,0,0,0,0)

theorem hfix141_18 : ∀ i, ((T141_18 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141) :=
  repsFix_of_siftB rK141 ⟨18, by decide⟩ T141_18 (by decide)

theorem hinj141_18 : Function.Injective
    (fun i => ((T141_18 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)) :=
  repsInj_of_reduceAux rK141 T141_18 (by decide)

theorem hcardT141_18 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK141 ⟨18, by decide⟩ R141 hpxR141 hcardq141 (by decide)).symm

/-- **Cell (141, 18).** -/
theorem cell141_18 (e : List (ZMod 25)) (heK : charOK (basisAt rK141) e = true)
    (h : ↥(reps (⟨18, by decide⟩ : Fin 148))) :
    species (reps (⟨18, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK141 e (h : Coordinate 1) T141_18 i :=
  species_entry_eq_sum rK141 ⟨18, by decide⟩ e heK h T141_18 hfix141_18 hinj141_18 hcardT141_18
    (fun i => conj_mem_of_fixedPoints (reps ⟨18, by decide⟩) (reps rK141) (T141_18 i) (hfix141_18 i) h)

/-! ## Cell (141, 19): |T| = 5 -/

def T141_19list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0)]
def T141_19 : Fin 5 → Coordinate 1 := fun i => T141_19list.getD i.val (0,0,0,0,0)

theorem hfix141_19 : ∀ i, ((T141_19 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141) :=
  repsFix_of_siftB rK141 ⟨19, by decide⟩ T141_19 (by decide)

theorem hinj141_19 : Function.Injective
    (fun i => ((T141_19 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)) :=
  repsInj_of_reduceAux rK141 T141_19 (by decide)

theorem hcardT141_19 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK141 ⟨19, by decide⟩ R141 hpxR141 hcardq141 (by decide)).symm

/-- **Cell (141, 19).** -/
theorem cell141_19 (e : List (ZMod 25)) (heK : charOK (basisAt rK141) e = true)
    (h : ↥(reps (⟨19, by decide⟩ : Fin 148))) :
    species (reps (⟨19, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK141 e (h : Coordinate 1) T141_19 i :=
  species_entry_eq_sum rK141 ⟨19, by decide⟩ e heK h T141_19 hfix141_19 hinj141_19 hcardT141_19
    (fun i => conj_mem_of_fixedPoints (reps ⟨19, by decide⟩) (reps rK141) (T141_19 i) (hfix141_19 i) h)

/-! ## Cell (141, 20): |T| = 5 -/

def T141_20list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0)]
def T141_20 : Fin 5 → Coordinate 1 := fun i => T141_20list.getD i.val (0,0,0,0,0)

theorem hfix141_20 : ∀ i, ((T141_20 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141) :=
  repsFix_of_siftB rK141 ⟨20, by decide⟩ T141_20 (by decide)

theorem hinj141_20 : Function.Injective
    (fun i => ((T141_20 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)) :=
  repsInj_of_reduceAux rK141 T141_20 (by decide)

theorem hcardT141_20 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK141 ⟨20, by decide⟩ R141 hpxR141 hcardq141 (by decide)).symm

/-- **Cell (141, 20).** -/
theorem cell141_20 (e : List (ZMod 25)) (heK : charOK (basisAt rK141) e = true)
    (h : ↥(reps (⟨20, by decide⟩ : Fin 148))) :
    species (reps (⟨20, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK141 e (h : Coordinate 1) T141_20 i :=
  species_entry_eq_sum rK141 ⟨20, by decide⟩ e heK h T141_20 hfix141_20 hinj141_20 hcardT141_20
    (fun i => conj_mem_of_fixedPoints (reps ⟨20, by decide⟩) (reps rK141) (T141_20 i) (hfix141_20 i) h)

/-! ## Cell (141, 21): |T| = 5 -/

def T141_21list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0)]
def T141_21 : Fin 5 → Coordinate 1 := fun i => T141_21list.getD i.val (0,0,0,0,0)

theorem hfix141_21 : ∀ i, ((T141_21 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141) :=
  repsFix_of_siftB rK141 ⟨21, by decide⟩ T141_21 (by decide)

theorem hinj141_21 : Function.Injective
    (fun i => ((T141_21 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)) :=
  repsInj_of_reduceAux rK141 T141_21 (by decide)

theorem hcardT141_21 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK141 ⟨21, by decide⟩ R141 hpxR141 hcardq141 (by decide)).symm

/-- **Cell (141, 21).** -/
theorem cell141_21 (e : List (ZMod 25)) (heK : charOK (basisAt rK141) e = true)
    (h : ↥(reps (⟨21, by decide⟩ : Fin 148))) :
    species (reps (⟨21, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK141 e (h : Coordinate 1) T141_21 i :=
  species_entry_eq_sum rK141 ⟨21, by decide⟩ e heK h T141_21 hfix141_21 hinj141_21 hcardT141_21
    (fun i => conj_mem_of_fixedPoints (reps ⟨21, by decide⟩) (reps rK141) (T141_21 i) (hfix141_21 i) h)

/-! ## Cell (141, 22): |T| = 5 -/

def T141_22list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0)]
def T141_22 : Fin 5 → Coordinate 1 := fun i => T141_22list.getD i.val (0,0,0,0,0)

theorem hfix141_22 : ∀ i, ((T141_22 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141) :=
  repsFix_of_siftB rK141 ⟨22, by decide⟩ T141_22 (by decide)

theorem hinj141_22 : Function.Injective
    (fun i => ((T141_22 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)) :=
  repsInj_of_reduceAux rK141 T141_22 (by decide)

theorem hcardT141_22 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK141 ⟨22, by decide⟩ R141 hpxR141 hcardq141 (by decide)).symm

/-- **Cell (141, 22).** -/
theorem cell141_22 (e : List (ZMod 25)) (heK : charOK (basisAt rK141) e = true)
    (h : ↥(reps (⟨22, by decide⟩ : Fin 148))) :
    species (reps (⟨22, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK141 e (h : Coordinate 1) T141_22 i :=
  species_entry_eq_sum rK141 ⟨22, by decide⟩ e heK h T141_22 hfix141_22 hinj141_22 hcardT141_22
    (fun i => conj_mem_of_fixedPoints (reps ⟨22, by decide⟩) (reps rK141) (T141_22 i) (hfix141_22 i) h)

/-! ## Cell (141, 23): |T| = 5 -/

def T141_23list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0)]
def T141_23 : Fin 5 → Coordinate 1 := fun i => T141_23list.getD i.val (0,0,0,0,0)

theorem hfix141_23 : ∀ i, ((T141_23 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141) :=
  repsFix_of_siftB rK141 ⟨23, by decide⟩ T141_23 (by decide)

theorem hinj141_23 : Function.Injective
    (fun i => ((T141_23 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)) :=
  repsInj_of_reduceAux rK141 T141_23 (by decide)

theorem hcardT141_23 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK141 ⟨23, by decide⟩ R141 hpxR141 hcardq141 (by decide)).symm

/-- **Cell (141, 23).** -/
theorem cell141_23 (e : List (ZMod 25)) (heK : charOK (basisAt rK141) e = true)
    (h : ↥(reps (⟨23, by decide⟩ : Fin 148))) :
    species (reps (⟨23, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK141 e (h : Coordinate 1) T141_23 i :=
  species_entry_eq_sum rK141 ⟨23, by decide⟩ e heK h T141_23 hfix141_23 hinj141_23 hcardT141_23
    (fun i => conj_mem_of_fixedPoints (reps ⟨23, by decide⟩) (reps rK141) (T141_23 i) (hfix141_23 i) h)

/-! ## Cell (141, 24): |T| = 5 -/

def T141_24list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0)]
def T141_24 : Fin 5 → Coordinate 1 := fun i => T141_24list.getD i.val (0,0,0,0,0)

theorem hfix141_24 : ∀ i, ((T141_24 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141) :=
  repsFix_of_siftB rK141 ⟨24, by decide⟩ T141_24 (by decide)

theorem hinj141_24 : Function.Injective
    (fun i => ((T141_24 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)) :=
  repsInj_of_reduceAux rK141 T141_24 (by decide)

theorem hcardT141_24 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK141 ⟨24, by decide⟩ R141 hpxR141 hcardq141 (by decide)).symm

/-- **Cell (141, 24).** -/
theorem cell141_24 (e : List (ZMod 25)) (heK : charOK (basisAt rK141) e = true)
    (h : ↥(reps (⟨24, by decide⟩ : Fin 148))) :
    species (reps (⟨24, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK141 e (h : Coordinate 1) T141_24 i :=
  species_entry_eq_sum rK141 ⟨24, by decide⟩ e heK h T141_24 hfix141_24 hinj141_24 hcardT141_24
    (fun i => conj_mem_of_fixedPoints (reps ⟨24, by decide⟩) (reps rK141) (T141_24 i) (hfix141_24 i) h)

/-! ## Cell (141, 25): |T| = 5 -/

def T141_25list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0)]
def T141_25 : Fin 5 → Coordinate 1 := fun i => T141_25list.getD i.val (0,0,0,0,0)

theorem hfix141_25 : ∀ i, ((T141_25 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141) :=
  repsFix_of_siftB rK141 ⟨25, by decide⟩ T141_25 (by decide)

theorem hinj141_25 : Function.Injective
    (fun i => ((T141_25 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)) :=
  repsInj_of_reduceAux rK141 T141_25 (by decide)

theorem hcardT141_25 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK141 ⟨25, by decide⟩ R141 hpxR141 hcardq141 (by decide)).symm

/-- **Cell (141, 25).** -/
theorem cell141_25 (e : List (ZMod 25)) (heK : charOK (basisAt rK141) e = true)
    (h : ↥(reps (⟨25, by decide⟩ : Fin 148))) :
    species (reps (⟨25, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK141 e (h : Coordinate 1) T141_25 i :=
  species_entry_eq_sum rK141 ⟨25, by decide⟩ e heK h T141_25 hfix141_25 hinj141_25 hcardT141_25
    (fun i => conj_mem_of_fixedPoints (reps ⟨25, by decide⟩) (reps rK141) (T141_25 i) (hfix141_25 i) h)

/-! ## Cell (141, 26): |T| = 5 -/

def T141_26list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0)]
def T141_26 : Fin 5 → Coordinate 1 := fun i => T141_26list.getD i.val (0,0,0,0,0)

theorem hfix141_26 : ∀ i, ((T141_26 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141) :=
  repsFix_of_siftB rK141 ⟨26, by decide⟩ T141_26 (by decide)

theorem hinj141_26 : Function.Injective
    (fun i => ((T141_26 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)) :=
  repsInj_of_reduceAux rK141 T141_26 (by decide)

theorem hcardT141_26 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK141 ⟨26, by decide⟩ R141 hpxR141 hcardq141 (by decide)).symm

/-- **Cell (141, 26).** -/
theorem cell141_26 (e : List (ZMod 25)) (heK : charOK (basisAt rK141) e = true)
    (h : ↥(reps (⟨26, by decide⟩ : Fin 148))) :
    species (reps (⟨26, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK141 e (h : Coordinate 1) T141_26 i :=
  species_entry_eq_sum rK141 ⟨26, by decide⟩ e heK h T141_26 hfix141_26 hinj141_26 hcardT141_26
    (fun i => conj_mem_of_fixedPoints (reps ⟨26, by decide⟩) (reps rK141) (T141_26 i) (hfix141_26 i) h)

/-! ## Cell (141, 27): |T| = 5 -/

def T141_27list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0)]
def T141_27 : Fin 5 → Coordinate 1 := fun i => T141_27list.getD i.val (0,0,0,0,0)

theorem hfix141_27 : ∀ i, ((T141_27 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141) :=
  repsFix_of_siftB rK141 ⟨27, by decide⟩ T141_27 (by decide)

theorem hinj141_27 : Function.Injective
    (fun i => ((T141_27 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)) :=
  repsInj_of_reduceAux rK141 T141_27 (by decide)

theorem hcardT141_27 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK141 ⟨27, by decide⟩ R141 hpxR141 hcardq141 (by decide)).symm

/-- **Cell (141, 27).** -/
theorem cell141_27 (e : List (ZMod 25)) (heK : charOK (basisAt rK141) e = true)
    (h : ↥(reps (⟨27, by decide⟩ : Fin 148))) :
    species (reps (⟨27, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK141 e (h : Coordinate 1) T141_27 i :=
  species_entry_eq_sum rK141 ⟨27, by decide⟩ e heK h T141_27 hfix141_27 hinj141_27 hcardT141_27
    (fun i => conj_mem_of_fixedPoints (reps ⟨27, by decide⟩) (reps rK141) (T141_27 i) (hfix141_27 i) h)

/-! ## Cell (141, 53): |T| = 5 -/

def T141_53list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0)]
def T141_53 : Fin 5 → Coordinate 1 := fun i => T141_53list.getD i.val (0,0,0,0,0)

theorem hfix141_53 : ∀ i, ((T141_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141) :=
  repsFix_of_siftB rK141 ⟨53, by decide⟩ T141_53 (by decide)

theorem hinj141_53 : Function.Injective
    (fun i => ((T141_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)) :=
  repsInj_of_reduceAux rK141 T141_53 (by decide)

theorem hcardT141_53 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK141 ⟨53, by decide⟩ R141 hpxR141 hcardq141 (by decide)).symm

/-- **Cell (141, 53).** -/
theorem cell141_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK141) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK141 e (h : Coordinate 1) T141_53 i :=
  species_entry_eq_sum rK141 ⟨53, by decide⟩ e heK h T141_53 hfix141_53 hinj141_53 hcardT141_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK141) (T141_53 i) (hfix141_53 i) h)

/-! ## Cell (141, 54): |T| = 5 -/

def T141_54list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0)]
def T141_54 : Fin 5 → Coordinate 1 := fun i => T141_54list.getD i.val (0,0,0,0,0)

theorem hfix141_54 : ∀ i, ((T141_54 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141) :=
  repsFix_of_siftB rK141 ⟨54, by decide⟩ T141_54 (by decide)

theorem hinj141_54 : Function.Injective
    (fun i => ((T141_54 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)) :=
  repsInj_of_reduceAux rK141 T141_54 (by decide)

theorem hcardT141_54 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK141 ⟨54, by decide⟩ R141 hpxR141 hcardq141 (by decide)).symm

/-- **Cell (141, 54).** -/
theorem cell141_54 (e : List (ZMod 25)) (heK : charOK (basisAt rK141) e = true)
    (h : ↥(reps (⟨54, by decide⟩ : Fin 148))) :
    species (reps (⟨54, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK141 e (h : Coordinate 1) T141_54 i :=
  species_entry_eq_sum rK141 ⟨54, by decide⟩ e heK h T141_54 hfix141_54 hinj141_54 hcardT141_54
    (fun i => conj_mem_of_fixedPoints (reps ⟨54, by decide⟩) (reps rK141) (T141_54 i) (hfix141_54 i) h)

/-! ## Cell (141, 80): |T| = 5 -/

def T141_80list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0)]
def T141_80 : Fin 5 → Coordinate 1 := fun i => T141_80list.getD i.val (0,0,0,0,0)

theorem hfix141_80 : ∀ i, ((T141_80 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141) :=
  repsFix_of_siftB rK141 ⟨80, by decide⟩ T141_80 (by decide)

theorem hinj141_80 : Function.Injective
    (fun i => ((T141_80 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)) :=
  repsInj_of_reduceAux rK141 T141_80 (by decide)

theorem hcardT141_80 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK141 ⟨80, by decide⟩ R141 hpxR141 hcardq141 (by decide)).symm

/-- **Cell (141, 80).** -/
theorem cell141_80 (e : List (ZMod 25)) (heK : charOK (basisAt rK141) e = true)
    (h : ↥(reps (⟨80, by decide⟩ : Fin 148))) :
    species (reps (⟨80, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK141 e (h : Coordinate 1) T141_80 i :=
  species_entry_eq_sum rK141 ⟨80, by decide⟩ e heK h T141_80 hfix141_80 hinj141_80 hcardT141_80
    (fun i => conj_mem_of_fixedPoints (reps ⟨80, by decide⟩) (reps rK141) (T141_80 i) (hfix141_80 i) h)

/-! ## Cell (141, 81): |T| = 5 -/

def T141_81list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0)]
def T141_81 : Fin 5 → Coordinate 1 := fun i => T141_81list.getD i.val (0,0,0,0,0)

theorem hfix141_81 : ∀ i, ((T141_81 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141) :=
  repsFix_of_siftB rK141 ⟨81, by decide⟩ T141_81 (by decide)

theorem hinj141_81 : Function.Injective
    (fun i => ((T141_81 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)) :=
  repsInj_of_reduceAux rK141 T141_81 (by decide)

theorem hcardT141_81 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK141 ⟨81, by decide⟩ R141 hpxR141 hcardq141 (by decide)).symm

/-- **Cell (141, 81).** -/
theorem cell141_81 (e : List (ZMod 25)) (heK : charOK (basisAt rK141) e = true)
    (h : ↥(reps (⟨81, by decide⟩ : Fin 148))) :
    species (reps (⟨81, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK141 e (h : Coordinate 1) T141_81 i :=
  species_entry_eq_sum rK141 ⟨81, by decide⟩ e heK h T141_81 hfix141_81 hinj141_81 hcardT141_81
    (fun i => conj_mem_of_fixedPoints (reps ⟨81, by decide⟩) (reps rK141) (T141_81 i) (hfix141_81 i) h)

/-! ## Cell (141, 82): |T| = 5 -/

def T141_82list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0)]
def T141_82 : Fin 5 → Coordinate 1 := fun i => T141_82list.getD i.val (0,0,0,0,0)

theorem hfix141_82 : ∀ i, ((T141_82 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141) :=
  repsFix_of_siftB rK141 ⟨82, by decide⟩ T141_82 (by decide)

theorem hinj141_82 : Function.Injective
    (fun i => ((T141_82 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)) :=
  repsInj_of_reduceAux rK141 T141_82 (by decide)

theorem hcardT141_82 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK141 ⟨82, by decide⟩ R141 hpxR141 hcardq141 (by decide)).symm

/-- **Cell (141, 82).** -/
theorem cell141_82 (e : List (ZMod 25)) (heK : charOK (basisAt rK141) e = true)
    (h : ↥(reps (⟨82, by decide⟩ : Fin 148))) :
    species (reps (⟨82, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK141 e (h : Coordinate 1) T141_82 i :=
  species_entry_eq_sum rK141 ⟨82, by decide⟩ e heK h T141_82 hfix141_82 hinj141_82 hcardT141_82
    (fun i => conj_mem_of_fixedPoints (reps ⟨82, by decide⟩) (reps rK141) (T141_82 i) (hfix141_82 i) h)

/-! ## Cell (141, 83): |T| = 5 -/

def T141_83list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0)]
def T141_83 : Fin 5 → Coordinate 1 := fun i => T141_83list.getD i.val (0,0,0,0,0)

theorem hfix141_83 : ∀ i, ((T141_83 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141) :=
  repsFix_of_siftB rK141 ⟨83, by decide⟩ T141_83 (by decide)

theorem hinj141_83 : Function.Injective
    (fun i => ((T141_83 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)) :=
  repsInj_of_reduceAux rK141 T141_83 (by decide)

theorem hcardT141_83 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK141 ⟨83, by decide⟩ R141 hpxR141 hcardq141 (by decide)).symm

/-- **Cell (141, 83).** -/
theorem cell141_83 (e : List (ZMod 25)) (heK : charOK (basisAt rK141) e = true)
    (h : ↥(reps (⟨83, by decide⟩ : Fin 148))) :
    species (reps (⟨83, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK141 e (h : Coordinate 1) T141_83 i :=
  species_entry_eq_sum rK141 ⟨83, by decide⟩ e heK h T141_83 hfix141_83 hinj141_83 hcardT141_83
    (fun i => conj_mem_of_fixedPoints (reps ⟨83, by decide⟩) (reps rK141) (T141_83 i) (hfix141_83 i) h)

/-! ## Cell (141, 84): |T| = 5 -/

def T141_84list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0)]
def T141_84 : Fin 5 → Coordinate 1 := fun i => T141_84list.getD i.val (0,0,0,0,0)

theorem hfix141_84 : ∀ i, ((T141_84 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141) :=
  repsFix_of_siftB rK141 ⟨84, by decide⟩ T141_84 (by decide)

theorem hinj141_84 : Function.Injective
    (fun i => ((T141_84 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)) :=
  repsInj_of_reduceAux rK141 T141_84 (by decide)

theorem hcardT141_84 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK141 ⟨84, by decide⟩ R141 hpxR141 hcardq141 (by decide)).symm

/-- **Cell (141, 84).** -/
theorem cell141_84 (e : List (ZMod 25)) (heK : charOK (basisAt rK141) e = true)
    (h : ↥(reps (⟨84, by decide⟩ : Fin 148))) :
    species (reps (⟨84, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK141 e (h : Coordinate 1) T141_84 i :=
  species_entry_eq_sum rK141 ⟨84, by decide⟩ e heK h T141_84 hfix141_84 hinj141_84 hcardT141_84
    (fun i => conj_mem_of_fixedPoints (reps ⟨84, by decide⟩) (reps rK141) (T141_84 i) (hfix141_84 i) h)

/-! ## Cell (141, 85): |T| = 5 -/

def T141_85list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0)]
def T141_85 : Fin 5 → Coordinate 1 := fun i => T141_85list.getD i.val (0,0,0,0,0)

theorem hfix141_85 : ∀ i, ((T141_85 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141) :=
  repsFix_of_siftB rK141 ⟨85, by decide⟩ T141_85 (by decide)

theorem hinj141_85 : Function.Injective
    (fun i => ((T141_85 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)) :=
  repsInj_of_reduceAux rK141 T141_85 (by decide)

theorem hcardT141_85 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK141 ⟨85, by decide⟩ R141 hpxR141 hcardq141 (by decide)).symm

/-- **Cell (141, 85).** -/
theorem cell141_85 (e : List (ZMod 25)) (heK : charOK (basisAt rK141) e = true)
    (h : ↥(reps (⟨85, by decide⟩ : Fin 148))) :
    species (reps (⟨85, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK141 e (h : Coordinate 1) T141_85 i :=
  species_entry_eq_sum rK141 ⟨85, by decide⟩ e heK h T141_85 hfix141_85 hinj141_85 hcardT141_85
    (fun i => conj_mem_of_fixedPoints (reps ⟨85, by decide⟩) (reps rK141) (T141_85 i) (hfix141_85 i) h)

/-! ## Cell (141, 86): |T| = 5 -/

def T141_86list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0)]
def T141_86 : Fin 5 → Coordinate 1 := fun i => T141_86list.getD i.val (0,0,0,0,0)

theorem hfix141_86 : ∀ i, ((T141_86 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141) :=
  repsFix_of_siftB rK141 ⟨86, by decide⟩ T141_86 (by decide)

theorem hinj141_86 : Function.Injective
    (fun i => ((T141_86 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)) :=
  repsInj_of_reduceAux rK141 T141_86 (by decide)

theorem hcardT141_86 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK141 ⟨86, by decide⟩ R141 hpxR141 hcardq141 (by decide)).symm

/-- **Cell (141, 86).** -/
theorem cell141_86 (e : List (ZMod 25)) (heK : charOK (basisAt rK141) e = true)
    (h : ↥(reps (⟨86, by decide⟩ : Fin 148))) :
    species (reps (⟨86, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK141 e (h : Coordinate 1) T141_86 i :=
  species_entry_eq_sum rK141 ⟨86, by decide⟩ e heK h T141_86 hfix141_86 hinj141_86 hcardT141_86
    (fun i => conj_mem_of_fixedPoints (reps ⟨86, by decide⟩) (reps rK141) (T141_86 i) (hfix141_86 i) h)

/-! ## Cell (141, 87): |T| = 5 -/

def T141_87list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0)]
def T141_87 : Fin 5 → Coordinate 1 := fun i => T141_87list.getD i.val (0,0,0,0,0)

theorem hfix141_87 : ∀ i, ((T141_87 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141) :=
  repsFix_of_siftB rK141 ⟨87, by decide⟩ T141_87 (by decide)

theorem hinj141_87 : Function.Injective
    (fun i => ((T141_87 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)) :=
  repsInj_of_reduceAux rK141 T141_87 (by decide)

theorem hcardT141_87 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK141 ⟨87, by decide⟩ R141 hpxR141 hcardq141 (by decide)).symm

/-- **Cell (141, 87).** -/
theorem cell141_87 (e : List (ZMod 25)) (heK : charOK (basisAt rK141) e = true)
    (h : ↥(reps (⟨87, by decide⟩ : Fin 148))) :
    species (reps (⟨87, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK141 e (h : Coordinate 1) T141_87 i :=
  species_entry_eq_sum rK141 ⟨87, by decide⟩ e heK h T141_87 hfix141_87 hinj141_87 hcardT141_87
    (fun i => conj_mem_of_fixedPoints (reps ⟨87, by decide⟩) (reps rK141) (T141_87 i) (hfix141_87 i) h)

/-! ## Cell (141, 88): |T| = 5 -/

def T141_88list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0)]
def T141_88 : Fin 5 → Coordinate 1 := fun i => T141_88list.getD i.val (0,0,0,0,0)

theorem hfix141_88 : ∀ i, ((T141_88 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141) :=
  repsFix_of_siftB rK141 ⟨88, by decide⟩ T141_88 (by decide)

theorem hinj141_88 : Function.Injective
    (fun i => ((T141_88 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)) :=
  repsInj_of_reduceAux rK141 T141_88 (by decide)

theorem hcardT141_88 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK141 ⟨88, by decide⟩ R141 hpxR141 hcardq141 (by decide)).symm

/-- **Cell (141, 88).** -/
theorem cell141_88 (e : List (ZMod 25)) (heK : charOK (basisAt rK141) e = true)
    (h : ↥(reps (⟨88, by decide⟩ : Fin 148))) :
    species (reps (⟨88, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK141 e (h : Coordinate 1) T141_88 i :=
  species_entry_eq_sum rK141 ⟨88, by decide⟩ e heK h T141_88 hfix141_88 hinj141_88 hcardT141_88
    (fun i => conj_mem_of_fixedPoints (reps ⟨88, by decide⟩) (reps rK141) (T141_88 i) (hfix141_88 i) h)

/-! ## Cell (141, 89): |T| = 5 -/

def T141_89list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0)]
def T141_89 : Fin 5 → Coordinate 1 := fun i => T141_89list.getD i.val (0,0,0,0,0)

theorem hfix141_89 : ∀ i, ((T141_89 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141) :=
  repsFix_of_siftB rK141 ⟨89, by decide⟩ T141_89 (by decide)

theorem hinj141_89 : Function.Injective
    (fun i => ((T141_89 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)) :=
  repsInj_of_reduceAux rK141 T141_89 (by decide)

theorem hcardT141_89 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK141 ⟨89, by decide⟩ R141 hpxR141 hcardq141 (by decide)).symm

/-- **Cell (141, 89).** -/
theorem cell141_89 (e : List (ZMod 25)) (heK : charOK (basisAt rK141) e = true)
    (h : ↥(reps (⟨89, by decide⟩ : Fin 148))) :
    species (reps (⟨89, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK141 e (h : Coordinate 1) T141_89 i :=
  species_entry_eq_sum rK141 ⟨89, by decide⟩ e heK h T141_89 hfix141_89 hinj141_89 hcardT141_89
    (fun i => conj_mem_of_fixedPoints (reps ⟨89, by decide⟩) (reps rK141) (T141_89 i) (hfix141_89 i) h)

/-! ## Cell (141, 115): |T| = 5 -/

def T141_115list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0)]
def T141_115 : Fin 5 → Coordinate 1 := fun i => T141_115list.getD i.val (0,0,0,0,0)

theorem hfix141_115 : ∀ i, ((T141_115 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141) :=
  repsFix_of_siftB rK141 ⟨115, by decide⟩ T141_115 (by decide)

theorem hinj141_115 : Function.Injective
    (fun i => ((T141_115 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)) :=
  repsInj_of_reduceAux rK141 T141_115 (by decide)

theorem hcardT141_115 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK141 ⟨115, by decide⟩ R141 hpxR141 hcardq141 (by decide)).symm

/-- **Cell (141, 115).** -/
theorem cell141_115 (e : List (ZMod 25)) (heK : charOK (basisAt rK141) e = true)
    (h : ↥(reps (⟨115, by decide⟩ : Fin 148))) :
    species (reps (⟨115, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK141 e (h : Coordinate 1) T141_115 i :=
  species_entry_eq_sum rK141 ⟨115, by decide⟩ e heK h T141_115 hfix141_115 hinj141_115 hcardT141_115
    (fun i => conj_mem_of_fixedPoints (reps ⟨115, by decide⟩) (reps rK141) (T141_115 i) (hfix141_115 i) h)

/-! ## Cell (141, 141): |T| = 5 -/

def T141_141list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0)]
def T141_141 : Fin 5 → Coordinate 1 := fun i => T141_141list.getD i.val (0,0,0,0,0)

theorem hfix141_141 : ∀ i, ((T141_141 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141) :=
  repsFix_of_siftB rK141 ⟨141, by decide⟩ T141_141 (by decide)

theorem hinj141_141 : Function.Injective
    (fun i => ((T141_141 i : Coordinate 1) : Coordinate 1 ⧸ reps rK141)) :=
  repsInj_of_reduceAux rK141 T141_141 (by decide)

theorem hcardT141_141 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK141 ⟨141, by decide⟩ R141 hpxR141 hcardq141 (by decide)).symm

/-- **Cell (141, 141).** -/
theorem cell141_141 (e : List (ZMod 25)) (heK : charOK (basisAt rK141) e = true)
    (h : ↥(reps (⟨141, by decide⟩ : Fin 148))) :
    species (reps (⟨141, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK141 e (h : Coordinate 1) T141_141 i :=
  species_entry_eq_sum rK141 ⟨141, by decide⟩ e heK h T141_141 hfix141_141 hinj141_141 hcardT141_141
    (fun i => conj_mem_of_fixedPoints (reps ⟨141, by decide⟩) (reps rK141) (T141_141 i) (hfix141_141 i) h)

namespace Q2

def R141_2 : Fin 5 → Coordinate 2 := fun i => R141list.getD i.val (0,0,0,0,0)
theorem hpxR141_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK141) (R141_2 i)) := by decide
theorem hcardq141_2 : Nat.card (Coordinate 2 ⧸ reps rK141) = 5 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (141, 0) twin -/

def T141_0_2 : Fin 5 → Coordinate 2 := fun i => T141_0list.getD i.val (0,0,0,0,0)

theorem hfix141_0_2 : ∀ i, ((T141_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141) :=
  repsFix_of_siftB2 rK141 ⟨0, by decide⟩ T141_0_2 (by decide)

theorem hinj141_0_2 : Function.Injective
    (fun i => ((T141_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)) :=
  repsInj_of_reduceAux2 rK141 T141_0_2 (by decide)

theorem hcardT141_0_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK141 ⟨0, by decide⟩ R141_2 hpxR141_2 hcardq141_2 (by decide)).symm

/-- **Cell (141, 0) twin (q=2).** -/
theorem cell141_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK141) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec2 rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK141 e (h : Coordinate 2) T141_0_2 i :=
  species_entry_eq_sum rK141 ⟨0, by decide⟩ e heK h T141_0_2 hfix141_0_2 hinj141_0_2 hcardT141_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK141) (T141_0_2 i) (hfix141_0_2 i) h)

/-! ### Cell (141, 1) twin -/

def T141_1_2 : Fin 5 → Coordinate 2 := fun i => T141_1list.getD i.val (0,0,0,0,0)

theorem hfix141_1_2 : ∀ i, ((T141_1_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141) :=
  repsFix_of_siftB2 rK141 ⟨1, by decide⟩ T141_1_2 (by decide)

theorem hinj141_1_2 : Function.Injective
    (fun i => ((T141_1_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)) :=
  repsInj_of_reduceAux2 rK141 T141_1_2 (by decide)

theorem hcardT141_1_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK141 ⟨1, by decide⟩ R141_2 hpxR141_2 hcardq141_2 (by decide)).symm

/-- **Cell (141, 1) twin (q=2).** -/
theorem cell141_1_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK141) e = true)
    (h : ↥(reps (⟨1, by decide⟩ : Fin 148))) :
    species (reps (⟨1, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec2 rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK141 e (h : Coordinate 2) T141_1_2 i :=
  species_entry_eq_sum rK141 ⟨1, by decide⟩ e heK h T141_1_2 hfix141_1_2 hinj141_1_2 hcardT141_1_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨1, by decide⟩) (reps rK141) (T141_1_2 i) (hfix141_1_2 i) h)

/-! ### Cell (141, 2) twin -/

def T141_2_2 : Fin 5 → Coordinate 2 := fun i => T141_2list.getD i.val (0,0,0,0,0)

theorem hfix141_2_2 : ∀ i, ((T141_2_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141) :=
  repsFix_of_siftB2 rK141 ⟨2, by decide⟩ T141_2_2 (by decide)

theorem hinj141_2_2 : Function.Injective
    (fun i => ((T141_2_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)) :=
  repsInj_of_reduceAux2 rK141 T141_2_2 (by decide)

theorem hcardT141_2_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK141 ⟨2, by decide⟩ R141_2 hpxR141_2 hcardq141_2 (by decide)).symm

/-- **Cell (141, 2) twin (q=2).** -/
theorem cell141_2_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK141) e = true)
    (h : ↥(reps (⟨2, by decide⟩ : Fin 148))) :
    species (reps (⟨2, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec2 rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK141 e (h : Coordinate 2) T141_2_2 i :=
  species_entry_eq_sum rK141 ⟨2, by decide⟩ e heK h T141_2_2 hfix141_2_2 hinj141_2_2 hcardT141_2_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨2, by decide⟩) (reps rK141) (T141_2_2 i) (hfix141_2_2 i) h)

/-! ### Cell (141, 3) twin -/

def T141_3_2 : Fin 5 → Coordinate 2 := fun i => T141_3list.getD i.val (0,0,0,0,0)

theorem hfix141_3_2 : ∀ i, ((T141_3_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141) :=
  repsFix_of_siftB2 rK141 ⟨3, by decide⟩ T141_3_2 (by decide)

theorem hinj141_3_2 : Function.Injective
    (fun i => ((T141_3_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)) :=
  repsInj_of_reduceAux2 rK141 T141_3_2 (by decide)

theorem hcardT141_3_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK141 ⟨3, by decide⟩ R141_2 hpxR141_2 hcardq141_2 (by decide)).symm

/-- **Cell (141, 3) twin (q=2).** -/
theorem cell141_3_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK141) e = true)
    (h : ↥(reps (⟨3, by decide⟩ : Fin 148))) :
    species (reps (⟨3, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec2 rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK141 e (h : Coordinate 2) T141_3_2 i :=
  species_entry_eq_sum rK141 ⟨3, by decide⟩ e heK h T141_3_2 hfix141_3_2 hinj141_3_2 hcardT141_3_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨3, by decide⟩) (reps rK141) (T141_3_2 i) (hfix141_3_2 i) h)

/-! ### Cell (141, 4) twin -/

def T141_4_2 : Fin 5 → Coordinate 2 := fun i => T141_4list.getD i.val (0,0,0,0,0)

theorem hfix141_4_2 : ∀ i, ((T141_4_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141) :=
  repsFix_of_siftB2 rK141 ⟨4, by decide⟩ T141_4_2 (by decide)

theorem hinj141_4_2 : Function.Injective
    (fun i => ((T141_4_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)) :=
  repsInj_of_reduceAux2 rK141 T141_4_2 (by decide)

theorem hcardT141_4_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK141 ⟨4, by decide⟩ R141_2 hpxR141_2 hcardq141_2 (by decide)).symm

/-- **Cell (141, 4) twin (q=2).** -/
theorem cell141_4_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK141) e = true)
    (h : ↥(reps (⟨4, by decide⟩ : Fin 148))) :
    species (reps (⟨4, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec2 rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK141 e (h : Coordinate 2) T141_4_2 i :=
  species_entry_eq_sum rK141 ⟨4, by decide⟩ e heK h T141_4_2 hfix141_4_2 hinj141_4_2 hcardT141_4_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨4, by decide⟩) (reps rK141) (T141_4_2 i) (hfix141_4_2 i) h)

/-! ### Cell (141, 5) twin -/

def T141_5_2 : Fin 5 → Coordinate 2 := fun i => T141_5list.getD i.val (0,0,0,0,0)

theorem hfix141_5_2 : ∀ i, ((T141_5_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141) :=
  repsFix_of_siftB2 rK141 ⟨5, by decide⟩ T141_5_2 (by decide)

theorem hinj141_5_2 : Function.Injective
    (fun i => ((T141_5_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)) :=
  repsInj_of_reduceAux2 rK141 T141_5_2 (by decide)

theorem hcardT141_5_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK141 ⟨5, by decide⟩ R141_2 hpxR141_2 hcardq141_2 (by decide)).symm

/-- **Cell (141, 5) twin (q=2).** -/
theorem cell141_5_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK141) e = true)
    (h : ↥(reps (⟨5, by decide⟩ : Fin 148))) :
    species (reps (⟨5, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec2 rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK141 e (h : Coordinate 2) T141_5_2 i :=
  species_entry_eq_sum rK141 ⟨5, by decide⟩ e heK h T141_5_2 hfix141_5_2 hinj141_5_2 hcardT141_5_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨5, by decide⟩) (reps rK141) (T141_5_2 i) (hfix141_5_2 i) h)

/-! ### Cell (141, 6) twin -/

def T141_6_2 : Fin 5 → Coordinate 2 := fun i => T141_6list.getD i.val (0,0,0,0,0)

theorem hfix141_6_2 : ∀ i, ((T141_6_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141) :=
  repsFix_of_siftB2 rK141 ⟨6, by decide⟩ T141_6_2 (by decide)

theorem hinj141_6_2 : Function.Injective
    (fun i => ((T141_6_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)) :=
  repsInj_of_reduceAux2 rK141 T141_6_2 (by decide)

theorem hcardT141_6_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK141 ⟨6, by decide⟩ R141_2 hpxR141_2 hcardq141_2 (by decide)).symm

/-- **Cell (141, 6) twin (q=2).** -/
theorem cell141_6_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK141) e = true)
    (h : ↥(reps (⟨6, by decide⟩ : Fin 148))) :
    species (reps (⟨6, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec2 rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK141 e (h : Coordinate 2) T141_6_2 i :=
  species_entry_eq_sum rK141 ⟨6, by decide⟩ e heK h T141_6_2 hfix141_6_2 hinj141_6_2 hcardT141_6_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨6, by decide⟩) (reps rK141) (T141_6_2 i) (hfix141_6_2 i) h)

/-! ### Cell (141, 7) twin -/

def T141_7_2 : Fin 5 → Coordinate 2 := fun i => T141_7list.getD i.val (0,0,0,0,0)

theorem hfix141_7_2 : ∀ i, ((T141_7_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141) :=
  repsFix_of_siftB2 rK141 ⟨7, by decide⟩ T141_7_2 (by decide)

theorem hinj141_7_2 : Function.Injective
    (fun i => ((T141_7_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)) :=
  repsInj_of_reduceAux2 rK141 T141_7_2 (by decide)

theorem hcardT141_7_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK141 ⟨7, by decide⟩ R141_2 hpxR141_2 hcardq141_2 (by decide)).symm

/-- **Cell (141, 7) twin (q=2).** -/
theorem cell141_7_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK141) e = true)
    (h : ↥(reps (⟨7, by decide⟩ : Fin 148))) :
    species (reps (⟨7, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec2 rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK141 e (h : Coordinate 2) T141_7_2 i :=
  species_entry_eq_sum rK141 ⟨7, by decide⟩ e heK h T141_7_2 hfix141_7_2 hinj141_7_2 hcardT141_7_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨7, by decide⟩) (reps rK141) (T141_7_2 i) (hfix141_7_2 i) h)

/-! ### Cell (141, 8) twin -/

def T141_8_2 : Fin 5 → Coordinate 2 := fun i => T141_8list.getD i.val (0,0,0,0,0)

theorem hfix141_8_2 : ∀ i, ((T141_8_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141) :=
  repsFix_of_siftB2 rK141 ⟨8, by decide⟩ T141_8_2 (by decide)

theorem hinj141_8_2 : Function.Injective
    (fun i => ((T141_8_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)) :=
  repsInj_of_reduceAux2 rK141 T141_8_2 (by decide)

theorem hcardT141_8_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK141 ⟨8, by decide⟩ R141_2 hpxR141_2 hcardq141_2 (by decide)).symm

/-- **Cell (141, 8) twin (q=2).** -/
theorem cell141_8_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK141) e = true)
    (h : ↥(reps (⟨8, by decide⟩ : Fin 148))) :
    species (reps (⟨8, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec2 rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK141 e (h : Coordinate 2) T141_8_2 i :=
  species_entry_eq_sum rK141 ⟨8, by decide⟩ e heK h T141_8_2 hfix141_8_2 hinj141_8_2 hcardT141_8_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨8, by decide⟩) (reps rK141) (T141_8_2 i) (hfix141_8_2 i) h)

/-! ### Cell (141, 9) twin -/

def T141_9_2 : Fin 5 → Coordinate 2 := fun i => T141_9list.getD i.val (0,0,0,0,0)

theorem hfix141_9_2 : ∀ i, ((T141_9_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141) :=
  repsFix_of_siftB2 rK141 ⟨9, by decide⟩ T141_9_2 (by decide)

theorem hinj141_9_2 : Function.Injective
    (fun i => ((T141_9_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)) :=
  repsInj_of_reduceAux2 rK141 T141_9_2 (by decide)

theorem hcardT141_9_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK141 ⟨9, by decide⟩ R141_2 hpxR141_2 hcardq141_2 (by decide)).symm

/-- **Cell (141, 9) twin (q=2).** -/
theorem cell141_9_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK141) e = true)
    (h : ↥(reps (⟨9, by decide⟩ : Fin 148))) :
    species (reps (⟨9, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec2 rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK141 e (h : Coordinate 2) T141_9_2 i :=
  species_entry_eq_sum rK141 ⟨9, by decide⟩ e heK h T141_9_2 hfix141_9_2 hinj141_9_2 hcardT141_9_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨9, by decide⟩) (reps rK141) (T141_9_2 i) (hfix141_9_2 i) h)

/-! ### Cell (141, 10) twin -/

def T141_10_2 : Fin 5 → Coordinate 2 := fun i => T141_10list.getD i.val (0,0,0,0,0)

theorem hfix141_10_2 : ∀ i, ((T141_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141) :=
  repsFix_of_siftB2 rK141 ⟨10, by decide⟩ T141_10_2 (by decide)

theorem hinj141_10_2 : Function.Injective
    (fun i => ((T141_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)) :=
  repsInj_of_reduceAux2 rK141 T141_10_2 (by decide)

theorem hcardT141_10_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK141 ⟨10, by decide⟩ R141_2 hpxR141_2 hcardq141_2 (by decide)).symm

/-- **Cell (141, 10) twin (q=2).** -/
theorem cell141_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK141) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec2 rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK141 e (h : Coordinate 2) T141_10_2 i :=
  species_entry_eq_sum rK141 ⟨10, by decide⟩ e heK h T141_10_2 hfix141_10_2 hinj141_10_2 hcardT141_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK141) (T141_10_2 i) (hfix141_10_2 i) h)

/-! ### Cell (141, 11) twin -/

def T141_11_2 : Fin 5 → Coordinate 2 := fun i => T141_11list.getD i.val (0,0,0,0,0)

theorem hfix141_11_2 : ∀ i, ((T141_11_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141) :=
  repsFix_of_siftB2 rK141 ⟨11, by decide⟩ T141_11_2 (by decide)

theorem hinj141_11_2 : Function.Injective
    (fun i => ((T141_11_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)) :=
  repsInj_of_reduceAux2 rK141 T141_11_2 (by decide)

theorem hcardT141_11_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK141 ⟨11, by decide⟩ R141_2 hpxR141_2 hcardq141_2 (by decide)).symm

/-- **Cell (141, 11) twin (q=2).** -/
theorem cell141_11_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK141) e = true)
    (h : ↥(reps (⟨11, by decide⟩ : Fin 148))) :
    species (reps (⟨11, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec2 rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK141 e (h : Coordinate 2) T141_11_2 i :=
  species_entry_eq_sum rK141 ⟨11, by decide⟩ e heK h T141_11_2 hfix141_11_2 hinj141_11_2 hcardT141_11_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨11, by decide⟩) (reps rK141) (T141_11_2 i) (hfix141_11_2 i) h)

/-! ### Cell (141, 12) twin -/

def T141_12_2 : Fin 5 → Coordinate 2 := fun i => T141_12list.getD i.val (0,0,0,0,0)

theorem hfix141_12_2 : ∀ i, ((T141_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141) :=
  repsFix_of_siftB2 rK141 ⟨12, by decide⟩ T141_12_2 (by decide)

theorem hinj141_12_2 : Function.Injective
    (fun i => ((T141_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)) :=
  repsInj_of_reduceAux2 rK141 T141_12_2 (by decide)

theorem hcardT141_12_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK141 ⟨12, by decide⟩ R141_2 hpxR141_2 hcardq141_2 (by decide)).symm

/-- **Cell (141, 12) twin (q=2).** -/
theorem cell141_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK141) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec2 rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK141 e (h : Coordinate 2) T141_12_2 i :=
  species_entry_eq_sum rK141 ⟨12, by decide⟩ e heK h T141_12_2 hfix141_12_2 hinj141_12_2 hcardT141_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK141) (T141_12_2 i) (hfix141_12_2 i) h)

/-! ### Cell (141, 13) twin -/

def T141_13_2 : Fin 5 → Coordinate 2 := fun i => T141_13list.getD i.val (0,0,0,0,0)

theorem hfix141_13_2 : ∀ i, ((T141_13_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141) :=
  repsFix_of_siftB2 rK141 ⟨13, by decide⟩ T141_13_2 (by decide)

theorem hinj141_13_2 : Function.Injective
    (fun i => ((T141_13_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)) :=
  repsInj_of_reduceAux2 rK141 T141_13_2 (by decide)

theorem hcardT141_13_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK141 ⟨13, by decide⟩ R141_2 hpxR141_2 hcardq141_2 (by decide)).symm

/-- **Cell (141, 13) twin (q=2).** -/
theorem cell141_13_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK141) e = true)
    (h : ↥(reps (⟨13, by decide⟩ : Fin 148))) :
    species (reps (⟨13, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec2 rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK141 e (h : Coordinate 2) T141_13_2 i :=
  species_entry_eq_sum rK141 ⟨13, by decide⟩ e heK h T141_13_2 hfix141_13_2 hinj141_13_2 hcardT141_13_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨13, by decide⟩) (reps rK141) (T141_13_2 i) (hfix141_13_2 i) h)

/-! ### Cell (141, 14) twin -/

def T141_14_2 : Fin 5 → Coordinate 2 := fun i => T141_14list.getD i.val (0,0,0,0,0)

theorem hfix141_14_2 : ∀ i, ((T141_14_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141) :=
  repsFix_of_siftB2 rK141 ⟨14, by decide⟩ T141_14_2 (by decide)

theorem hinj141_14_2 : Function.Injective
    (fun i => ((T141_14_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)) :=
  repsInj_of_reduceAux2 rK141 T141_14_2 (by decide)

theorem hcardT141_14_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK141 ⟨14, by decide⟩ R141_2 hpxR141_2 hcardq141_2 (by decide)).symm

/-- **Cell (141, 14) twin (q=2).** -/
theorem cell141_14_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK141) e = true)
    (h : ↥(reps (⟨14, by decide⟩ : Fin 148))) :
    species (reps (⟨14, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec2 rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK141 e (h : Coordinate 2) T141_14_2 i :=
  species_entry_eq_sum rK141 ⟨14, by decide⟩ e heK h T141_14_2 hfix141_14_2 hinj141_14_2 hcardT141_14_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨14, by decide⟩) (reps rK141) (T141_14_2 i) (hfix141_14_2 i) h)

/-! ### Cell (141, 15) twin -/

def T141_15_2 : Fin 5 → Coordinate 2 := fun i => T141_15list.getD i.val (0,0,0,0,0)

theorem hfix141_15_2 : ∀ i, ((T141_15_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141) :=
  repsFix_of_siftB2 rK141 ⟨15, by decide⟩ T141_15_2 (by decide)

theorem hinj141_15_2 : Function.Injective
    (fun i => ((T141_15_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)) :=
  repsInj_of_reduceAux2 rK141 T141_15_2 (by decide)

theorem hcardT141_15_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK141 ⟨15, by decide⟩ R141_2 hpxR141_2 hcardq141_2 (by decide)).symm

/-- **Cell (141, 15) twin (q=2).** -/
theorem cell141_15_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK141) e = true)
    (h : ↥(reps (⟨15, by decide⟩ : Fin 148))) :
    species (reps (⟨15, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec2 rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK141 e (h : Coordinate 2) T141_15_2 i :=
  species_entry_eq_sum rK141 ⟨15, by decide⟩ e heK h T141_15_2 hfix141_15_2 hinj141_15_2 hcardT141_15_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨15, by decide⟩) (reps rK141) (T141_15_2 i) (hfix141_15_2 i) h)

/-! ### Cell (141, 16) twin -/

def T141_16_2 : Fin 5 → Coordinate 2 := fun i => T141_16list.getD i.val (0,0,0,0,0)

theorem hfix141_16_2 : ∀ i, ((T141_16_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141) :=
  repsFix_of_siftB2 rK141 ⟨16, by decide⟩ T141_16_2 (by decide)

theorem hinj141_16_2 : Function.Injective
    (fun i => ((T141_16_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)) :=
  repsInj_of_reduceAux2 rK141 T141_16_2 (by decide)

theorem hcardT141_16_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK141 ⟨16, by decide⟩ R141_2 hpxR141_2 hcardq141_2 (by decide)).symm

/-- **Cell (141, 16) twin (q=2).** -/
theorem cell141_16_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK141) e = true)
    (h : ↥(reps (⟨16, by decide⟩ : Fin 148))) :
    species (reps (⟨16, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec2 rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK141 e (h : Coordinate 2) T141_16_2 i :=
  species_entry_eq_sum rK141 ⟨16, by decide⟩ e heK h T141_16_2 hfix141_16_2 hinj141_16_2 hcardT141_16_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨16, by decide⟩) (reps rK141) (T141_16_2 i) (hfix141_16_2 i) h)

/-! ### Cell (141, 17) twin -/

def T141_17_2 : Fin 5 → Coordinate 2 := fun i => T141_17list.getD i.val (0,0,0,0,0)

theorem hfix141_17_2 : ∀ i, ((T141_17_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141) :=
  repsFix_of_siftB2 rK141 ⟨17, by decide⟩ T141_17_2 (by decide)

theorem hinj141_17_2 : Function.Injective
    (fun i => ((T141_17_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)) :=
  repsInj_of_reduceAux2 rK141 T141_17_2 (by decide)

theorem hcardT141_17_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK141 ⟨17, by decide⟩ R141_2 hpxR141_2 hcardq141_2 (by decide)).symm

/-- **Cell (141, 17) twin (q=2).** -/
theorem cell141_17_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK141) e = true)
    (h : ↥(reps (⟨17, by decide⟩ : Fin 148))) :
    species (reps (⟨17, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec2 rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK141 e (h : Coordinate 2) T141_17_2 i :=
  species_entry_eq_sum rK141 ⟨17, by decide⟩ e heK h T141_17_2 hfix141_17_2 hinj141_17_2 hcardT141_17_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨17, by decide⟩) (reps rK141) (T141_17_2 i) (hfix141_17_2 i) h)

/-! ### Cell (141, 18) twin -/

def T141_18_2 : Fin 5 → Coordinate 2 := fun i => T141_18list.getD i.val (0,0,0,0,0)

theorem hfix141_18_2 : ∀ i, ((T141_18_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141) :=
  repsFix_of_siftB2 rK141 ⟨18, by decide⟩ T141_18_2 (by decide)

theorem hinj141_18_2 : Function.Injective
    (fun i => ((T141_18_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)) :=
  repsInj_of_reduceAux2 rK141 T141_18_2 (by decide)

theorem hcardT141_18_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK141 ⟨18, by decide⟩ R141_2 hpxR141_2 hcardq141_2 (by decide)).symm

/-- **Cell (141, 18) twin (q=2).** -/
theorem cell141_18_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK141) e = true)
    (h : ↥(reps (⟨18, by decide⟩ : Fin 148))) :
    species (reps (⟨18, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec2 rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK141 e (h : Coordinate 2) T141_18_2 i :=
  species_entry_eq_sum rK141 ⟨18, by decide⟩ e heK h T141_18_2 hfix141_18_2 hinj141_18_2 hcardT141_18_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨18, by decide⟩) (reps rK141) (T141_18_2 i) (hfix141_18_2 i) h)

/-! ### Cell (141, 19) twin -/

def T141_19_2 : Fin 5 → Coordinate 2 := fun i => T141_19list.getD i.val (0,0,0,0,0)

theorem hfix141_19_2 : ∀ i, ((T141_19_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141) :=
  repsFix_of_siftB2 rK141 ⟨19, by decide⟩ T141_19_2 (by decide)

theorem hinj141_19_2 : Function.Injective
    (fun i => ((T141_19_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)) :=
  repsInj_of_reduceAux2 rK141 T141_19_2 (by decide)

theorem hcardT141_19_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK141 ⟨19, by decide⟩ R141_2 hpxR141_2 hcardq141_2 (by decide)).symm

/-- **Cell (141, 19) twin (q=2).** -/
theorem cell141_19_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK141) e = true)
    (h : ↥(reps (⟨19, by decide⟩ : Fin 148))) :
    species (reps (⟨19, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec2 rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK141 e (h : Coordinate 2) T141_19_2 i :=
  species_entry_eq_sum rK141 ⟨19, by decide⟩ e heK h T141_19_2 hfix141_19_2 hinj141_19_2 hcardT141_19_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨19, by decide⟩) (reps rK141) (T141_19_2 i) (hfix141_19_2 i) h)

/-! ### Cell (141, 20) twin -/

def T141_20_2 : Fin 5 → Coordinate 2 := fun i => T141_20list.getD i.val (0,0,0,0,0)

theorem hfix141_20_2 : ∀ i, ((T141_20_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141) :=
  repsFix_of_siftB2 rK141 ⟨20, by decide⟩ T141_20_2 (by decide)

theorem hinj141_20_2 : Function.Injective
    (fun i => ((T141_20_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)) :=
  repsInj_of_reduceAux2 rK141 T141_20_2 (by decide)

theorem hcardT141_20_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK141 ⟨20, by decide⟩ R141_2 hpxR141_2 hcardq141_2 (by decide)).symm

/-- **Cell (141, 20) twin (q=2).** -/
theorem cell141_20_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK141) e = true)
    (h : ↥(reps (⟨20, by decide⟩ : Fin 148))) :
    species (reps (⟨20, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec2 rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK141 e (h : Coordinate 2) T141_20_2 i :=
  species_entry_eq_sum rK141 ⟨20, by decide⟩ e heK h T141_20_2 hfix141_20_2 hinj141_20_2 hcardT141_20_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨20, by decide⟩) (reps rK141) (T141_20_2 i) (hfix141_20_2 i) h)

/-! ### Cell (141, 21) twin -/

def T141_21_2 : Fin 5 → Coordinate 2 := fun i => T141_21list.getD i.val (0,0,0,0,0)

theorem hfix141_21_2 : ∀ i, ((T141_21_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141) :=
  repsFix_of_siftB2 rK141 ⟨21, by decide⟩ T141_21_2 (by decide)

theorem hinj141_21_2 : Function.Injective
    (fun i => ((T141_21_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)) :=
  repsInj_of_reduceAux2 rK141 T141_21_2 (by decide)

theorem hcardT141_21_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK141 ⟨21, by decide⟩ R141_2 hpxR141_2 hcardq141_2 (by decide)).symm

/-- **Cell (141, 21) twin (q=2).** -/
theorem cell141_21_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK141) e = true)
    (h : ↥(reps (⟨21, by decide⟩ : Fin 148))) :
    species (reps (⟨21, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec2 rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK141 e (h : Coordinate 2) T141_21_2 i :=
  species_entry_eq_sum rK141 ⟨21, by decide⟩ e heK h T141_21_2 hfix141_21_2 hinj141_21_2 hcardT141_21_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨21, by decide⟩) (reps rK141) (T141_21_2 i) (hfix141_21_2 i) h)

/-! ### Cell (141, 22) twin -/

def T141_22_2 : Fin 5 → Coordinate 2 := fun i => T141_22list.getD i.val (0,0,0,0,0)

theorem hfix141_22_2 : ∀ i, ((T141_22_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141) :=
  repsFix_of_siftB2 rK141 ⟨22, by decide⟩ T141_22_2 (by decide)

theorem hinj141_22_2 : Function.Injective
    (fun i => ((T141_22_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)) :=
  repsInj_of_reduceAux2 rK141 T141_22_2 (by decide)

theorem hcardT141_22_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK141 ⟨22, by decide⟩ R141_2 hpxR141_2 hcardq141_2 (by decide)).symm

/-- **Cell (141, 22) twin (q=2).** -/
theorem cell141_22_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK141) e = true)
    (h : ↥(reps (⟨22, by decide⟩ : Fin 148))) :
    species (reps (⟨22, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec2 rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK141 e (h : Coordinate 2) T141_22_2 i :=
  species_entry_eq_sum rK141 ⟨22, by decide⟩ e heK h T141_22_2 hfix141_22_2 hinj141_22_2 hcardT141_22_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨22, by decide⟩) (reps rK141) (T141_22_2 i) (hfix141_22_2 i) h)

/-! ### Cell (141, 23) twin -/

def T141_23_2 : Fin 5 → Coordinate 2 := fun i => T141_23list.getD i.val (0,0,0,0,0)

theorem hfix141_23_2 : ∀ i, ((T141_23_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141) :=
  repsFix_of_siftB2 rK141 ⟨23, by decide⟩ T141_23_2 (by decide)

theorem hinj141_23_2 : Function.Injective
    (fun i => ((T141_23_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)) :=
  repsInj_of_reduceAux2 rK141 T141_23_2 (by decide)

theorem hcardT141_23_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK141 ⟨23, by decide⟩ R141_2 hpxR141_2 hcardq141_2 (by decide)).symm

/-- **Cell (141, 23) twin (q=2).** -/
theorem cell141_23_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK141) e = true)
    (h : ↥(reps (⟨23, by decide⟩ : Fin 148))) :
    species (reps (⟨23, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec2 rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK141 e (h : Coordinate 2) T141_23_2 i :=
  species_entry_eq_sum rK141 ⟨23, by decide⟩ e heK h T141_23_2 hfix141_23_2 hinj141_23_2 hcardT141_23_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨23, by decide⟩) (reps rK141) (T141_23_2 i) (hfix141_23_2 i) h)

/-! ### Cell (141, 24) twin -/

def T141_24_2 : Fin 5 → Coordinate 2 := fun i => T141_24list.getD i.val (0,0,0,0,0)

theorem hfix141_24_2 : ∀ i, ((T141_24_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141) :=
  repsFix_of_siftB2 rK141 ⟨24, by decide⟩ T141_24_2 (by decide)

theorem hinj141_24_2 : Function.Injective
    (fun i => ((T141_24_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)) :=
  repsInj_of_reduceAux2 rK141 T141_24_2 (by decide)

theorem hcardT141_24_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK141 ⟨24, by decide⟩ R141_2 hpxR141_2 hcardq141_2 (by decide)).symm

/-- **Cell (141, 24) twin (q=2).** -/
theorem cell141_24_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK141) e = true)
    (h : ↥(reps (⟨24, by decide⟩ : Fin 148))) :
    species (reps (⟨24, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec2 rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK141 e (h : Coordinate 2) T141_24_2 i :=
  species_entry_eq_sum rK141 ⟨24, by decide⟩ e heK h T141_24_2 hfix141_24_2 hinj141_24_2 hcardT141_24_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨24, by decide⟩) (reps rK141) (T141_24_2 i) (hfix141_24_2 i) h)

/-! ### Cell (141, 25) twin -/

def T141_25_2 : Fin 5 → Coordinate 2 := fun i => T141_25list.getD i.val (0,0,0,0,0)

theorem hfix141_25_2 : ∀ i, ((T141_25_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141) :=
  repsFix_of_siftB2 rK141 ⟨25, by decide⟩ T141_25_2 (by decide)

theorem hinj141_25_2 : Function.Injective
    (fun i => ((T141_25_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)) :=
  repsInj_of_reduceAux2 rK141 T141_25_2 (by decide)

theorem hcardT141_25_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK141 ⟨25, by decide⟩ R141_2 hpxR141_2 hcardq141_2 (by decide)).symm

/-- **Cell (141, 25) twin (q=2).** -/
theorem cell141_25_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK141) e = true)
    (h : ↥(reps (⟨25, by decide⟩ : Fin 148))) :
    species (reps (⟨25, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec2 rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK141 e (h : Coordinate 2) T141_25_2 i :=
  species_entry_eq_sum rK141 ⟨25, by decide⟩ e heK h T141_25_2 hfix141_25_2 hinj141_25_2 hcardT141_25_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨25, by decide⟩) (reps rK141) (T141_25_2 i) (hfix141_25_2 i) h)

/-! ### Cell (141, 26) twin -/

def T141_26_2 : Fin 5 → Coordinate 2 := fun i => T141_26list.getD i.val (0,0,0,0,0)

theorem hfix141_26_2 : ∀ i, ((T141_26_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141) :=
  repsFix_of_siftB2 rK141 ⟨26, by decide⟩ T141_26_2 (by decide)

theorem hinj141_26_2 : Function.Injective
    (fun i => ((T141_26_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)) :=
  repsInj_of_reduceAux2 rK141 T141_26_2 (by decide)

theorem hcardT141_26_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK141 ⟨26, by decide⟩ R141_2 hpxR141_2 hcardq141_2 (by decide)).symm

/-- **Cell (141, 26) twin (q=2).** -/
theorem cell141_26_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK141) e = true)
    (h : ↥(reps (⟨26, by decide⟩ : Fin 148))) :
    species (reps (⟨26, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec2 rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK141 e (h : Coordinate 2) T141_26_2 i :=
  species_entry_eq_sum rK141 ⟨26, by decide⟩ e heK h T141_26_2 hfix141_26_2 hinj141_26_2 hcardT141_26_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨26, by decide⟩) (reps rK141) (T141_26_2 i) (hfix141_26_2 i) h)

/-! ### Cell (141, 27) twin -/

def T141_27_2 : Fin 5 → Coordinate 2 := fun i => T141_27list.getD i.val (0,0,0,0,0)

theorem hfix141_27_2 : ∀ i, ((T141_27_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141) :=
  repsFix_of_siftB2 rK141 ⟨27, by decide⟩ T141_27_2 (by decide)

theorem hinj141_27_2 : Function.Injective
    (fun i => ((T141_27_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)) :=
  repsInj_of_reduceAux2 rK141 T141_27_2 (by decide)

theorem hcardT141_27_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK141 ⟨27, by decide⟩ R141_2 hpxR141_2 hcardq141_2 (by decide)).symm

/-- **Cell (141, 27) twin (q=2).** -/
theorem cell141_27_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK141) e = true)
    (h : ↥(reps (⟨27, by decide⟩ : Fin 148))) :
    species (reps (⟨27, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec2 rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK141 e (h : Coordinate 2) T141_27_2 i :=
  species_entry_eq_sum rK141 ⟨27, by decide⟩ e heK h T141_27_2 hfix141_27_2 hinj141_27_2 hcardT141_27_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨27, by decide⟩) (reps rK141) (T141_27_2 i) (hfix141_27_2 i) h)

/-! ### Cell (141, 53) twin -/

def T141_53_2 : Fin 5 → Coordinate 2 := fun i => T141_53list.getD i.val (0,0,0,0,0)

theorem hfix141_53_2 : ∀ i, ((T141_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141) :=
  repsFix_of_siftB2 rK141 ⟨53, by decide⟩ T141_53_2 (by decide)

theorem hinj141_53_2 : Function.Injective
    (fun i => ((T141_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)) :=
  repsInj_of_reduceAux2 rK141 T141_53_2 (by decide)

theorem hcardT141_53_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK141 ⟨53, by decide⟩ R141_2 hpxR141_2 hcardq141_2 (by decide)).symm

/-- **Cell (141, 53) twin (q=2).** -/
theorem cell141_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK141) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec2 rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK141 e (h : Coordinate 2) T141_53_2 i :=
  species_entry_eq_sum rK141 ⟨53, by decide⟩ e heK h T141_53_2 hfix141_53_2 hinj141_53_2 hcardT141_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK141) (T141_53_2 i) (hfix141_53_2 i) h)

/-! ### Cell (141, 54) twin -/

def T141_54_2 : Fin 5 → Coordinate 2 := fun i => T141_54list.getD i.val (0,0,0,0,0)

theorem hfix141_54_2 : ∀ i, ((T141_54_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141) :=
  repsFix_of_siftB2 rK141 ⟨54, by decide⟩ T141_54_2 (by decide)

theorem hinj141_54_2 : Function.Injective
    (fun i => ((T141_54_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)) :=
  repsInj_of_reduceAux2 rK141 T141_54_2 (by decide)

theorem hcardT141_54_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK141 ⟨54, by decide⟩ R141_2 hpxR141_2 hcardq141_2 (by decide)).symm

/-- **Cell (141, 54) twin (q=2).** -/
theorem cell141_54_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK141) e = true)
    (h : ↥(reps (⟨54, by decide⟩ : Fin 148))) :
    species (reps (⟨54, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec2 rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK141 e (h : Coordinate 2) T141_54_2 i :=
  species_entry_eq_sum rK141 ⟨54, by decide⟩ e heK h T141_54_2 hfix141_54_2 hinj141_54_2 hcardT141_54_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨54, by decide⟩) (reps rK141) (T141_54_2 i) (hfix141_54_2 i) h)

/-! ### Cell (141, 80) twin -/

def T141_80_2 : Fin 5 → Coordinate 2 := fun i => T141_80list.getD i.val (0,0,0,0,0)

theorem hfix141_80_2 : ∀ i, ((T141_80_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141) :=
  repsFix_of_siftB2 rK141 ⟨80, by decide⟩ T141_80_2 (by decide)

theorem hinj141_80_2 : Function.Injective
    (fun i => ((T141_80_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)) :=
  repsInj_of_reduceAux2 rK141 T141_80_2 (by decide)

theorem hcardT141_80_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK141 ⟨80, by decide⟩ R141_2 hpxR141_2 hcardq141_2 (by decide)).symm

/-- **Cell (141, 80) twin (q=2).** -/
theorem cell141_80_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK141) e = true)
    (h : ↥(reps (⟨80, by decide⟩ : Fin 148))) :
    species (reps (⟨80, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec2 rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK141 e (h : Coordinate 2) T141_80_2 i :=
  species_entry_eq_sum rK141 ⟨80, by decide⟩ e heK h T141_80_2 hfix141_80_2 hinj141_80_2 hcardT141_80_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨80, by decide⟩) (reps rK141) (T141_80_2 i) (hfix141_80_2 i) h)

/-! ### Cell (141, 81) twin -/

def T141_81_2 : Fin 5 → Coordinate 2 := fun i => T141_81list.getD i.val (0,0,0,0,0)

theorem hfix141_81_2 : ∀ i, ((T141_81_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141) :=
  repsFix_of_siftB2 rK141 ⟨81, by decide⟩ T141_81_2 (by decide)

theorem hinj141_81_2 : Function.Injective
    (fun i => ((T141_81_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)) :=
  repsInj_of_reduceAux2 rK141 T141_81_2 (by decide)

theorem hcardT141_81_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK141 ⟨81, by decide⟩ R141_2 hpxR141_2 hcardq141_2 (by decide)).symm

/-- **Cell (141, 81) twin (q=2).** -/
theorem cell141_81_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK141) e = true)
    (h : ↥(reps (⟨81, by decide⟩ : Fin 148))) :
    species (reps (⟨81, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec2 rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK141 e (h : Coordinate 2) T141_81_2 i :=
  species_entry_eq_sum rK141 ⟨81, by decide⟩ e heK h T141_81_2 hfix141_81_2 hinj141_81_2 hcardT141_81_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨81, by decide⟩) (reps rK141) (T141_81_2 i) (hfix141_81_2 i) h)

/-! ### Cell (141, 82) twin -/

def T141_82_2 : Fin 5 → Coordinate 2 := fun i => T141_82list.getD i.val (0,0,0,0,0)

theorem hfix141_82_2 : ∀ i, ((T141_82_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141) :=
  repsFix_of_siftB2 rK141 ⟨82, by decide⟩ T141_82_2 (by decide)

theorem hinj141_82_2 : Function.Injective
    (fun i => ((T141_82_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)) :=
  repsInj_of_reduceAux2 rK141 T141_82_2 (by decide)

theorem hcardT141_82_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK141 ⟨82, by decide⟩ R141_2 hpxR141_2 hcardq141_2 (by decide)).symm

/-- **Cell (141, 82) twin (q=2).** -/
theorem cell141_82_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK141) e = true)
    (h : ↥(reps (⟨82, by decide⟩ : Fin 148))) :
    species (reps (⟨82, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec2 rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK141 e (h : Coordinate 2) T141_82_2 i :=
  species_entry_eq_sum rK141 ⟨82, by decide⟩ e heK h T141_82_2 hfix141_82_2 hinj141_82_2 hcardT141_82_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨82, by decide⟩) (reps rK141) (T141_82_2 i) (hfix141_82_2 i) h)

/-! ### Cell (141, 83) twin -/

def T141_83_2 : Fin 5 → Coordinate 2 := fun i => T141_83list.getD i.val (0,0,0,0,0)

theorem hfix141_83_2 : ∀ i, ((T141_83_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141) :=
  repsFix_of_siftB2 rK141 ⟨83, by decide⟩ T141_83_2 (by decide)

theorem hinj141_83_2 : Function.Injective
    (fun i => ((T141_83_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)) :=
  repsInj_of_reduceAux2 rK141 T141_83_2 (by decide)

theorem hcardT141_83_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK141 ⟨83, by decide⟩ R141_2 hpxR141_2 hcardq141_2 (by decide)).symm

/-- **Cell (141, 83) twin (q=2).** -/
theorem cell141_83_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK141) e = true)
    (h : ↥(reps (⟨83, by decide⟩ : Fin 148))) :
    species (reps (⟨83, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec2 rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK141 e (h : Coordinate 2) T141_83_2 i :=
  species_entry_eq_sum rK141 ⟨83, by decide⟩ e heK h T141_83_2 hfix141_83_2 hinj141_83_2 hcardT141_83_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨83, by decide⟩) (reps rK141) (T141_83_2 i) (hfix141_83_2 i) h)

/-! ### Cell (141, 84) twin -/

def T141_84_2 : Fin 5 → Coordinate 2 := fun i => T141_84list.getD i.val (0,0,0,0,0)

theorem hfix141_84_2 : ∀ i, ((T141_84_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141) :=
  repsFix_of_siftB2 rK141 ⟨84, by decide⟩ T141_84_2 (by decide)

theorem hinj141_84_2 : Function.Injective
    (fun i => ((T141_84_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)) :=
  repsInj_of_reduceAux2 rK141 T141_84_2 (by decide)

theorem hcardT141_84_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK141 ⟨84, by decide⟩ R141_2 hpxR141_2 hcardq141_2 (by decide)).symm

/-- **Cell (141, 84) twin (q=2).** -/
theorem cell141_84_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK141) e = true)
    (h : ↥(reps (⟨84, by decide⟩ : Fin 148))) :
    species (reps (⟨84, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec2 rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK141 e (h : Coordinate 2) T141_84_2 i :=
  species_entry_eq_sum rK141 ⟨84, by decide⟩ e heK h T141_84_2 hfix141_84_2 hinj141_84_2 hcardT141_84_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨84, by decide⟩) (reps rK141) (T141_84_2 i) (hfix141_84_2 i) h)

/-! ### Cell (141, 85) twin -/

def T141_85_2 : Fin 5 → Coordinate 2 := fun i => T141_85list.getD i.val (0,0,0,0,0)

theorem hfix141_85_2 : ∀ i, ((T141_85_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141) :=
  repsFix_of_siftB2 rK141 ⟨85, by decide⟩ T141_85_2 (by decide)

theorem hinj141_85_2 : Function.Injective
    (fun i => ((T141_85_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)) :=
  repsInj_of_reduceAux2 rK141 T141_85_2 (by decide)

theorem hcardT141_85_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK141 ⟨85, by decide⟩ R141_2 hpxR141_2 hcardq141_2 (by decide)).symm

/-- **Cell (141, 85) twin (q=2).** -/
theorem cell141_85_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK141) e = true)
    (h : ↥(reps (⟨85, by decide⟩ : Fin 148))) :
    species (reps (⟨85, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec2 rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK141 e (h : Coordinate 2) T141_85_2 i :=
  species_entry_eq_sum rK141 ⟨85, by decide⟩ e heK h T141_85_2 hfix141_85_2 hinj141_85_2 hcardT141_85_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨85, by decide⟩) (reps rK141) (T141_85_2 i) (hfix141_85_2 i) h)

/-! ### Cell (141, 86) twin -/

def T141_86_2 : Fin 5 → Coordinate 2 := fun i => T141_86list.getD i.val (0,0,0,0,0)

theorem hfix141_86_2 : ∀ i, ((T141_86_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141) :=
  repsFix_of_siftB2 rK141 ⟨86, by decide⟩ T141_86_2 (by decide)

theorem hinj141_86_2 : Function.Injective
    (fun i => ((T141_86_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)) :=
  repsInj_of_reduceAux2 rK141 T141_86_2 (by decide)

theorem hcardT141_86_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK141 ⟨86, by decide⟩ R141_2 hpxR141_2 hcardq141_2 (by decide)).symm

/-- **Cell (141, 86) twin (q=2).** -/
theorem cell141_86_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK141) e = true)
    (h : ↥(reps (⟨86, by decide⟩ : Fin 148))) :
    species (reps (⟨86, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec2 rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK141 e (h : Coordinate 2) T141_86_2 i :=
  species_entry_eq_sum rK141 ⟨86, by decide⟩ e heK h T141_86_2 hfix141_86_2 hinj141_86_2 hcardT141_86_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨86, by decide⟩) (reps rK141) (T141_86_2 i) (hfix141_86_2 i) h)

/-! ### Cell (141, 87) twin -/

def T141_87_2 : Fin 5 → Coordinate 2 := fun i => T141_87list.getD i.val (0,0,0,0,0)

theorem hfix141_87_2 : ∀ i, ((T141_87_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141) :=
  repsFix_of_siftB2 rK141 ⟨87, by decide⟩ T141_87_2 (by decide)

theorem hinj141_87_2 : Function.Injective
    (fun i => ((T141_87_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)) :=
  repsInj_of_reduceAux2 rK141 T141_87_2 (by decide)

theorem hcardT141_87_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK141 ⟨87, by decide⟩ R141_2 hpxR141_2 hcardq141_2 (by decide)).symm

/-- **Cell (141, 87) twin (q=2).** -/
theorem cell141_87_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK141) e = true)
    (h : ↥(reps (⟨87, by decide⟩ : Fin 148))) :
    species (reps (⟨87, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec2 rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK141 e (h : Coordinate 2) T141_87_2 i :=
  species_entry_eq_sum rK141 ⟨87, by decide⟩ e heK h T141_87_2 hfix141_87_2 hinj141_87_2 hcardT141_87_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨87, by decide⟩) (reps rK141) (T141_87_2 i) (hfix141_87_2 i) h)

/-! ### Cell (141, 88) twin -/

def T141_88_2 : Fin 5 → Coordinate 2 := fun i => T141_88list.getD i.val (0,0,0,0,0)

theorem hfix141_88_2 : ∀ i, ((T141_88_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141) :=
  repsFix_of_siftB2 rK141 ⟨88, by decide⟩ T141_88_2 (by decide)

theorem hinj141_88_2 : Function.Injective
    (fun i => ((T141_88_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)) :=
  repsInj_of_reduceAux2 rK141 T141_88_2 (by decide)

theorem hcardT141_88_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK141 ⟨88, by decide⟩ R141_2 hpxR141_2 hcardq141_2 (by decide)).symm

/-- **Cell (141, 88) twin (q=2).** -/
theorem cell141_88_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK141) e = true)
    (h : ↥(reps (⟨88, by decide⟩ : Fin 148))) :
    species (reps (⟨88, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec2 rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK141 e (h : Coordinate 2) T141_88_2 i :=
  species_entry_eq_sum rK141 ⟨88, by decide⟩ e heK h T141_88_2 hfix141_88_2 hinj141_88_2 hcardT141_88_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨88, by decide⟩) (reps rK141) (T141_88_2 i) (hfix141_88_2 i) h)

/-! ### Cell (141, 89) twin -/

def T141_89_2 : Fin 5 → Coordinate 2 := fun i => T141_89list.getD i.val (0,0,0,0,0)

theorem hfix141_89_2 : ∀ i, ((T141_89_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141) :=
  repsFix_of_siftB2 rK141 ⟨89, by decide⟩ T141_89_2 (by decide)

theorem hinj141_89_2 : Function.Injective
    (fun i => ((T141_89_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)) :=
  repsInj_of_reduceAux2 rK141 T141_89_2 (by decide)

theorem hcardT141_89_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK141 ⟨89, by decide⟩ R141_2 hpxR141_2 hcardq141_2 (by decide)).symm

/-- **Cell (141, 89) twin (q=2).** -/
theorem cell141_89_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK141) e = true)
    (h : ↥(reps (⟨89, by decide⟩ : Fin 148))) :
    species (reps (⟨89, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec2 rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK141 e (h : Coordinate 2) T141_89_2 i :=
  species_entry_eq_sum rK141 ⟨89, by decide⟩ e heK h T141_89_2 hfix141_89_2 hinj141_89_2 hcardT141_89_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨89, by decide⟩) (reps rK141) (T141_89_2 i) (hfix141_89_2 i) h)

/-! ### Cell (141, 115) twin -/

def T141_115_2 : Fin 5 → Coordinate 2 := fun i => T141_115list.getD i.val (0,0,0,0,0)

theorem hfix141_115_2 : ∀ i, ((T141_115_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141) :=
  repsFix_of_siftB2 rK141 ⟨115, by decide⟩ T141_115_2 (by decide)

theorem hinj141_115_2 : Function.Injective
    (fun i => ((T141_115_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)) :=
  repsInj_of_reduceAux2 rK141 T141_115_2 (by decide)

theorem hcardT141_115_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK141 ⟨115, by decide⟩ R141_2 hpxR141_2 hcardq141_2 (by decide)).symm

/-- **Cell (141, 115) twin (q=2).** -/
theorem cell141_115_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK141) e = true)
    (h : ↥(reps (⟨115, by decide⟩ : Fin 148))) :
    species (reps (⟨115, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec2 rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK141 e (h : Coordinate 2) T141_115_2 i :=
  species_entry_eq_sum rK141 ⟨115, by decide⟩ e heK h T141_115_2 hfix141_115_2 hinj141_115_2 hcardT141_115_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨115, by decide⟩) (reps rK141) (T141_115_2 i) (hfix141_115_2 i) h)

/-! ### Cell (141, 141) twin -/

def T141_141_2 : Fin 5 → Coordinate 2 := fun i => T141_141list.getD i.val (0,0,0,0,0)

theorem hfix141_141_2 : ∀ i, ((T141_141_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)
    ∈ fixedPoints (reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141) :=
  repsFix_of_siftB2 rK141 ⟨141, by decide⟩ T141_141_2 (by decide)

theorem hinj141_141_2 : Function.Injective
    (fun i => ((T141_141_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK141)) :=
  repsInj_of_reduceAux2 rK141 T141_141_2 (by decide)

theorem hcardT141_141_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK141)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK141 ⟨141, by decide⟩ R141_2 hpxR141_2 hcardq141_2 (by decide)).symm

/-- **Cell (141, 141) twin (q=2).** -/
theorem cell141_141_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK141) e = true)
    (h : ↥(reps (⟨141, by decide⟩ : Fin 148))) :
    species (reps (⟨141, by decide⟩ : Fin 148)) h (basisElt (reps rK141) (charOfVec2 rK141 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK141 e (h : Coordinate 2) T141_141_2 i :=
  species_entry_eq_sum rK141 ⟨141, by decide⟩ e heK h T141_141_2 hfix141_141_2 hinj141_141_2 hcardT141_141_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨141, by decide⟩) (reps rK141) (T141_141_2 i) (hfix141_141_2 i) h)

end Q2

end LeanDring.P5Presentation
