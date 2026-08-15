/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, K-strata data (5^3 stratum, rK 85-87): certified per-cell species-entry instantiations, both
twins.

Covers K-classes 85, 86, 87 (order-5^3 K, |R|=25).  For each nonzero `H`-column
(`(G/K)^H ≠ ∅`), the full coset transversal `R85..` and each `H`-fixed
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

/-! # K-class rK = 85  (|G/K| = 25) -/

def rK85 : Fin 148 := ⟨85, by decide⟩

def R85list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0)]
def R85 : Fin 25 → Coordinate 1 := fun i => R85list.getD i.val (0,0,0,0,0)

theorem hpxR85 : Function.Injective (fun i => reduceAux 1 (basisAt rK85) (R85 i)) := by decide
theorem hcardq85 : Nat.card (Coordinate 1 ⧸ reps rK85) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (85, 0): |T| = 25 -/

def T85_0list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0)]
def T85_0 : Fin 25 → Coordinate 1 := fun i => T85_0list.getD i.val (0,0,0,0,0)

theorem hfix85_0 : ∀ i, ((T85_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK85)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85) :=
  repsFix_of_siftB rK85 ⟨0, by decide⟩ T85_0 (by decide)

theorem hinj85_0 : Function.Injective
    (fun i => ((T85_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK85)) :=
  repsInj_of_reduceAux rK85 T85_0 (by decide)

theorem hcardT85_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK85 ⟨0, by decide⟩ R85 hpxR85 hcardq85 (by decide)).symm

/-- **Cell (85, 0).** -/
theorem cell85_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK85) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK85) (charOfVec rK85 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK85 e (h : Coordinate 1) T85_0 i :=
  species_entry_eq_sum rK85 ⟨0, by decide⟩ e heK h T85_0 hfix85_0 hinj85_0 hcardT85_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK85) (T85_0 i) (hfix85_0 i) h)

/-! ## Cell (85, 2): |T| = 5 -/

def T85_2list : List Coordinates := [(0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0)]
def T85_2 : Fin 5 → Coordinate 1 := fun i => T85_2list.getD i.val (0,0,0,0,0)

theorem hfix85_2 : ∀ i, ((T85_2 i : Coordinate 1) : Coordinate 1 ⧸ reps rK85)
    ∈ fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85) :=
  repsFix_of_siftB rK85 ⟨2, by decide⟩ T85_2 (by decide)

theorem hinj85_2 : Function.Injective
    (fun i => ((T85_2 i : Coordinate 1) : Coordinate 1 ⧸ reps rK85)) :=
  repsInj_of_reduceAux rK85 T85_2 (by decide)

theorem hcardT85_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK85 ⟨2, by decide⟩ R85 hpxR85 hcardq85 (by decide)).symm

/-- **Cell (85, 2).** -/
theorem cell85_2 (e : List (ZMod 25)) (heK : charOK (basisAt rK85) e = true)
    (h : ↥(reps (⟨2, by decide⟩ : Fin 148))) :
    species (reps (⟨2, by decide⟩ : Fin 148)) h (basisElt (reps rK85) (charOfVec rK85 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK85 e (h : Coordinate 1) T85_2 i :=
  species_entry_eq_sum rK85 ⟨2, by decide⟩ e heK h T85_2 hfix85_2 hinj85_2 hcardT85_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨2, by decide⟩) (reps rK85) (T85_2 i) (hfix85_2 i) h)

/-! ## Cell (85, 3): |T| = 5 -/

def T85_3list : List Coordinates := [(0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0)]
def T85_3 : Fin 5 → Coordinate 1 := fun i => T85_3list.getD i.val (0,0,0,0,0)

theorem hfix85_3 : ∀ i, ((T85_3 i : Coordinate 1) : Coordinate 1 ⧸ reps rK85)
    ∈ fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85) :=
  repsFix_of_siftB rK85 ⟨3, by decide⟩ T85_3 (by decide)

theorem hinj85_3 : Function.Injective
    (fun i => ((T85_3 i : Coordinate 1) : Coordinate 1 ⧸ reps rK85)) :=
  repsInj_of_reduceAux rK85 T85_3 (by decide)

theorem hcardT85_3 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK85 ⟨3, by decide⟩ R85 hpxR85 hcardq85 (by decide)).symm

/-- **Cell (85, 3).** -/
theorem cell85_3 (e : List (ZMod 25)) (heK : charOK (basisAt rK85) e = true)
    (h : ↥(reps (⟨3, by decide⟩ : Fin 148))) :
    species (reps (⟨3, by decide⟩ : Fin 148)) h (basisElt (reps rK85) (charOfVec rK85 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK85 e (h : Coordinate 1) T85_3 i :=
  species_entry_eq_sum rK85 ⟨3, by decide⟩ e heK h T85_3 hfix85_3 hinj85_3 hcardT85_3
    (fun i => conj_mem_of_fixedPoints (reps ⟨3, by decide⟩) (reps rK85) (T85_3 i) (hfix85_3 i) h)

/-! ## Cell (85, 4): |T| = 5 -/

def T85_4list : List Coordinates := [(0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0)]
def T85_4 : Fin 5 → Coordinate 1 := fun i => T85_4list.getD i.val (0,0,0,0,0)

theorem hfix85_4 : ∀ i, ((T85_4 i : Coordinate 1) : Coordinate 1 ⧸ reps rK85)
    ∈ fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85) :=
  repsFix_of_siftB rK85 ⟨4, by decide⟩ T85_4 (by decide)

theorem hinj85_4 : Function.Injective
    (fun i => ((T85_4 i : Coordinate 1) : Coordinate 1 ⧸ reps rK85)) :=
  repsInj_of_reduceAux rK85 T85_4 (by decide)

theorem hcardT85_4 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK85 ⟨4, by decide⟩ R85 hpxR85 hcardq85 (by decide)).symm

/-- **Cell (85, 4).** -/
theorem cell85_4 (e : List (ZMod 25)) (heK : charOK (basisAt rK85) e = true)
    (h : ↥(reps (⟨4, by decide⟩ : Fin 148))) :
    species (reps (⟨4, by decide⟩ : Fin 148)) h (basisElt (reps rK85) (charOfVec rK85 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK85 e (h : Coordinate 1) T85_4 i :=
  species_entry_eq_sum rK85 ⟨4, by decide⟩ e heK h T85_4 hfix85_4 hinj85_4 hcardT85_4
    (fun i => conj_mem_of_fixedPoints (reps ⟨4, by decide⟩) (reps rK85) (T85_4 i) (hfix85_4 i) h)

/-! ## Cell (85, 5): |T| = 5 -/

def T85_5list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0)]
def T85_5 : Fin 5 → Coordinate 1 := fun i => T85_5list.getD i.val (0,0,0,0,0)

theorem hfix85_5 : ∀ i, ((T85_5 i : Coordinate 1) : Coordinate 1 ⧸ reps rK85)
    ∈ fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85) :=
  repsFix_of_siftB rK85 ⟨5, by decide⟩ T85_5 (by decide)

theorem hinj85_5 : Function.Injective
    (fun i => ((T85_5 i : Coordinate 1) : Coordinate 1 ⧸ reps rK85)) :=
  repsInj_of_reduceAux rK85 T85_5 (by decide)

theorem hcardT85_5 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK85 ⟨5, by decide⟩ R85 hpxR85 hcardq85 (by decide)).symm

/-- **Cell (85, 5).** -/
theorem cell85_5 (e : List (ZMod 25)) (heK : charOK (basisAt rK85) e = true)
    (h : ↥(reps (⟨5, by decide⟩ : Fin 148))) :
    species (reps (⟨5, by decide⟩ : Fin 148)) h (basisElt (reps rK85) (charOfVec rK85 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK85 e (h : Coordinate 1) T85_5 i :=
  species_entry_eq_sum rK85 ⟨5, by decide⟩ e heK h T85_5 hfix85_5 hinj85_5 hcardT85_5
    (fun i => conj_mem_of_fixedPoints (reps ⟨5, by decide⟩) (reps rK85) (T85_5 i) (hfix85_5 i) h)

/-! ## Cell (85, 9): |T| = 25 -/

def T85_9list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0)]
def T85_9 : Fin 25 → Coordinate 1 := fun i => T85_9list.getD i.val (0,0,0,0,0)

theorem hfix85_9 : ∀ i, ((T85_9 i : Coordinate 1) : Coordinate 1 ⧸ reps rK85)
    ∈ fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85) :=
  repsFix_of_siftB rK85 ⟨9, by decide⟩ T85_9 (by decide)

theorem hinj85_9 : Function.Injective
    (fun i => ((T85_9 i : Coordinate 1) : Coordinate 1 ⧸ reps rK85)) :=
  repsInj_of_reduceAux rK85 T85_9 (by decide)

theorem hcardT85_9 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK85 ⟨9, by decide⟩ R85 hpxR85 hcardq85 (by decide)).symm

/-- **Cell (85, 9).** -/
theorem cell85_9 (e : List (ZMod 25)) (heK : charOK (basisAt rK85) e = true)
    (h : ↥(reps (⟨9, by decide⟩ : Fin 148))) :
    species (reps (⟨9, by decide⟩ : Fin 148)) h (basisElt (reps rK85) (charOfVec rK85 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK85 e (h : Coordinate 1) T85_9 i :=
  species_entry_eq_sum rK85 ⟨9, by decide⟩ e heK h T85_9 hfix85_9 hinj85_9 hcardT85_9
    (fun i => conj_mem_of_fixedPoints (reps ⟨9, by decide⟩) (reps rK85) (T85_9 i) (hfix85_9 i) h)

/-! ## Cell (85, 11): |T| = 5 -/

def T85_11list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0)]
def T85_11 : Fin 5 → Coordinate 1 := fun i => T85_11list.getD i.val (0,0,0,0,0)

theorem hfix85_11 : ∀ i, ((T85_11 i : Coordinate 1) : Coordinate 1 ⧸ reps rK85)
    ∈ fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85) :=
  repsFix_of_siftB rK85 ⟨11, by decide⟩ T85_11 (by decide)

theorem hinj85_11 : Function.Injective
    (fun i => ((T85_11 i : Coordinate 1) : Coordinate 1 ⧸ reps rK85)) :=
  repsInj_of_reduceAux rK85 T85_11 (by decide)

theorem hcardT85_11 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK85 ⟨11, by decide⟩ R85 hpxR85 hcardq85 (by decide)).symm

/-- **Cell (85, 11).** -/
theorem cell85_11 (e : List (ZMod 25)) (heK : charOK (basisAt rK85) e = true)
    (h : ↥(reps (⟨11, by decide⟩ : Fin 148))) :
    species (reps (⟨11, by decide⟩ : Fin 148)) h (basisElt (reps rK85) (charOfVec rK85 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK85 e (h : Coordinate 1) T85_11 i :=
  species_entry_eq_sum rK85 ⟨11, by decide⟩ e heK h T85_11 hfix85_11 hinj85_11 hcardT85_11
    (fun i => conj_mem_of_fixedPoints (reps ⟨11, by decide⟩) (reps rK85) (T85_11 i) (hfix85_11 i) h)

/-! ## Cell (85, 12): |T| = 25 -/

def T85_12list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0)]
def T85_12 : Fin 25 → Coordinate 1 := fun i => T85_12list.getD i.val (0,0,0,0,0)

theorem hfix85_12 : ∀ i, ((T85_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK85)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85) :=
  repsFix_of_siftB rK85 ⟨12, by decide⟩ T85_12 (by decide)

theorem hinj85_12 : Function.Injective
    (fun i => ((T85_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK85)) :=
  repsInj_of_reduceAux rK85 T85_12 (by decide)

theorem hcardT85_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK85 ⟨12, by decide⟩ R85 hpxR85 hcardq85 (by decide)).symm

/-- **Cell (85, 12).** -/
theorem cell85_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK85) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK85) (charOfVec rK85 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK85 e (h : Coordinate 1) T85_12 i :=
  species_entry_eq_sum rK85 ⟨12, by decide⟩ e heK h T85_12 hfix85_12 hinj85_12 hcardT85_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK85) (T85_12 i) (hfix85_12 i) h)

/-! ## Cell (85, 14): |T| = 5 -/

def T85_14list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0)]
def T85_14 : Fin 5 → Coordinate 1 := fun i => T85_14list.getD i.val (0,0,0,0,0)

theorem hfix85_14 : ∀ i, ((T85_14 i : Coordinate 1) : Coordinate 1 ⧸ reps rK85)
    ∈ fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85) :=
  repsFix_of_siftB rK85 ⟨14, by decide⟩ T85_14 (by decide)

theorem hinj85_14 : Function.Injective
    (fun i => ((T85_14 i : Coordinate 1) : Coordinate 1 ⧸ reps rK85)) :=
  repsInj_of_reduceAux rK85 T85_14 (by decide)

theorem hcardT85_14 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK85 ⟨14, by decide⟩ R85 hpxR85 hcardq85 (by decide)).symm

/-- **Cell (85, 14).** -/
theorem cell85_14 (e : List (ZMod 25)) (heK : charOK (basisAt rK85) e = true)
    (h : ↥(reps (⟨14, by decide⟩ : Fin 148))) :
    species (reps (⟨14, by decide⟩ : Fin 148)) h (basisElt (reps rK85) (charOfVec rK85 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK85 e (h : Coordinate 1) T85_14 i :=
  species_entry_eq_sum rK85 ⟨14, by decide⟩ e heK h T85_14 hfix85_14 hinj85_14 hcardT85_14
    (fun i => conj_mem_of_fixedPoints (reps ⟨14, by decide⟩) (reps rK85) (T85_14 i) (hfix85_14 i) h)

/-! ## Cell (85, 15): |T| = 5 -/

def T85_15list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0)]
def T85_15 : Fin 5 → Coordinate 1 := fun i => T85_15list.getD i.val (0,0,0,0,0)

theorem hfix85_15 : ∀ i, ((T85_15 i : Coordinate 1) : Coordinate 1 ⧸ reps rK85)
    ∈ fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85) :=
  repsFix_of_siftB rK85 ⟨15, by decide⟩ T85_15 (by decide)

theorem hinj85_15 : Function.Injective
    (fun i => ((T85_15 i : Coordinate 1) : Coordinate 1 ⧸ reps rK85)) :=
  repsInj_of_reduceAux rK85 T85_15 (by decide)

theorem hcardT85_15 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK85 ⟨15, by decide⟩ R85 hpxR85 hcardq85 (by decide)).symm

/-- **Cell (85, 15).** -/
theorem cell85_15 (e : List (ZMod 25)) (heK : charOK (basisAt rK85) e = true)
    (h : ↥(reps (⟨15, by decide⟩ : Fin 148))) :
    species (reps (⟨15, by decide⟩ : Fin 148)) h (basisElt (reps rK85) (charOfVec rK85 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK85 e (h : Coordinate 1) T85_15 i :=
  species_entry_eq_sum rK85 ⟨15, by decide⟩ e heK h T85_15 hfix85_15 hinj85_15 hcardT85_15
    (fun i => conj_mem_of_fixedPoints (reps ⟨15, by decide⟩) (reps rK85) (T85_15 i) (hfix85_15 i) h)

/-! ## Cell (85, 16): |T| = 5 -/

def T85_16list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0)]
def T85_16 : Fin 5 → Coordinate 1 := fun i => T85_16list.getD i.val (0,0,0,0,0)

theorem hfix85_16 : ∀ i, ((T85_16 i : Coordinate 1) : Coordinate 1 ⧸ reps rK85)
    ∈ fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85) :=
  repsFix_of_siftB rK85 ⟨16, by decide⟩ T85_16 (by decide)

theorem hinj85_16 : Function.Injective
    (fun i => ((T85_16 i : Coordinate 1) : Coordinate 1 ⧸ reps rK85)) :=
  repsInj_of_reduceAux rK85 T85_16 (by decide)

theorem hcardT85_16 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK85 ⟨16, by decide⟩ R85 hpxR85 hcardq85 (by decide)).symm

/-- **Cell (85, 16).** -/
theorem cell85_16 (e : List (ZMod 25)) (heK : charOK (basisAt rK85) e = true)
    (h : ↥(reps (⟨16, by decide⟩ : Fin 148))) :
    species (reps (⟨16, by decide⟩ : Fin 148)) h (basisElt (reps rK85) (charOfVec rK85 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK85 e (h : Coordinate 1) T85_16 i :=
  species_entry_eq_sum rK85 ⟨16, by decide⟩ e heK h T85_16 hfix85_16 hinj85_16 hcardT85_16
    (fun i => conj_mem_of_fixedPoints (reps ⟨16, by decide⟩) (reps rK85) (T85_16 i) (hfix85_16 i) h)

/-! ## Cell (85, 17): |T| = 5 -/

def T85_17list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0)]
def T85_17 : Fin 5 → Coordinate 1 := fun i => T85_17list.getD i.val (0,0,0,0,0)

theorem hfix85_17 : ∀ i, ((T85_17 i : Coordinate 1) : Coordinate 1 ⧸ reps rK85)
    ∈ fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85) :=
  repsFix_of_siftB rK85 ⟨17, by decide⟩ T85_17 (by decide)

theorem hinj85_17 : Function.Injective
    (fun i => ((T85_17 i : Coordinate 1) : Coordinate 1 ⧸ reps rK85)) :=
  repsInj_of_reduceAux rK85 T85_17 (by decide)

theorem hcardT85_17 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK85 ⟨17, by decide⟩ R85 hpxR85 hcardq85 (by decide)).symm

/-- **Cell (85, 17).** -/
theorem cell85_17 (e : List (ZMod 25)) (heK : charOK (basisAt rK85) e = true)
    (h : ↥(reps (⟨17, by decide⟩ : Fin 148))) :
    species (reps (⟨17, by decide⟩ : Fin 148)) h (basisElt (reps rK85) (charOfVec rK85 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK85 e (h : Coordinate 1) T85_17 i :=
  species_entry_eq_sum rK85 ⟨17, by decide⟩ e heK h T85_17 hfix85_17 hinj85_17 hcardT85_17
    (fun i => conj_mem_of_fixedPoints (reps ⟨17, by decide⟩) (reps rK85) (T85_17 i) (hfix85_17 i) h)

/-! ## Cell (85, 18): |T| = 5 -/

def T85_18list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0)]
def T85_18 : Fin 5 → Coordinate 1 := fun i => T85_18list.getD i.val (0,0,0,0,0)

theorem hfix85_18 : ∀ i, ((T85_18 i : Coordinate 1) : Coordinate 1 ⧸ reps rK85)
    ∈ fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85) :=
  repsFix_of_siftB rK85 ⟨18, by decide⟩ T85_18 (by decide)

theorem hinj85_18 : Function.Injective
    (fun i => ((T85_18 i : Coordinate 1) : Coordinate 1 ⧸ reps rK85)) :=
  repsInj_of_reduceAux rK85 T85_18 (by decide)

theorem hcardT85_18 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK85 ⟨18, by decide⟩ R85 hpxR85 hcardq85 (by decide)).symm

/-- **Cell (85, 18).** -/
theorem cell85_18 (e : List (ZMod 25)) (heK : charOK (basisAt rK85) e = true)
    (h : ↥(reps (⟨18, by decide⟩ : Fin 148))) :
    species (reps (⟨18, by decide⟩ : Fin 148)) h (basisElt (reps rK85) (charOfVec rK85 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK85 e (h : Coordinate 1) T85_18 i :=
  species_entry_eq_sum rK85 ⟨18, by decide⟩ e heK h T85_18 hfix85_18 hinj85_18 hcardT85_18
    (fun i => conj_mem_of_fixedPoints (reps ⟨18, by decide⟩) (reps rK85) (T85_18 i) (hfix85_18 i) h)

/-! ## Cell (85, 20): |T| = 5 -/

def T85_20list : List Coordinates := [(0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0)]
def T85_20 : Fin 5 → Coordinate 1 := fun i => T85_20list.getD i.val (0,0,0,0,0)

theorem hfix85_20 : ∀ i, ((T85_20 i : Coordinate 1) : Coordinate 1 ⧸ reps rK85)
    ∈ fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85) :=
  repsFix_of_siftB rK85 ⟨20, by decide⟩ T85_20 (by decide)

theorem hinj85_20 : Function.Injective
    (fun i => ((T85_20 i : Coordinate 1) : Coordinate 1 ⧸ reps rK85)) :=
  repsInj_of_reduceAux rK85 T85_20 (by decide)

theorem hcardT85_20 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK85 ⟨20, by decide⟩ R85 hpxR85 hcardq85 (by decide)).symm

/-- **Cell (85, 20).** -/
theorem cell85_20 (e : List (ZMod 25)) (heK : charOK (basisAt rK85) e = true)
    (h : ↥(reps (⟨20, by decide⟩ : Fin 148))) :
    species (reps (⟨20, by decide⟩ : Fin 148)) h (basisElt (reps rK85) (charOfVec rK85 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK85 e (h : Coordinate 1) T85_20 i :=
  species_entry_eq_sum rK85 ⟨20, by decide⟩ e heK h T85_20 hfix85_20 hinj85_20 hcardT85_20
    (fun i => conj_mem_of_fixedPoints (reps ⟨20, by decide⟩) (reps rK85) (T85_20 i) (hfix85_20 i) h)

/-! ## Cell (85, 21): |T| = 5 -/

def T85_21list : List Coordinates := [(0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0)]
def T85_21 : Fin 5 → Coordinate 1 := fun i => T85_21list.getD i.val (0,0,0,0,0)

theorem hfix85_21 : ∀ i, ((T85_21 i : Coordinate 1) : Coordinate 1 ⧸ reps rK85)
    ∈ fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85) :=
  repsFix_of_siftB rK85 ⟨21, by decide⟩ T85_21 (by decide)

theorem hinj85_21 : Function.Injective
    (fun i => ((T85_21 i : Coordinate 1) : Coordinate 1 ⧸ reps rK85)) :=
  repsInj_of_reduceAux rK85 T85_21 (by decide)

theorem hcardT85_21 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK85 ⟨21, by decide⟩ R85 hpxR85 hcardq85 (by decide)).symm

/-- **Cell (85, 21).** -/
theorem cell85_21 (e : List (ZMod 25)) (heK : charOK (basisAt rK85) e = true)
    (h : ↥(reps (⟨21, by decide⟩ : Fin 148))) :
    species (reps (⟨21, by decide⟩ : Fin 148)) h (basisElt (reps rK85) (charOfVec rK85 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK85 e (h : Coordinate 1) T85_21 i :=
  species_entry_eq_sum rK85 ⟨21, by decide⟩ e heK h T85_21 hfix85_21 hinj85_21 hcardT85_21
    (fun i => conj_mem_of_fixedPoints (reps ⟨21, by decide⟩) (reps rK85) (T85_21 i) (hfix85_21 i) h)

/-! ## Cell (85, 22): |T| = 5 -/

def T85_22list : List Coordinates := [(0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0)]
def T85_22 : Fin 5 → Coordinate 1 := fun i => T85_22list.getD i.val (0,0,0,0,0)

theorem hfix85_22 : ∀ i, ((T85_22 i : Coordinate 1) : Coordinate 1 ⧸ reps rK85)
    ∈ fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85) :=
  repsFix_of_siftB rK85 ⟨22, by decide⟩ T85_22 (by decide)

theorem hinj85_22 : Function.Injective
    (fun i => ((T85_22 i : Coordinate 1) : Coordinate 1 ⧸ reps rK85)) :=
  repsInj_of_reduceAux rK85 T85_22 (by decide)

theorem hcardT85_22 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK85 ⟨22, by decide⟩ R85 hpxR85 hcardq85 (by decide)).symm

/-- **Cell (85, 22).** -/
theorem cell85_22 (e : List (ZMod 25)) (heK : charOK (basisAt rK85) e = true)
    (h : ↥(reps (⟨22, by decide⟩ : Fin 148))) :
    species (reps (⟨22, by decide⟩ : Fin 148)) h (basisElt (reps rK85) (charOfVec rK85 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK85 e (h : Coordinate 1) T85_22 i :=
  species_entry_eq_sum rK85 ⟨22, by decide⟩ e heK h T85_22 hfix85_22 hinj85_22 hcardT85_22
    (fun i => conj_mem_of_fixedPoints (reps ⟨22, by decide⟩) (reps rK85) (T85_22 i) (hfix85_22 i) h)

/-! ## Cell (85, 23): |T| = 5 -/

def T85_23list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0)]
def T85_23 : Fin 5 → Coordinate 1 := fun i => T85_23list.getD i.val (0,0,0,0,0)

theorem hfix85_23 : ∀ i, ((T85_23 i : Coordinate 1) : Coordinate 1 ⧸ reps rK85)
    ∈ fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85) :=
  repsFix_of_siftB rK85 ⟨23, by decide⟩ T85_23 (by decide)

theorem hinj85_23 : Function.Injective
    (fun i => ((T85_23 i : Coordinate 1) : Coordinate 1 ⧸ reps rK85)) :=
  repsInj_of_reduceAux rK85 T85_23 (by decide)

theorem hcardT85_23 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK85 ⟨23, by decide⟩ R85 hpxR85 hcardq85 (by decide)).symm

/-- **Cell (85, 23).** -/
theorem cell85_23 (e : List (ZMod 25)) (heK : charOK (basisAt rK85) e = true)
    (h : ↥(reps (⟨23, by decide⟩ : Fin 148))) :
    species (reps (⟨23, by decide⟩ : Fin 148)) h (basisElt (reps rK85) (charOfVec rK85 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK85 e (h : Coordinate 1) T85_23 i :=
  species_entry_eq_sum rK85 ⟨23, by decide⟩ e heK h T85_23 hfix85_23 hinj85_23 hcardT85_23
    (fun i => conj_mem_of_fixedPoints (reps ⟨23, by decide⟩) (reps rK85) (T85_23 i) (hfix85_23 i) h)

/-! ## Cell (85, 27): |T| = 25 -/

def T85_27list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0)]
def T85_27 : Fin 25 → Coordinate 1 := fun i => T85_27list.getD i.val (0,0,0,0,0)

theorem hfix85_27 : ∀ i, ((T85_27 i : Coordinate 1) : Coordinate 1 ⧸ reps rK85)
    ∈ fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85) :=
  repsFix_of_siftB rK85 ⟨27, by decide⟩ T85_27 (by decide)

theorem hinj85_27 : Function.Injective
    (fun i => ((T85_27 i : Coordinate 1) : Coordinate 1 ⧸ reps rK85)) :=
  repsInj_of_reduceAux rK85 T85_27 (by decide)

theorem hcardT85_27 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK85 ⟨27, by decide⟩ R85 hpxR85 hcardq85 (by decide)).symm

/-- **Cell (85, 27).** -/
theorem cell85_27 (e : List (ZMod 25)) (heK : charOK (basisAt rK85) e = true)
    (h : ↥(reps (⟨27, by decide⟩ : Fin 148))) :
    species (reps (⟨27, by decide⟩ : Fin 148)) h (basisElt (reps rK85) (charOfVec rK85 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK85 e (h : Coordinate 1) T85_27 i :=
  species_entry_eq_sum rK85 ⟨27, by decide⟩ e heK h T85_27 hfix85_27 hinj85_27 hcardT85_27
    (fun i => conj_mem_of_fixedPoints (reps ⟨27, by decide⟩) (reps rK85) (T85_27 i) (hfix85_27 i) h)

/-! ## Cell (85, 54): |T| = 5 -/

def T85_54list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0)]
def T85_54 : Fin 5 → Coordinate 1 := fun i => T85_54list.getD i.val (0,0,0,0,0)

theorem hfix85_54 : ∀ i, ((T85_54 i : Coordinate 1) : Coordinate 1 ⧸ reps rK85)
    ∈ fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85) :=
  repsFix_of_siftB rK85 ⟨54, by decide⟩ T85_54 (by decide)

theorem hinj85_54 : Function.Injective
    (fun i => ((T85_54 i : Coordinate 1) : Coordinate 1 ⧸ reps rK85)) :=
  repsInj_of_reduceAux rK85 T85_54 (by decide)

theorem hcardT85_54 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK85 ⟨54, by decide⟩ R85 hpxR85 hcardq85 (by decide)).symm

/-- **Cell (85, 54).** -/
theorem cell85_54 (e : List (ZMod 25)) (heK : charOK (basisAt rK85) e = true)
    (h : ↥(reps (⟨54, by decide⟩ : Fin 148))) :
    species (reps (⟨54, by decide⟩ : Fin 148)) h (basisElt (reps rK85) (charOfVec rK85 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK85 e (h : Coordinate 1) T85_54 i :=
  species_entry_eq_sum rK85 ⟨54, by decide⟩ e heK h T85_54 hfix85_54 hinj85_54 hcardT85_54
    (fun i => conj_mem_of_fixedPoints (reps ⟨54, by decide⟩) (reps rK85) (T85_54 i) (hfix85_54 i) h)

/-! ## Cell (85, 85): |T| = 5 -/

def T85_85list : List Coordinates := [(0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0)]
def T85_85 : Fin 5 → Coordinate 1 := fun i => T85_85list.getD i.val (0,0,0,0,0)

theorem hfix85_85 : ∀ i, ((T85_85 i : Coordinate 1) : Coordinate 1 ⧸ reps rK85)
    ∈ fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85) :=
  repsFix_of_siftB rK85 ⟨85, by decide⟩ T85_85 (by decide)

theorem hinj85_85 : Function.Injective
    (fun i => ((T85_85 i : Coordinate 1) : Coordinate 1 ⧸ reps rK85)) :=
  repsInj_of_reduceAux rK85 T85_85 (by decide)

theorem hcardT85_85 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK85 ⟨85, by decide⟩ R85 hpxR85 hcardq85 (by decide)).symm

/-- **Cell (85, 85).** -/
theorem cell85_85 (e : List (ZMod 25)) (heK : charOK (basisAt rK85) e = true)
    (h : ↥(reps (⟨85, by decide⟩ : Fin 148))) :
    species (reps (⟨85, by decide⟩ : Fin 148)) h (basisElt (reps rK85) (charOfVec rK85 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK85 e (h : Coordinate 1) T85_85 i :=
  species_entry_eq_sum rK85 ⟨85, by decide⟩ e heK h T85_85 hfix85_85 hinj85_85 hcardT85_85
    (fun i => conj_mem_of_fixedPoints (reps ⟨85, by decide⟩) (reps rK85) (T85_85 i) (hfix85_85 i) h)

namespace Q2

def R85_2 : Fin 25 → Coordinate 2 := fun i => R85list.getD i.val (0,0,0,0,0)
theorem hpxR85_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK85) (R85_2 i)) := by decide
theorem hcardq85_2 : Nat.card (Coordinate 2 ⧸ reps rK85) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (85, 0) twin -/

def T85_0_2 : Fin 25 → Coordinate 2 := fun i => T85_0list.getD i.val (0,0,0,0,0)

theorem hfix85_0_2 : ∀ i, ((T85_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK85)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK85) :=
  repsFix_of_siftB2 rK85 ⟨0, by decide⟩ T85_0_2 (by decide)

theorem hinj85_0_2 : Function.Injective
    (fun i => ((T85_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK85)) :=
  repsInj_of_reduceAux2 rK85 T85_0_2 (by decide)

theorem hcardT85_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK85)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK85 ⟨0, by decide⟩ R85_2 hpxR85_2 hcardq85_2 (by decide)).symm

/-- **Cell (85, 0) twin (q=2).** -/
theorem cell85_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK85) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK85) (charOfVec2 rK85 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK85 e (h : Coordinate 2) T85_0_2 i :=
  species_entry_eq_sum rK85 ⟨0, by decide⟩ e heK h T85_0_2 hfix85_0_2 hinj85_0_2 hcardT85_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK85) (T85_0_2 i) (hfix85_0_2 i) h)

/-! ### Cell (85, 2) twin -/

def T85_2_2 : Fin 5 → Coordinate 2 := fun i => T85_2list.getD i.val (0,0,0,0,0)

theorem hfix85_2_2 : ∀ i, ((T85_2_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK85)
    ∈ fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK85) :=
  repsFix_of_siftB2 rK85 ⟨2, by decide⟩ T85_2_2 (by decide)

theorem hinj85_2_2 : Function.Injective
    (fun i => ((T85_2_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK85)) :=
  repsInj_of_reduceAux2 rK85 T85_2_2 (by decide)

theorem hcardT85_2_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK85)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK85 ⟨2, by decide⟩ R85_2 hpxR85_2 hcardq85_2 (by decide)).symm

/-- **Cell (85, 2) twin (q=2).** -/
theorem cell85_2_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK85) e = true)
    (h : ↥(reps (⟨2, by decide⟩ : Fin 148))) :
    species (reps (⟨2, by decide⟩ : Fin 148)) h (basisElt (reps rK85) (charOfVec2 rK85 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK85 e (h : Coordinate 2) T85_2_2 i :=
  species_entry_eq_sum rK85 ⟨2, by decide⟩ e heK h T85_2_2 hfix85_2_2 hinj85_2_2 hcardT85_2_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨2, by decide⟩) (reps rK85) (T85_2_2 i) (hfix85_2_2 i) h)

/-! ### Cell (85, 3) twin -/

def T85_3_2 : Fin 5 → Coordinate 2 := fun i => T85_3list.getD i.val (0,0,0,0,0)

theorem hfix85_3_2 : ∀ i, ((T85_3_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK85)
    ∈ fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK85) :=
  repsFix_of_siftB2 rK85 ⟨3, by decide⟩ T85_3_2 (by decide)

theorem hinj85_3_2 : Function.Injective
    (fun i => ((T85_3_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK85)) :=
  repsInj_of_reduceAux2 rK85 T85_3_2 (by decide)

theorem hcardT85_3_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK85)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK85 ⟨3, by decide⟩ R85_2 hpxR85_2 hcardq85_2 (by decide)).symm

/-- **Cell (85, 3) twin (q=2).** -/
theorem cell85_3_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK85) e = true)
    (h : ↥(reps (⟨3, by decide⟩ : Fin 148))) :
    species (reps (⟨3, by decide⟩ : Fin 148)) h (basisElt (reps rK85) (charOfVec2 rK85 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK85 e (h : Coordinate 2) T85_3_2 i :=
  species_entry_eq_sum rK85 ⟨3, by decide⟩ e heK h T85_3_2 hfix85_3_2 hinj85_3_2 hcardT85_3_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨3, by decide⟩) (reps rK85) (T85_3_2 i) (hfix85_3_2 i) h)

/-! ### Cell (85, 4) twin -/

def T85_4_2 : Fin 5 → Coordinate 2 := fun i => T85_4list.getD i.val (0,0,0,0,0)

theorem hfix85_4_2 : ∀ i, ((T85_4_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK85)
    ∈ fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK85) :=
  repsFix_of_siftB2 rK85 ⟨4, by decide⟩ T85_4_2 (by decide)

theorem hinj85_4_2 : Function.Injective
    (fun i => ((T85_4_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK85)) :=
  repsInj_of_reduceAux2 rK85 T85_4_2 (by decide)

theorem hcardT85_4_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK85)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK85 ⟨4, by decide⟩ R85_2 hpxR85_2 hcardq85_2 (by decide)).symm

/-- **Cell (85, 4) twin (q=2).** -/
theorem cell85_4_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK85) e = true)
    (h : ↥(reps (⟨4, by decide⟩ : Fin 148))) :
    species (reps (⟨4, by decide⟩ : Fin 148)) h (basisElt (reps rK85) (charOfVec2 rK85 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK85 e (h : Coordinate 2) T85_4_2 i :=
  species_entry_eq_sum rK85 ⟨4, by decide⟩ e heK h T85_4_2 hfix85_4_2 hinj85_4_2 hcardT85_4_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨4, by decide⟩) (reps rK85) (T85_4_2 i) (hfix85_4_2 i) h)

/-! ### Cell (85, 5) twin -/

def T85_5_2 : Fin 5 → Coordinate 2 := fun i => T85_5list.getD i.val (0,0,0,0,0)

theorem hfix85_5_2 : ∀ i, ((T85_5_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK85)
    ∈ fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK85) :=
  repsFix_of_siftB2 rK85 ⟨5, by decide⟩ T85_5_2 (by decide)

theorem hinj85_5_2 : Function.Injective
    (fun i => ((T85_5_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK85)) :=
  repsInj_of_reduceAux2 rK85 T85_5_2 (by decide)

theorem hcardT85_5_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK85)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK85 ⟨5, by decide⟩ R85_2 hpxR85_2 hcardq85_2 (by decide)).symm

/-- **Cell (85, 5) twin (q=2).** -/
theorem cell85_5_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK85) e = true)
    (h : ↥(reps (⟨5, by decide⟩ : Fin 148))) :
    species (reps (⟨5, by decide⟩ : Fin 148)) h (basisElt (reps rK85) (charOfVec2 rK85 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK85 e (h : Coordinate 2) T85_5_2 i :=
  species_entry_eq_sum rK85 ⟨5, by decide⟩ e heK h T85_5_2 hfix85_5_2 hinj85_5_2 hcardT85_5_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨5, by decide⟩) (reps rK85) (T85_5_2 i) (hfix85_5_2 i) h)

/-! ### Cell (85, 9) twin -/

def T85_9_2 : Fin 25 → Coordinate 2 := fun i => T85_9list.getD i.val (0,0,0,0,0)

theorem hfix85_9_2 : ∀ i, ((T85_9_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK85)
    ∈ fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK85) :=
  repsFix_of_siftB2 rK85 ⟨9, by decide⟩ T85_9_2 (by decide)

theorem hinj85_9_2 : Function.Injective
    (fun i => ((T85_9_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK85)) :=
  repsInj_of_reduceAux2 rK85 T85_9_2 (by decide)

theorem hcardT85_9_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK85)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK85 ⟨9, by decide⟩ R85_2 hpxR85_2 hcardq85_2 (by decide)).symm

/-- **Cell (85, 9) twin (q=2).** -/
theorem cell85_9_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK85) e = true)
    (h : ↥(reps (⟨9, by decide⟩ : Fin 148))) :
    species (reps (⟨9, by decide⟩ : Fin 148)) h (basisElt (reps rK85) (charOfVec2 rK85 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK85 e (h : Coordinate 2) T85_9_2 i :=
  species_entry_eq_sum rK85 ⟨9, by decide⟩ e heK h T85_9_2 hfix85_9_2 hinj85_9_2 hcardT85_9_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨9, by decide⟩) (reps rK85) (T85_9_2 i) (hfix85_9_2 i) h)

/-! ### Cell (85, 11) twin -/

def T85_11_2 : Fin 5 → Coordinate 2 := fun i => T85_11list.getD i.val (0,0,0,0,0)

theorem hfix85_11_2 : ∀ i, ((T85_11_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK85)
    ∈ fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK85) :=
  repsFix_of_siftB2 rK85 ⟨11, by decide⟩ T85_11_2 (by decide)

theorem hinj85_11_2 : Function.Injective
    (fun i => ((T85_11_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK85)) :=
  repsInj_of_reduceAux2 rK85 T85_11_2 (by decide)

theorem hcardT85_11_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK85)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK85 ⟨11, by decide⟩ R85_2 hpxR85_2 hcardq85_2 (by decide)).symm

/-- **Cell (85, 11) twin (q=2).** -/
theorem cell85_11_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK85) e = true)
    (h : ↥(reps (⟨11, by decide⟩ : Fin 148))) :
    species (reps (⟨11, by decide⟩ : Fin 148)) h (basisElt (reps rK85) (charOfVec2 rK85 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK85 e (h : Coordinate 2) T85_11_2 i :=
  species_entry_eq_sum rK85 ⟨11, by decide⟩ e heK h T85_11_2 hfix85_11_2 hinj85_11_2 hcardT85_11_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨11, by decide⟩) (reps rK85) (T85_11_2 i) (hfix85_11_2 i) h)

/-! ### Cell (85, 12) twin -/

def T85_12_2 : Fin 25 → Coordinate 2 := fun i => T85_12list.getD i.val (0,0,0,0,0)

theorem hfix85_12_2 : ∀ i, ((T85_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK85)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK85) :=
  repsFix_of_siftB2 rK85 ⟨12, by decide⟩ T85_12_2 (by decide)

theorem hinj85_12_2 : Function.Injective
    (fun i => ((T85_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK85)) :=
  repsInj_of_reduceAux2 rK85 T85_12_2 (by decide)

theorem hcardT85_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK85)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK85 ⟨12, by decide⟩ R85_2 hpxR85_2 hcardq85_2 (by decide)).symm

/-- **Cell (85, 12) twin (q=2).** -/
theorem cell85_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK85) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK85) (charOfVec2 rK85 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK85 e (h : Coordinate 2) T85_12_2 i :=
  species_entry_eq_sum rK85 ⟨12, by decide⟩ e heK h T85_12_2 hfix85_12_2 hinj85_12_2 hcardT85_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK85) (T85_12_2 i) (hfix85_12_2 i) h)

/-! ### Cell (85, 14) twin -/

def T85_14_2 : Fin 5 → Coordinate 2 := fun i => T85_14list.getD i.val (0,0,0,0,0)

theorem hfix85_14_2 : ∀ i, ((T85_14_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK85)
    ∈ fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK85) :=
  repsFix_of_siftB2 rK85 ⟨14, by decide⟩ T85_14_2 (by decide)

theorem hinj85_14_2 : Function.Injective
    (fun i => ((T85_14_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK85)) :=
  repsInj_of_reduceAux2 rK85 T85_14_2 (by decide)

theorem hcardT85_14_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK85)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK85 ⟨14, by decide⟩ R85_2 hpxR85_2 hcardq85_2 (by decide)).symm

/-- **Cell (85, 14) twin (q=2).** -/
theorem cell85_14_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK85) e = true)
    (h : ↥(reps (⟨14, by decide⟩ : Fin 148))) :
    species (reps (⟨14, by decide⟩ : Fin 148)) h (basisElt (reps rK85) (charOfVec2 rK85 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK85 e (h : Coordinate 2) T85_14_2 i :=
  species_entry_eq_sum rK85 ⟨14, by decide⟩ e heK h T85_14_2 hfix85_14_2 hinj85_14_2 hcardT85_14_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨14, by decide⟩) (reps rK85) (T85_14_2 i) (hfix85_14_2 i) h)

/-! ### Cell (85, 15) twin -/

def T85_15_2 : Fin 5 → Coordinate 2 := fun i => T85_15list.getD i.val (0,0,0,0,0)

theorem hfix85_15_2 : ∀ i, ((T85_15_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK85)
    ∈ fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK85) :=
  repsFix_of_siftB2 rK85 ⟨15, by decide⟩ T85_15_2 (by decide)

theorem hinj85_15_2 : Function.Injective
    (fun i => ((T85_15_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK85)) :=
  repsInj_of_reduceAux2 rK85 T85_15_2 (by decide)

theorem hcardT85_15_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK85)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK85 ⟨15, by decide⟩ R85_2 hpxR85_2 hcardq85_2 (by decide)).symm

/-- **Cell (85, 15) twin (q=2).** -/
theorem cell85_15_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK85) e = true)
    (h : ↥(reps (⟨15, by decide⟩ : Fin 148))) :
    species (reps (⟨15, by decide⟩ : Fin 148)) h (basisElt (reps rK85) (charOfVec2 rK85 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK85 e (h : Coordinate 2) T85_15_2 i :=
  species_entry_eq_sum rK85 ⟨15, by decide⟩ e heK h T85_15_2 hfix85_15_2 hinj85_15_2 hcardT85_15_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨15, by decide⟩) (reps rK85) (T85_15_2 i) (hfix85_15_2 i) h)

/-! ### Cell (85, 16) twin -/

def T85_16_2 : Fin 5 → Coordinate 2 := fun i => T85_16list.getD i.val (0,0,0,0,0)

theorem hfix85_16_2 : ∀ i, ((T85_16_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK85)
    ∈ fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK85) :=
  repsFix_of_siftB2 rK85 ⟨16, by decide⟩ T85_16_2 (by decide)

theorem hinj85_16_2 : Function.Injective
    (fun i => ((T85_16_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK85)) :=
  repsInj_of_reduceAux2 rK85 T85_16_2 (by decide)

theorem hcardT85_16_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK85)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK85 ⟨16, by decide⟩ R85_2 hpxR85_2 hcardq85_2 (by decide)).symm

/-- **Cell (85, 16) twin (q=2).** -/
theorem cell85_16_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK85) e = true)
    (h : ↥(reps (⟨16, by decide⟩ : Fin 148))) :
    species (reps (⟨16, by decide⟩ : Fin 148)) h (basisElt (reps rK85) (charOfVec2 rK85 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK85 e (h : Coordinate 2) T85_16_2 i :=
  species_entry_eq_sum rK85 ⟨16, by decide⟩ e heK h T85_16_2 hfix85_16_2 hinj85_16_2 hcardT85_16_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨16, by decide⟩) (reps rK85) (T85_16_2 i) (hfix85_16_2 i) h)

/-! ### Cell (85, 17) twin -/

def T85_17_2 : Fin 5 → Coordinate 2 := fun i => T85_17list.getD i.val (0,0,0,0,0)

theorem hfix85_17_2 : ∀ i, ((T85_17_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK85)
    ∈ fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK85) :=
  repsFix_of_siftB2 rK85 ⟨17, by decide⟩ T85_17_2 (by decide)

theorem hinj85_17_2 : Function.Injective
    (fun i => ((T85_17_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK85)) :=
  repsInj_of_reduceAux2 rK85 T85_17_2 (by decide)

theorem hcardT85_17_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK85)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK85 ⟨17, by decide⟩ R85_2 hpxR85_2 hcardq85_2 (by decide)).symm

/-- **Cell (85, 17) twin (q=2).** -/
theorem cell85_17_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK85) e = true)
    (h : ↥(reps (⟨17, by decide⟩ : Fin 148))) :
    species (reps (⟨17, by decide⟩ : Fin 148)) h (basisElt (reps rK85) (charOfVec2 rK85 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK85 e (h : Coordinate 2) T85_17_2 i :=
  species_entry_eq_sum rK85 ⟨17, by decide⟩ e heK h T85_17_2 hfix85_17_2 hinj85_17_2 hcardT85_17_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨17, by decide⟩) (reps rK85) (T85_17_2 i) (hfix85_17_2 i) h)

/-! ### Cell (85, 18) twin -/

def T85_18_2 : Fin 5 → Coordinate 2 := fun i => T85_18list.getD i.val (0,0,0,0,0)

theorem hfix85_18_2 : ∀ i, ((T85_18_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK85)
    ∈ fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK85) :=
  repsFix_of_siftB2 rK85 ⟨18, by decide⟩ T85_18_2 (by decide)

theorem hinj85_18_2 : Function.Injective
    (fun i => ((T85_18_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK85)) :=
  repsInj_of_reduceAux2 rK85 T85_18_2 (by decide)

theorem hcardT85_18_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK85)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK85 ⟨18, by decide⟩ R85_2 hpxR85_2 hcardq85_2 (by decide)).symm

/-- **Cell (85, 18) twin (q=2).** -/
theorem cell85_18_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK85) e = true)
    (h : ↥(reps (⟨18, by decide⟩ : Fin 148))) :
    species (reps (⟨18, by decide⟩ : Fin 148)) h (basisElt (reps rK85) (charOfVec2 rK85 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK85 e (h : Coordinate 2) T85_18_2 i :=
  species_entry_eq_sum rK85 ⟨18, by decide⟩ e heK h T85_18_2 hfix85_18_2 hinj85_18_2 hcardT85_18_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨18, by decide⟩) (reps rK85) (T85_18_2 i) (hfix85_18_2 i) h)

/-! ### Cell (85, 20) twin -/

def T85_20_2 : Fin 5 → Coordinate 2 := fun i => T85_20list.getD i.val (0,0,0,0,0)

theorem hfix85_20_2 : ∀ i, ((T85_20_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK85)
    ∈ fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK85) :=
  repsFix_of_siftB2 rK85 ⟨20, by decide⟩ T85_20_2 (by decide)

theorem hinj85_20_2 : Function.Injective
    (fun i => ((T85_20_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK85)) :=
  repsInj_of_reduceAux2 rK85 T85_20_2 (by decide)

theorem hcardT85_20_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK85)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK85 ⟨20, by decide⟩ R85_2 hpxR85_2 hcardq85_2 (by decide)).symm

/-- **Cell (85, 20) twin (q=2).** -/
theorem cell85_20_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK85) e = true)
    (h : ↥(reps (⟨20, by decide⟩ : Fin 148))) :
    species (reps (⟨20, by decide⟩ : Fin 148)) h (basisElt (reps rK85) (charOfVec2 rK85 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK85 e (h : Coordinate 2) T85_20_2 i :=
  species_entry_eq_sum rK85 ⟨20, by decide⟩ e heK h T85_20_2 hfix85_20_2 hinj85_20_2 hcardT85_20_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨20, by decide⟩) (reps rK85) (T85_20_2 i) (hfix85_20_2 i) h)

/-! ### Cell (85, 21) twin -/

def T85_21_2 : Fin 5 → Coordinate 2 := fun i => T85_21list.getD i.val (0,0,0,0,0)

theorem hfix85_21_2 : ∀ i, ((T85_21_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK85)
    ∈ fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK85) :=
  repsFix_of_siftB2 rK85 ⟨21, by decide⟩ T85_21_2 (by decide)

theorem hinj85_21_2 : Function.Injective
    (fun i => ((T85_21_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK85)) :=
  repsInj_of_reduceAux2 rK85 T85_21_2 (by decide)

theorem hcardT85_21_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK85)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK85 ⟨21, by decide⟩ R85_2 hpxR85_2 hcardq85_2 (by decide)).symm

/-- **Cell (85, 21) twin (q=2).** -/
theorem cell85_21_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK85) e = true)
    (h : ↥(reps (⟨21, by decide⟩ : Fin 148))) :
    species (reps (⟨21, by decide⟩ : Fin 148)) h (basisElt (reps rK85) (charOfVec2 rK85 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK85 e (h : Coordinate 2) T85_21_2 i :=
  species_entry_eq_sum rK85 ⟨21, by decide⟩ e heK h T85_21_2 hfix85_21_2 hinj85_21_2 hcardT85_21_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨21, by decide⟩) (reps rK85) (T85_21_2 i) (hfix85_21_2 i) h)

/-! ### Cell (85, 22) twin -/

def T85_22_2 : Fin 5 → Coordinate 2 := fun i => T85_22list.getD i.val (0,0,0,0,0)

theorem hfix85_22_2 : ∀ i, ((T85_22_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK85)
    ∈ fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK85) :=
  repsFix_of_siftB2 rK85 ⟨22, by decide⟩ T85_22_2 (by decide)

theorem hinj85_22_2 : Function.Injective
    (fun i => ((T85_22_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK85)) :=
  repsInj_of_reduceAux2 rK85 T85_22_2 (by decide)

theorem hcardT85_22_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK85)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK85 ⟨22, by decide⟩ R85_2 hpxR85_2 hcardq85_2 (by decide)).symm

/-- **Cell (85, 22) twin (q=2).** -/
theorem cell85_22_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK85) e = true)
    (h : ↥(reps (⟨22, by decide⟩ : Fin 148))) :
    species (reps (⟨22, by decide⟩ : Fin 148)) h (basisElt (reps rK85) (charOfVec2 rK85 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK85 e (h : Coordinate 2) T85_22_2 i :=
  species_entry_eq_sum rK85 ⟨22, by decide⟩ e heK h T85_22_2 hfix85_22_2 hinj85_22_2 hcardT85_22_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨22, by decide⟩) (reps rK85) (T85_22_2 i) (hfix85_22_2 i) h)

/-! ### Cell (85, 23) twin -/

def T85_23_2 : Fin 5 → Coordinate 2 := fun i => T85_23list.getD i.val (0,0,0,0,0)

theorem hfix85_23_2 : ∀ i, ((T85_23_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK85)
    ∈ fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK85) :=
  repsFix_of_siftB2 rK85 ⟨23, by decide⟩ T85_23_2 (by decide)

theorem hinj85_23_2 : Function.Injective
    (fun i => ((T85_23_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK85)) :=
  repsInj_of_reduceAux2 rK85 T85_23_2 (by decide)

theorem hcardT85_23_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK85)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK85 ⟨23, by decide⟩ R85_2 hpxR85_2 hcardq85_2 (by decide)).symm

/-- **Cell (85, 23) twin (q=2).** -/
theorem cell85_23_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK85) e = true)
    (h : ↥(reps (⟨23, by decide⟩ : Fin 148))) :
    species (reps (⟨23, by decide⟩ : Fin 148)) h (basisElt (reps rK85) (charOfVec2 rK85 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK85 e (h : Coordinate 2) T85_23_2 i :=
  species_entry_eq_sum rK85 ⟨23, by decide⟩ e heK h T85_23_2 hfix85_23_2 hinj85_23_2 hcardT85_23_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨23, by decide⟩) (reps rK85) (T85_23_2 i) (hfix85_23_2 i) h)

/-! ### Cell (85, 27) twin -/

def T85_27_2 : Fin 25 → Coordinate 2 := fun i => T85_27list.getD i.val (0,0,0,0,0)

theorem hfix85_27_2 : ∀ i, ((T85_27_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK85)
    ∈ fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK85) :=
  repsFix_of_siftB2 rK85 ⟨27, by decide⟩ T85_27_2 (by decide)

theorem hinj85_27_2 : Function.Injective
    (fun i => ((T85_27_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK85)) :=
  repsInj_of_reduceAux2 rK85 T85_27_2 (by decide)

theorem hcardT85_27_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK85)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK85 ⟨27, by decide⟩ R85_2 hpxR85_2 hcardq85_2 (by decide)).symm

/-- **Cell (85, 27) twin (q=2).** -/
theorem cell85_27_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK85) e = true)
    (h : ↥(reps (⟨27, by decide⟩ : Fin 148))) :
    species (reps (⟨27, by decide⟩ : Fin 148)) h (basisElt (reps rK85) (charOfVec2 rK85 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK85 e (h : Coordinate 2) T85_27_2 i :=
  species_entry_eq_sum rK85 ⟨27, by decide⟩ e heK h T85_27_2 hfix85_27_2 hinj85_27_2 hcardT85_27_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨27, by decide⟩) (reps rK85) (T85_27_2 i) (hfix85_27_2 i) h)

/-! ### Cell (85, 54) twin -/

def T85_54_2 : Fin 5 → Coordinate 2 := fun i => T85_54list.getD i.val (0,0,0,0,0)

theorem hfix85_54_2 : ∀ i, ((T85_54_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK85)
    ∈ fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK85) :=
  repsFix_of_siftB2 rK85 ⟨54, by decide⟩ T85_54_2 (by decide)

theorem hinj85_54_2 : Function.Injective
    (fun i => ((T85_54_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK85)) :=
  repsInj_of_reduceAux2 rK85 T85_54_2 (by decide)

theorem hcardT85_54_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK85)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK85 ⟨54, by decide⟩ R85_2 hpxR85_2 hcardq85_2 (by decide)).symm

/-- **Cell (85, 54) twin (q=2).** -/
theorem cell85_54_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK85) e = true)
    (h : ↥(reps (⟨54, by decide⟩ : Fin 148))) :
    species (reps (⟨54, by decide⟩ : Fin 148)) h (basisElt (reps rK85) (charOfVec2 rK85 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK85 e (h : Coordinate 2) T85_54_2 i :=
  species_entry_eq_sum rK85 ⟨54, by decide⟩ e heK h T85_54_2 hfix85_54_2 hinj85_54_2 hcardT85_54_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨54, by decide⟩) (reps rK85) (T85_54_2 i) (hfix85_54_2 i) h)

/-! ### Cell (85, 85) twin -/

def T85_85_2 : Fin 5 → Coordinate 2 := fun i => T85_85list.getD i.val (0,0,0,0,0)

theorem hfix85_85_2 : ∀ i, ((T85_85_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK85)
    ∈ fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK85) :=
  repsFix_of_siftB2 rK85 ⟨85, by decide⟩ T85_85_2 (by decide)

theorem hinj85_85_2 : Function.Injective
    (fun i => ((T85_85_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK85)) :=
  repsInj_of_reduceAux2 rK85 T85_85_2 (by decide)

theorem hcardT85_85_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK85)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK85 ⟨85, by decide⟩ R85_2 hpxR85_2 hcardq85_2 (by decide)).symm

/-- **Cell (85, 85) twin (q=2).** -/
theorem cell85_85_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK85) e = true)
    (h : ↥(reps (⟨85, by decide⟩ : Fin 148))) :
    species (reps (⟨85, by decide⟩ : Fin 148)) h (basisElt (reps rK85) (charOfVec2 rK85 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK85 e (h : Coordinate 2) T85_85_2 i :=
  species_entry_eq_sum rK85 ⟨85, by decide⟩ e heK h T85_85_2 hfix85_85_2 hinj85_85_2 hcardT85_85_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨85, by decide⟩) (reps rK85) (T85_85_2 i) (hfix85_85_2 i) h)

end Q2

/-! # K-class rK = 86  (|G/K| = 25) -/

def rK86 : Fin 148 := ⟨86, by decide⟩

def R86list : List Coordinates := [(0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0)]
def R86 : Fin 25 → Coordinate 1 := fun i => R86list.getD i.val (0,0,0,0,0)

theorem hpxR86 : Function.Injective (fun i => reduceAux 1 (basisAt rK86) (R86 i)) := by decide
theorem hcardq86 : Nat.card (Coordinate 1 ⧸ reps rK86) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (86, 0): |T| = 25 -/

def T86_0list : List Coordinates := [(0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0)]
def T86_0 : Fin 25 → Coordinate 1 := fun i => T86_0list.getD i.val (0,0,0,0,0)

theorem hfix86_0 : ∀ i, ((T86_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK86)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86) :=
  repsFix_of_siftB rK86 ⟨0, by decide⟩ T86_0 (by decide)

theorem hinj86_0 : Function.Injective
    (fun i => ((T86_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK86)) :=
  repsInj_of_reduceAux rK86 T86_0 (by decide)

theorem hcardT86_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK86 ⟨0, by decide⟩ R86 hpxR86 hcardq86 (by decide)).symm

/-- **Cell (86, 0).** -/
theorem cell86_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK86) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK86) (charOfVec rK86 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK86 e (h : Coordinate 1) T86_0 i :=
  species_entry_eq_sum rK86 ⟨0, by decide⟩ e heK h T86_0 hfix86_0 hinj86_0 hcardT86_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK86) (T86_0 i) (hfix86_0 i) h)

/-! ## Cell (86, 1): |T| = 25 -/

def T86_1list : List Coordinates := [(0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0)]
def T86_1 : Fin 25 → Coordinate 1 := fun i => T86_1list.getD i.val (0,0,0,0,0)

theorem hfix86_1 : ∀ i, ((T86_1 i : Coordinate 1) : Coordinate 1 ⧸ reps rK86)
    ∈ fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86) :=
  repsFix_of_siftB rK86 ⟨1, by decide⟩ T86_1 (by decide)

theorem hinj86_1 : Function.Injective
    (fun i => ((T86_1 i : Coordinate 1) : Coordinate 1 ⧸ reps rK86)) :=
  repsInj_of_reduceAux rK86 T86_1 (by decide)

theorem hcardT86_1 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK86 ⟨1, by decide⟩ R86 hpxR86 hcardq86 (by decide)).symm

/-- **Cell (86, 1).** -/
theorem cell86_1 (e : List (ZMod 25)) (heK : charOK (basisAt rK86) e = true)
    (h : ↥(reps (⟨1, by decide⟩ : Fin 148))) :
    species (reps (⟨1, by decide⟩ : Fin 148)) h (basisElt (reps rK86) (charOfVec rK86 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK86 e (h : Coordinate 1) T86_1 i :=
  species_entry_eq_sum rK86 ⟨1, by decide⟩ e heK h T86_1 hfix86_1 hinj86_1 hcardT86_1
    (fun i => conj_mem_of_fixedPoints (reps ⟨1, by decide⟩) (reps rK86) (T86_1 i) (hfix86_1 i) h)

/-! ## Cell (86, 2): |T| = 5 -/

def T86_2list : List Coordinates := [(0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0)]
def T86_2 : Fin 5 → Coordinate 1 := fun i => T86_2list.getD i.val (0,0,0,0,0)

theorem hfix86_2 : ∀ i, ((T86_2 i : Coordinate 1) : Coordinate 1 ⧸ reps rK86)
    ∈ fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86) :=
  repsFix_of_siftB rK86 ⟨2, by decide⟩ T86_2 (by decide)

theorem hinj86_2 : Function.Injective
    (fun i => ((T86_2 i : Coordinate 1) : Coordinate 1 ⧸ reps rK86)) :=
  repsInj_of_reduceAux rK86 T86_2 (by decide)

theorem hcardT86_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK86 ⟨2, by decide⟩ R86 hpxR86 hcardq86 (by decide)).symm

/-- **Cell (86, 2).** -/
theorem cell86_2 (e : List (ZMod 25)) (heK : charOK (basisAt rK86) e = true)
    (h : ↥(reps (⟨2, by decide⟩ : Fin 148))) :
    species (reps (⟨2, by decide⟩ : Fin 148)) h (basisElt (reps rK86) (charOfVec rK86 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK86 e (h : Coordinate 1) T86_2 i :=
  species_entry_eq_sum rK86 ⟨2, by decide⟩ e heK h T86_2 hfix86_2 hinj86_2 hcardT86_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨2, by decide⟩) (reps rK86) (T86_2 i) (hfix86_2 i) h)

/-! ## Cell (86, 3): |T| = 5 -/

def T86_3list : List Coordinates := [(0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0)]
def T86_3 : Fin 5 → Coordinate 1 := fun i => T86_3list.getD i.val (0,0,0,0,0)

theorem hfix86_3 : ∀ i, ((T86_3 i : Coordinate 1) : Coordinate 1 ⧸ reps rK86)
    ∈ fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86) :=
  repsFix_of_siftB rK86 ⟨3, by decide⟩ T86_3 (by decide)

theorem hinj86_3 : Function.Injective
    (fun i => ((T86_3 i : Coordinate 1) : Coordinate 1 ⧸ reps rK86)) :=
  repsInj_of_reduceAux rK86 T86_3 (by decide)

theorem hcardT86_3 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK86 ⟨3, by decide⟩ R86 hpxR86 hcardq86 (by decide)).symm

/-- **Cell (86, 3).** -/
theorem cell86_3 (e : List (ZMod 25)) (heK : charOK (basisAt rK86) e = true)
    (h : ↥(reps (⟨3, by decide⟩ : Fin 148))) :
    species (reps (⟨3, by decide⟩ : Fin 148)) h (basisElt (reps rK86) (charOfVec rK86 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK86 e (h : Coordinate 1) T86_3 i :=
  species_entry_eq_sum rK86 ⟨3, by decide⟩ e heK h T86_3 hfix86_3 hinj86_3 hcardT86_3
    (fun i => conj_mem_of_fixedPoints (reps ⟨3, by decide⟩) (reps rK86) (T86_3 i) (hfix86_3 i) h)

/-! ## Cell (86, 4): |T| = 5 -/

def T86_4list : List Coordinates := [(0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0)]
def T86_4 : Fin 5 → Coordinate 1 := fun i => T86_4list.getD i.val (0,0,0,0,0)

theorem hfix86_4 : ∀ i, ((T86_4 i : Coordinate 1) : Coordinate 1 ⧸ reps rK86)
    ∈ fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86) :=
  repsFix_of_siftB rK86 ⟨4, by decide⟩ T86_4 (by decide)

theorem hinj86_4 : Function.Injective
    (fun i => ((T86_4 i : Coordinate 1) : Coordinate 1 ⧸ reps rK86)) :=
  repsInj_of_reduceAux rK86 T86_4 (by decide)

theorem hcardT86_4 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK86 ⟨4, by decide⟩ R86 hpxR86 hcardq86 (by decide)).symm

/-- **Cell (86, 4).** -/
theorem cell86_4 (e : List (ZMod 25)) (heK : charOK (basisAt rK86) e = true)
    (h : ↥(reps (⟨4, by decide⟩ : Fin 148))) :
    species (reps (⟨4, by decide⟩ : Fin 148)) h (basisElt (reps rK86) (charOfVec rK86 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK86 e (h : Coordinate 1) T86_4 i :=
  species_entry_eq_sum rK86 ⟨4, by decide⟩ e heK h T86_4 hfix86_4 hinj86_4 hcardT86_4
    (fun i => conj_mem_of_fixedPoints (reps ⟨4, by decide⟩) (reps rK86) (T86_4 i) (hfix86_4 i) h)

/-! ## Cell (86, 5): |T| = 5 -/

def T86_5list : List Coordinates := [(0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0)]
def T86_5 : Fin 5 → Coordinate 1 := fun i => T86_5list.getD i.val (0,0,0,0,0)

theorem hfix86_5 : ∀ i, ((T86_5 i : Coordinate 1) : Coordinate 1 ⧸ reps rK86)
    ∈ fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86) :=
  repsFix_of_siftB rK86 ⟨5, by decide⟩ T86_5 (by decide)

theorem hinj86_5 : Function.Injective
    (fun i => ((T86_5 i : Coordinate 1) : Coordinate 1 ⧸ reps rK86)) :=
  repsInj_of_reduceAux rK86 T86_5 (by decide)

theorem hcardT86_5 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK86 ⟨5, by decide⟩ R86 hpxR86 hcardq86 (by decide)).symm

/-- **Cell (86, 5).** -/
theorem cell86_5 (e : List (ZMod 25)) (heK : charOK (basisAt rK86) e = true)
    (h : ↥(reps (⟨5, by decide⟩ : Fin 148))) :
    species (reps (⟨5, by decide⟩ : Fin 148)) h (basisElt (reps rK86) (charOfVec rK86 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK86 e (h : Coordinate 1) T86_5 i :=
  species_entry_eq_sum rK86 ⟨5, by decide⟩ e heK h T86_5 hfix86_5 hinj86_5 hcardT86_5
    (fun i => conj_mem_of_fixedPoints (reps ⟨5, by decide⟩) (reps rK86) (T86_5 i) (hfix86_5 i) h)

/-! ## Cell (86, 11): |T| = 5 -/

def T86_11list : List Coordinates := [(0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0)]
def T86_11 : Fin 5 → Coordinate 1 := fun i => T86_11list.getD i.val (0,0,0,0,0)

theorem hfix86_11 : ∀ i, ((T86_11 i : Coordinate 1) : Coordinate 1 ⧸ reps rK86)
    ∈ fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86) :=
  repsFix_of_siftB rK86 ⟨11, by decide⟩ T86_11 (by decide)

theorem hinj86_11 : Function.Injective
    (fun i => ((T86_11 i : Coordinate 1) : Coordinate 1 ⧸ reps rK86)) :=
  repsInj_of_reduceAux rK86 T86_11 (by decide)

theorem hcardT86_11 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK86 ⟨11, by decide⟩ R86 hpxR86 hcardq86 (by decide)).symm

/-- **Cell (86, 11).** -/
theorem cell86_11 (e : List (ZMod 25)) (heK : charOK (basisAt rK86) e = true)
    (h : ↥(reps (⟨11, by decide⟩ : Fin 148))) :
    species (reps (⟨11, by decide⟩ : Fin 148)) h (basisElt (reps rK86) (charOfVec rK86 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK86 e (h : Coordinate 1) T86_11 i :=
  species_entry_eq_sum rK86 ⟨11, by decide⟩ e heK h T86_11 hfix86_11 hinj86_11 hcardT86_11
    (fun i => conj_mem_of_fixedPoints (reps ⟨11, by decide⟩) (reps rK86) (T86_11 i) (hfix86_11 i) h)

/-! ## Cell (86, 12): |T| = 25 -/

def T86_12list : List Coordinates := [(0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0)]
def T86_12 : Fin 25 → Coordinate 1 := fun i => T86_12list.getD i.val (0,0,0,0,0)

theorem hfix86_12 : ∀ i, ((T86_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK86)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86) :=
  repsFix_of_siftB rK86 ⟨12, by decide⟩ T86_12 (by decide)

theorem hinj86_12 : Function.Injective
    (fun i => ((T86_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK86)) :=
  repsInj_of_reduceAux rK86 T86_12 (by decide)

theorem hcardT86_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK86 ⟨12, by decide⟩ R86 hpxR86 hcardq86 (by decide)).symm

/-- **Cell (86, 12).** -/
theorem cell86_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK86) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK86) (charOfVec rK86 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK86 e (h : Coordinate 1) T86_12 i :=
  species_entry_eq_sum rK86 ⟨12, by decide⟩ e heK h T86_12 hfix86_12 hinj86_12 hcardT86_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK86) (T86_12 i) (hfix86_12 i) h)

/-! ## Cell (86, 19): |T| = 25 -/

def T86_19list : List Coordinates := [(0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0)]
def T86_19 : Fin 25 → Coordinate 1 := fun i => T86_19list.getD i.val (0,0,0,0,0)

theorem hfix86_19 : ∀ i, ((T86_19 i : Coordinate 1) : Coordinate 1 ⧸ reps rK86)
    ∈ fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86) :=
  repsFix_of_siftB rK86 ⟨19, by decide⟩ T86_19 (by decide)

theorem hinj86_19 : Function.Injective
    (fun i => ((T86_19 i : Coordinate 1) : Coordinate 1 ⧸ reps rK86)) :=
  repsInj_of_reduceAux rK86 T86_19 (by decide)

theorem hcardT86_19 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK86 ⟨19, by decide⟩ R86 hpxR86 hcardq86 (by decide)).symm

/-- **Cell (86, 19).** -/
theorem cell86_19 (e : List (ZMod 25)) (heK : charOK (basisAt rK86) e = true)
    (h : ↥(reps (⟨19, by decide⟩ : Fin 148))) :
    species (reps (⟨19, by decide⟩ : Fin 148)) h (basisElt (reps rK86) (charOfVec rK86 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK86 e (h : Coordinate 1) T86_19 i :=
  species_entry_eq_sum rK86 ⟨19, by decide⟩ e heK h T86_19 hfix86_19 hinj86_19 hcardT86_19
    (fun i => conj_mem_of_fixedPoints (reps ⟨19, by decide⟩) (reps rK86) (T86_19 i) (hfix86_19 i) h)

/-! ## Cell (86, 20): |T| = 5 -/

def T86_20list : List Coordinates := [(0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0)]
def T86_20 : Fin 5 → Coordinate 1 := fun i => T86_20list.getD i.val (0,0,0,0,0)

theorem hfix86_20 : ∀ i, ((T86_20 i : Coordinate 1) : Coordinate 1 ⧸ reps rK86)
    ∈ fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86) :=
  repsFix_of_siftB rK86 ⟨20, by decide⟩ T86_20 (by decide)

theorem hinj86_20 : Function.Injective
    (fun i => ((T86_20 i : Coordinate 1) : Coordinate 1 ⧸ reps rK86)) :=
  repsInj_of_reduceAux rK86 T86_20 (by decide)

theorem hcardT86_20 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK86 ⟨20, by decide⟩ R86 hpxR86 hcardq86 (by decide)).symm

/-- **Cell (86, 20).** -/
theorem cell86_20 (e : List (ZMod 25)) (heK : charOK (basisAt rK86) e = true)
    (h : ↥(reps (⟨20, by decide⟩ : Fin 148))) :
    species (reps (⟨20, by decide⟩ : Fin 148)) h (basisElt (reps rK86) (charOfVec rK86 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK86 e (h : Coordinate 1) T86_20 i :=
  species_entry_eq_sum rK86 ⟨20, by decide⟩ e heK h T86_20 hfix86_20 hinj86_20 hcardT86_20
    (fun i => conj_mem_of_fixedPoints (reps ⟨20, by decide⟩) (reps rK86) (T86_20 i) (hfix86_20 i) h)

/-! ## Cell (86, 21): |T| = 5 -/

def T86_21list : List Coordinates := [(0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0)]
def T86_21 : Fin 5 → Coordinate 1 := fun i => T86_21list.getD i.val (0,0,0,0,0)

theorem hfix86_21 : ∀ i, ((T86_21 i : Coordinate 1) : Coordinate 1 ⧸ reps rK86)
    ∈ fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86) :=
  repsFix_of_siftB rK86 ⟨21, by decide⟩ T86_21 (by decide)

theorem hinj86_21 : Function.Injective
    (fun i => ((T86_21 i : Coordinate 1) : Coordinate 1 ⧸ reps rK86)) :=
  repsInj_of_reduceAux rK86 T86_21 (by decide)

theorem hcardT86_21 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK86 ⟨21, by decide⟩ R86 hpxR86 hcardq86 (by decide)).symm

/-- **Cell (86, 21).** -/
theorem cell86_21 (e : List (ZMod 25)) (heK : charOK (basisAt rK86) e = true)
    (h : ↥(reps (⟨21, by decide⟩ : Fin 148))) :
    species (reps (⟨21, by decide⟩ : Fin 148)) h (basisElt (reps rK86) (charOfVec rK86 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK86 e (h : Coordinate 1) T86_21 i :=
  species_entry_eq_sum rK86 ⟨21, by decide⟩ e heK h T86_21 hfix86_21 hinj86_21 hcardT86_21
    (fun i => conj_mem_of_fixedPoints (reps ⟨21, by decide⟩) (reps rK86) (T86_21 i) (hfix86_21 i) h)

/-! ## Cell (86, 22): |T| = 5 -/

def T86_22list : List Coordinates := [(0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0)]
def T86_22 : Fin 5 → Coordinate 1 := fun i => T86_22list.getD i.val (0,0,0,0,0)

theorem hfix86_22 : ∀ i, ((T86_22 i : Coordinate 1) : Coordinate 1 ⧸ reps rK86)
    ∈ fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86) :=
  repsFix_of_siftB rK86 ⟨22, by decide⟩ T86_22 (by decide)

theorem hinj86_22 : Function.Injective
    (fun i => ((T86_22 i : Coordinate 1) : Coordinate 1 ⧸ reps rK86)) :=
  repsInj_of_reduceAux rK86 T86_22 (by decide)

theorem hcardT86_22 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK86 ⟨22, by decide⟩ R86 hpxR86 hcardq86 (by decide)).symm

/-- **Cell (86, 22).** -/
theorem cell86_22 (e : List (ZMod 25)) (heK : charOK (basisAt rK86) e = true)
    (h : ↥(reps (⟨22, by decide⟩ : Fin 148))) :
    species (reps (⟨22, by decide⟩ : Fin 148)) h (basisElt (reps rK86) (charOfVec rK86 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK86 e (h : Coordinate 1) T86_22 i :=
  species_entry_eq_sum rK86 ⟨22, by decide⟩ e heK h T86_22 hfix86_22 hinj86_22 hcardT86_22
    (fun i => conj_mem_of_fixedPoints (reps ⟨22, by decide⟩) (reps rK86) (T86_22 i) (hfix86_22 i) h)

/-! ## Cell (86, 23): |T| = 5 -/

def T86_23list : List Coordinates := [(0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0)]
def T86_23 : Fin 5 → Coordinate 1 := fun i => T86_23list.getD i.val (0,0,0,0,0)

theorem hfix86_23 : ∀ i, ((T86_23 i : Coordinate 1) : Coordinate 1 ⧸ reps rK86)
    ∈ fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86) :=
  repsFix_of_siftB rK86 ⟨23, by decide⟩ T86_23 (by decide)

theorem hinj86_23 : Function.Injective
    (fun i => ((T86_23 i : Coordinate 1) : Coordinate 1 ⧸ reps rK86)) :=
  repsInj_of_reduceAux rK86 T86_23 (by decide)

theorem hcardT86_23 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK86 ⟨23, by decide⟩ R86 hpxR86 hcardq86 (by decide)).symm

/-- **Cell (86, 23).** -/
theorem cell86_23 (e : List (ZMod 25)) (heK : charOK (basisAt rK86) e = true)
    (h : ↥(reps (⟨23, by decide⟩ : Fin 148))) :
    species (reps (⟨23, by decide⟩ : Fin 148)) h (basisElt (reps rK86) (charOfVec rK86 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK86 e (h : Coordinate 1) T86_23 i :=
  species_entry_eq_sum rK86 ⟨23, by decide⟩ e heK h T86_23 hfix86_23 hinj86_23 hcardT86_23
    (fun i => conj_mem_of_fixedPoints (reps ⟨23, by decide⟩) (reps rK86) (T86_23 i) (hfix86_23 i) h)

/-! ## Cell (86, 54): |T| = 5 -/

def T86_54list : List Coordinates := [(0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0)]
def T86_54 : Fin 5 → Coordinate 1 := fun i => T86_54list.getD i.val (0,0,0,0,0)

theorem hfix86_54 : ∀ i, ((T86_54 i : Coordinate 1) : Coordinate 1 ⧸ reps rK86)
    ∈ fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86) :=
  repsFix_of_siftB rK86 ⟨54, by decide⟩ T86_54 (by decide)

theorem hinj86_54 : Function.Injective
    (fun i => ((T86_54 i : Coordinate 1) : Coordinate 1 ⧸ reps rK86)) :=
  repsInj_of_reduceAux rK86 T86_54 (by decide)

theorem hcardT86_54 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK86 ⟨54, by decide⟩ R86 hpxR86 hcardq86 (by decide)).symm

/-- **Cell (86, 54).** -/
theorem cell86_54 (e : List (ZMod 25)) (heK : charOK (basisAt rK86) e = true)
    (h : ↥(reps (⟨54, by decide⟩ : Fin 148))) :
    species (reps (⟨54, by decide⟩ : Fin 148)) h (basisElt (reps rK86) (charOfVec rK86 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK86 e (h : Coordinate 1) T86_54 i :=
  species_entry_eq_sum rK86 ⟨54, by decide⟩ e heK h T86_54 hfix86_54 hinj86_54 hcardT86_54
    (fun i => conj_mem_of_fixedPoints (reps ⟨54, by decide⟩) (reps rK86) (T86_54 i) (hfix86_54 i) h)

/-! ## Cell (86, 86): |T| = 5 -/

def T86_86list : List Coordinates := [(0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0)]
def T86_86 : Fin 5 → Coordinate 1 := fun i => T86_86list.getD i.val (0,0,0,0,0)

theorem hfix86_86 : ∀ i, ((T86_86 i : Coordinate 1) : Coordinate 1 ⧸ reps rK86)
    ∈ fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86) :=
  repsFix_of_siftB rK86 ⟨86, by decide⟩ T86_86 (by decide)

theorem hinj86_86 : Function.Injective
    (fun i => ((T86_86 i : Coordinate 1) : Coordinate 1 ⧸ reps rK86)) :=
  repsInj_of_reduceAux rK86 T86_86 (by decide)

theorem hcardT86_86 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK86 ⟨86, by decide⟩ R86 hpxR86 hcardq86 (by decide)).symm

/-- **Cell (86, 86).** -/
theorem cell86_86 (e : List (ZMod 25)) (heK : charOK (basisAt rK86) e = true)
    (h : ↥(reps (⟨86, by decide⟩ : Fin 148))) :
    species (reps (⟨86, by decide⟩ : Fin 148)) h (basisElt (reps rK86) (charOfVec rK86 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK86 e (h : Coordinate 1) T86_86 i :=
  species_entry_eq_sum rK86 ⟨86, by decide⟩ e heK h T86_86 hfix86_86 hinj86_86 hcardT86_86
    (fun i => conj_mem_of_fixedPoints (reps ⟨86, by decide⟩) (reps rK86) (T86_86 i) (hfix86_86 i) h)

namespace Q2

def R86_2 : Fin 25 → Coordinate 2 := fun i => R86list.getD i.val (0,0,0,0,0)
theorem hpxR86_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK86) (R86_2 i)) := by decide
theorem hcardq86_2 : Nat.card (Coordinate 2 ⧸ reps rK86) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (86, 0) twin -/

def T86_0_2 : Fin 25 → Coordinate 2 := fun i => T86_0list.getD i.val (0,0,0,0,0)

theorem hfix86_0_2 : ∀ i, ((T86_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK86)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK86) :=
  repsFix_of_siftB2 rK86 ⟨0, by decide⟩ T86_0_2 (by decide)

theorem hinj86_0_2 : Function.Injective
    (fun i => ((T86_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK86)) :=
  repsInj_of_reduceAux2 rK86 T86_0_2 (by decide)

theorem hcardT86_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK86)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK86 ⟨0, by decide⟩ R86_2 hpxR86_2 hcardq86_2 (by decide)).symm

/-- **Cell (86, 0) twin (q=2).** -/
theorem cell86_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK86) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK86) (charOfVec2 rK86 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK86 e (h : Coordinate 2) T86_0_2 i :=
  species_entry_eq_sum rK86 ⟨0, by decide⟩ e heK h T86_0_2 hfix86_0_2 hinj86_0_2 hcardT86_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK86) (T86_0_2 i) (hfix86_0_2 i) h)

/-! ### Cell (86, 1) twin -/

def T86_1_2 : Fin 25 → Coordinate 2 := fun i => T86_1list.getD i.val (0,0,0,0,0)

theorem hfix86_1_2 : ∀ i, ((T86_1_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK86)
    ∈ fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK86) :=
  repsFix_of_siftB2 rK86 ⟨1, by decide⟩ T86_1_2 (by decide)

theorem hinj86_1_2 : Function.Injective
    (fun i => ((T86_1_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK86)) :=
  repsInj_of_reduceAux2 rK86 T86_1_2 (by decide)

theorem hcardT86_1_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK86)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK86 ⟨1, by decide⟩ R86_2 hpxR86_2 hcardq86_2 (by decide)).symm

/-- **Cell (86, 1) twin (q=2).** -/
theorem cell86_1_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK86) e = true)
    (h : ↥(reps (⟨1, by decide⟩ : Fin 148))) :
    species (reps (⟨1, by decide⟩ : Fin 148)) h (basisElt (reps rK86) (charOfVec2 rK86 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK86 e (h : Coordinate 2) T86_1_2 i :=
  species_entry_eq_sum rK86 ⟨1, by decide⟩ e heK h T86_1_2 hfix86_1_2 hinj86_1_2 hcardT86_1_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨1, by decide⟩) (reps rK86) (T86_1_2 i) (hfix86_1_2 i) h)

/-! ### Cell (86, 2) twin -/

def T86_2_2 : Fin 5 → Coordinate 2 := fun i => T86_2list.getD i.val (0,0,0,0,0)

theorem hfix86_2_2 : ∀ i, ((T86_2_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK86)
    ∈ fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK86) :=
  repsFix_of_siftB2 rK86 ⟨2, by decide⟩ T86_2_2 (by decide)

theorem hinj86_2_2 : Function.Injective
    (fun i => ((T86_2_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK86)) :=
  repsInj_of_reduceAux2 rK86 T86_2_2 (by decide)

theorem hcardT86_2_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK86)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK86 ⟨2, by decide⟩ R86_2 hpxR86_2 hcardq86_2 (by decide)).symm

/-- **Cell (86, 2) twin (q=2).** -/
theorem cell86_2_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK86) e = true)
    (h : ↥(reps (⟨2, by decide⟩ : Fin 148))) :
    species (reps (⟨2, by decide⟩ : Fin 148)) h (basisElt (reps rK86) (charOfVec2 rK86 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK86 e (h : Coordinate 2) T86_2_2 i :=
  species_entry_eq_sum rK86 ⟨2, by decide⟩ e heK h T86_2_2 hfix86_2_2 hinj86_2_2 hcardT86_2_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨2, by decide⟩) (reps rK86) (T86_2_2 i) (hfix86_2_2 i) h)

/-! ### Cell (86, 3) twin -/

def T86_3_2 : Fin 5 → Coordinate 2 := fun i => T86_3list.getD i.val (0,0,0,0,0)

theorem hfix86_3_2 : ∀ i, ((T86_3_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK86)
    ∈ fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK86) :=
  repsFix_of_siftB2 rK86 ⟨3, by decide⟩ T86_3_2 (by decide)

theorem hinj86_3_2 : Function.Injective
    (fun i => ((T86_3_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK86)) :=
  repsInj_of_reduceAux2 rK86 T86_3_2 (by decide)

theorem hcardT86_3_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK86)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK86 ⟨3, by decide⟩ R86_2 hpxR86_2 hcardq86_2 (by decide)).symm

/-- **Cell (86, 3) twin (q=2).** -/
theorem cell86_3_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK86) e = true)
    (h : ↥(reps (⟨3, by decide⟩ : Fin 148))) :
    species (reps (⟨3, by decide⟩ : Fin 148)) h (basisElt (reps rK86) (charOfVec2 rK86 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK86 e (h : Coordinate 2) T86_3_2 i :=
  species_entry_eq_sum rK86 ⟨3, by decide⟩ e heK h T86_3_2 hfix86_3_2 hinj86_3_2 hcardT86_3_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨3, by decide⟩) (reps rK86) (T86_3_2 i) (hfix86_3_2 i) h)

/-! ### Cell (86, 4) twin -/

def T86_4_2 : Fin 5 → Coordinate 2 := fun i => T86_4list.getD i.val (0,0,0,0,0)

theorem hfix86_4_2 : ∀ i, ((T86_4_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK86)
    ∈ fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK86) :=
  repsFix_of_siftB2 rK86 ⟨4, by decide⟩ T86_4_2 (by decide)

theorem hinj86_4_2 : Function.Injective
    (fun i => ((T86_4_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK86)) :=
  repsInj_of_reduceAux2 rK86 T86_4_2 (by decide)

theorem hcardT86_4_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK86)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK86 ⟨4, by decide⟩ R86_2 hpxR86_2 hcardq86_2 (by decide)).symm

/-- **Cell (86, 4) twin (q=2).** -/
theorem cell86_4_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK86) e = true)
    (h : ↥(reps (⟨4, by decide⟩ : Fin 148))) :
    species (reps (⟨4, by decide⟩ : Fin 148)) h (basisElt (reps rK86) (charOfVec2 rK86 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK86 e (h : Coordinate 2) T86_4_2 i :=
  species_entry_eq_sum rK86 ⟨4, by decide⟩ e heK h T86_4_2 hfix86_4_2 hinj86_4_2 hcardT86_4_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨4, by decide⟩) (reps rK86) (T86_4_2 i) (hfix86_4_2 i) h)

/-! ### Cell (86, 5) twin -/

def T86_5_2 : Fin 5 → Coordinate 2 := fun i => T86_5list.getD i.val (0,0,0,0,0)

theorem hfix86_5_2 : ∀ i, ((T86_5_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK86)
    ∈ fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK86) :=
  repsFix_of_siftB2 rK86 ⟨5, by decide⟩ T86_5_2 (by decide)

theorem hinj86_5_2 : Function.Injective
    (fun i => ((T86_5_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK86)) :=
  repsInj_of_reduceAux2 rK86 T86_5_2 (by decide)

theorem hcardT86_5_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK86)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK86 ⟨5, by decide⟩ R86_2 hpxR86_2 hcardq86_2 (by decide)).symm

/-- **Cell (86, 5) twin (q=2).** -/
theorem cell86_5_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK86) e = true)
    (h : ↥(reps (⟨5, by decide⟩ : Fin 148))) :
    species (reps (⟨5, by decide⟩ : Fin 148)) h (basisElt (reps rK86) (charOfVec2 rK86 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK86 e (h : Coordinate 2) T86_5_2 i :=
  species_entry_eq_sum rK86 ⟨5, by decide⟩ e heK h T86_5_2 hfix86_5_2 hinj86_5_2 hcardT86_5_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨5, by decide⟩) (reps rK86) (T86_5_2 i) (hfix86_5_2 i) h)

/-! ### Cell (86, 11) twin -/

def T86_11_2 : Fin 5 → Coordinate 2 := fun i => T86_11list.getD i.val (0,0,0,0,0)

theorem hfix86_11_2 : ∀ i, ((T86_11_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK86)
    ∈ fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK86) :=
  repsFix_of_siftB2 rK86 ⟨11, by decide⟩ T86_11_2 (by decide)

theorem hinj86_11_2 : Function.Injective
    (fun i => ((T86_11_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK86)) :=
  repsInj_of_reduceAux2 rK86 T86_11_2 (by decide)

theorem hcardT86_11_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK86)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK86 ⟨11, by decide⟩ R86_2 hpxR86_2 hcardq86_2 (by decide)).symm

/-- **Cell (86, 11) twin (q=2).** -/
theorem cell86_11_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK86) e = true)
    (h : ↥(reps (⟨11, by decide⟩ : Fin 148))) :
    species (reps (⟨11, by decide⟩ : Fin 148)) h (basisElt (reps rK86) (charOfVec2 rK86 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK86 e (h : Coordinate 2) T86_11_2 i :=
  species_entry_eq_sum rK86 ⟨11, by decide⟩ e heK h T86_11_2 hfix86_11_2 hinj86_11_2 hcardT86_11_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨11, by decide⟩) (reps rK86) (T86_11_2 i) (hfix86_11_2 i) h)

/-! ### Cell (86, 12) twin -/

def T86_12_2 : Fin 25 → Coordinate 2 := fun i => T86_12list.getD i.val (0,0,0,0,0)

theorem hfix86_12_2 : ∀ i, ((T86_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK86)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK86) :=
  repsFix_of_siftB2 rK86 ⟨12, by decide⟩ T86_12_2 (by decide)

theorem hinj86_12_2 : Function.Injective
    (fun i => ((T86_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK86)) :=
  repsInj_of_reduceAux2 rK86 T86_12_2 (by decide)

theorem hcardT86_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK86)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK86 ⟨12, by decide⟩ R86_2 hpxR86_2 hcardq86_2 (by decide)).symm

/-- **Cell (86, 12) twin (q=2).** -/
theorem cell86_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK86) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK86) (charOfVec2 rK86 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK86 e (h : Coordinate 2) T86_12_2 i :=
  species_entry_eq_sum rK86 ⟨12, by decide⟩ e heK h T86_12_2 hfix86_12_2 hinj86_12_2 hcardT86_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK86) (T86_12_2 i) (hfix86_12_2 i) h)

/-! ### Cell (86, 19) twin -/

def T86_19_2 : Fin 25 → Coordinate 2 := fun i => T86_19list.getD i.val (0,0,0,0,0)

theorem hfix86_19_2 : ∀ i, ((T86_19_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK86)
    ∈ fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK86) :=
  repsFix_of_siftB2 rK86 ⟨19, by decide⟩ T86_19_2 (by decide)

theorem hinj86_19_2 : Function.Injective
    (fun i => ((T86_19_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK86)) :=
  repsInj_of_reduceAux2 rK86 T86_19_2 (by decide)

theorem hcardT86_19_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK86)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK86 ⟨19, by decide⟩ R86_2 hpxR86_2 hcardq86_2 (by decide)).symm

/-- **Cell (86, 19) twin (q=2).** -/
theorem cell86_19_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK86) e = true)
    (h : ↥(reps (⟨19, by decide⟩ : Fin 148))) :
    species (reps (⟨19, by decide⟩ : Fin 148)) h (basisElt (reps rK86) (charOfVec2 rK86 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK86 e (h : Coordinate 2) T86_19_2 i :=
  species_entry_eq_sum rK86 ⟨19, by decide⟩ e heK h T86_19_2 hfix86_19_2 hinj86_19_2 hcardT86_19_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨19, by decide⟩) (reps rK86) (T86_19_2 i) (hfix86_19_2 i) h)

/-! ### Cell (86, 20) twin -/

def T86_20_2 : Fin 5 → Coordinate 2 := fun i => T86_20list.getD i.val (0,0,0,0,0)

theorem hfix86_20_2 : ∀ i, ((T86_20_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK86)
    ∈ fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK86) :=
  repsFix_of_siftB2 rK86 ⟨20, by decide⟩ T86_20_2 (by decide)

theorem hinj86_20_2 : Function.Injective
    (fun i => ((T86_20_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK86)) :=
  repsInj_of_reduceAux2 rK86 T86_20_2 (by decide)

theorem hcardT86_20_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK86)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK86 ⟨20, by decide⟩ R86_2 hpxR86_2 hcardq86_2 (by decide)).symm

/-- **Cell (86, 20) twin (q=2).** -/
theorem cell86_20_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK86) e = true)
    (h : ↥(reps (⟨20, by decide⟩ : Fin 148))) :
    species (reps (⟨20, by decide⟩ : Fin 148)) h (basisElt (reps rK86) (charOfVec2 rK86 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK86 e (h : Coordinate 2) T86_20_2 i :=
  species_entry_eq_sum rK86 ⟨20, by decide⟩ e heK h T86_20_2 hfix86_20_2 hinj86_20_2 hcardT86_20_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨20, by decide⟩) (reps rK86) (T86_20_2 i) (hfix86_20_2 i) h)

/-! ### Cell (86, 21) twin -/

def T86_21_2 : Fin 5 → Coordinate 2 := fun i => T86_21list.getD i.val (0,0,0,0,0)

theorem hfix86_21_2 : ∀ i, ((T86_21_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK86)
    ∈ fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK86) :=
  repsFix_of_siftB2 rK86 ⟨21, by decide⟩ T86_21_2 (by decide)

theorem hinj86_21_2 : Function.Injective
    (fun i => ((T86_21_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK86)) :=
  repsInj_of_reduceAux2 rK86 T86_21_2 (by decide)

theorem hcardT86_21_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK86)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK86 ⟨21, by decide⟩ R86_2 hpxR86_2 hcardq86_2 (by decide)).symm

/-- **Cell (86, 21) twin (q=2).** -/
theorem cell86_21_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK86) e = true)
    (h : ↥(reps (⟨21, by decide⟩ : Fin 148))) :
    species (reps (⟨21, by decide⟩ : Fin 148)) h (basisElt (reps rK86) (charOfVec2 rK86 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK86 e (h : Coordinate 2) T86_21_2 i :=
  species_entry_eq_sum rK86 ⟨21, by decide⟩ e heK h T86_21_2 hfix86_21_2 hinj86_21_2 hcardT86_21_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨21, by decide⟩) (reps rK86) (T86_21_2 i) (hfix86_21_2 i) h)

/-! ### Cell (86, 22) twin -/

def T86_22_2 : Fin 5 → Coordinate 2 := fun i => T86_22list.getD i.val (0,0,0,0,0)

theorem hfix86_22_2 : ∀ i, ((T86_22_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK86)
    ∈ fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK86) :=
  repsFix_of_siftB2 rK86 ⟨22, by decide⟩ T86_22_2 (by decide)

theorem hinj86_22_2 : Function.Injective
    (fun i => ((T86_22_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK86)) :=
  repsInj_of_reduceAux2 rK86 T86_22_2 (by decide)

theorem hcardT86_22_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK86)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK86 ⟨22, by decide⟩ R86_2 hpxR86_2 hcardq86_2 (by decide)).symm

/-- **Cell (86, 22) twin (q=2).** -/
theorem cell86_22_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK86) e = true)
    (h : ↥(reps (⟨22, by decide⟩ : Fin 148))) :
    species (reps (⟨22, by decide⟩ : Fin 148)) h (basisElt (reps rK86) (charOfVec2 rK86 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK86 e (h : Coordinate 2) T86_22_2 i :=
  species_entry_eq_sum rK86 ⟨22, by decide⟩ e heK h T86_22_2 hfix86_22_2 hinj86_22_2 hcardT86_22_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨22, by decide⟩) (reps rK86) (T86_22_2 i) (hfix86_22_2 i) h)

/-! ### Cell (86, 23) twin -/

def T86_23_2 : Fin 5 → Coordinate 2 := fun i => T86_23list.getD i.val (0,0,0,0,0)

theorem hfix86_23_2 : ∀ i, ((T86_23_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK86)
    ∈ fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK86) :=
  repsFix_of_siftB2 rK86 ⟨23, by decide⟩ T86_23_2 (by decide)

theorem hinj86_23_2 : Function.Injective
    (fun i => ((T86_23_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK86)) :=
  repsInj_of_reduceAux2 rK86 T86_23_2 (by decide)

theorem hcardT86_23_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK86)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK86 ⟨23, by decide⟩ R86_2 hpxR86_2 hcardq86_2 (by decide)).symm

/-- **Cell (86, 23) twin (q=2).** -/
theorem cell86_23_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK86) e = true)
    (h : ↥(reps (⟨23, by decide⟩ : Fin 148))) :
    species (reps (⟨23, by decide⟩ : Fin 148)) h (basisElt (reps rK86) (charOfVec2 rK86 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK86 e (h : Coordinate 2) T86_23_2 i :=
  species_entry_eq_sum rK86 ⟨23, by decide⟩ e heK h T86_23_2 hfix86_23_2 hinj86_23_2 hcardT86_23_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨23, by decide⟩) (reps rK86) (T86_23_2 i) (hfix86_23_2 i) h)

/-! ### Cell (86, 54) twin -/

def T86_54_2 : Fin 5 → Coordinate 2 := fun i => T86_54list.getD i.val (0,0,0,0,0)

theorem hfix86_54_2 : ∀ i, ((T86_54_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK86)
    ∈ fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK86) :=
  repsFix_of_siftB2 rK86 ⟨54, by decide⟩ T86_54_2 (by decide)

theorem hinj86_54_2 : Function.Injective
    (fun i => ((T86_54_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK86)) :=
  repsInj_of_reduceAux2 rK86 T86_54_2 (by decide)

theorem hcardT86_54_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK86)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK86 ⟨54, by decide⟩ R86_2 hpxR86_2 hcardq86_2 (by decide)).symm

/-- **Cell (86, 54) twin (q=2).** -/
theorem cell86_54_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK86) e = true)
    (h : ↥(reps (⟨54, by decide⟩ : Fin 148))) :
    species (reps (⟨54, by decide⟩ : Fin 148)) h (basisElt (reps rK86) (charOfVec2 rK86 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK86 e (h : Coordinate 2) T86_54_2 i :=
  species_entry_eq_sum rK86 ⟨54, by decide⟩ e heK h T86_54_2 hfix86_54_2 hinj86_54_2 hcardT86_54_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨54, by decide⟩) (reps rK86) (T86_54_2 i) (hfix86_54_2 i) h)

/-! ### Cell (86, 86) twin -/

def T86_86_2 : Fin 5 → Coordinate 2 := fun i => T86_86list.getD i.val (0,0,0,0,0)

theorem hfix86_86_2 : ∀ i, ((T86_86_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK86)
    ∈ fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK86) :=
  repsFix_of_siftB2 rK86 ⟨86, by decide⟩ T86_86_2 (by decide)

theorem hinj86_86_2 : Function.Injective
    (fun i => ((T86_86_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK86)) :=
  repsInj_of_reduceAux2 rK86 T86_86_2 (by decide)

theorem hcardT86_86_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK86)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK86 ⟨86, by decide⟩ R86_2 hpxR86_2 hcardq86_2 (by decide)).symm

/-- **Cell (86, 86) twin (q=2).** -/
theorem cell86_86_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK86) e = true)
    (h : ↥(reps (⟨86, by decide⟩ : Fin 148))) :
    species (reps (⟨86, by decide⟩ : Fin 148)) h (basisElt (reps rK86) (charOfVec2 rK86 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK86 e (h : Coordinate 2) T86_86_2 i :=
  species_entry_eq_sum rK86 ⟨86, by decide⟩ e heK h T86_86_2 hfix86_86_2 hinj86_86_2 hcardT86_86_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨86, by decide⟩) (reps rK86) (T86_86_2 i) (hfix86_86_2 i) h)

end Q2

/-! # K-class rK = 87  (|G/K| = 25) -/

def rK87 : Fin 148 := ⟨87, by decide⟩

def R87list : List Coordinates := [(0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0)]
def R87 : Fin 25 → Coordinate 1 := fun i => R87list.getD i.val (0,0,0,0,0)

theorem hpxR87 : Function.Injective (fun i => reduceAux 1 (basisAt rK87) (R87 i)) := by decide
theorem hcardq87 : Nat.card (Coordinate 1 ⧸ reps rK87) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (87, 0): |T| = 25 -/

def T87_0list : List Coordinates := [(0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0)]
def T87_0 : Fin 25 → Coordinate 1 := fun i => T87_0list.getD i.val (0,0,0,0,0)

theorem hfix87_0 : ∀ i, ((T87_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK87)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87) :=
  repsFix_of_siftB rK87 ⟨0, by decide⟩ T87_0 (by decide)

theorem hinj87_0 : Function.Injective
    (fun i => ((T87_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK87)) :=
  repsInj_of_reduceAux rK87 T87_0 (by decide)

theorem hcardT87_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK87 ⟨0, by decide⟩ R87 hpxR87 hcardq87 (by decide)).symm

/-- **Cell (87, 0).** -/
theorem cell87_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK87) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK87) (charOfVec rK87 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK87 e (h : Coordinate 1) T87_0 i :=
  species_entry_eq_sum rK87 ⟨0, by decide⟩ e heK h T87_0 hfix87_0 hinj87_0 hcardT87_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK87) (T87_0 i) (hfix87_0 i) h)

/-! ## Cell (87, 2): |T| = 5 -/

def T87_2list : List Coordinates := [(0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0)]
def T87_2 : Fin 5 → Coordinate 1 := fun i => T87_2list.getD i.val (0,0,0,0,0)

theorem hfix87_2 : ∀ i, ((T87_2 i : Coordinate 1) : Coordinate 1 ⧸ reps rK87)
    ∈ fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87) :=
  repsFix_of_siftB rK87 ⟨2, by decide⟩ T87_2 (by decide)

theorem hinj87_2 : Function.Injective
    (fun i => ((T87_2 i : Coordinate 1) : Coordinate 1 ⧸ reps rK87)) :=
  repsInj_of_reduceAux rK87 T87_2 (by decide)

theorem hcardT87_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK87 ⟨2, by decide⟩ R87 hpxR87 hcardq87 (by decide)).symm

/-- **Cell (87, 2).** -/
theorem cell87_2 (e : List (ZMod 25)) (heK : charOK (basisAt rK87) e = true)
    (h : ↥(reps (⟨2, by decide⟩ : Fin 148))) :
    species (reps (⟨2, by decide⟩ : Fin 148)) h (basisElt (reps rK87) (charOfVec rK87 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK87 e (h : Coordinate 1) T87_2 i :=
  species_entry_eq_sum rK87 ⟨2, by decide⟩ e heK h T87_2 hfix87_2 hinj87_2 hcardT87_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨2, by decide⟩) (reps rK87) (T87_2 i) (hfix87_2 i) h)

/-! ## Cell (87, 3): |T| = 5 -/

def T87_3list : List Coordinates := [(0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0)]
def T87_3 : Fin 5 → Coordinate 1 := fun i => T87_3list.getD i.val (0,0,0,0,0)

theorem hfix87_3 : ∀ i, ((T87_3 i : Coordinate 1) : Coordinate 1 ⧸ reps rK87)
    ∈ fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87) :=
  repsFix_of_siftB rK87 ⟨3, by decide⟩ T87_3 (by decide)

theorem hinj87_3 : Function.Injective
    (fun i => ((T87_3 i : Coordinate 1) : Coordinate 1 ⧸ reps rK87)) :=
  repsInj_of_reduceAux rK87 T87_3 (by decide)

theorem hcardT87_3 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK87 ⟨3, by decide⟩ R87 hpxR87 hcardq87 (by decide)).symm

/-- **Cell (87, 3).** -/
theorem cell87_3 (e : List (ZMod 25)) (heK : charOK (basisAt rK87) e = true)
    (h : ↥(reps (⟨3, by decide⟩ : Fin 148))) :
    species (reps (⟨3, by decide⟩ : Fin 148)) h (basisElt (reps rK87) (charOfVec rK87 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK87 e (h : Coordinate 1) T87_3 i :=
  species_entry_eq_sum rK87 ⟨3, by decide⟩ e heK h T87_3 hfix87_3 hinj87_3 hcardT87_3
    (fun i => conj_mem_of_fixedPoints (reps ⟨3, by decide⟩) (reps rK87) (T87_3 i) (hfix87_3 i) h)

/-! ## Cell (87, 4): |T| = 5 -/

def T87_4list : List Coordinates := [(0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0)]
def T87_4 : Fin 5 → Coordinate 1 := fun i => T87_4list.getD i.val (0,0,0,0,0)

theorem hfix87_4 : ∀ i, ((T87_4 i : Coordinate 1) : Coordinate 1 ⧸ reps rK87)
    ∈ fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87) :=
  repsFix_of_siftB rK87 ⟨4, by decide⟩ T87_4 (by decide)

theorem hinj87_4 : Function.Injective
    (fun i => ((T87_4 i : Coordinate 1) : Coordinate 1 ⧸ reps rK87)) :=
  repsInj_of_reduceAux rK87 T87_4 (by decide)

theorem hcardT87_4 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK87 ⟨4, by decide⟩ R87 hpxR87 hcardq87 (by decide)).symm

/-- **Cell (87, 4).** -/
theorem cell87_4 (e : List (ZMod 25)) (heK : charOK (basisAt rK87) e = true)
    (h : ↥(reps (⟨4, by decide⟩ : Fin 148))) :
    species (reps (⟨4, by decide⟩ : Fin 148)) h (basisElt (reps rK87) (charOfVec rK87 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK87 e (h : Coordinate 1) T87_4 i :=
  species_entry_eq_sum rK87 ⟨4, by decide⟩ e heK h T87_4 hfix87_4 hinj87_4 hcardT87_4
    (fun i => conj_mem_of_fixedPoints (reps ⟨4, by decide⟩) (reps rK87) (T87_4 i) (hfix87_4 i) h)

/-! ## Cell (87, 5): |T| = 5 -/

def T87_5list : List Coordinates := [(0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0)]
def T87_5 : Fin 5 → Coordinate 1 := fun i => T87_5list.getD i.val (0,0,0,0,0)

theorem hfix87_5 : ∀ i, ((T87_5 i : Coordinate 1) : Coordinate 1 ⧸ reps rK87)
    ∈ fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87) :=
  repsFix_of_siftB rK87 ⟨5, by decide⟩ T87_5 (by decide)

theorem hinj87_5 : Function.Injective
    (fun i => ((T87_5 i : Coordinate 1) : Coordinate 1 ⧸ reps rK87)) :=
  repsInj_of_reduceAux rK87 T87_5 (by decide)

theorem hcardT87_5 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK87 ⟨5, by decide⟩ R87 hpxR87 hcardq87 (by decide)).symm

/-- **Cell (87, 5).** -/
theorem cell87_5 (e : List (ZMod 25)) (heK : charOK (basisAt rK87) e = true)
    (h : ↥(reps (⟨5, by decide⟩ : Fin 148))) :
    species (reps (⟨5, by decide⟩ : Fin 148)) h (basisElt (reps rK87) (charOfVec rK87 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK87 e (h : Coordinate 1) T87_5 i :=
  species_entry_eq_sum rK87 ⟨5, by decide⟩ e heK h T87_5 hfix87_5 hinj87_5 hcardT87_5
    (fun i => conj_mem_of_fixedPoints (reps ⟨5, by decide⟩) (reps rK87) (T87_5 i) (hfix87_5 i) h)

/-! ## Cell (87, 7): |T| = 25 -/

def T87_7list : List Coordinates := [(0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0)]
def T87_7 : Fin 25 → Coordinate 1 := fun i => T87_7list.getD i.val (0,0,0,0,0)

theorem hfix87_7 : ∀ i, ((T87_7 i : Coordinate 1) : Coordinate 1 ⧸ reps rK87)
    ∈ fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87) :=
  repsFix_of_siftB rK87 ⟨7, by decide⟩ T87_7 (by decide)

theorem hinj87_7 : Function.Injective
    (fun i => ((T87_7 i : Coordinate 1) : Coordinate 1 ⧸ reps rK87)) :=
  repsInj_of_reduceAux rK87 T87_7 (by decide)

theorem hcardT87_7 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK87 ⟨7, by decide⟩ R87 hpxR87 hcardq87 (by decide)).symm

/-- **Cell (87, 7).** -/
theorem cell87_7 (e : List (ZMod 25)) (heK : charOK (basisAt rK87) e = true)
    (h : ↥(reps (⟨7, by decide⟩ : Fin 148))) :
    species (reps (⟨7, by decide⟩ : Fin 148)) h (basisElt (reps rK87) (charOfVec rK87 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK87 e (h : Coordinate 1) T87_7 i :=
  species_entry_eq_sum rK87 ⟨7, by decide⟩ e heK h T87_7 hfix87_7 hinj87_7 hcardT87_7
    (fun i => conj_mem_of_fixedPoints (reps ⟨7, by decide⟩) (reps rK87) (T87_7 i) (hfix87_7 i) h)

/-! ## Cell (87, 11): |T| = 5 -/

def T87_11list : List Coordinates := [(0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0)]
def T87_11 : Fin 5 → Coordinate 1 := fun i => T87_11list.getD i.val (0,0,0,0,0)

theorem hfix87_11 : ∀ i, ((T87_11 i : Coordinate 1) : Coordinate 1 ⧸ reps rK87)
    ∈ fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87) :=
  repsFix_of_siftB rK87 ⟨11, by decide⟩ T87_11 (by decide)

theorem hinj87_11 : Function.Injective
    (fun i => ((T87_11 i : Coordinate 1) : Coordinate 1 ⧸ reps rK87)) :=
  repsInj_of_reduceAux rK87 T87_11 (by decide)

theorem hcardT87_11 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK87 ⟨11, by decide⟩ R87 hpxR87 hcardq87 (by decide)).symm

/-- **Cell (87, 11).** -/
theorem cell87_11 (e : List (ZMod 25)) (heK : charOK (basisAt rK87) e = true)
    (h : ↥(reps (⟨11, by decide⟩ : Fin 148))) :
    species (reps (⟨11, by decide⟩ : Fin 148)) h (basisElt (reps rK87) (charOfVec rK87 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK87 e (h : Coordinate 1) T87_11 i :=
  species_entry_eq_sum rK87 ⟨11, by decide⟩ e heK h T87_11 hfix87_11 hinj87_11 hcardT87_11
    (fun i => conj_mem_of_fixedPoints (reps ⟨11, by decide⟩) (reps rK87) (T87_11 i) (hfix87_11 i) h)

/-! ## Cell (87, 12): |T| = 25 -/

def T87_12list : List Coordinates := [(0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0)]
def T87_12 : Fin 25 → Coordinate 1 := fun i => T87_12list.getD i.val (0,0,0,0,0)

theorem hfix87_12 : ∀ i, ((T87_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK87)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87) :=
  repsFix_of_siftB rK87 ⟨12, by decide⟩ T87_12 (by decide)

theorem hinj87_12 : Function.Injective
    (fun i => ((T87_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK87)) :=
  repsInj_of_reduceAux rK87 T87_12 (by decide)

theorem hcardT87_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK87 ⟨12, by decide⟩ R87 hpxR87 hcardq87 (by decide)).symm

/-- **Cell (87, 12).** -/
theorem cell87_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK87) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK87) (charOfVec rK87 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK87 e (h : Coordinate 1) T87_12 i :=
  species_entry_eq_sum rK87 ⟨12, by decide⟩ e heK h T87_12 hfix87_12 hinj87_12 hcardT87_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK87) (T87_12 i) (hfix87_12 i) h)

/-! ## Cell (87, 20): |T| = 5 -/

def T87_20list : List Coordinates := [(0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0)]
def T87_20 : Fin 5 → Coordinate 1 := fun i => T87_20list.getD i.val (0,0,0,0,0)

theorem hfix87_20 : ∀ i, ((T87_20 i : Coordinate 1) : Coordinate 1 ⧸ reps rK87)
    ∈ fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87) :=
  repsFix_of_siftB rK87 ⟨20, by decide⟩ T87_20 (by decide)

theorem hinj87_20 : Function.Injective
    (fun i => ((T87_20 i : Coordinate 1) : Coordinate 1 ⧸ reps rK87)) :=
  repsInj_of_reduceAux rK87 T87_20 (by decide)

theorem hcardT87_20 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK87 ⟨20, by decide⟩ R87 hpxR87 hcardq87 (by decide)).symm

/-- **Cell (87, 20).** -/
theorem cell87_20 (e : List (ZMod 25)) (heK : charOK (basisAt rK87) e = true)
    (h : ↥(reps (⟨20, by decide⟩ : Fin 148))) :
    species (reps (⟨20, by decide⟩ : Fin 148)) h (basisElt (reps rK87) (charOfVec rK87 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK87 e (h : Coordinate 1) T87_20 i :=
  species_entry_eq_sum rK87 ⟨20, by decide⟩ e heK h T87_20 hfix87_20 hinj87_20 hcardT87_20
    (fun i => conj_mem_of_fixedPoints (reps ⟨20, by decide⟩) (reps rK87) (T87_20 i) (hfix87_20 i) h)

/-! ## Cell (87, 21): |T| = 5 -/

def T87_21list : List Coordinates := [(0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0)]
def T87_21 : Fin 5 → Coordinate 1 := fun i => T87_21list.getD i.val (0,0,0,0,0)

theorem hfix87_21 : ∀ i, ((T87_21 i : Coordinate 1) : Coordinate 1 ⧸ reps rK87)
    ∈ fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87) :=
  repsFix_of_siftB rK87 ⟨21, by decide⟩ T87_21 (by decide)

theorem hinj87_21 : Function.Injective
    (fun i => ((T87_21 i : Coordinate 1) : Coordinate 1 ⧸ reps rK87)) :=
  repsInj_of_reduceAux rK87 T87_21 (by decide)

theorem hcardT87_21 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK87 ⟨21, by decide⟩ R87 hpxR87 hcardq87 (by decide)).symm

/-- **Cell (87, 21).** -/
theorem cell87_21 (e : List (ZMod 25)) (heK : charOK (basisAt rK87) e = true)
    (h : ↥(reps (⟨21, by decide⟩ : Fin 148))) :
    species (reps (⟨21, by decide⟩ : Fin 148)) h (basisElt (reps rK87) (charOfVec rK87 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK87 e (h : Coordinate 1) T87_21 i :=
  species_entry_eq_sum rK87 ⟨21, by decide⟩ e heK h T87_21 hfix87_21 hinj87_21 hcardT87_21
    (fun i => conj_mem_of_fixedPoints (reps ⟨21, by decide⟩) (reps rK87) (T87_21 i) (hfix87_21 i) h)

/-! ## Cell (87, 22): |T| = 5 -/

def T87_22list : List Coordinates := [(0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0)]
def T87_22 : Fin 5 → Coordinate 1 := fun i => T87_22list.getD i.val (0,0,0,0,0)

theorem hfix87_22 : ∀ i, ((T87_22 i : Coordinate 1) : Coordinate 1 ⧸ reps rK87)
    ∈ fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87) :=
  repsFix_of_siftB rK87 ⟨22, by decide⟩ T87_22 (by decide)

theorem hinj87_22 : Function.Injective
    (fun i => ((T87_22 i : Coordinate 1) : Coordinate 1 ⧸ reps rK87)) :=
  repsInj_of_reduceAux rK87 T87_22 (by decide)

theorem hcardT87_22 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK87 ⟨22, by decide⟩ R87 hpxR87 hcardq87 (by decide)).symm

/-- **Cell (87, 22).** -/
theorem cell87_22 (e : List (ZMod 25)) (heK : charOK (basisAt rK87) e = true)
    (h : ↥(reps (⟨22, by decide⟩ : Fin 148))) :
    species (reps (⟨22, by decide⟩ : Fin 148)) h (basisElt (reps rK87) (charOfVec rK87 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK87 e (h : Coordinate 1) T87_22 i :=
  species_entry_eq_sum rK87 ⟨22, by decide⟩ e heK h T87_22 hfix87_22 hinj87_22 hcardT87_22
    (fun i => conj_mem_of_fixedPoints (reps ⟨22, by decide⟩) (reps rK87) (T87_22 i) (hfix87_22 i) h)

/-! ## Cell (87, 23): |T| = 5 -/

def T87_23list : List Coordinates := [(0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0)]
def T87_23 : Fin 5 → Coordinate 1 := fun i => T87_23list.getD i.val (0,0,0,0,0)

theorem hfix87_23 : ∀ i, ((T87_23 i : Coordinate 1) : Coordinate 1 ⧸ reps rK87)
    ∈ fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87) :=
  repsFix_of_siftB rK87 ⟨23, by decide⟩ T87_23 (by decide)

theorem hinj87_23 : Function.Injective
    (fun i => ((T87_23 i : Coordinate 1) : Coordinate 1 ⧸ reps rK87)) :=
  repsInj_of_reduceAux rK87 T87_23 (by decide)

theorem hcardT87_23 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK87 ⟨23, by decide⟩ R87 hpxR87 hcardq87 (by decide)).symm

/-- **Cell (87, 23).** -/
theorem cell87_23 (e : List (ZMod 25)) (heK : charOK (basisAt rK87) e = true)
    (h : ↥(reps (⟨23, by decide⟩ : Fin 148))) :
    species (reps (⟨23, by decide⟩ : Fin 148)) h (basisElt (reps rK87) (charOfVec rK87 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK87 e (h : Coordinate 1) T87_23 i :=
  species_entry_eq_sum rK87 ⟨23, by decide⟩ e heK h T87_23 hfix87_23 hinj87_23 hcardT87_23
    (fun i => conj_mem_of_fixedPoints (reps ⟨23, by decide⟩) (reps rK87) (T87_23 i) (hfix87_23 i) h)

/-! ## Cell (87, 25): |T| = 25 -/

def T87_25list : List Coordinates := [(0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0)]
def T87_25 : Fin 25 → Coordinate 1 := fun i => T87_25list.getD i.val (0,0,0,0,0)

theorem hfix87_25 : ∀ i, ((T87_25 i : Coordinate 1) : Coordinate 1 ⧸ reps rK87)
    ∈ fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87) :=
  repsFix_of_siftB rK87 ⟨25, by decide⟩ T87_25 (by decide)

theorem hinj87_25 : Function.Injective
    (fun i => ((T87_25 i : Coordinate 1) : Coordinate 1 ⧸ reps rK87)) :=
  repsInj_of_reduceAux rK87 T87_25 (by decide)

theorem hcardT87_25 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK87 ⟨25, by decide⟩ R87 hpxR87 hcardq87 (by decide)).symm

/-- **Cell (87, 25).** -/
theorem cell87_25 (e : List (ZMod 25)) (heK : charOK (basisAt rK87) e = true)
    (h : ↥(reps (⟨25, by decide⟩ : Fin 148))) :
    species (reps (⟨25, by decide⟩ : Fin 148)) h (basisElt (reps rK87) (charOfVec rK87 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK87 e (h : Coordinate 1) T87_25 i :=
  species_entry_eq_sum rK87 ⟨25, by decide⟩ e heK h T87_25 hfix87_25 hinj87_25 hcardT87_25
    (fun i => conj_mem_of_fixedPoints (reps ⟨25, by decide⟩) (reps rK87) (T87_25 i) (hfix87_25 i) h)

/-! ## Cell (87, 54): |T| = 5 -/

def T87_54list : List Coordinates := [(0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0)]
def T87_54 : Fin 5 → Coordinate 1 := fun i => T87_54list.getD i.val (0,0,0,0,0)

theorem hfix87_54 : ∀ i, ((T87_54 i : Coordinate 1) : Coordinate 1 ⧸ reps rK87)
    ∈ fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87) :=
  repsFix_of_siftB rK87 ⟨54, by decide⟩ T87_54 (by decide)

theorem hinj87_54 : Function.Injective
    (fun i => ((T87_54 i : Coordinate 1) : Coordinate 1 ⧸ reps rK87)) :=
  repsInj_of_reduceAux rK87 T87_54 (by decide)

theorem hcardT87_54 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK87 ⟨54, by decide⟩ R87 hpxR87 hcardq87 (by decide)).symm

/-- **Cell (87, 54).** -/
theorem cell87_54 (e : List (ZMod 25)) (heK : charOK (basisAt rK87) e = true)
    (h : ↥(reps (⟨54, by decide⟩ : Fin 148))) :
    species (reps (⟨54, by decide⟩ : Fin 148)) h (basisElt (reps rK87) (charOfVec rK87 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK87 e (h : Coordinate 1) T87_54 i :=
  species_entry_eq_sum rK87 ⟨54, by decide⟩ e heK h T87_54 hfix87_54 hinj87_54 hcardT87_54
    (fun i => conj_mem_of_fixedPoints (reps ⟨54, by decide⟩) (reps rK87) (T87_54 i) (hfix87_54 i) h)

/-! ## Cell (87, 87): |T| = 5 -/

def T87_87list : List Coordinates := [(0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,0,0,1,0)]
def T87_87 : Fin 5 → Coordinate 1 := fun i => T87_87list.getD i.val (0,0,0,0,0)

theorem hfix87_87 : ∀ i, ((T87_87 i : Coordinate 1) : Coordinate 1 ⧸ reps rK87)
    ∈ fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87) :=
  repsFix_of_siftB rK87 ⟨87, by decide⟩ T87_87 (by decide)

theorem hinj87_87 : Function.Injective
    (fun i => ((T87_87 i : Coordinate 1) : Coordinate 1 ⧸ reps rK87)) :=
  repsInj_of_reduceAux rK87 T87_87 (by decide)

theorem hcardT87_87 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK87 ⟨87, by decide⟩ R87 hpxR87 hcardq87 (by decide)).symm

/-- **Cell (87, 87).** -/
theorem cell87_87 (e : List (ZMod 25)) (heK : charOK (basisAt rK87) e = true)
    (h : ↥(reps (⟨87, by decide⟩ : Fin 148))) :
    species (reps (⟨87, by decide⟩ : Fin 148)) h (basisElt (reps rK87) (charOfVec rK87 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK87 e (h : Coordinate 1) T87_87 i :=
  species_entry_eq_sum rK87 ⟨87, by decide⟩ e heK h T87_87 hfix87_87 hinj87_87 hcardT87_87
    (fun i => conj_mem_of_fixedPoints (reps ⟨87, by decide⟩) (reps rK87) (T87_87 i) (hfix87_87 i) h)

namespace Q2

def R87_2 : Fin 25 → Coordinate 2 := fun i => R87list.getD i.val (0,0,0,0,0)
theorem hpxR87_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK87) (R87_2 i)) := by decide
theorem hcardq87_2 : Nat.card (Coordinate 2 ⧸ reps rK87) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (87, 0) twin -/

def T87_0_2 : Fin 25 → Coordinate 2 := fun i => T87_0list.getD i.val (0,0,0,0,0)

theorem hfix87_0_2 : ∀ i, ((T87_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK87)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK87) :=
  repsFix_of_siftB2 rK87 ⟨0, by decide⟩ T87_0_2 (by decide)

theorem hinj87_0_2 : Function.Injective
    (fun i => ((T87_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK87)) :=
  repsInj_of_reduceAux2 rK87 T87_0_2 (by decide)

theorem hcardT87_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK87)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK87 ⟨0, by decide⟩ R87_2 hpxR87_2 hcardq87_2 (by decide)).symm

/-- **Cell (87, 0) twin (q=2).** -/
theorem cell87_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK87) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK87) (charOfVec2 rK87 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK87 e (h : Coordinate 2) T87_0_2 i :=
  species_entry_eq_sum rK87 ⟨0, by decide⟩ e heK h T87_0_2 hfix87_0_2 hinj87_0_2 hcardT87_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK87) (T87_0_2 i) (hfix87_0_2 i) h)

/-! ### Cell (87, 2) twin -/

def T87_2_2 : Fin 5 → Coordinate 2 := fun i => T87_2list.getD i.val (0,0,0,0,0)

theorem hfix87_2_2 : ∀ i, ((T87_2_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK87)
    ∈ fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK87) :=
  repsFix_of_siftB2 rK87 ⟨2, by decide⟩ T87_2_2 (by decide)

theorem hinj87_2_2 : Function.Injective
    (fun i => ((T87_2_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK87)) :=
  repsInj_of_reduceAux2 rK87 T87_2_2 (by decide)

theorem hcardT87_2_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK87)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK87 ⟨2, by decide⟩ R87_2 hpxR87_2 hcardq87_2 (by decide)).symm

/-- **Cell (87, 2) twin (q=2).** -/
theorem cell87_2_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK87) e = true)
    (h : ↥(reps (⟨2, by decide⟩ : Fin 148))) :
    species (reps (⟨2, by decide⟩ : Fin 148)) h (basisElt (reps rK87) (charOfVec2 rK87 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK87 e (h : Coordinate 2) T87_2_2 i :=
  species_entry_eq_sum rK87 ⟨2, by decide⟩ e heK h T87_2_2 hfix87_2_2 hinj87_2_2 hcardT87_2_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨2, by decide⟩) (reps rK87) (T87_2_2 i) (hfix87_2_2 i) h)

/-! ### Cell (87, 3) twin -/

def T87_3_2 : Fin 5 → Coordinate 2 := fun i => T87_3list.getD i.val (0,0,0,0,0)

theorem hfix87_3_2 : ∀ i, ((T87_3_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK87)
    ∈ fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK87) :=
  repsFix_of_siftB2 rK87 ⟨3, by decide⟩ T87_3_2 (by decide)

theorem hinj87_3_2 : Function.Injective
    (fun i => ((T87_3_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK87)) :=
  repsInj_of_reduceAux2 rK87 T87_3_2 (by decide)

theorem hcardT87_3_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK87)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK87 ⟨3, by decide⟩ R87_2 hpxR87_2 hcardq87_2 (by decide)).symm

/-- **Cell (87, 3) twin (q=2).** -/
theorem cell87_3_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK87) e = true)
    (h : ↥(reps (⟨3, by decide⟩ : Fin 148))) :
    species (reps (⟨3, by decide⟩ : Fin 148)) h (basisElt (reps rK87) (charOfVec2 rK87 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK87 e (h : Coordinate 2) T87_3_2 i :=
  species_entry_eq_sum rK87 ⟨3, by decide⟩ e heK h T87_3_2 hfix87_3_2 hinj87_3_2 hcardT87_3_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨3, by decide⟩) (reps rK87) (T87_3_2 i) (hfix87_3_2 i) h)

/-! ### Cell (87, 4) twin -/

def T87_4_2 : Fin 5 → Coordinate 2 := fun i => T87_4list.getD i.val (0,0,0,0,0)

theorem hfix87_4_2 : ∀ i, ((T87_4_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK87)
    ∈ fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK87) :=
  repsFix_of_siftB2 rK87 ⟨4, by decide⟩ T87_4_2 (by decide)

theorem hinj87_4_2 : Function.Injective
    (fun i => ((T87_4_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK87)) :=
  repsInj_of_reduceAux2 rK87 T87_4_2 (by decide)

theorem hcardT87_4_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK87)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK87 ⟨4, by decide⟩ R87_2 hpxR87_2 hcardq87_2 (by decide)).symm

/-- **Cell (87, 4) twin (q=2).** -/
theorem cell87_4_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK87) e = true)
    (h : ↥(reps (⟨4, by decide⟩ : Fin 148))) :
    species (reps (⟨4, by decide⟩ : Fin 148)) h (basisElt (reps rK87) (charOfVec2 rK87 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK87 e (h : Coordinate 2) T87_4_2 i :=
  species_entry_eq_sum rK87 ⟨4, by decide⟩ e heK h T87_4_2 hfix87_4_2 hinj87_4_2 hcardT87_4_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨4, by decide⟩) (reps rK87) (T87_4_2 i) (hfix87_4_2 i) h)

/-! ### Cell (87, 5) twin -/

def T87_5_2 : Fin 5 → Coordinate 2 := fun i => T87_5list.getD i.val (0,0,0,0,0)

theorem hfix87_5_2 : ∀ i, ((T87_5_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK87)
    ∈ fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK87) :=
  repsFix_of_siftB2 rK87 ⟨5, by decide⟩ T87_5_2 (by decide)

theorem hinj87_5_2 : Function.Injective
    (fun i => ((T87_5_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK87)) :=
  repsInj_of_reduceAux2 rK87 T87_5_2 (by decide)

theorem hcardT87_5_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK87)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK87 ⟨5, by decide⟩ R87_2 hpxR87_2 hcardq87_2 (by decide)).symm

/-- **Cell (87, 5) twin (q=2).** -/
theorem cell87_5_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK87) e = true)
    (h : ↥(reps (⟨5, by decide⟩ : Fin 148))) :
    species (reps (⟨5, by decide⟩ : Fin 148)) h (basisElt (reps rK87) (charOfVec2 rK87 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK87 e (h : Coordinate 2) T87_5_2 i :=
  species_entry_eq_sum rK87 ⟨5, by decide⟩ e heK h T87_5_2 hfix87_5_2 hinj87_5_2 hcardT87_5_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨5, by decide⟩) (reps rK87) (T87_5_2 i) (hfix87_5_2 i) h)

/-! ### Cell (87, 7) twin -/

def T87_7_2 : Fin 25 → Coordinate 2 := fun i => T87_7list.getD i.val (0,0,0,0,0)

theorem hfix87_7_2 : ∀ i, ((T87_7_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK87)
    ∈ fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK87) :=
  repsFix_of_siftB2 rK87 ⟨7, by decide⟩ T87_7_2 (by decide)

theorem hinj87_7_2 : Function.Injective
    (fun i => ((T87_7_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK87)) :=
  repsInj_of_reduceAux2 rK87 T87_7_2 (by decide)

theorem hcardT87_7_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK87)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK87 ⟨7, by decide⟩ R87_2 hpxR87_2 hcardq87_2 (by decide)).symm

/-- **Cell (87, 7) twin (q=2).** -/
theorem cell87_7_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK87) e = true)
    (h : ↥(reps (⟨7, by decide⟩ : Fin 148))) :
    species (reps (⟨7, by decide⟩ : Fin 148)) h (basisElt (reps rK87) (charOfVec2 rK87 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK87 e (h : Coordinate 2) T87_7_2 i :=
  species_entry_eq_sum rK87 ⟨7, by decide⟩ e heK h T87_7_2 hfix87_7_2 hinj87_7_2 hcardT87_7_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨7, by decide⟩) (reps rK87) (T87_7_2 i) (hfix87_7_2 i) h)

/-! ### Cell (87, 11) twin -/

def T87_11_2 : Fin 5 → Coordinate 2 := fun i => T87_11list.getD i.val (0,0,0,0,0)

theorem hfix87_11_2 : ∀ i, ((T87_11_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK87)
    ∈ fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK87) :=
  repsFix_of_siftB2 rK87 ⟨11, by decide⟩ T87_11_2 (by decide)

theorem hinj87_11_2 : Function.Injective
    (fun i => ((T87_11_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK87)) :=
  repsInj_of_reduceAux2 rK87 T87_11_2 (by decide)

theorem hcardT87_11_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK87)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK87 ⟨11, by decide⟩ R87_2 hpxR87_2 hcardq87_2 (by decide)).symm

/-- **Cell (87, 11) twin (q=2).** -/
theorem cell87_11_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK87) e = true)
    (h : ↥(reps (⟨11, by decide⟩ : Fin 148))) :
    species (reps (⟨11, by decide⟩ : Fin 148)) h (basisElt (reps rK87) (charOfVec2 rK87 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK87 e (h : Coordinate 2) T87_11_2 i :=
  species_entry_eq_sum rK87 ⟨11, by decide⟩ e heK h T87_11_2 hfix87_11_2 hinj87_11_2 hcardT87_11_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨11, by decide⟩) (reps rK87) (T87_11_2 i) (hfix87_11_2 i) h)

/-! ### Cell (87, 12) twin -/

def T87_12_2 : Fin 25 → Coordinate 2 := fun i => T87_12list.getD i.val (0,0,0,0,0)

theorem hfix87_12_2 : ∀ i, ((T87_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK87)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK87) :=
  repsFix_of_siftB2 rK87 ⟨12, by decide⟩ T87_12_2 (by decide)

theorem hinj87_12_2 : Function.Injective
    (fun i => ((T87_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK87)) :=
  repsInj_of_reduceAux2 rK87 T87_12_2 (by decide)

theorem hcardT87_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK87)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK87 ⟨12, by decide⟩ R87_2 hpxR87_2 hcardq87_2 (by decide)).symm

/-- **Cell (87, 12) twin (q=2).** -/
theorem cell87_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK87) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK87) (charOfVec2 rK87 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK87 e (h : Coordinate 2) T87_12_2 i :=
  species_entry_eq_sum rK87 ⟨12, by decide⟩ e heK h T87_12_2 hfix87_12_2 hinj87_12_2 hcardT87_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK87) (T87_12_2 i) (hfix87_12_2 i) h)

/-! ### Cell (87, 20) twin -/

def T87_20_2 : Fin 5 → Coordinate 2 := fun i => T87_20list.getD i.val (0,0,0,0,0)

theorem hfix87_20_2 : ∀ i, ((T87_20_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK87)
    ∈ fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK87) :=
  repsFix_of_siftB2 rK87 ⟨20, by decide⟩ T87_20_2 (by decide)

theorem hinj87_20_2 : Function.Injective
    (fun i => ((T87_20_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK87)) :=
  repsInj_of_reduceAux2 rK87 T87_20_2 (by decide)

theorem hcardT87_20_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK87)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK87 ⟨20, by decide⟩ R87_2 hpxR87_2 hcardq87_2 (by decide)).symm

/-- **Cell (87, 20) twin (q=2).** -/
theorem cell87_20_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK87) e = true)
    (h : ↥(reps (⟨20, by decide⟩ : Fin 148))) :
    species (reps (⟨20, by decide⟩ : Fin 148)) h (basisElt (reps rK87) (charOfVec2 rK87 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK87 e (h : Coordinate 2) T87_20_2 i :=
  species_entry_eq_sum rK87 ⟨20, by decide⟩ e heK h T87_20_2 hfix87_20_2 hinj87_20_2 hcardT87_20_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨20, by decide⟩) (reps rK87) (T87_20_2 i) (hfix87_20_2 i) h)

/-! ### Cell (87, 21) twin -/

def T87_21_2 : Fin 5 → Coordinate 2 := fun i => T87_21list.getD i.val (0,0,0,0,0)

theorem hfix87_21_2 : ∀ i, ((T87_21_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK87)
    ∈ fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK87) :=
  repsFix_of_siftB2 rK87 ⟨21, by decide⟩ T87_21_2 (by decide)

theorem hinj87_21_2 : Function.Injective
    (fun i => ((T87_21_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK87)) :=
  repsInj_of_reduceAux2 rK87 T87_21_2 (by decide)

theorem hcardT87_21_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK87)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK87 ⟨21, by decide⟩ R87_2 hpxR87_2 hcardq87_2 (by decide)).symm

/-- **Cell (87, 21) twin (q=2).** -/
theorem cell87_21_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK87) e = true)
    (h : ↥(reps (⟨21, by decide⟩ : Fin 148))) :
    species (reps (⟨21, by decide⟩ : Fin 148)) h (basisElt (reps rK87) (charOfVec2 rK87 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK87 e (h : Coordinate 2) T87_21_2 i :=
  species_entry_eq_sum rK87 ⟨21, by decide⟩ e heK h T87_21_2 hfix87_21_2 hinj87_21_2 hcardT87_21_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨21, by decide⟩) (reps rK87) (T87_21_2 i) (hfix87_21_2 i) h)

/-! ### Cell (87, 22) twin -/

def T87_22_2 : Fin 5 → Coordinate 2 := fun i => T87_22list.getD i.val (0,0,0,0,0)

theorem hfix87_22_2 : ∀ i, ((T87_22_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK87)
    ∈ fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK87) :=
  repsFix_of_siftB2 rK87 ⟨22, by decide⟩ T87_22_2 (by decide)

theorem hinj87_22_2 : Function.Injective
    (fun i => ((T87_22_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK87)) :=
  repsInj_of_reduceAux2 rK87 T87_22_2 (by decide)

theorem hcardT87_22_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK87)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK87 ⟨22, by decide⟩ R87_2 hpxR87_2 hcardq87_2 (by decide)).symm

/-- **Cell (87, 22) twin (q=2).** -/
theorem cell87_22_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK87) e = true)
    (h : ↥(reps (⟨22, by decide⟩ : Fin 148))) :
    species (reps (⟨22, by decide⟩ : Fin 148)) h (basisElt (reps rK87) (charOfVec2 rK87 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK87 e (h : Coordinate 2) T87_22_2 i :=
  species_entry_eq_sum rK87 ⟨22, by decide⟩ e heK h T87_22_2 hfix87_22_2 hinj87_22_2 hcardT87_22_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨22, by decide⟩) (reps rK87) (T87_22_2 i) (hfix87_22_2 i) h)

/-! ### Cell (87, 23) twin -/

def T87_23_2 : Fin 5 → Coordinate 2 := fun i => T87_23list.getD i.val (0,0,0,0,0)

theorem hfix87_23_2 : ∀ i, ((T87_23_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK87)
    ∈ fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK87) :=
  repsFix_of_siftB2 rK87 ⟨23, by decide⟩ T87_23_2 (by decide)

theorem hinj87_23_2 : Function.Injective
    (fun i => ((T87_23_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK87)) :=
  repsInj_of_reduceAux2 rK87 T87_23_2 (by decide)

theorem hcardT87_23_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK87)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK87 ⟨23, by decide⟩ R87_2 hpxR87_2 hcardq87_2 (by decide)).symm

/-- **Cell (87, 23) twin (q=2).** -/
theorem cell87_23_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK87) e = true)
    (h : ↥(reps (⟨23, by decide⟩ : Fin 148))) :
    species (reps (⟨23, by decide⟩ : Fin 148)) h (basisElt (reps rK87) (charOfVec2 rK87 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK87 e (h : Coordinate 2) T87_23_2 i :=
  species_entry_eq_sum rK87 ⟨23, by decide⟩ e heK h T87_23_2 hfix87_23_2 hinj87_23_2 hcardT87_23_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨23, by decide⟩) (reps rK87) (T87_23_2 i) (hfix87_23_2 i) h)

/-! ### Cell (87, 25) twin -/

def T87_25_2 : Fin 25 → Coordinate 2 := fun i => T87_25list.getD i.val (0,0,0,0,0)

theorem hfix87_25_2 : ∀ i, ((T87_25_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK87)
    ∈ fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK87) :=
  repsFix_of_siftB2 rK87 ⟨25, by decide⟩ T87_25_2 (by decide)

theorem hinj87_25_2 : Function.Injective
    (fun i => ((T87_25_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK87)) :=
  repsInj_of_reduceAux2 rK87 T87_25_2 (by decide)

theorem hcardT87_25_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK87)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK87 ⟨25, by decide⟩ R87_2 hpxR87_2 hcardq87_2 (by decide)).symm

/-- **Cell (87, 25) twin (q=2).** -/
theorem cell87_25_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK87) e = true)
    (h : ↥(reps (⟨25, by decide⟩ : Fin 148))) :
    species (reps (⟨25, by decide⟩ : Fin 148)) h (basisElt (reps rK87) (charOfVec2 rK87 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK87 e (h : Coordinate 2) T87_25_2 i :=
  species_entry_eq_sum rK87 ⟨25, by decide⟩ e heK h T87_25_2 hfix87_25_2 hinj87_25_2 hcardT87_25_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨25, by decide⟩) (reps rK87) (T87_25_2 i) (hfix87_25_2 i) h)

/-! ### Cell (87, 54) twin -/

def T87_54_2 : Fin 5 → Coordinate 2 := fun i => T87_54list.getD i.val (0,0,0,0,0)

theorem hfix87_54_2 : ∀ i, ((T87_54_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK87)
    ∈ fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK87) :=
  repsFix_of_siftB2 rK87 ⟨54, by decide⟩ T87_54_2 (by decide)

theorem hinj87_54_2 : Function.Injective
    (fun i => ((T87_54_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK87)) :=
  repsInj_of_reduceAux2 rK87 T87_54_2 (by decide)

theorem hcardT87_54_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK87)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK87 ⟨54, by decide⟩ R87_2 hpxR87_2 hcardq87_2 (by decide)).symm

/-- **Cell (87, 54) twin (q=2).** -/
theorem cell87_54_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK87) e = true)
    (h : ↥(reps (⟨54, by decide⟩ : Fin 148))) :
    species (reps (⟨54, by decide⟩ : Fin 148)) h (basisElt (reps rK87) (charOfVec2 rK87 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK87 e (h : Coordinate 2) T87_54_2 i :=
  species_entry_eq_sum rK87 ⟨54, by decide⟩ e heK h T87_54_2 hfix87_54_2 hinj87_54_2 hcardT87_54_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨54, by decide⟩) (reps rK87) (T87_54_2 i) (hfix87_54_2 i) h)

/-! ### Cell (87, 87) twin -/

def T87_87_2 : Fin 5 → Coordinate 2 := fun i => T87_87list.getD i.val (0,0,0,0,0)

theorem hfix87_87_2 : ∀ i, ((T87_87_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK87)
    ∈ fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK87) :=
  repsFix_of_siftB2 rK87 ⟨87, by decide⟩ T87_87_2 (by decide)

theorem hinj87_87_2 : Function.Injective
    (fun i => ((T87_87_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK87)) :=
  repsInj_of_reduceAux2 rK87 T87_87_2 (by decide)

theorem hcardT87_87_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK87)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK87 ⟨87, by decide⟩ R87_2 hpxR87_2 hcardq87_2 (by decide)).symm

/-- **Cell (87, 87) twin (q=2).** -/
theorem cell87_87_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK87) e = true)
    (h : ↥(reps (⟨87, by decide⟩ : Fin 148))) :
    species (reps (⟨87, by decide⟩ : Fin 148)) h (basisElt (reps rK87) (charOfVec2 rK87 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK87 e (h : Coordinate 2) T87_87_2 i :=
  species_entry_eq_sum rK87 ⟨87, by decide⟩ e heK h T87_87_2 hfix87_87_2 hinj87_87_2 hcardT87_87_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨87, by decide⟩) (reps rK87) (T87_87_2 i) (hfix87_87_2 i) h)

end Q2

end LeanDring.P5Presentation
