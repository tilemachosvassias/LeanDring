/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, K-strata data (5^4 stratum, rK 138-139): certified per-cell species-entry instantiations, both
twins.

Covers K-classes 138, 139 (order-5^4 K, |R|=5).  For each nonzero `H`-column
(`(G/K)^H ≠ ∅`), the full coset transversal `R138..` and each `H`-fixed
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

/-! # K-class rK = 138  (|G/K| = 5) -/

def rK138 : Fin 148 := ⟨138, by decide⟩

def R138list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def R138 : Fin 5 → Coordinate 1 := fun i => R138list.getD i.val (0,0,0,0,0)

theorem hpxR138 : Function.Injective (fun i => reduceAux 1 (basisAt rK138) (R138 i)) := by decide
theorem hcardq138 : Nat.card (Coordinate 1 ⧸ reps rK138) = 5 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (138, 0): |T| = 5 -/

def T138_0list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T138_0 : Fin 5 → Coordinate 1 := fun i => T138_0list.getD i.val (0,0,0,0,0)

theorem hfix138_0 : ∀ i, ((T138_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK138)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138) :=
  repsFix_of_siftB rK138 ⟨0, by decide⟩ T138_0 (by decide)

theorem hinj138_0 : Function.Injective
    (fun i => ((T138_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK138)) :=
  repsInj_of_reduceAux rK138 T138_0 (by decide)

theorem hcardT138_0 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK138 ⟨0, by decide⟩ R138 hpxR138 hcardq138 (by decide)).symm

/-- **Cell (138, 0).** -/
theorem cell138_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK138) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK138) (charOfVec rK138 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK138 e (h : Coordinate 1) T138_0 i :=
  species_entry_eq_sum rK138 ⟨0, by decide⟩ e heK h T138_0 hfix138_0 hinj138_0 hcardT138_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK138) (T138_0 i) (hfix138_0 i) h)

/-! ## Cell (138, 5): |T| = 5 -/

def T138_5list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T138_5 : Fin 5 → Coordinate 1 := fun i => T138_5list.getD i.val (0,0,0,0,0)

theorem hfix138_5 : ∀ i, ((T138_5 i : Coordinate 1) : Coordinate 1 ⧸ reps rK138)
    ∈ fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138) :=
  repsFix_of_siftB rK138 ⟨5, by decide⟩ T138_5 (by decide)

theorem hinj138_5 : Function.Injective
    (fun i => ((T138_5 i : Coordinate 1) : Coordinate 1 ⧸ reps rK138)) :=
  repsInj_of_reduceAux rK138 T138_5 (by decide)

theorem hcardT138_5 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK138 ⟨5, by decide⟩ R138 hpxR138 hcardq138 (by decide)).symm

/-- **Cell (138, 5).** -/
theorem cell138_5 (e : List (ZMod 25)) (heK : charOK (basisAt rK138) e = true)
    (h : ↥(reps (⟨5, by decide⟩ : Fin 148))) :
    species (reps (⟨5, by decide⟩ : Fin 148)) h (basisElt (reps rK138) (charOfVec rK138 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK138 e (h : Coordinate 1) T138_5 i :=
  species_entry_eq_sum rK138 ⟨5, by decide⟩ e heK h T138_5 hfix138_5 hinj138_5 hcardT138_5
    (fun i => conj_mem_of_fixedPoints (reps ⟨5, by decide⟩) (reps rK138) (T138_5 i) (hfix138_5 i) h)

/-! ## Cell (138, 10): |T| = 5 -/

def T138_10list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T138_10 : Fin 5 → Coordinate 1 := fun i => T138_10list.getD i.val (0,0,0,0,0)

theorem hfix138_10 : ∀ i, ((T138_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK138)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138) :=
  repsFix_of_siftB rK138 ⟨10, by decide⟩ T138_10 (by decide)

theorem hinj138_10 : Function.Injective
    (fun i => ((T138_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK138)) :=
  repsInj_of_reduceAux rK138 T138_10 (by decide)

theorem hcardT138_10 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK138 ⟨10, by decide⟩ R138 hpxR138 hcardq138 (by decide)).symm

/-- **Cell (138, 10).** -/
theorem cell138_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK138) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK138) (charOfVec rK138 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK138 e (h : Coordinate 1) T138_10 i :=
  species_entry_eq_sum rK138 ⟨10, by decide⟩ e heK h T138_10 hfix138_10 hinj138_10 hcardT138_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK138) (T138_10 i) (hfix138_10 i) h)

/-! ## Cell (138, 12): |T| = 5 -/

def T138_12list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T138_12 : Fin 5 → Coordinate 1 := fun i => T138_12list.getD i.val (0,0,0,0,0)

theorem hfix138_12 : ∀ i, ((T138_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK138)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138) :=
  repsFix_of_siftB rK138 ⟨12, by decide⟩ T138_12 (by decide)

theorem hinj138_12 : Function.Injective
    (fun i => ((T138_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK138)) :=
  repsInj_of_reduceAux rK138 T138_12 (by decide)

theorem hcardT138_12 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK138 ⟨12, by decide⟩ R138 hpxR138 hcardq138 (by decide)).symm

/-- **Cell (138, 12).** -/
theorem cell138_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK138) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK138) (charOfVec rK138 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK138 e (h : Coordinate 1) T138_12 i :=
  species_entry_eq_sum rK138 ⟨12, by decide⟩ e heK h T138_12 hfix138_12 hinj138_12 hcardT138_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK138) (T138_12 i) (hfix138_12 i) h)

/-! ## Cell (138, 23): |T| = 5 -/

def T138_23list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T138_23 : Fin 5 → Coordinate 1 := fun i => T138_23list.getD i.val (0,0,0,0,0)

theorem hfix138_23 : ∀ i, ((T138_23 i : Coordinate 1) : Coordinate 1 ⧸ reps rK138)
    ∈ fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138) :=
  repsFix_of_siftB rK138 ⟨23, by decide⟩ T138_23 (by decide)

theorem hinj138_23 : Function.Injective
    (fun i => ((T138_23 i : Coordinate 1) : Coordinate 1 ⧸ reps rK138)) :=
  repsInj_of_reduceAux rK138 T138_23 (by decide)

theorem hcardT138_23 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK138 ⟨23, by decide⟩ R138 hpxR138 hcardq138 (by decide)).symm

/-- **Cell (138, 23).** -/
theorem cell138_23 (e : List (ZMod 25)) (heK : charOK (basisAt rK138) e = true)
    (h : ↥(reps (⟨23, by decide⟩ : Fin 148))) :
    species (reps (⟨23, by decide⟩ : Fin 148)) h (basisElt (reps rK138) (charOfVec rK138 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK138 e (h : Coordinate 1) T138_23 i :=
  species_entry_eq_sum rK138 ⟨23, by decide⟩ e heK h T138_23 hfix138_23 hinj138_23 hcardT138_23
    (fun i => conj_mem_of_fixedPoints (reps ⟨23, by decide⟩) (reps rK138) (T138_23 i) (hfix138_23 i) h)

/-! ## Cell (138, 31): |T| = 5 -/

def T138_31list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T138_31 : Fin 5 → Coordinate 1 := fun i => T138_31list.getD i.val (0,0,0,0,0)

theorem hfix138_31 : ∀ i, ((T138_31 i : Coordinate 1) : Coordinate 1 ⧸ reps rK138)
    ∈ fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138) :=
  repsFix_of_siftB rK138 ⟨31, by decide⟩ T138_31 (by decide)

theorem hinj138_31 : Function.Injective
    (fun i => ((T138_31 i : Coordinate 1) : Coordinate 1 ⧸ reps rK138)) :=
  repsInj_of_reduceAux rK138 T138_31 (by decide)

theorem hcardT138_31 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK138 ⟨31, by decide⟩ R138 hpxR138 hcardq138 (by decide)).symm

/-- **Cell (138, 31).** -/
theorem cell138_31 (e : List (ZMod 25)) (heK : charOK (basisAt rK138) e = true)
    (h : ↥(reps (⟨31, by decide⟩ : Fin 148))) :
    species (reps (⟨31, by decide⟩ : Fin 148)) h (basisElt (reps rK138) (charOfVec rK138 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK138 e (h : Coordinate 1) T138_31 i :=
  species_entry_eq_sum rK138 ⟨31, by decide⟩ e heK h T138_31 hfix138_31 hinj138_31 hcardT138_31
    (fun i => conj_mem_of_fixedPoints (reps ⟨31, by decide⟩) (reps rK138) (T138_31 i) (hfix138_31 i) h)

/-! ## Cell (138, 33): |T| = 5 -/

def T138_33list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T138_33 : Fin 5 → Coordinate 1 := fun i => T138_33list.getD i.val (0,0,0,0,0)

theorem hfix138_33 : ∀ i, ((T138_33 i : Coordinate 1) : Coordinate 1 ⧸ reps rK138)
    ∈ fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138) :=
  repsFix_of_siftB rK138 ⟨33, by decide⟩ T138_33 (by decide)

theorem hinj138_33 : Function.Injective
    (fun i => ((T138_33 i : Coordinate 1) : Coordinate 1 ⧸ reps rK138)) :=
  repsInj_of_reduceAux rK138 T138_33 (by decide)

theorem hcardT138_33 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK138 ⟨33, by decide⟩ R138 hpxR138 hcardq138 (by decide)).symm

/-- **Cell (138, 33).** -/
theorem cell138_33 (e : List (ZMod 25)) (heK : charOK (basisAt rK138) e = true)
    (h : ↥(reps (⟨33, by decide⟩ : Fin 148))) :
    species (reps (⟨33, by decide⟩ : Fin 148)) h (basisElt (reps rK138) (charOfVec rK138 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK138 e (h : Coordinate 1) T138_33 i :=
  species_entry_eq_sum rK138 ⟨33, by decide⟩ e heK h T138_33 hfix138_33 hinj138_33 hcardT138_33
    (fun i => conj_mem_of_fixedPoints (reps ⟨33, by decide⟩) (reps rK138) (T138_33 i) (hfix138_33 i) h)

/-! ## Cell (138, 42): |T| = 5 -/

def T138_42list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T138_42 : Fin 5 → Coordinate 1 := fun i => T138_42list.getD i.val (0,0,0,0,0)

theorem hfix138_42 : ∀ i, ((T138_42 i : Coordinate 1) : Coordinate 1 ⧸ reps rK138)
    ∈ fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138) :=
  repsFix_of_siftB rK138 ⟨42, by decide⟩ T138_42 (by decide)

theorem hinj138_42 : Function.Injective
    (fun i => ((T138_42 i : Coordinate 1) : Coordinate 1 ⧸ reps rK138)) :=
  repsInj_of_reduceAux rK138 T138_42 (by decide)

theorem hcardT138_42 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK138 ⟨42, by decide⟩ R138 hpxR138 hcardq138 (by decide)).symm

/-- **Cell (138, 42).** -/
theorem cell138_42 (e : List (ZMod 25)) (heK : charOK (basisAt rK138) e = true)
    (h : ↥(reps (⟨42, by decide⟩ : Fin 148))) :
    species (reps (⟨42, by decide⟩ : Fin 148)) h (basisElt (reps rK138) (charOfVec rK138 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK138 e (h : Coordinate 1) T138_42 i :=
  species_entry_eq_sum rK138 ⟨42, by decide⟩ e heK h T138_42 hfix138_42 hinj138_42 hcardT138_42
    (fun i => conj_mem_of_fixedPoints (reps ⟨42, by decide⟩) (reps rK138) (T138_42 i) (hfix138_42 i) h)

/-! ## Cell (138, 44): |T| = 5 -/

def T138_44list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T138_44 : Fin 5 → Coordinate 1 := fun i => T138_44list.getD i.val (0,0,0,0,0)

theorem hfix138_44 : ∀ i, ((T138_44 i : Coordinate 1) : Coordinate 1 ⧸ reps rK138)
    ∈ fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138) :=
  repsFix_of_siftB rK138 ⟨44, by decide⟩ T138_44 (by decide)

theorem hinj138_44 : Function.Injective
    (fun i => ((T138_44 i : Coordinate 1) : Coordinate 1 ⧸ reps rK138)) :=
  repsInj_of_reduceAux rK138 T138_44 (by decide)

theorem hcardT138_44 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK138 ⟨44, by decide⟩ R138 hpxR138 hcardq138 (by decide)).symm

/-- **Cell (138, 44).** -/
theorem cell138_44 (e : List (ZMod 25)) (heK : charOK (basisAt rK138) e = true)
    (h : ↥(reps (⟨44, by decide⟩ : Fin 148))) :
    species (reps (⟨44, by decide⟩ : Fin 148)) h (basisElt (reps rK138) (charOfVec rK138 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK138 e (h : Coordinate 1) T138_44 i :=
  species_entry_eq_sum rK138 ⟨44, by decide⟩ e heK h T138_44 hfix138_44 hinj138_44 hcardT138_44
    (fun i => conj_mem_of_fixedPoints (reps ⟨44, by decide⟩) (reps rK138) (T138_44 i) (hfix138_44 i) h)

/-! ## Cell (138, 50): |T| = 5 -/

def T138_50list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T138_50 : Fin 5 → Coordinate 1 := fun i => T138_50list.getD i.val (0,0,0,0,0)

theorem hfix138_50 : ∀ i, ((T138_50 i : Coordinate 1) : Coordinate 1 ⧸ reps rK138)
    ∈ fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138) :=
  repsFix_of_siftB rK138 ⟨50, by decide⟩ T138_50 (by decide)

theorem hinj138_50 : Function.Injective
    (fun i => ((T138_50 i : Coordinate 1) : Coordinate 1 ⧸ reps rK138)) :=
  repsInj_of_reduceAux rK138 T138_50 (by decide)

theorem hcardT138_50 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK138 ⟨50, by decide⟩ R138 hpxR138 hcardq138 (by decide)).symm

/-- **Cell (138, 50).** -/
theorem cell138_50 (e : List (ZMod 25)) (heK : charOK (basisAt rK138) e = true)
    (h : ↥(reps (⟨50, by decide⟩ : Fin 148))) :
    species (reps (⟨50, by decide⟩ : Fin 148)) h (basisElt (reps rK138) (charOfVec rK138 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK138 e (h : Coordinate 1) T138_50 i :=
  species_entry_eq_sum rK138 ⟨50, by decide⟩ e heK h T138_50 hfix138_50 hinj138_50 hcardT138_50
    (fun i => conj_mem_of_fixedPoints (reps ⟨50, by decide⟩) (reps rK138) (T138_50 i) (hfix138_50 i) h)

/-! ## Cell (138, 53): |T| = 5 -/

def T138_53list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T138_53 : Fin 5 → Coordinate 1 := fun i => T138_53list.getD i.val (0,0,0,0,0)

theorem hfix138_53 : ∀ i, ((T138_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK138)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138) :=
  repsFix_of_siftB rK138 ⟨53, by decide⟩ T138_53 (by decide)

theorem hinj138_53 : Function.Injective
    (fun i => ((T138_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK138)) :=
  repsInj_of_reduceAux rK138 T138_53 (by decide)

theorem hcardT138_53 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK138 ⟨53, by decide⟩ R138 hpxR138 hcardq138 (by decide)).symm

/-- **Cell (138, 53).** -/
theorem cell138_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK138) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK138) (charOfVec rK138 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK138 e (h : Coordinate 1) T138_53 i :=
  species_entry_eq_sum rK138 ⟨53, by decide⟩ e heK h T138_53 hfix138_53 hinj138_53 hcardT138_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK138) (T138_53 i) (hfix138_53 i) h)

/-! ## Cell (138, 84): |T| = 5 -/

def T138_84list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T138_84 : Fin 5 → Coordinate 1 := fun i => T138_84list.getD i.val (0,0,0,0,0)

theorem hfix138_84 : ∀ i, ((T138_84 i : Coordinate 1) : Coordinate 1 ⧸ reps rK138)
    ∈ fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138) :=
  repsFix_of_siftB rK138 ⟨84, by decide⟩ T138_84 (by decide)

theorem hinj138_84 : Function.Injective
    (fun i => ((T138_84 i : Coordinate 1) : Coordinate 1 ⧸ reps rK138)) :=
  repsInj_of_reduceAux rK138 T138_84 (by decide)

theorem hcardT138_84 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK138 ⟨84, by decide⟩ R138 hpxR138 hcardq138 (by decide)).symm

/-- **Cell (138, 84).** -/
theorem cell138_84 (e : List (ZMod 25)) (heK : charOK (basisAt rK138) e = true)
    (h : ↥(reps (⟨84, by decide⟩ : Fin 148))) :
    species (reps (⟨84, by decide⟩ : Fin 148)) h (basisElt (reps rK138) (charOfVec rK138 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK138 e (h : Coordinate 1) T138_84 i :=
  species_entry_eq_sum rK138 ⟨84, by decide⟩ e heK h T138_84 hfix138_84 hinj138_84 hcardT138_84
    (fun i => conj_mem_of_fixedPoints (reps ⟨84, by decide⟩) (reps rK138) (T138_84 i) (hfix138_84 i) h)

/-! ## Cell (138, 93): |T| = 5 -/

def T138_93list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T138_93 : Fin 5 → Coordinate 1 := fun i => T138_93list.getD i.val (0,0,0,0,0)

theorem hfix138_93 : ∀ i, ((T138_93 i : Coordinate 1) : Coordinate 1 ⧸ reps rK138)
    ∈ fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138) :=
  repsFix_of_siftB rK138 ⟨93, by decide⟩ T138_93 (by decide)

theorem hinj138_93 : Function.Injective
    (fun i => ((T138_93 i : Coordinate 1) : Coordinate 1 ⧸ reps rK138)) :=
  repsInj_of_reduceAux rK138 T138_93 (by decide)

theorem hcardT138_93 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK138 ⟨93, by decide⟩ R138 hpxR138 hcardq138 (by decide)).symm

/-- **Cell (138, 93).** -/
theorem cell138_93 (e : List (ZMod 25)) (heK : charOK (basisAt rK138) e = true)
    (h : ↥(reps (⟨93, by decide⟩ : Fin 148))) :
    species (reps (⟨93, by decide⟩ : Fin 148)) h (basisElt (reps rK138) (charOfVec rK138 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK138 e (h : Coordinate 1) T138_93 i :=
  species_entry_eq_sum rK138 ⟨93, by decide⟩ e heK h T138_93 hfix138_93 hinj138_93 hcardT138_93
    (fun i => conj_mem_of_fixedPoints (reps ⟨93, by decide⟩) (reps rK138) (T138_93 i) (hfix138_93 i) h)

/-! ## Cell (138, 95): |T| = 5 -/

def T138_95list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T138_95 : Fin 5 → Coordinate 1 := fun i => T138_95list.getD i.val (0,0,0,0,0)

theorem hfix138_95 : ∀ i, ((T138_95 i : Coordinate 1) : Coordinate 1 ⧸ reps rK138)
    ∈ fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138) :=
  repsFix_of_siftB rK138 ⟨95, by decide⟩ T138_95 (by decide)

theorem hinj138_95 : Function.Injective
    (fun i => ((T138_95 i : Coordinate 1) : Coordinate 1 ⧸ reps rK138)) :=
  repsInj_of_reduceAux rK138 T138_95 (by decide)

theorem hcardT138_95 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK138 ⟨95, by decide⟩ R138 hpxR138 hcardq138 (by decide)).symm

/-- **Cell (138, 95).** -/
theorem cell138_95 (e : List (ZMod 25)) (heK : charOK (basisAt rK138) e = true)
    (h : ↥(reps (⟨95, by decide⟩ : Fin 148))) :
    species (reps (⟨95, by decide⟩ : Fin 148)) h (basisElt (reps rK138) (charOfVec rK138 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK138 e (h : Coordinate 1) T138_95 i :=
  species_entry_eq_sum rK138 ⟨95, by decide⟩ e heK h T138_95 hfix138_95 hinj138_95 hcardT138_95
    (fun i => conj_mem_of_fixedPoints (reps ⟨95, by decide⟩) (reps rK138) (T138_95 i) (hfix138_95 i) h)

/-! ## Cell (138, 104): |T| = 5 -/

def T138_104list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T138_104 : Fin 5 → Coordinate 1 := fun i => T138_104list.getD i.val (0,0,0,0,0)

theorem hfix138_104 : ∀ i, ((T138_104 i : Coordinate 1) : Coordinate 1 ⧸ reps rK138)
    ∈ fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138) :=
  repsFix_of_siftB rK138 ⟨104, by decide⟩ T138_104 (by decide)

theorem hinj138_104 : Function.Injective
    (fun i => ((T138_104 i : Coordinate 1) : Coordinate 1 ⧸ reps rK138)) :=
  repsInj_of_reduceAux rK138 T138_104 (by decide)

theorem hcardT138_104 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK138 ⟨104, by decide⟩ R138 hpxR138 hcardq138 (by decide)).symm

/-- **Cell (138, 104).** -/
theorem cell138_104 (e : List (ZMod 25)) (heK : charOK (basisAt rK138) e = true)
    (h : ↥(reps (⟨104, by decide⟩ : Fin 148))) :
    species (reps (⟨104, by decide⟩ : Fin 148)) h (basisElt (reps rK138) (charOfVec rK138 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK138 e (h : Coordinate 1) T138_104 i :=
  species_entry_eq_sum rK138 ⟨104, by decide⟩ e heK h T138_104 hfix138_104 hinj138_104 hcardT138_104
    (fun i => conj_mem_of_fixedPoints (reps ⟨104, by decide⟩) (reps rK138) (T138_104 i) (hfix138_104 i) h)

/-! ## Cell (138, 106): |T| = 5 -/

def T138_106list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T138_106 : Fin 5 → Coordinate 1 := fun i => T138_106list.getD i.val (0,0,0,0,0)

theorem hfix138_106 : ∀ i, ((T138_106 i : Coordinate 1) : Coordinate 1 ⧸ reps rK138)
    ∈ fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138) :=
  repsFix_of_siftB rK138 ⟨106, by decide⟩ T138_106 (by decide)

theorem hinj138_106 : Function.Injective
    (fun i => ((T138_106 i : Coordinate 1) : Coordinate 1 ⧸ reps rK138)) :=
  repsInj_of_reduceAux rK138 T138_106 (by decide)

theorem hcardT138_106 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK138 ⟨106, by decide⟩ R138 hpxR138 hcardq138 (by decide)).symm

/-- **Cell (138, 106).** -/
theorem cell138_106 (e : List (ZMod 25)) (heK : charOK (basisAt rK138) e = true)
    (h : ↥(reps (⟨106, by decide⟩ : Fin 148))) :
    species (reps (⟨106, by decide⟩ : Fin 148)) h (basisElt (reps rK138) (charOfVec rK138 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK138 e (h : Coordinate 1) T138_106 i :=
  species_entry_eq_sum rK138 ⟨106, by decide⟩ e heK h T138_106 hfix138_106 hinj138_106 hcardT138_106
    (fun i => conj_mem_of_fixedPoints (reps ⟨106, by decide⟩) (reps rK138) (T138_106 i) (hfix138_106 i) h)

/-! ## Cell (138, 112): |T| = 5 -/

def T138_112list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T138_112 : Fin 5 → Coordinate 1 := fun i => T138_112list.getD i.val (0,0,0,0,0)

theorem hfix138_112 : ∀ i, ((T138_112 i : Coordinate 1) : Coordinate 1 ⧸ reps rK138)
    ∈ fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138) :=
  repsFix_of_siftB rK138 ⟨112, by decide⟩ T138_112 (by decide)

theorem hinj138_112 : Function.Injective
    (fun i => ((T138_112 i : Coordinate 1) : Coordinate 1 ⧸ reps rK138)) :=
  repsInj_of_reduceAux rK138 T138_112 (by decide)

theorem hcardT138_112 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK138 ⟨112, by decide⟩ R138 hpxR138 hcardq138 (by decide)).symm

/-- **Cell (138, 112).** -/
theorem cell138_112 (e : List (ZMod 25)) (heK : charOK (basisAt rK138) e = true)
    (h : ↥(reps (⟨112, by decide⟩ : Fin 148))) :
    species (reps (⟨112, by decide⟩ : Fin 148)) h (basisElt (reps rK138) (charOfVec rK138 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK138 e (h : Coordinate 1) T138_112 i :=
  species_entry_eq_sum rK138 ⟨112, by decide⟩ e heK h T138_112 hfix138_112 hinj138_112 hcardT138_112
    (fun i => conj_mem_of_fixedPoints (reps ⟨112, by decide⟩) (reps rK138) (T138_112 i) (hfix138_112 i) h)

/-! ## Cell (138, 138): |T| = 5 -/

def T138_138list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T138_138 : Fin 5 → Coordinate 1 := fun i => T138_138list.getD i.val (0,0,0,0,0)

theorem hfix138_138 : ∀ i, ((T138_138 i : Coordinate 1) : Coordinate 1 ⧸ reps rK138)
    ∈ fixedPoints (reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138) :=
  repsFix_of_siftB rK138 ⟨138, by decide⟩ T138_138 (by decide)

theorem hinj138_138 : Function.Injective
    (fun i => ((T138_138 i : Coordinate 1) : Coordinate 1 ⧸ reps rK138)) :=
  repsInj_of_reduceAux rK138 T138_138 (by decide)

theorem hcardT138_138 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK138 ⟨138, by decide⟩ R138 hpxR138 hcardq138 (by decide)).symm

/-- **Cell (138, 138).** -/
theorem cell138_138 (e : List (ZMod 25)) (heK : charOK (basisAt rK138) e = true)
    (h : ↥(reps (⟨138, by decide⟩ : Fin 148))) :
    species (reps (⟨138, by decide⟩ : Fin 148)) h (basisElt (reps rK138) (charOfVec rK138 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK138 e (h : Coordinate 1) T138_138 i :=
  species_entry_eq_sum rK138 ⟨138, by decide⟩ e heK h T138_138 hfix138_138 hinj138_138 hcardT138_138
    (fun i => conj_mem_of_fixedPoints (reps ⟨138, by decide⟩) (reps rK138) (T138_138 i) (hfix138_138 i) h)

namespace Q2

def R138_2 : Fin 5 → Coordinate 2 := fun i => R138list.getD i.val (0,0,0,0,0)
theorem hpxR138_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK138) (R138_2 i)) := by decide
theorem hcardq138_2 : Nat.card (Coordinate 2 ⧸ reps rK138) = 5 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (138, 0) twin -/

def T138_0_2 : Fin 5 → Coordinate 2 := fun i => T138_0list.getD i.val (0,0,0,0,0)

theorem hfix138_0_2 : ∀ i, ((T138_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK138)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK138) :=
  repsFix_of_siftB2 rK138 ⟨0, by decide⟩ T138_0_2 (by decide)

theorem hinj138_0_2 : Function.Injective
    (fun i => ((T138_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK138)) :=
  repsInj_of_reduceAux2 rK138 T138_0_2 (by decide)

theorem hcardT138_0_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK138)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK138 ⟨0, by decide⟩ R138_2 hpxR138_2 hcardq138_2 (by decide)).symm

/-- **Cell (138, 0) twin (q=2).** -/
theorem cell138_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK138) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK138) (charOfVec2 rK138 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK138 e (h : Coordinate 2) T138_0_2 i :=
  species_entry_eq_sum rK138 ⟨0, by decide⟩ e heK h T138_0_2 hfix138_0_2 hinj138_0_2 hcardT138_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK138) (T138_0_2 i) (hfix138_0_2 i) h)

/-! ### Cell (138, 5) twin -/

def T138_5_2 : Fin 5 → Coordinate 2 := fun i => T138_5list.getD i.val (0,0,0,0,0)

theorem hfix138_5_2 : ∀ i, ((T138_5_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK138)
    ∈ fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK138) :=
  repsFix_of_siftB2 rK138 ⟨5, by decide⟩ T138_5_2 (by decide)

theorem hinj138_5_2 : Function.Injective
    (fun i => ((T138_5_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK138)) :=
  repsInj_of_reduceAux2 rK138 T138_5_2 (by decide)

theorem hcardT138_5_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK138)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK138 ⟨5, by decide⟩ R138_2 hpxR138_2 hcardq138_2 (by decide)).symm

/-- **Cell (138, 5) twin (q=2).** -/
theorem cell138_5_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK138) e = true)
    (h : ↥(reps (⟨5, by decide⟩ : Fin 148))) :
    species (reps (⟨5, by decide⟩ : Fin 148)) h (basisElt (reps rK138) (charOfVec2 rK138 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK138 e (h : Coordinate 2) T138_5_2 i :=
  species_entry_eq_sum rK138 ⟨5, by decide⟩ e heK h T138_5_2 hfix138_5_2 hinj138_5_2 hcardT138_5_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨5, by decide⟩) (reps rK138) (T138_5_2 i) (hfix138_5_2 i) h)

/-! ### Cell (138, 10) twin -/

def T138_10_2 : Fin 5 → Coordinate 2 := fun i => T138_10list.getD i.val (0,0,0,0,0)

theorem hfix138_10_2 : ∀ i, ((T138_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK138)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK138) :=
  repsFix_of_siftB2 rK138 ⟨10, by decide⟩ T138_10_2 (by decide)

theorem hinj138_10_2 : Function.Injective
    (fun i => ((T138_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK138)) :=
  repsInj_of_reduceAux2 rK138 T138_10_2 (by decide)

theorem hcardT138_10_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK138)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK138 ⟨10, by decide⟩ R138_2 hpxR138_2 hcardq138_2 (by decide)).symm

/-- **Cell (138, 10) twin (q=2).** -/
theorem cell138_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK138) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK138) (charOfVec2 rK138 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK138 e (h : Coordinate 2) T138_10_2 i :=
  species_entry_eq_sum rK138 ⟨10, by decide⟩ e heK h T138_10_2 hfix138_10_2 hinj138_10_2 hcardT138_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK138) (T138_10_2 i) (hfix138_10_2 i) h)

/-! ### Cell (138, 12) twin -/

def T138_12_2 : Fin 5 → Coordinate 2 := fun i => T138_12list.getD i.val (0,0,0,0,0)

theorem hfix138_12_2 : ∀ i, ((T138_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK138)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK138) :=
  repsFix_of_siftB2 rK138 ⟨12, by decide⟩ T138_12_2 (by decide)

theorem hinj138_12_2 : Function.Injective
    (fun i => ((T138_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK138)) :=
  repsInj_of_reduceAux2 rK138 T138_12_2 (by decide)

theorem hcardT138_12_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK138)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK138 ⟨12, by decide⟩ R138_2 hpxR138_2 hcardq138_2 (by decide)).symm

/-- **Cell (138, 12) twin (q=2).** -/
theorem cell138_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK138) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK138) (charOfVec2 rK138 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK138 e (h : Coordinate 2) T138_12_2 i :=
  species_entry_eq_sum rK138 ⟨12, by decide⟩ e heK h T138_12_2 hfix138_12_2 hinj138_12_2 hcardT138_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK138) (T138_12_2 i) (hfix138_12_2 i) h)

/-! ### Cell (138, 23) twin -/

def T138_23_2 : Fin 5 → Coordinate 2 := fun i => T138_23list.getD i.val (0,0,0,0,0)

theorem hfix138_23_2 : ∀ i, ((T138_23_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK138)
    ∈ fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK138) :=
  repsFix_of_siftB2 rK138 ⟨23, by decide⟩ T138_23_2 (by decide)

theorem hinj138_23_2 : Function.Injective
    (fun i => ((T138_23_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK138)) :=
  repsInj_of_reduceAux2 rK138 T138_23_2 (by decide)

theorem hcardT138_23_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK138)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK138 ⟨23, by decide⟩ R138_2 hpxR138_2 hcardq138_2 (by decide)).symm

/-- **Cell (138, 23) twin (q=2).** -/
theorem cell138_23_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK138) e = true)
    (h : ↥(reps (⟨23, by decide⟩ : Fin 148))) :
    species (reps (⟨23, by decide⟩ : Fin 148)) h (basisElt (reps rK138) (charOfVec2 rK138 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK138 e (h : Coordinate 2) T138_23_2 i :=
  species_entry_eq_sum rK138 ⟨23, by decide⟩ e heK h T138_23_2 hfix138_23_2 hinj138_23_2 hcardT138_23_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨23, by decide⟩) (reps rK138) (T138_23_2 i) (hfix138_23_2 i) h)

/-! ### Cell (138, 31) twin -/

def T138_31_2 : Fin 5 → Coordinate 2 := fun i => T138_31list.getD i.val (0,0,0,0,0)

theorem hfix138_31_2 : ∀ i, ((T138_31_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK138)
    ∈ fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK138) :=
  repsFix_of_siftB2 rK138 ⟨31, by decide⟩ T138_31_2 (by decide)

theorem hinj138_31_2 : Function.Injective
    (fun i => ((T138_31_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK138)) :=
  repsInj_of_reduceAux2 rK138 T138_31_2 (by decide)

theorem hcardT138_31_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK138)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK138 ⟨31, by decide⟩ R138_2 hpxR138_2 hcardq138_2 (by decide)).symm

/-- **Cell (138, 31) twin (q=2).** -/
theorem cell138_31_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK138) e = true)
    (h : ↥(reps (⟨31, by decide⟩ : Fin 148))) :
    species (reps (⟨31, by decide⟩ : Fin 148)) h (basisElt (reps rK138) (charOfVec2 rK138 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK138 e (h : Coordinate 2) T138_31_2 i :=
  species_entry_eq_sum rK138 ⟨31, by decide⟩ e heK h T138_31_2 hfix138_31_2 hinj138_31_2 hcardT138_31_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨31, by decide⟩) (reps rK138) (T138_31_2 i) (hfix138_31_2 i) h)

/-! ### Cell (138, 33) twin -/

def T138_33_2 : Fin 5 → Coordinate 2 := fun i => T138_33list.getD i.val (0,0,0,0,0)

theorem hfix138_33_2 : ∀ i, ((T138_33_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK138)
    ∈ fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK138) :=
  repsFix_of_siftB2 rK138 ⟨33, by decide⟩ T138_33_2 (by decide)

theorem hinj138_33_2 : Function.Injective
    (fun i => ((T138_33_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK138)) :=
  repsInj_of_reduceAux2 rK138 T138_33_2 (by decide)

theorem hcardT138_33_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK138)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK138 ⟨33, by decide⟩ R138_2 hpxR138_2 hcardq138_2 (by decide)).symm

/-- **Cell (138, 33) twin (q=2).** -/
theorem cell138_33_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK138) e = true)
    (h : ↥(reps (⟨33, by decide⟩ : Fin 148))) :
    species (reps (⟨33, by decide⟩ : Fin 148)) h (basisElt (reps rK138) (charOfVec2 rK138 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK138 e (h : Coordinate 2) T138_33_2 i :=
  species_entry_eq_sum rK138 ⟨33, by decide⟩ e heK h T138_33_2 hfix138_33_2 hinj138_33_2 hcardT138_33_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨33, by decide⟩) (reps rK138) (T138_33_2 i) (hfix138_33_2 i) h)

/-! ### Cell (138, 42) twin -/

def T138_42_2 : Fin 5 → Coordinate 2 := fun i => T138_42list.getD i.val (0,0,0,0,0)

theorem hfix138_42_2 : ∀ i, ((T138_42_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK138)
    ∈ fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK138) :=
  repsFix_of_siftB2 rK138 ⟨42, by decide⟩ T138_42_2 (by decide)

theorem hinj138_42_2 : Function.Injective
    (fun i => ((T138_42_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK138)) :=
  repsInj_of_reduceAux2 rK138 T138_42_2 (by decide)

theorem hcardT138_42_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK138)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK138 ⟨42, by decide⟩ R138_2 hpxR138_2 hcardq138_2 (by decide)).symm

/-- **Cell (138, 42) twin (q=2).** -/
theorem cell138_42_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK138) e = true)
    (h : ↥(reps (⟨42, by decide⟩ : Fin 148))) :
    species (reps (⟨42, by decide⟩ : Fin 148)) h (basisElt (reps rK138) (charOfVec2 rK138 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK138 e (h : Coordinate 2) T138_42_2 i :=
  species_entry_eq_sum rK138 ⟨42, by decide⟩ e heK h T138_42_2 hfix138_42_2 hinj138_42_2 hcardT138_42_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨42, by decide⟩) (reps rK138) (T138_42_2 i) (hfix138_42_2 i) h)

/-! ### Cell (138, 44) twin -/

def T138_44_2 : Fin 5 → Coordinate 2 := fun i => T138_44list.getD i.val (0,0,0,0,0)

theorem hfix138_44_2 : ∀ i, ((T138_44_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK138)
    ∈ fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK138) :=
  repsFix_of_siftB2 rK138 ⟨44, by decide⟩ T138_44_2 (by decide)

theorem hinj138_44_2 : Function.Injective
    (fun i => ((T138_44_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK138)) :=
  repsInj_of_reduceAux2 rK138 T138_44_2 (by decide)

theorem hcardT138_44_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK138)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK138 ⟨44, by decide⟩ R138_2 hpxR138_2 hcardq138_2 (by decide)).symm

/-- **Cell (138, 44) twin (q=2).** -/
theorem cell138_44_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK138) e = true)
    (h : ↥(reps (⟨44, by decide⟩ : Fin 148))) :
    species (reps (⟨44, by decide⟩ : Fin 148)) h (basisElt (reps rK138) (charOfVec2 rK138 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK138 e (h : Coordinate 2) T138_44_2 i :=
  species_entry_eq_sum rK138 ⟨44, by decide⟩ e heK h T138_44_2 hfix138_44_2 hinj138_44_2 hcardT138_44_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨44, by decide⟩) (reps rK138) (T138_44_2 i) (hfix138_44_2 i) h)

/-! ### Cell (138, 50) twin -/

def T138_50_2 : Fin 5 → Coordinate 2 := fun i => T138_50list.getD i.val (0,0,0,0,0)

theorem hfix138_50_2 : ∀ i, ((T138_50_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK138)
    ∈ fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK138) :=
  repsFix_of_siftB2 rK138 ⟨50, by decide⟩ T138_50_2 (by decide)

theorem hinj138_50_2 : Function.Injective
    (fun i => ((T138_50_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK138)) :=
  repsInj_of_reduceAux2 rK138 T138_50_2 (by decide)

theorem hcardT138_50_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK138)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK138 ⟨50, by decide⟩ R138_2 hpxR138_2 hcardq138_2 (by decide)).symm

/-- **Cell (138, 50) twin (q=2).** -/
theorem cell138_50_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK138) e = true)
    (h : ↥(reps (⟨50, by decide⟩ : Fin 148))) :
    species (reps (⟨50, by decide⟩ : Fin 148)) h (basisElt (reps rK138) (charOfVec2 rK138 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK138 e (h : Coordinate 2) T138_50_2 i :=
  species_entry_eq_sum rK138 ⟨50, by decide⟩ e heK h T138_50_2 hfix138_50_2 hinj138_50_2 hcardT138_50_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨50, by decide⟩) (reps rK138) (T138_50_2 i) (hfix138_50_2 i) h)

/-! ### Cell (138, 53) twin -/

def T138_53_2 : Fin 5 → Coordinate 2 := fun i => T138_53list.getD i.val (0,0,0,0,0)

theorem hfix138_53_2 : ∀ i, ((T138_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK138)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK138) :=
  repsFix_of_siftB2 rK138 ⟨53, by decide⟩ T138_53_2 (by decide)

theorem hinj138_53_2 : Function.Injective
    (fun i => ((T138_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK138)) :=
  repsInj_of_reduceAux2 rK138 T138_53_2 (by decide)

theorem hcardT138_53_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK138)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK138 ⟨53, by decide⟩ R138_2 hpxR138_2 hcardq138_2 (by decide)).symm

/-- **Cell (138, 53) twin (q=2).** -/
theorem cell138_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK138) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK138) (charOfVec2 rK138 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK138 e (h : Coordinate 2) T138_53_2 i :=
  species_entry_eq_sum rK138 ⟨53, by decide⟩ e heK h T138_53_2 hfix138_53_2 hinj138_53_2 hcardT138_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK138) (T138_53_2 i) (hfix138_53_2 i) h)

/-! ### Cell (138, 84) twin -/

def T138_84_2 : Fin 5 → Coordinate 2 := fun i => T138_84list.getD i.val (0,0,0,0,0)

theorem hfix138_84_2 : ∀ i, ((T138_84_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK138)
    ∈ fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK138) :=
  repsFix_of_siftB2 rK138 ⟨84, by decide⟩ T138_84_2 (by decide)

theorem hinj138_84_2 : Function.Injective
    (fun i => ((T138_84_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK138)) :=
  repsInj_of_reduceAux2 rK138 T138_84_2 (by decide)

theorem hcardT138_84_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK138)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK138 ⟨84, by decide⟩ R138_2 hpxR138_2 hcardq138_2 (by decide)).symm

/-- **Cell (138, 84) twin (q=2).** -/
theorem cell138_84_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK138) e = true)
    (h : ↥(reps (⟨84, by decide⟩ : Fin 148))) :
    species (reps (⟨84, by decide⟩ : Fin 148)) h (basisElt (reps rK138) (charOfVec2 rK138 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK138 e (h : Coordinate 2) T138_84_2 i :=
  species_entry_eq_sum rK138 ⟨84, by decide⟩ e heK h T138_84_2 hfix138_84_2 hinj138_84_2 hcardT138_84_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨84, by decide⟩) (reps rK138) (T138_84_2 i) (hfix138_84_2 i) h)

/-! ### Cell (138, 93) twin -/

def T138_93_2 : Fin 5 → Coordinate 2 := fun i => T138_93list.getD i.val (0,0,0,0,0)

theorem hfix138_93_2 : ∀ i, ((T138_93_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK138)
    ∈ fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK138) :=
  repsFix_of_siftB2 rK138 ⟨93, by decide⟩ T138_93_2 (by decide)

theorem hinj138_93_2 : Function.Injective
    (fun i => ((T138_93_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK138)) :=
  repsInj_of_reduceAux2 rK138 T138_93_2 (by decide)

theorem hcardT138_93_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK138)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK138 ⟨93, by decide⟩ R138_2 hpxR138_2 hcardq138_2 (by decide)).symm

/-- **Cell (138, 93) twin (q=2).** -/
theorem cell138_93_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK138) e = true)
    (h : ↥(reps (⟨93, by decide⟩ : Fin 148))) :
    species (reps (⟨93, by decide⟩ : Fin 148)) h (basisElt (reps rK138) (charOfVec2 rK138 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK138 e (h : Coordinate 2) T138_93_2 i :=
  species_entry_eq_sum rK138 ⟨93, by decide⟩ e heK h T138_93_2 hfix138_93_2 hinj138_93_2 hcardT138_93_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨93, by decide⟩) (reps rK138) (T138_93_2 i) (hfix138_93_2 i) h)

/-! ### Cell (138, 95) twin -/

def T138_95_2 : Fin 5 → Coordinate 2 := fun i => T138_95list.getD i.val (0,0,0,0,0)

theorem hfix138_95_2 : ∀ i, ((T138_95_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK138)
    ∈ fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK138) :=
  repsFix_of_siftB2 rK138 ⟨95, by decide⟩ T138_95_2 (by decide)

theorem hinj138_95_2 : Function.Injective
    (fun i => ((T138_95_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK138)) :=
  repsInj_of_reduceAux2 rK138 T138_95_2 (by decide)

theorem hcardT138_95_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK138)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK138 ⟨95, by decide⟩ R138_2 hpxR138_2 hcardq138_2 (by decide)).symm

/-- **Cell (138, 95) twin (q=2).** -/
theorem cell138_95_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK138) e = true)
    (h : ↥(reps (⟨95, by decide⟩ : Fin 148))) :
    species (reps (⟨95, by decide⟩ : Fin 148)) h (basisElt (reps rK138) (charOfVec2 rK138 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK138 e (h : Coordinate 2) T138_95_2 i :=
  species_entry_eq_sum rK138 ⟨95, by decide⟩ e heK h T138_95_2 hfix138_95_2 hinj138_95_2 hcardT138_95_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨95, by decide⟩) (reps rK138) (T138_95_2 i) (hfix138_95_2 i) h)

/-! ### Cell (138, 104) twin -/

def T138_104_2 : Fin 5 → Coordinate 2 := fun i => T138_104list.getD i.val (0,0,0,0,0)

theorem hfix138_104_2 : ∀ i, ((T138_104_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK138)
    ∈ fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK138) :=
  repsFix_of_siftB2 rK138 ⟨104, by decide⟩ T138_104_2 (by decide)

theorem hinj138_104_2 : Function.Injective
    (fun i => ((T138_104_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK138)) :=
  repsInj_of_reduceAux2 rK138 T138_104_2 (by decide)

theorem hcardT138_104_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK138)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK138 ⟨104, by decide⟩ R138_2 hpxR138_2 hcardq138_2 (by decide)).symm

/-- **Cell (138, 104) twin (q=2).** -/
theorem cell138_104_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK138) e = true)
    (h : ↥(reps (⟨104, by decide⟩ : Fin 148))) :
    species (reps (⟨104, by decide⟩ : Fin 148)) h (basisElt (reps rK138) (charOfVec2 rK138 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK138 e (h : Coordinate 2) T138_104_2 i :=
  species_entry_eq_sum rK138 ⟨104, by decide⟩ e heK h T138_104_2 hfix138_104_2 hinj138_104_2 hcardT138_104_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨104, by decide⟩) (reps rK138) (T138_104_2 i) (hfix138_104_2 i) h)

/-! ### Cell (138, 106) twin -/

def T138_106_2 : Fin 5 → Coordinate 2 := fun i => T138_106list.getD i.val (0,0,0,0,0)

theorem hfix138_106_2 : ∀ i, ((T138_106_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK138)
    ∈ fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK138) :=
  repsFix_of_siftB2 rK138 ⟨106, by decide⟩ T138_106_2 (by decide)

theorem hinj138_106_2 : Function.Injective
    (fun i => ((T138_106_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK138)) :=
  repsInj_of_reduceAux2 rK138 T138_106_2 (by decide)

theorem hcardT138_106_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK138)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK138 ⟨106, by decide⟩ R138_2 hpxR138_2 hcardq138_2 (by decide)).symm

/-- **Cell (138, 106) twin (q=2).** -/
theorem cell138_106_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK138) e = true)
    (h : ↥(reps (⟨106, by decide⟩ : Fin 148))) :
    species (reps (⟨106, by decide⟩ : Fin 148)) h (basisElt (reps rK138) (charOfVec2 rK138 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK138 e (h : Coordinate 2) T138_106_2 i :=
  species_entry_eq_sum rK138 ⟨106, by decide⟩ e heK h T138_106_2 hfix138_106_2 hinj138_106_2 hcardT138_106_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨106, by decide⟩) (reps rK138) (T138_106_2 i) (hfix138_106_2 i) h)

/-! ### Cell (138, 112) twin -/

def T138_112_2 : Fin 5 → Coordinate 2 := fun i => T138_112list.getD i.val (0,0,0,0,0)

theorem hfix138_112_2 : ∀ i, ((T138_112_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK138)
    ∈ fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK138) :=
  repsFix_of_siftB2 rK138 ⟨112, by decide⟩ T138_112_2 (by decide)

theorem hinj138_112_2 : Function.Injective
    (fun i => ((T138_112_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK138)) :=
  repsInj_of_reduceAux2 rK138 T138_112_2 (by decide)

theorem hcardT138_112_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK138)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK138 ⟨112, by decide⟩ R138_2 hpxR138_2 hcardq138_2 (by decide)).symm

/-- **Cell (138, 112) twin (q=2).** -/
theorem cell138_112_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK138) e = true)
    (h : ↥(reps (⟨112, by decide⟩ : Fin 148))) :
    species (reps (⟨112, by decide⟩ : Fin 148)) h (basisElt (reps rK138) (charOfVec2 rK138 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK138 e (h : Coordinate 2) T138_112_2 i :=
  species_entry_eq_sum rK138 ⟨112, by decide⟩ e heK h T138_112_2 hfix138_112_2 hinj138_112_2 hcardT138_112_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨112, by decide⟩) (reps rK138) (T138_112_2 i) (hfix138_112_2 i) h)

/-! ### Cell (138, 138) twin -/

def T138_138_2 : Fin 5 → Coordinate 2 := fun i => T138_138list.getD i.val (0,0,0,0,0)

theorem hfix138_138_2 : ∀ i, ((T138_138_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK138)
    ∈ fixedPoints (reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK138) :=
  repsFix_of_siftB2 rK138 ⟨138, by decide⟩ T138_138_2 (by decide)

theorem hinj138_138_2 : Function.Injective
    (fun i => ((T138_138_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK138)) :=
  repsInj_of_reduceAux2 rK138 T138_138_2 (by decide)

theorem hcardT138_138_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK138)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK138 ⟨138, by decide⟩ R138_2 hpxR138_2 hcardq138_2 (by decide)).symm

/-- **Cell (138, 138) twin (q=2).** -/
theorem cell138_138_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK138) e = true)
    (h : ↥(reps (⟨138, by decide⟩ : Fin 148))) :
    species (reps (⟨138, by decide⟩ : Fin 148)) h (basisElt (reps rK138) (charOfVec2 rK138 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK138 e (h : Coordinate 2) T138_138_2 i :=
  species_entry_eq_sum rK138 ⟨138, by decide⟩ e heK h T138_138_2 hfix138_138_2 hinj138_138_2 hcardT138_138_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨138, by decide⟩) (reps rK138) (T138_138_2 i) (hfix138_138_2 i) h)

end Q2

/-! # K-class rK = 139  (|G/K| = 5) -/

def rK139 : Fin 148 := ⟨139, by decide⟩

def R139list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def R139 : Fin 5 → Coordinate 1 := fun i => R139list.getD i.val (0,0,0,0,0)

theorem hpxR139 : Function.Injective (fun i => reduceAux 1 (basisAt rK139) (R139 i)) := by decide
theorem hcardq139 : Nat.card (Coordinate 1 ⧸ reps rK139) = 5 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (139, 0): |T| = 5 -/

def T139_0list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T139_0 : Fin 5 → Coordinate 1 := fun i => T139_0list.getD i.val (0,0,0,0,0)

theorem hfix139_0 : ∀ i, ((T139_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK139)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139) :=
  repsFix_of_siftB rK139 ⟨0, by decide⟩ T139_0 (by decide)

theorem hinj139_0 : Function.Injective
    (fun i => ((T139_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK139)) :=
  repsInj_of_reduceAux rK139 T139_0 (by decide)

theorem hcardT139_0 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK139 ⟨0, by decide⟩ R139 hpxR139 hcardq139 (by decide)).symm

/-- **Cell (139, 0).** -/
theorem cell139_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK139) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK139) (charOfVec rK139 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK139 e (h : Coordinate 1) T139_0 i :=
  species_entry_eq_sum rK139 ⟨0, by decide⟩ e heK h T139_0 hfix139_0 hinj139_0 hcardT139_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK139) (T139_0 i) (hfix139_0 i) h)

/-! ## Cell (139, 5): |T| = 5 -/

def T139_5list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T139_5 : Fin 5 → Coordinate 1 := fun i => T139_5list.getD i.val (0,0,0,0,0)

theorem hfix139_5 : ∀ i, ((T139_5 i : Coordinate 1) : Coordinate 1 ⧸ reps rK139)
    ∈ fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139) :=
  repsFix_of_siftB rK139 ⟨5, by decide⟩ T139_5 (by decide)

theorem hinj139_5 : Function.Injective
    (fun i => ((T139_5 i : Coordinate 1) : Coordinate 1 ⧸ reps rK139)) :=
  repsInj_of_reduceAux rK139 T139_5 (by decide)

theorem hcardT139_5 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK139 ⟨5, by decide⟩ R139 hpxR139 hcardq139 (by decide)).symm

/-- **Cell (139, 5).** -/
theorem cell139_5 (e : List (ZMod 25)) (heK : charOK (basisAt rK139) e = true)
    (h : ↥(reps (⟨5, by decide⟩ : Fin 148))) :
    species (reps (⟨5, by decide⟩ : Fin 148)) h (basisElt (reps rK139) (charOfVec rK139 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK139 e (h : Coordinate 1) T139_5 i :=
  species_entry_eq_sum rK139 ⟨5, by decide⟩ e heK h T139_5 hfix139_5 hinj139_5 hcardT139_5
    (fun i => conj_mem_of_fixedPoints (reps ⟨5, by decide⟩) (reps rK139) (T139_5 i) (hfix139_5 i) h)

/-! ## Cell (139, 10): |T| = 5 -/

def T139_10list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T139_10 : Fin 5 → Coordinate 1 := fun i => T139_10list.getD i.val (0,0,0,0,0)

theorem hfix139_10 : ∀ i, ((T139_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK139)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139) :=
  repsFix_of_siftB rK139 ⟨10, by decide⟩ T139_10 (by decide)

theorem hinj139_10 : Function.Injective
    (fun i => ((T139_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK139)) :=
  repsInj_of_reduceAux rK139 T139_10 (by decide)

theorem hcardT139_10 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK139 ⟨10, by decide⟩ R139 hpxR139 hcardq139 (by decide)).symm

/-- **Cell (139, 10).** -/
theorem cell139_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK139) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK139) (charOfVec rK139 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK139 e (h : Coordinate 1) T139_10 i :=
  species_entry_eq_sum rK139 ⟨10, by decide⟩ e heK h T139_10 hfix139_10 hinj139_10 hcardT139_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK139) (T139_10 i) (hfix139_10 i) h)

/-! ## Cell (139, 12): |T| = 5 -/

def T139_12list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T139_12 : Fin 5 → Coordinate 1 := fun i => T139_12list.getD i.val (0,0,0,0,0)

theorem hfix139_12 : ∀ i, ((T139_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK139)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139) :=
  repsFix_of_siftB rK139 ⟨12, by decide⟩ T139_12 (by decide)

theorem hinj139_12 : Function.Injective
    (fun i => ((T139_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK139)) :=
  repsInj_of_reduceAux rK139 T139_12 (by decide)

theorem hcardT139_12 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK139 ⟨12, by decide⟩ R139 hpxR139 hcardq139 (by decide)).symm

/-- **Cell (139, 12).** -/
theorem cell139_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK139) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK139) (charOfVec rK139 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK139 e (h : Coordinate 1) T139_12 i :=
  species_entry_eq_sum rK139 ⟨12, by decide⟩ e heK h T139_12 hfix139_12 hinj139_12 hcardT139_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK139) (T139_12 i) (hfix139_12 i) h)

/-! ## Cell (139, 23): |T| = 5 -/

def T139_23list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T139_23 : Fin 5 → Coordinate 1 := fun i => T139_23list.getD i.val (0,0,0,0,0)

theorem hfix139_23 : ∀ i, ((T139_23 i : Coordinate 1) : Coordinate 1 ⧸ reps rK139)
    ∈ fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139) :=
  repsFix_of_siftB rK139 ⟨23, by decide⟩ T139_23 (by decide)

theorem hinj139_23 : Function.Injective
    (fun i => ((T139_23 i : Coordinate 1) : Coordinate 1 ⧸ reps rK139)) :=
  repsInj_of_reduceAux rK139 T139_23 (by decide)

theorem hcardT139_23 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK139 ⟨23, by decide⟩ R139 hpxR139 hcardq139 (by decide)).symm

/-- **Cell (139, 23).** -/
theorem cell139_23 (e : List (ZMod 25)) (heK : charOK (basisAt rK139) e = true)
    (h : ↥(reps (⟨23, by decide⟩ : Fin 148))) :
    species (reps (⟨23, by decide⟩ : Fin 148)) h (basisElt (reps rK139) (charOfVec rK139 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK139 e (h : Coordinate 1) T139_23 i :=
  species_entry_eq_sum rK139 ⟨23, by decide⟩ e heK h T139_23 hfix139_23 hinj139_23 hcardT139_23
    (fun i => conj_mem_of_fixedPoints (reps ⟨23, by decide⟩) (reps rK139) (T139_23 i) (hfix139_23 i) h)

/-! ## Cell (139, 32): |T| = 5 -/

def T139_32list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T139_32 : Fin 5 → Coordinate 1 := fun i => T139_32list.getD i.val (0,0,0,0,0)

theorem hfix139_32 : ∀ i, ((T139_32 i : Coordinate 1) : Coordinate 1 ⧸ reps rK139)
    ∈ fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139) :=
  repsFix_of_siftB rK139 ⟨32, by decide⟩ T139_32 (by decide)

theorem hinj139_32 : Function.Injective
    (fun i => ((T139_32 i : Coordinate 1) : Coordinate 1 ⧸ reps rK139)) :=
  repsInj_of_reduceAux rK139 T139_32 (by decide)

theorem hcardT139_32 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK139 ⟨32, by decide⟩ R139 hpxR139 hcardq139 (by decide)).symm

/-- **Cell (139, 32).** -/
theorem cell139_32 (e : List (ZMod 25)) (heK : charOK (basisAt rK139) e = true)
    (h : ↥(reps (⟨32, by decide⟩ : Fin 148))) :
    species (reps (⟨32, by decide⟩ : Fin 148)) h (basisElt (reps rK139) (charOfVec rK139 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK139 e (h : Coordinate 1) T139_32 i :=
  species_entry_eq_sum rK139 ⟨32, by decide⟩ e heK h T139_32 hfix139_32 hinj139_32 hcardT139_32
    (fun i => conj_mem_of_fixedPoints (reps ⟨32, by decide⟩) (reps rK139) (T139_32 i) (hfix139_32 i) h)

/-! ## Cell (139, 34): |T| = 5 -/

def T139_34list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T139_34 : Fin 5 → Coordinate 1 := fun i => T139_34list.getD i.val (0,0,0,0,0)

theorem hfix139_34 : ∀ i, ((T139_34 i : Coordinate 1) : Coordinate 1 ⧸ reps rK139)
    ∈ fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139) :=
  repsFix_of_siftB rK139 ⟨34, by decide⟩ T139_34 (by decide)

theorem hinj139_34 : Function.Injective
    (fun i => ((T139_34 i : Coordinate 1) : Coordinate 1 ⧸ reps rK139)) :=
  repsInj_of_reduceAux rK139 T139_34 (by decide)

theorem hcardT139_34 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK139 ⟨34, by decide⟩ R139 hpxR139 hcardq139 (by decide)).symm

/-- **Cell (139, 34).** -/
theorem cell139_34 (e : List (ZMod 25)) (heK : charOK (basisAt rK139) e = true)
    (h : ↥(reps (⟨34, by decide⟩ : Fin 148))) :
    species (reps (⟨34, by decide⟩ : Fin 148)) h (basisElt (reps rK139) (charOfVec rK139 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK139 e (h : Coordinate 1) T139_34 i :=
  species_entry_eq_sum rK139 ⟨34, by decide⟩ e heK h T139_34 hfix139_34 hinj139_34 hcardT139_34
    (fun i => conj_mem_of_fixedPoints (reps ⟨34, by decide⟩) (reps rK139) (T139_34 i) (hfix139_34 i) h)

/-! ## Cell (139, 38): |T| = 5 -/

def T139_38list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T139_38 : Fin 5 → Coordinate 1 := fun i => T139_38list.getD i.val (0,0,0,0,0)

theorem hfix139_38 : ∀ i, ((T139_38 i : Coordinate 1) : Coordinate 1 ⧸ reps rK139)
    ∈ fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139) :=
  repsFix_of_siftB rK139 ⟨38, by decide⟩ T139_38 (by decide)

theorem hinj139_38 : Function.Injective
    (fun i => ((T139_38 i : Coordinate 1) : Coordinate 1 ⧸ reps rK139)) :=
  repsInj_of_reduceAux rK139 T139_38 (by decide)

theorem hcardT139_38 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK139 ⟨38, by decide⟩ R139 hpxR139 hcardq139 (by decide)).symm

/-- **Cell (139, 38).** -/
theorem cell139_38 (e : List (ZMod 25)) (heK : charOK (basisAt rK139) e = true)
    (h : ↥(reps (⟨38, by decide⟩ : Fin 148))) :
    species (reps (⟨38, by decide⟩ : Fin 148)) h (basisElt (reps rK139) (charOfVec rK139 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK139 e (h : Coordinate 1) T139_38 i :=
  species_entry_eq_sum rK139 ⟨38, by decide⟩ e heK h T139_38 hfix139_38 hinj139_38 hcardT139_38
    (fun i => conj_mem_of_fixedPoints (reps ⟨38, by decide⟩) (reps rK139) (T139_38 i) (hfix139_38 i) h)

/-! ## Cell (139, 45): |T| = 5 -/

def T139_45list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T139_45 : Fin 5 → Coordinate 1 := fun i => T139_45list.getD i.val (0,0,0,0,0)

theorem hfix139_45 : ∀ i, ((T139_45 i : Coordinate 1) : Coordinate 1 ⧸ reps rK139)
    ∈ fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139) :=
  repsFix_of_siftB rK139 ⟨45, by decide⟩ T139_45 (by decide)

theorem hinj139_45 : Function.Injective
    (fun i => ((T139_45 i : Coordinate 1) : Coordinate 1 ⧸ reps rK139)) :=
  repsInj_of_reduceAux rK139 T139_45 (by decide)

theorem hcardT139_45 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK139 ⟨45, by decide⟩ R139 hpxR139 hcardq139 (by decide)).symm

/-- **Cell (139, 45).** -/
theorem cell139_45 (e : List (ZMod 25)) (heK : charOK (basisAt rK139) e = true)
    (h : ↥(reps (⟨45, by decide⟩ : Fin 148))) :
    species (reps (⟨45, by decide⟩ : Fin 148)) h (basisElt (reps rK139) (charOfVec rK139 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK139 e (h : Coordinate 1) T139_45 i :=
  species_entry_eq_sum rK139 ⟨45, by decide⟩ e heK h T139_45 hfix139_45 hinj139_45 hcardT139_45
    (fun i => conj_mem_of_fixedPoints (reps ⟨45, by decide⟩) (reps rK139) (T139_45 i) (hfix139_45 i) h)

/-! ## Cell (139, 51): |T| = 5 -/

def T139_51list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T139_51 : Fin 5 → Coordinate 1 := fun i => T139_51list.getD i.val (0,0,0,0,0)

theorem hfix139_51 : ∀ i, ((T139_51 i : Coordinate 1) : Coordinate 1 ⧸ reps rK139)
    ∈ fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139) :=
  repsFix_of_siftB rK139 ⟨51, by decide⟩ T139_51 (by decide)

theorem hinj139_51 : Function.Injective
    (fun i => ((T139_51 i : Coordinate 1) : Coordinate 1 ⧸ reps rK139)) :=
  repsInj_of_reduceAux rK139 T139_51 (by decide)

theorem hcardT139_51 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK139 ⟨51, by decide⟩ R139 hpxR139 hcardq139 (by decide)).symm

/-- **Cell (139, 51).** -/
theorem cell139_51 (e : List (ZMod 25)) (heK : charOK (basisAt rK139) e = true)
    (h : ↥(reps (⟨51, by decide⟩ : Fin 148))) :
    species (reps (⟨51, by decide⟩ : Fin 148)) h (basisElt (reps rK139) (charOfVec rK139 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK139 e (h : Coordinate 1) T139_51 i :=
  species_entry_eq_sum rK139 ⟨51, by decide⟩ e heK h T139_51 hfix139_51 hinj139_51 hcardT139_51
    (fun i => conj_mem_of_fixedPoints (reps ⟨51, by decide⟩) (reps rK139) (T139_51 i) (hfix139_51 i) h)

/-! ## Cell (139, 53): |T| = 5 -/

def T139_53list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T139_53 : Fin 5 → Coordinate 1 := fun i => T139_53list.getD i.val (0,0,0,0,0)

theorem hfix139_53 : ∀ i, ((T139_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK139)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139) :=
  repsFix_of_siftB rK139 ⟨53, by decide⟩ T139_53 (by decide)

theorem hinj139_53 : Function.Injective
    (fun i => ((T139_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK139)) :=
  repsInj_of_reduceAux rK139 T139_53 (by decide)

theorem hcardT139_53 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK139 ⟨53, by decide⟩ R139 hpxR139 hcardq139 (by decide)).symm

/-- **Cell (139, 53).** -/
theorem cell139_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK139) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK139) (charOfVec rK139 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK139 e (h : Coordinate 1) T139_53 i :=
  species_entry_eq_sum rK139 ⟨53, by decide⟩ e heK h T139_53 hfix139_53 hinj139_53 hcardT139_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK139) (T139_53 i) (hfix139_53 i) h)

/-! ## Cell (139, 84): |T| = 5 -/

def T139_84list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T139_84 : Fin 5 → Coordinate 1 := fun i => T139_84list.getD i.val (0,0,0,0,0)

theorem hfix139_84 : ∀ i, ((T139_84 i : Coordinate 1) : Coordinate 1 ⧸ reps rK139)
    ∈ fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139) :=
  repsFix_of_siftB rK139 ⟨84, by decide⟩ T139_84 (by decide)

theorem hinj139_84 : Function.Injective
    (fun i => ((T139_84 i : Coordinate 1) : Coordinate 1 ⧸ reps rK139)) :=
  repsInj_of_reduceAux rK139 T139_84 (by decide)

theorem hcardT139_84 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK139 ⟨84, by decide⟩ R139 hpxR139 hcardq139 (by decide)).symm

/-- **Cell (139, 84).** -/
theorem cell139_84 (e : List (ZMod 25)) (heK : charOK (basisAt rK139) e = true)
    (h : ↥(reps (⟨84, by decide⟩ : Fin 148))) :
    species (reps (⟨84, by decide⟩ : Fin 148)) h (basisElt (reps rK139) (charOfVec rK139 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK139 e (h : Coordinate 1) T139_84 i :=
  species_entry_eq_sum rK139 ⟨84, by decide⟩ e heK h T139_84 hfix139_84 hinj139_84 hcardT139_84
    (fun i => conj_mem_of_fixedPoints (reps ⟨84, by decide⟩) (reps rK139) (T139_84 i) (hfix139_84 i) h)

/-! ## Cell (139, 94): |T| = 5 -/

def T139_94list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T139_94 : Fin 5 → Coordinate 1 := fun i => T139_94list.getD i.val (0,0,0,0,0)

theorem hfix139_94 : ∀ i, ((T139_94 i : Coordinate 1) : Coordinate 1 ⧸ reps rK139)
    ∈ fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139) :=
  repsFix_of_siftB rK139 ⟨94, by decide⟩ T139_94 (by decide)

theorem hinj139_94 : Function.Injective
    (fun i => ((T139_94 i : Coordinate 1) : Coordinate 1 ⧸ reps rK139)) :=
  repsInj_of_reduceAux rK139 T139_94 (by decide)

theorem hcardT139_94 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK139 ⟨94, by decide⟩ R139 hpxR139 hcardq139 (by decide)).symm

/-- **Cell (139, 94).** -/
theorem cell139_94 (e : List (ZMod 25)) (heK : charOK (basisAt rK139) e = true)
    (h : ↥(reps (⟨94, by decide⟩ : Fin 148))) :
    species (reps (⟨94, by decide⟩ : Fin 148)) h (basisElt (reps rK139) (charOfVec rK139 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK139 e (h : Coordinate 1) T139_94 i :=
  species_entry_eq_sum rK139 ⟨94, by decide⟩ e heK h T139_94 hfix139_94 hinj139_94 hcardT139_94
    (fun i => conj_mem_of_fixedPoints (reps ⟨94, by decide⟩) (reps rK139) (T139_94 i) (hfix139_94 i) h)

/-! ## Cell (139, 96): |T| = 5 -/

def T139_96list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T139_96 : Fin 5 → Coordinate 1 := fun i => T139_96list.getD i.val (0,0,0,0,0)

theorem hfix139_96 : ∀ i, ((T139_96 i : Coordinate 1) : Coordinate 1 ⧸ reps rK139)
    ∈ fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139) :=
  repsFix_of_siftB rK139 ⟨96, by decide⟩ T139_96 (by decide)

theorem hinj139_96 : Function.Injective
    (fun i => ((T139_96 i : Coordinate 1) : Coordinate 1 ⧸ reps rK139)) :=
  repsInj_of_reduceAux rK139 T139_96 (by decide)

theorem hcardT139_96 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK139 ⟨96, by decide⟩ R139 hpxR139 hcardq139 (by decide)).symm

/-- **Cell (139, 96).** -/
theorem cell139_96 (e : List (ZMod 25)) (heK : charOK (basisAt rK139) e = true)
    (h : ↥(reps (⟨96, by decide⟩ : Fin 148))) :
    species (reps (⟨96, by decide⟩ : Fin 148)) h (basisElt (reps rK139) (charOfVec rK139 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK139 e (h : Coordinate 1) T139_96 i :=
  species_entry_eq_sum rK139 ⟨96, by decide⟩ e heK h T139_96 hfix139_96 hinj139_96 hcardT139_96
    (fun i => conj_mem_of_fixedPoints (reps ⟨96, by decide⟩) (reps rK139) (T139_96 i) (hfix139_96 i) h)

/-! ## Cell (139, 100): |T| = 5 -/

def T139_100list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T139_100 : Fin 5 → Coordinate 1 := fun i => T139_100list.getD i.val (0,0,0,0,0)

theorem hfix139_100 : ∀ i, ((T139_100 i : Coordinate 1) : Coordinate 1 ⧸ reps rK139)
    ∈ fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139) :=
  repsFix_of_siftB rK139 ⟨100, by decide⟩ T139_100 (by decide)

theorem hinj139_100 : Function.Injective
    (fun i => ((T139_100 i : Coordinate 1) : Coordinate 1 ⧸ reps rK139)) :=
  repsInj_of_reduceAux rK139 T139_100 (by decide)

theorem hcardT139_100 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK139 ⟨100, by decide⟩ R139 hpxR139 hcardq139 (by decide)).symm

/-- **Cell (139, 100).** -/
theorem cell139_100 (e : List (ZMod 25)) (heK : charOK (basisAt rK139) e = true)
    (h : ↥(reps (⟨100, by decide⟩ : Fin 148))) :
    species (reps (⟨100, by decide⟩ : Fin 148)) h (basisElt (reps rK139) (charOfVec rK139 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK139 e (h : Coordinate 1) T139_100 i :=
  species_entry_eq_sum rK139 ⟨100, by decide⟩ e heK h T139_100 hfix139_100 hinj139_100 hcardT139_100
    (fun i => conj_mem_of_fixedPoints (reps ⟨100, by decide⟩) (reps rK139) (T139_100 i) (hfix139_100 i) h)

/-! ## Cell (139, 107): |T| = 5 -/

def T139_107list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T139_107 : Fin 5 → Coordinate 1 := fun i => T139_107list.getD i.val (0,0,0,0,0)

theorem hfix139_107 : ∀ i, ((T139_107 i : Coordinate 1) : Coordinate 1 ⧸ reps rK139)
    ∈ fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139) :=
  repsFix_of_siftB rK139 ⟨107, by decide⟩ T139_107 (by decide)

theorem hinj139_107 : Function.Injective
    (fun i => ((T139_107 i : Coordinate 1) : Coordinate 1 ⧸ reps rK139)) :=
  repsInj_of_reduceAux rK139 T139_107 (by decide)

theorem hcardT139_107 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK139 ⟨107, by decide⟩ R139 hpxR139 hcardq139 (by decide)).symm

/-- **Cell (139, 107).** -/
theorem cell139_107 (e : List (ZMod 25)) (heK : charOK (basisAt rK139) e = true)
    (h : ↥(reps (⟨107, by decide⟩ : Fin 148))) :
    species (reps (⟨107, by decide⟩ : Fin 148)) h (basisElt (reps rK139) (charOfVec rK139 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK139 e (h : Coordinate 1) T139_107 i :=
  species_entry_eq_sum rK139 ⟨107, by decide⟩ e heK h T139_107 hfix139_107 hinj139_107 hcardT139_107
    (fun i => conj_mem_of_fixedPoints (reps ⟨107, by decide⟩) (reps rK139) (T139_107 i) (hfix139_107 i) h)

/-! ## Cell (139, 113): |T| = 5 -/

def T139_113list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T139_113 : Fin 5 → Coordinate 1 := fun i => T139_113list.getD i.val (0,0,0,0,0)

theorem hfix139_113 : ∀ i, ((T139_113 i : Coordinate 1) : Coordinate 1 ⧸ reps rK139)
    ∈ fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139) :=
  repsFix_of_siftB rK139 ⟨113, by decide⟩ T139_113 (by decide)

theorem hinj139_113 : Function.Injective
    (fun i => ((T139_113 i : Coordinate 1) : Coordinate 1 ⧸ reps rK139)) :=
  repsInj_of_reduceAux rK139 T139_113 (by decide)

theorem hcardT139_113 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK139 ⟨113, by decide⟩ R139 hpxR139 hcardq139 (by decide)).symm

/-- **Cell (139, 113).** -/
theorem cell139_113 (e : List (ZMod 25)) (heK : charOK (basisAt rK139) e = true)
    (h : ↥(reps (⟨113, by decide⟩ : Fin 148))) :
    species (reps (⟨113, by decide⟩ : Fin 148)) h (basisElt (reps rK139) (charOfVec rK139 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK139 e (h : Coordinate 1) T139_113 i :=
  species_entry_eq_sum rK139 ⟨113, by decide⟩ e heK h T139_113 hfix139_113 hinj139_113 hcardT139_113
    (fun i => conj_mem_of_fixedPoints (reps ⟨113, by decide⟩) (reps rK139) (T139_113 i) (hfix139_113 i) h)

/-! ## Cell (139, 139): |T| = 5 -/

def T139_139list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T139_139 : Fin 5 → Coordinate 1 := fun i => T139_139list.getD i.val (0,0,0,0,0)

theorem hfix139_139 : ∀ i, ((T139_139 i : Coordinate 1) : Coordinate 1 ⧸ reps rK139)
    ∈ fixedPoints (reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139) :=
  repsFix_of_siftB rK139 ⟨139, by decide⟩ T139_139 (by decide)

theorem hinj139_139 : Function.Injective
    (fun i => ((T139_139 i : Coordinate 1) : Coordinate 1 ⧸ reps rK139)) :=
  repsInj_of_reduceAux rK139 T139_139 (by decide)

theorem hcardT139_139 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK139 ⟨139, by decide⟩ R139 hpxR139 hcardq139 (by decide)).symm

/-- **Cell (139, 139).** -/
theorem cell139_139 (e : List (ZMod 25)) (heK : charOK (basisAt rK139) e = true)
    (h : ↥(reps (⟨139, by decide⟩ : Fin 148))) :
    species (reps (⟨139, by decide⟩ : Fin 148)) h (basisElt (reps rK139) (charOfVec rK139 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK139 e (h : Coordinate 1) T139_139 i :=
  species_entry_eq_sum rK139 ⟨139, by decide⟩ e heK h T139_139 hfix139_139 hinj139_139 hcardT139_139
    (fun i => conj_mem_of_fixedPoints (reps ⟨139, by decide⟩) (reps rK139) (T139_139 i) (hfix139_139 i) h)

namespace Q2

def R139_2 : Fin 5 → Coordinate 2 := fun i => R139list.getD i.val (0,0,0,0,0)
theorem hpxR139_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK139) (R139_2 i)) := by decide
theorem hcardq139_2 : Nat.card (Coordinate 2 ⧸ reps rK139) = 5 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (139, 0) twin -/

def T139_0_2 : Fin 5 → Coordinate 2 := fun i => T139_0list.getD i.val (0,0,0,0,0)

theorem hfix139_0_2 : ∀ i, ((T139_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK139)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK139) :=
  repsFix_of_siftB2 rK139 ⟨0, by decide⟩ T139_0_2 (by decide)

theorem hinj139_0_2 : Function.Injective
    (fun i => ((T139_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK139)) :=
  repsInj_of_reduceAux2 rK139 T139_0_2 (by decide)

theorem hcardT139_0_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK139)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK139 ⟨0, by decide⟩ R139_2 hpxR139_2 hcardq139_2 (by decide)).symm

/-- **Cell (139, 0) twin (q=2).** -/
theorem cell139_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK139) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK139) (charOfVec2 rK139 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK139 e (h : Coordinate 2) T139_0_2 i :=
  species_entry_eq_sum rK139 ⟨0, by decide⟩ e heK h T139_0_2 hfix139_0_2 hinj139_0_2 hcardT139_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK139) (T139_0_2 i) (hfix139_0_2 i) h)

/-! ### Cell (139, 5) twin -/

def T139_5_2 : Fin 5 → Coordinate 2 := fun i => T139_5list.getD i.val (0,0,0,0,0)

theorem hfix139_5_2 : ∀ i, ((T139_5_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK139)
    ∈ fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK139) :=
  repsFix_of_siftB2 rK139 ⟨5, by decide⟩ T139_5_2 (by decide)

theorem hinj139_5_2 : Function.Injective
    (fun i => ((T139_5_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK139)) :=
  repsInj_of_reduceAux2 rK139 T139_5_2 (by decide)

theorem hcardT139_5_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK139)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK139 ⟨5, by decide⟩ R139_2 hpxR139_2 hcardq139_2 (by decide)).symm

/-- **Cell (139, 5) twin (q=2).** -/
theorem cell139_5_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK139) e = true)
    (h : ↥(reps (⟨5, by decide⟩ : Fin 148))) :
    species (reps (⟨5, by decide⟩ : Fin 148)) h (basisElt (reps rK139) (charOfVec2 rK139 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK139 e (h : Coordinate 2) T139_5_2 i :=
  species_entry_eq_sum rK139 ⟨5, by decide⟩ e heK h T139_5_2 hfix139_5_2 hinj139_5_2 hcardT139_5_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨5, by decide⟩) (reps rK139) (T139_5_2 i) (hfix139_5_2 i) h)

/-! ### Cell (139, 10) twin -/

def T139_10_2 : Fin 5 → Coordinate 2 := fun i => T139_10list.getD i.val (0,0,0,0,0)

theorem hfix139_10_2 : ∀ i, ((T139_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK139)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK139) :=
  repsFix_of_siftB2 rK139 ⟨10, by decide⟩ T139_10_2 (by decide)

theorem hinj139_10_2 : Function.Injective
    (fun i => ((T139_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK139)) :=
  repsInj_of_reduceAux2 rK139 T139_10_2 (by decide)

theorem hcardT139_10_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK139)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK139 ⟨10, by decide⟩ R139_2 hpxR139_2 hcardq139_2 (by decide)).symm

/-- **Cell (139, 10) twin (q=2).** -/
theorem cell139_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK139) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK139) (charOfVec2 rK139 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK139 e (h : Coordinate 2) T139_10_2 i :=
  species_entry_eq_sum rK139 ⟨10, by decide⟩ e heK h T139_10_2 hfix139_10_2 hinj139_10_2 hcardT139_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK139) (T139_10_2 i) (hfix139_10_2 i) h)

/-! ### Cell (139, 12) twin -/

def T139_12_2 : Fin 5 → Coordinate 2 := fun i => T139_12list.getD i.val (0,0,0,0,0)

theorem hfix139_12_2 : ∀ i, ((T139_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK139)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK139) :=
  repsFix_of_siftB2 rK139 ⟨12, by decide⟩ T139_12_2 (by decide)

theorem hinj139_12_2 : Function.Injective
    (fun i => ((T139_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK139)) :=
  repsInj_of_reduceAux2 rK139 T139_12_2 (by decide)

theorem hcardT139_12_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK139)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK139 ⟨12, by decide⟩ R139_2 hpxR139_2 hcardq139_2 (by decide)).symm

/-- **Cell (139, 12) twin (q=2).** -/
theorem cell139_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK139) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK139) (charOfVec2 rK139 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK139 e (h : Coordinate 2) T139_12_2 i :=
  species_entry_eq_sum rK139 ⟨12, by decide⟩ e heK h T139_12_2 hfix139_12_2 hinj139_12_2 hcardT139_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK139) (T139_12_2 i) (hfix139_12_2 i) h)

/-! ### Cell (139, 23) twin -/

def T139_23_2 : Fin 5 → Coordinate 2 := fun i => T139_23list.getD i.val (0,0,0,0,0)

theorem hfix139_23_2 : ∀ i, ((T139_23_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK139)
    ∈ fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK139) :=
  repsFix_of_siftB2 rK139 ⟨23, by decide⟩ T139_23_2 (by decide)

theorem hinj139_23_2 : Function.Injective
    (fun i => ((T139_23_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK139)) :=
  repsInj_of_reduceAux2 rK139 T139_23_2 (by decide)

theorem hcardT139_23_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK139)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK139 ⟨23, by decide⟩ R139_2 hpxR139_2 hcardq139_2 (by decide)).symm

/-- **Cell (139, 23) twin (q=2).** -/
theorem cell139_23_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK139) e = true)
    (h : ↥(reps (⟨23, by decide⟩ : Fin 148))) :
    species (reps (⟨23, by decide⟩ : Fin 148)) h (basisElt (reps rK139) (charOfVec2 rK139 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK139 e (h : Coordinate 2) T139_23_2 i :=
  species_entry_eq_sum rK139 ⟨23, by decide⟩ e heK h T139_23_2 hfix139_23_2 hinj139_23_2 hcardT139_23_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨23, by decide⟩) (reps rK139) (T139_23_2 i) (hfix139_23_2 i) h)

/-! ### Cell (139, 32) twin -/

def T139_32_2 : Fin 5 → Coordinate 2 := fun i => T139_32list.getD i.val (0,0,0,0,0)

theorem hfix139_32_2 : ∀ i, ((T139_32_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK139)
    ∈ fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK139) :=
  repsFix_of_siftB2 rK139 ⟨32, by decide⟩ T139_32_2 (by decide)

theorem hinj139_32_2 : Function.Injective
    (fun i => ((T139_32_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK139)) :=
  repsInj_of_reduceAux2 rK139 T139_32_2 (by decide)

theorem hcardT139_32_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK139)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK139 ⟨32, by decide⟩ R139_2 hpxR139_2 hcardq139_2 (by decide)).symm

/-- **Cell (139, 32) twin (q=2).** -/
theorem cell139_32_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK139) e = true)
    (h : ↥(reps (⟨32, by decide⟩ : Fin 148))) :
    species (reps (⟨32, by decide⟩ : Fin 148)) h (basisElt (reps rK139) (charOfVec2 rK139 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK139 e (h : Coordinate 2) T139_32_2 i :=
  species_entry_eq_sum rK139 ⟨32, by decide⟩ e heK h T139_32_2 hfix139_32_2 hinj139_32_2 hcardT139_32_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨32, by decide⟩) (reps rK139) (T139_32_2 i) (hfix139_32_2 i) h)

/-! ### Cell (139, 34) twin -/

def T139_34_2 : Fin 5 → Coordinate 2 := fun i => T139_34list.getD i.val (0,0,0,0,0)

theorem hfix139_34_2 : ∀ i, ((T139_34_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK139)
    ∈ fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK139) :=
  repsFix_of_siftB2 rK139 ⟨34, by decide⟩ T139_34_2 (by decide)

theorem hinj139_34_2 : Function.Injective
    (fun i => ((T139_34_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK139)) :=
  repsInj_of_reduceAux2 rK139 T139_34_2 (by decide)

theorem hcardT139_34_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK139)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK139 ⟨34, by decide⟩ R139_2 hpxR139_2 hcardq139_2 (by decide)).symm

/-- **Cell (139, 34) twin (q=2).** -/
theorem cell139_34_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK139) e = true)
    (h : ↥(reps (⟨34, by decide⟩ : Fin 148))) :
    species (reps (⟨34, by decide⟩ : Fin 148)) h (basisElt (reps rK139) (charOfVec2 rK139 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK139 e (h : Coordinate 2) T139_34_2 i :=
  species_entry_eq_sum rK139 ⟨34, by decide⟩ e heK h T139_34_2 hfix139_34_2 hinj139_34_2 hcardT139_34_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨34, by decide⟩) (reps rK139) (T139_34_2 i) (hfix139_34_2 i) h)

/-! ### Cell (139, 38) twin -/

def T139_38_2 : Fin 5 → Coordinate 2 := fun i => T139_38list.getD i.val (0,0,0,0,0)

theorem hfix139_38_2 : ∀ i, ((T139_38_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK139)
    ∈ fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK139) :=
  repsFix_of_siftB2 rK139 ⟨38, by decide⟩ T139_38_2 (by decide)

theorem hinj139_38_2 : Function.Injective
    (fun i => ((T139_38_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK139)) :=
  repsInj_of_reduceAux2 rK139 T139_38_2 (by decide)

theorem hcardT139_38_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK139)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK139 ⟨38, by decide⟩ R139_2 hpxR139_2 hcardq139_2 (by decide)).symm

/-- **Cell (139, 38) twin (q=2).** -/
theorem cell139_38_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK139) e = true)
    (h : ↥(reps (⟨38, by decide⟩ : Fin 148))) :
    species (reps (⟨38, by decide⟩ : Fin 148)) h (basisElt (reps rK139) (charOfVec2 rK139 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK139 e (h : Coordinate 2) T139_38_2 i :=
  species_entry_eq_sum rK139 ⟨38, by decide⟩ e heK h T139_38_2 hfix139_38_2 hinj139_38_2 hcardT139_38_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨38, by decide⟩) (reps rK139) (T139_38_2 i) (hfix139_38_2 i) h)

/-! ### Cell (139, 45) twin -/

def T139_45_2 : Fin 5 → Coordinate 2 := fun i => T139_45list.getD i.val (0,0,0,0,0)

theorem hfix139_45_2 : ∀ i, ((T139_45_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK139)
    ∈ fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK139) :=
  repsFix_of_siftB2 rK139 ⟨45, by decide⟩ T139_45_2 (by decide)

theorem hinj139_45_2 : Function.Injective
    (fun i => ((T139_45_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK139)) :=
  repsInj_of_reduceAux2 rK139 T139_45_2 (by decide)

theorem hcardT139_45_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK139)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK139 ⟨45, by decide⟩ R139_2 hpxR139_2 hcardq139_2 (by decide)).symm

/-- **Cell (139, 45) twin (q=2).** -/
theorem cell139_45_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK139) e = true)
    (h : ↥(reps (⟨45, by decide⟩ : Fin 148))) :
    species (reps (⟨45, by decide⟩ : Fin 148)) h (basisElt (reps rK139) (charOfVec2 rK139 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK139 e (h : Coordinate 2) T139_45_2 i :=
  species_entry_eq_sum rK139 ⟨45, by decide⟩ e heK h T139_45_2 hfix139_45_2 hinj139_45_2 hcardT139_45_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨45, by decide⟩) (reps rK139) (T139_45_2 i) (hfix139_45_2 i) h)

/-! ### Cell (139, 51) twin -/

def T139_51_2 : Fin 5 → Coordinate 2 := fun i => T139_51list.getD i.val (0,0,0,0,0)

theorem hfix139_51_2 : ∀ i, ((T139_51_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK139)
    ∈ fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK139) :=
  repsFix_of_siftB2 rK139 ⟨51, by decide⟩ T139_51_2 (by decide)

theorem hinj139_51_2 : Function.Injective
    (fun i => ((T139_51_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK139)) :=
  repsInj_of_reduceAux2 rK139 T139_51_2 (by decide)

theorem hcardT139_51_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK139)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK139 ⟨51, by decide⟩ R139_2 hpxR139_2 hcardq139_2 (by decide)).symm

/-- **Cell (139, 51) twin (q=2).** -/
theorem cell139_51_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK139) e = true)
    (h : ↥(reps (⟨51, by decide⟩ : Fin 148))) :
    species (reps (⟨51, by decide⟩ : Fin 148)) h (basisElt (reps rK139) (charOfVec2 rK139 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK139 e (h : Coordinate 2) T139_51_2 i :=
  species_entry_eq_sum rK139 ⟨51, by decide⟩ e heK h T139_51_2 hfix139_51_2 hinj139_51_2 hcardT139_51_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨51, by decide⟩) (reps rK139) (T139_51_2 i) (hfix139_51_2 i) h)

/-! ### Cell (139, 53) twin -/

def T139_53_2 : Fin 5 → Coordinate 2 := fun i => T139_53list.getD i.val (0,0,0,0,0)

theorem hfix139_53_2 : ∀ i, ((T139_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK139)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK139) :=
  repsFix_of_siftB2 rK139 ⟨53, by decide⟩ T139_53_2 (by decide)

theorem hinj139_53_2 : Function.Injective
    (fun i => ((T139_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK139)) :=
  repsInj_of_reduceAux2 rK139 T139_53_2 (by decide)

theorem hcardT139_53_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK139)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK139 ⟨53, by decide⟩ R139_2 hpxR139_2 hcardq139_2 (by decide)).symm

/-- **Cell (139, 53) twin (q=2).** -/
theorem cell139_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK139) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK139) (charOfVec2 rK139 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK139 e (h : Coordinate 2) T139_53_2 i :=
  species_entry_eq_sum rK139 ⟨53, by decide⟩ e heK h T139_53_2 hfix139_53_2 hinj139_53_2 hcardT139_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK139) (T139_53_2 i) (hfix139_53_2 i) h)

/-! ### Cell (139, 84) twin -/

def T139_84_2 : Fin 5 → Coordinate 2 := fun i => T139_84list.getD i.val (0,0,0,0,0)

theorem hfix139_84_2 : ∀ i, ((T139_84_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK139)
    ∈ fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK139) :=
  repsFix_of_siftB2 rK139 ⟨84, by decide⟩ T139_84_2 (by decide)

theorem hinj139_84_2 : Function.Injective
    (fun i => ((T139_84_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK139)) :=
  repsInj_of_reduceAux2 rK139 T139_84_2 (by decide)

theorem hcardT139_84_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK139)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK139 ⟨84, by decide⟩ R139_2 hpxR139_2 hcardq139_2 (by decide)).symm

/-- **Cell (139, 84) twin (q=2).** -/
theorem cell139_84_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK139) e = true)
    (h : ↥(reps (⟨84, by decide⟩ : Fin 148))) :
    species (reps (⟨84, by decide⟩ : Fin 148)) h (basisElt (reps rK139) (charOfVec2 rK139 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK139 e (h : Coordinate 2) T139_84_2 i :=
  species_entry_eq_sum rK139 ⟨84, by decide⟩ e heK h T139_84_2 hfix139_84_2 hinj139_84_2 hcardT139_84_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨84, by decide⟩) (reps rK139) (T139_84_2 i) (hfix139_84_2 i) h)

/-! ### Cell (139, 94) twin -/

def T139_94_2 : Fin 5 → Coordinate 2 := fun i => T139_94list.getD i.val (0,0,0,0,0)

theorem hfix139_94_2 : ∀ i, ((T139_94_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK139)
    ∈ fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK139) :=
  repsFix_of_siftB2 rK139 ⟨94, by decide⟩ T139_94_2 (by decide)

theorem hinj139_94_2 : Function.Injective
    (fun i => ((T139_94_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK139)) :=
  repsInj_of_reduceAux2 rK139 T139_94_2 (by decide)

theorem hcardT139_94_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK139)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK139 ⟨94, by decide⟩ R139_2 hpxR139_2 hcardq139_2 (by decide)).symm

/-- **Cell (139, 94) twin (q=2).** -/
theorem cell139_94_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK139) e = true)
    (h : ↥(reps (⟨94, by decide⟩ : Fin 148))) :
    species (reps (⟨94, by decide⟩ : Fin 148)) h (basisElt (reps rK139) (charOfVec2 rK139 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK139 e (h : Coordinate 2) T139_94_2 i :=
  species_entry_eq_sum rK139 ⟨94, by decide⟩ e heK h T139_94_2 hfix139_94_2 hinj139_94_2 hcardT139_94_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨94, by decide⟩) (reps rK139) (T139_94_2 i) (hfix139_94_2 i) h)

/-! ### Cell (139, 96) twin -/

def T139_96_2 : Fin 5 → Coordinate 2 := fun i => T139_96list.getD i.val (0,0,0,0,0)

theorem hfix139_96_2 : ∀ i, ((T139_96_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK139)
    ∈ fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK139) :=
  repsFix_of_siftB2 rK139 ⟨96, by decide⟩ T139_96_2 (by decide)

theorem hinj139_96_2 : Function.Injective
    (fun i => ((T139_96_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK139)) :=
  repsInj_of_reduceAux2 rK139 T139_96_2 (by decide)

theorem hcardT139_96_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK139)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK139 ⟨96, by decide⟩ R139_2 hpxR139_2 hcardq139_2 (by decide)).symm

/-- **Cell (139, 96) twin (q=2).** -/
theorem cell139_96_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK139) e = true)
    (h : ↥(reps (⟨96, by decide⟩ : Fin 148))) :
    species (reps (⟨96, by decide⟩ : Fin 148)) h (basisElt (reps rK139) (charOfVec2 rK139 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK139 e (h : Coordinate 2) T139_96_2 i :=
  species_entry_eq_sum rK139 ⟨96, by decide⟩ e heK h T139_96_2 hfix139_96_2 hinj139_96_2 hcardT139_96_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨96, by decide⟩) (reps rK139) (T139_96_2 i) (hfix139_96_2 i) h)

/-! ### Cell (139, 100) twin -/

def T139_100_2 : Fin 5 → Coordinate 2 := fun i => T139_100list.getD i.val (0,0,0,0,0)

theorem hfix139_100_2 : ∀ i, ((T139_100_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK139)
    ∈ fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK139) :=
  repsFix_of_siftB2 rK139 ⟨100, by decide⟩ T139_100_2 (by decide)

theorem hinj139_100_2 : Function.Injective
    (fun i => ((T139_100_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK139)) :=
  repsInj_of_reduceAux2 rK139 T139_100_2 (by decide)

theorem hcardT139_100_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK139)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK139 ⟨100, by decide⟩ R139_2 hpxR139_2 hcardq139_2 (by decide)).symm

/-- **Cell (139, 100) twin (q=2).** -/
theorem cell139_100_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK139) e = true)
    (h : ↥(reps (⟨100, by decide⟩ : Fin 148))) :
    species (reps (⟨100, by decide⟩ : Fin 148)) h (basisElt (reps rK139) (charOfVec2 rK139 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK139 e (h : Coordinate 2) T139_100_2 i :=
  species_entry_eq_sum rK139 ⟨100, by decide⟩ e heK h T139_100_2 hfix139_100_2 hinj139_100_2 hcardT139_100_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨100, by decide⟩) (reps rK139) (T139_100_2 i) (hfix139_100_2 i) h)

/-! ### Cell (139, 107) twin -/

def T139_107_2 : Fin 5 → Coordinate 2 := fun i => T139_107list.getD i.val (0,0,0,0,0)

theorem hfix139_107_2 : ∀ i, ((T139_107_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK139)
    ∈ fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK139) :=
  repsFix_of_siftB2 rK139 ⟨107, by decide⟩ T139_107_2 (by decide)

theorem hinj139_107_2 : Function.Injective
    (fun i => ((T139_107_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK139)) :=
  repsInj_of_reduceAux2 rK139 T139_107_2 (by decide)

theorem hcardT139_107_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK139)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK139 ⟨107, by decide⟩ R139_2 hpxR139_2 hcardq139_2 (by decide)).symm

/-- **Cell (139, 107) twin (q=2).** -/
theorem cell139_107_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK139) e = true)
    (h : ↥(reps (⟨107, by decide⟩ : Fin 148))) :
    species (reps (⟨107, by decide⟩ : Fin 148)) h (basisElt (reps rK139) (charOfVec2 rK139 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK139 e (h : Coordinate 2) T139_107_2 i :=
  species_entry_eq_sum rK139 ⟨107, by decide⟩ e heK h T139_107_2 hfix139_107_2 hinj139_107_2 hcardT139_107_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨107, by decide⟩) (reps rK139) (T139_107_2 i) (hfix139_107_2 i) h)

/-! ### Cell (139, 113) twin -/

def T139_113_2 : Fin 5 → Coordinate 2 := fun i => T139_113list.getD i.val (0,0,0,0,0)

theorem hfix139_113_2 : ∀ i, ((T139_113_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK139)
    ∈ fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK139) :=
  repsFix_of_siftB2 rK139 ⟨113, by decide⟩ T139_113_2 (by decide)

theorem hinj139_113_2 : Function.Injective
    (fun i => ((T139_113_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK139)) :=
  repsInj_of_reduceAux2 rK139 T139_113_2 (by decide)

theorem hcardT139_113_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK139)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK139 ⟨113, by decide⟩ R139_2 hpxR139_2 hcardq139_2 (by decide)).symm

/-- **Cell (139, 113) twin (q=2).** -/
theorem cell139_113_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK139) e = true)
    (h : ↥(reps (⟨113, by decide⟩ : Fin 148))) :
    species (reps (⟨113, by decide⟩ : Fin 148)) h (basisElt (reps rK139) (charOfVec2 rK139 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK139 e (h : Coordinate 2) T139_113_2 i :=
  species_entry_eq_sum rK139 ⟨113, by decide⟩ e heK h T139_113_2 hfix139_113_2 hinj139_113_2 hcardT139_113_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨113, by decide⟩) (reps rK139) (T139_113_2 i) (hfix139_113_2 i) h)

/-! ### Cell (139, 139) twin -/

def T139_139_2 : Fin 5 → Coordinate 2 := fun i => T139_139list.getD i.val (0,0,0,0,0)

theorem hfix139_139_2 : ∀ i, ((T139_139_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK139)
    ∈ fixedPoints (reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK139) :=
  repsFix_of_siftB2 rK139 ⟨139, by decide⟩ T139_139_2 (by decide)

theorem hinj139_139_2 : Function.Injective
    (fun i => ((T139_139_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK139)) :=
  repsInj_of_reduceAux2 rK139 T139_139_2 (by decide)

theorem hcardT139_139_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK139)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK139 ⟨139, by decide⟩ R139_2 hpxR139_2 hcardq139_2 (by decide)).symm

/-- **Cell (139, 139) twin (q=2).** -/
theorem cell139_139_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK139) e = true)
    (h : ↥(reps (⟨139, by decide⟩ : Fin 148))) :
    species (reps (⟨139, by decide⟩ : Fin 148)) h (basisElt (reps rK139) (charOfVec2 rK139 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK139 e (h : Coordinate 2) T139_139_2 i :=
  species_entry_eq_sum rK139 ⟨139, by decide⟩ e heK h T139_139_2 hfix139_139_2 hinj139_139_2 hcardT139_139_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨139, by decide⟩) (reps rK139) (T139_139_2 i) (hfix139_139_2 i) h)

end Q2

end LeanDring.P5Presentation
