/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, K-strata data (5^4 stratum, rK 118-118): certified per-cell species-entry instantiations, both
twins.

Covers K-classes 118 (order-5^4 K, |R|=5).  For each nonzero `H`-column
(`(G/K)^H ≠ ∅`), the full coset transversal `R118..` and each `H`-fixed
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

/-! # K-class rK = 118  (|G/K| = 5) -/

def rK118 : Fin 148 := ⟨118, by decide⟩

def R118list : List Coordinates := [(0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0)]
def R118 : Fin 5 → Coordinate 1 := fun i => R118list.getD i.val (0,0,0,0,0)

theorem hpxR118 : Function.Injective (fun i => reduceAux 1 (basisAt rK118) (R118 i)) := by decide
theorem hcardq118 : Nat.card (Coordinate 1 ⧸ reps rK118) = 5 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (118, 0): |T| = 5 -/

def T118_0list : List Coordinates := [(0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0)]
def T118_0 : Fin 5 → Coordinate 1 := fun i => T118_0list.getD i.val (0,0,0,0,0)

theorem hfix118_0 : ∀ i, ((T118_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118) :=
  repsFix_of_siftB rK118 ⟨0, by decide⟩ T118_0 (by decide)

theorem hinj118_0 : Function.Injective
    (fun i => ((T118_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)) :=
  repsInj_of_reduceAux rK118 T118_0 (by decide)

theorem hcardT118_0 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK118 ⟨0, by decide⟩ R118 hpxR118 hcardq118 (by decide)).symm

/-- **Cell (118, 0).** -/
theorem cell118_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK118) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK118 e (h : Coordinate 1) T118_0 i :=
  species_entry_eq_sum rK118 ⟨0, by decide⟩ e heK h T118_0 hfix118_0 hinj118_0 hcardT118_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK118) (T118_0 i) (hfix118_0 i) h)

/-! ## Cell (118, 1): |T| = 5 -/

def T118_1list : List Coordinates := [(0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0)]
def T118_1 : Fin 5 → Coordinate 1 := fun i => T118_1list.getD i.val (0,0,0,0,0)

theorem hfix118_1 : ∀ i, ((T118_1 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118) :=
  repsFix_of_siftB rK118 ⟨1, by decide⟩ T118_1 (by decide)

theorem hinj118_1 : Function.Injective
    (fun i => ((T118_1 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)) :=
  repsInj_of_reduceAux rK118 T118_1 (by decide)

theorem hcardT118_1 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK118 ⟨1, by decide⟩ R118 hpxR118 hcardq118 (by decide)).symm

/-- **Cell (118, 1).** -/
theorem cell118_1 (e : List (ZMod 25)) (heK : charOK (basisAt rK118) e = true)
    (h : ↥(reps (⟨1, by decide⟩ : Fin 148))) :
    species (reps (⟨1, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK118 e (h : Coordinate 1) T118_1 i :=
  species_entry_eq_sum rK118 ⟨1, by decide⟩ e heK h T118_1 hfix118_1 hinj118_1 hcardT118_1
    (fun i => conj_mem_of_fixedPoints (reps ⟨1, by decide⟩) (reps rK118) (T118_1 i) (hfix118_1 i) h)

/-! ## Cell (118, 6): |T| = 5 -/

def T118_6list : List Coordinates := [(0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0)]
def T118_6 : Fin 5 → Coordinate 1 := fun i => T118_6list.getD i.val (0,0,0,0,0)

theorem hfix118_6 : ∀ i, ((T118_6 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118) :=
  repsFix_of_siftB rK118 ⟨6, by decide⟩ T118_6 (by decide)

theorem hinj118_6 : Function.Injective
    (fun i => ((T118_6 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)) :=
  repsInj_of_reduceAux rK118 T118_6 (by decide)

theorem hcardT118_6 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK118 ⟨6, by decide⟩ R118 hpxR118 hcardq118 (by decide)).symm

/-- **Cell (118, 6).** -/
theorem cell118_6 (e : List (ZMod 25)) (heK : charOK (basisAt rK118) e = true)
    (h : ↥(reps (⟨6, by decide⟩ : Fin 148))) :
    species (reps (⟨6, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK118 e (h : Coordinate 1) T118_6 i :=
  species_entry_eq_sum rK118 ⟨6, by decide⟩ e heK h T118_6 hfix118_6 hinj118_6 hcardT118_6
    (fun i => conj_mem_of_fixedPoints (reps ⟨6, by decide⟩) (reps rK118) (T118_6 i) (hfix118_6 i) h)

/-! ## Cell (118, 7): |T| = 5 -/

def T118_7list : List Coordinates := [(0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0)]
def T118_7 : Fin 5 → Coordinate 1 := fun i => T118_7list.getD i.val (0,0,0,0,0)

theorem hfix118_7 : ∀ i, ((T118_7 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118) :=
  repsFix_of_siftB rK118 ⟨7, by decide⟩ T118_7 (by decide)

theorem hinj118_7 : Function.Injective
    (fun i => ((T118_7 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)) :=
  repsInj_of_reduceAux rK118 T118_7 (by decide)

theorem hcardT118_7 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK118 ⟨7, by decide⟩ R118 hpxR118 hcardq118 (by decide)).symm

/-- **Cell (118, 7).** -/
theorem cell118_7 (e : List (ZMod 25)) (heK : charOK (basisAt rK118) e = true)
    (h : ↥(reps (⟨7, by decide⟩ : Fin 148))) :
    species (reps (⟨7, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK118 e (h : Coordinate 1) T118_7 i :=
  species_entry_eq_sum rK118 ⟨7, by decide⟩ e heK h T118_7 hfix118_7 hinj118_7 hcardT118_7
    (fun i => conj_mem_of_fixedPoints (reps ⟨7, by decide⟩) (reps rK118) (T118_7 i) (hfix118_7 i) h)

/-! ## Cell (118, 8): |T| = 5 -/

def T118_8list : List Coordinates := [(0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0)]
def T118_8 : Fin 5 → Coordinate 1 := fun i => T118_8list.getD i.val (0,0,0,0,0)

theorem hfix118_8 : ∀ i, ((T118_8 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118) :=
  repsFix_of_siftB rK118 ⟨8, by decide⟩ T118_8 (by decide)

theorem hinj118_8 : Function.Injective
    (fun i => ((T118_8 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)) :=
  repsInj_of_reduceAux rK118 T118_8 (by decide)

theorem hcardT118_8 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK118 ⟨8, by decide⟩ R118 hpxR118 hcardq118 (by decide)).symm

/-- **Cell (118, 8).** -/
theorem cell118_8 (e : List (ZMod 25)) (heK : charOK (basisAt rK118) e = true)
    (h : ↥(reps (⟨8, by decide⟩ : Fin 148))) :
    species (reps (⟨8, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK118 e (h : Coordinate 1) T118_8 i :=
  species_entry_eq_sum rK118 ⟨8, by decide⟩ e heK h T118_8 hfix118_8 hinj118_8 hcardT118_8
    (fun i => conj_mem_of_fixedPoints (reps ⟨8, by decide⟩) (reps rK118) (T118_8 i) (hfix118_8 i) h)

/-! ## Cell (118, 9): |T| = 5 -/

def T118_9list : List Coordinates := [(0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0)]
def T118_9 : Fin 5 → Coordinate 1 := fun i => T118_9list.getD i.val (0,0,0,0,0)

theorem hfix118_9 : ∀ i, ((T118_9 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118) :=
  repsFix_of_siftB rK118 ⟨9, by decide⟩ T118_9 (by decide)

theorem hinj118_9 : Function.Injective
    (fun i => ((T118_9 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)) :=
  repsInj_of_reduceAux rK118 T118_9 (by decide)

theorem hcardT118_9 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK118 ⟨9, by decide⟩ R118 hpxR118 hcardq118 (by decide)).symm

/-- **Cell (118, 9).** -/
theorem cell118_9 (e : List (ZMod 25)) (heK : charOK (basisAt rK118) e = true)
    (h : ↥(reps (⟨9, by decide⟩ : Fin 148))) :
    species (reps (⟨9, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK118 e (h : Coordinate 1) T118_9 i :=
  species_entry_eq_sum rK118 ⟨9, by decide⟩ e heK h T118_9 hfix118_9 hinj118_9 hcardT118_9
    (fun i => conj_mem_of_fixedPoints (reps ⟨9, by decide⟩) (reps rK118) (T118_9 i) (hfix118_9 i) h)

/-! ## Cell (118, 10): |T| = 5 -/

def T118_10list : List Coordinates := [(0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0)]
def T118_10 : Fin 5 → Coordinate 1 := fun i => T118_10list.getD i.val (0,0,0,0,0)

theorem hfix118_10 : ∀ i, ((T118_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118) :=
  repsFix_of_siftB rK118 ⟨10, by decide⟩ T118_10 (by decide)

theorem hinj118_10 : Function.Injective
    (fun i => ((T118_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)) :=
  repsInj_of_reduceAux rK118 T118_10 (by decide)

theorem hcardT118_10 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK118 ⟨10, by decide⟩ R118 hpxR118 hcardq118 (by decide)).symm

/-- **Cell (118, 10).** -/
theorem cell118_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK118) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK118 e (h : Coordinate 1) T118_10 i :=
  species_entry_eq_sum rK118 ⟨10, by decide⟩ e heK h T118_10 hfix118_10 hinj118_10 hcardT118_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK118) (T118_10 i) (hfix118_10 i) h)

/-! ## Cell (118, 12): |T| = 5 -/

def T118_12list : List Coordinates := [(0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0)]
def T118_12 : Fin 5 → Coordinate 1 := fun i => T118_12list.getD i.val (0,0,0,0,0)

theorem hfix118_12 : ∀ i, ((T118_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118) :=
  repsFix_of_siftB rK118 ⟨12, by decide⟩ T118_12 (by decide)

theorem hinj118_12 : Function.Injective
    (fun i => ((T118_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)) :=
  repsInj_of_reduceAux rK118 T118_12 (by decide)

theorem hcardT118_12 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK118 ⟨12, by decide⟩ R118 hpxR118 hcardq118 (by decide)).symm

/-- **Cell (118, 12).** -/
theorem cell118_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK118) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK118 e (h : Coordinate 1) T118_12 i :=
  species_entry_eq_sum rK118 ⟨12, by decide⟩ e heK h T118_12 hfix118_12 hinj118_12 hcardT118_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK118) (T118_12 i) (hfix118_12 i) h)

/-! ## Cell (118, 13): |T| = 5 -/

def T118_13list : List Coordinates := [(0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0)]
def T118_13 : Fin 5 → Coordinate 1 := fun i => T118_13list.getD i.val (0,0,0,0,0)

theorem hfix118_13 : ∀ i, ((T118_13 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118) :=
  repsFix_of_siftB rK118 ⟨13, by decide⟩ T118_13 (by decide)

theorem hinj118_13 : Function.Injective
    (fun i => ((T118_13 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)) :=
  repsInj_of_reduceAux rK118 T118_13 (by decide)

theorem hcardT118_13 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK118 ⟨13, by decide⟩ R118 hpxR118 hcardq118 (by decide)).symm

/-- **Cell (118, 13).** -/
theorem cell118_13 (e : List (ZMod 25)) (heK : charOK (basisAt rK118) e = true)
    (h : ↥(reps (⟨13, by decide⟩ : Fin 148))) :
    species (reps (⟨13, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK118 e (h : Coordinate 1) T118_13 i :=
  species_entry_eq_sum rK118 ⟨13, by decide⟩ e heK h T118_13 hfix118_13 hinj118_13 hcardT118_13
    (fun i => conj_mem_of_fixedPoints (reps ⟨13, by decide⟩) (reps rK118) (T118_13 i) (hfix118_13 i) h)

/-! ## Cell (118, 19): |T| = 5 -/

def T118_19list : List Coordinates := [(0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0)]
def T118_19 : Fin 5 → Coordinate 1 := fun i => T118_19list.getD i.val (0,0,0,0,0)

theorem hfix118_19 : ∀ i, ((T118_19 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118) :=
  repsFix_of_siftB rK118 ⟨19, by decide⟩ T118_19 (by decide)

theorem hinj118_19 : Function.Injective
    (fun i => ((T118_19 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)) :=
  repsInj_of_reduceAux rK118 T118_19 (by decide)

theorem hcardT118_19 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK118 ⟨19, by decide⟩ R118 hpxR118 hcardq118 (by decide)).symm

/-- **Cell (118, 19).** -/
theorem cell118_19 (e : List (ZMod 25)) (heK : charOK (basisAt rK118) e = true)
    (h : ↥(reps (⟨19, by decide⟩ : Fin 148))) :
    species (reps (⟨19, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK118 e (h : Coordinate 1) T118_19 i :=
  species_entry_eq_sum rK118 ⟨19, by decide⟩ e heK h T118_19 hfix118_19 hinj118_19 hcardT118_19
    (fun i => conj_mem_of_fixedPoints (reps ⟨19, by decide⟩) (reps rK118) (T118_19 i) (hfix118_19 i) h)

/-! ## Cell (118, 24): |T| = 5 -/

def T118_24list : List Coordinates := [(0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0)]
def T118_24 : Fin 5 → Coordinate 1 := fun i => T118_24list.getD i.val (0,0,0,0,0)

theorem hfix118_24 : ∀ i, ((T118_24 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118) :=
  repsFix_of_siftB rK118 ⟨24, by decide⟩ T118_24 (by decide)

theorem hinj118_24 : Function.Injective
    (fun i => ((T118_24 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)) :=
  repsInj_of_reduceAux rK118 T118_24 (by decide)

theorem hcardT118_24 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK118 ⟨24, by decide⟩ R118 hpxR118 hcardq118 (by decide)).symm

/-- **Cell (118, 24).** -/
theorem cell118_24 (e : List (ZMod 25)) (heK : charOK (basisAt rK118) e = true)
    (h : ↥(reps (⟨24, by decide⟩ : Fin 148))) :
    species (reps (⟨24, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK118 e (h : Coordinate 1) T118_24 i :=
  species_entry_eq_sum rK118 ⟨24, by decide⟩ e heK h T118_24 hfix118_24 hinj118_24 hcardT118_24
    (fun i => conj_mem_of_fixedPoints (reps ⟨24, by decide⟩) (reps rK118) (T118_24 i) (hfix118_24 i) h)

/-! ## Cell (118, 25): |T| = 5 -/

def T118_25list : List Coordinates := [(0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0)]
def T118_25 : Fin 5 → Coordinate 1 := fun i => T118_25list.getD i.val (0,0,0,0,0)

theorem hfix118_25 : ∀ i, ((T118_25 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118) :=
  repsFix_of_siftB rK118 ⟨25, by decide⟩ T118_25 (by decide)

theorem hinj118_25 : Function.Injective
    (fun i => ((T118_25 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)) :=
  repsInj_of_reduceAux rK118 T118_25 (by decide)

theorem hcardT118_25 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK118 ⟨25, by decide⟩ R118 hpxR118 hcardq118 (by decide)).symm

/-- **Cell (118, 25).** -/
theorem cell118_25 (e : List (ZMod 25)) (heK : charOK (basisAt rK118) e = true)
    (h : ↥(reps (⟨25, by decide⟩ : Fin 148))) :
    species (reps (⟨25, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK118 e (h : Coordinate 1) T118_25 i :=
  species_entry_eq_sum rK118 ⟨25, by decide⟩ e heK h T118_25 hfix118_25 hinj118_25 hcardT118_25
    (fun i => conj_mem_of_fixedPoints (reps ⟨25, by decide⟩) (reps rK118) (T118_25 i) (hfix118_25 i) h)

/-! ## Cell (118, 26): |T| = 5 -/

def T118_26list : List Coordinates := [(0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0)]
def T118_26 : Fin 5 → Coordinate 1 := fun i => T118_26list.getD i.val (0,0,0,0,0)

theorem hfix118_26 : ∀ i, ((T118_26 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118) :=
  repsFix_of_siftB rK118 ⟨26, by decide⟩ T118_26 (by decide)

theorem hinj118_26 : Function.Injective
    (fun i => ((T118_26 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)) :=
  repsInj_of_reduceAux rK118 T118_26 (by decide)

theorem hcardT118_26 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK118 ⟨26, by decide⟩ R118 hpxR118 hcardq118 (by decide)).symm

/-- **Cell (118, 26).** -/
theorem cell118_26 (e : List (ZMod 25)) (heK : charOK (basisAt rK118) e = true)
    (h : ↥(reps (⟨26, by decide⟩ : Fin 148))) :
    species (reps (⟨26, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK118 e (h : Coordinate 1) T118_26 i :=
  species_entry_eq_sum rK118 ⟨26, by decide⟩ e heK h T118_26 hfix118_26 hinj118_26 hcardT118_26
    (fun i => conj_mem_of_fixedPoints (reps ⟨26, by decide⟩) (reps rK118) (T118_26 i) (hfix118_26 i) h)

/-! ## Cell (118, 27): |T| = 5 -/

def T118_27list : List Coordinates := [(0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0)]
def T118_27 : Fin 5 → Coordinate 1 := fun i => T118_27list.getD i.val (0,0,0,0,0)

theorem hfix118_27 : ∀ i, ((T118_27 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118) :=
  repsFix_of_siftB rK118 ⟨27, by decide⟩ T118_27 (by decide)

theorem hinj118_27 : Function.Injective
    (fun i => ((T118_27 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)) :=
  repsInj_of_reduceAux rK118 T118_27 (by decide)

theorem hcardT118_27 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK118 ⟨27, by decide⟩ R118 hpxR118 hcardq118 (by decide)).symm

/-- **Cell (118, 27).** -/
theorem cell118_27 (e : List (ZMod 25)) (heK : charOK (basisAt rK118) e = true)
    (h : ↥(reps (⟨27, by decide⟩ : Fin 148))) :
    species (reps (⟨27, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK118 e (h : Coordinate 1) T118_27 i :=
  species_entry_eq_sum rK118 ⟨27, by decide⟩ e heK h T118_27 hfix118_27 hinj118_27 hcardT118_27
    (fun i => conj_mem_of_fixedPoints (reps ⟨27, by decide⟩) (reps rK118) (T118_27 i) (hfix118_27 i) h)

/-! ## Cell (118, 30): |T| = 5 -/

def T118_30list : List Coordinates := [(0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0)]
def T118_30 : Fin 5 → Coordinate 1 := fun i => T118_30list.getD i.val (0,0,0,0,0)

theorem hfix118_30 : ∀ i, ((T118_30 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118) :=
  repsFix_of_siftB rK118 ⟨30, by decide⟩ T118_30 (by decide)

theorem hinj118_30 : Function.Injective
    (fun i => ((T118_30 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)) :=
  repsInj_of_reduceAux rK118 T118_30 (by decide)

theorem hcardT118_30 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK118 ⟨30, by decide⟩ R118 hpxR118 hcardq118 (by decide)).symm

/-- **Cell (118, 30).** -/
theorem cell118_30 (e : List (ZMod 25)) (heK : charOK (basisAt rK118) e = true)
    (h : ↥(reps (⟨30, by decide⟩ : Fin 148))) :
    species (reps (⟨30, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK118 e (h : Coordinate 1) T118_30 i :=
  species_entry_eq_sum rK118 ⟨30, by decide⟩ e heK h T118_30 hfix118_30 hinj118_30 hcardT118_30
    (fun i => conj_mem_of_fixedPoints (reps ⟨30, by decide⟩) (reps rK118) (T118_30 i) (hfix118_30 i) h)

/-! ## Cell (118, 35): |T| = 5 -/

def T118_35list : List Coordinates := [(0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0)]
def T118_35 : Fin 5 → Coordinate 1 := fun i => T118_35list.getD i.val (0,0,0,0,0)

theorem hfix118_35 : ∀ i, ((T118_35 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118) :=
  repsFix_of_siftB rK118 ⟨35, by decide⟩ T118_35 (by decide)

theorem hinj118_35 : Function.Injective
    (fun i => ((T118_35 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)) :=
  repsInj_of_reduceAux rK118 T118_35 (by decide)

theorem hcardT118_35 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK118 ⟨35, by decide⟩ R118 hpxR118 hcardq118 (by decide)).symm

/-- **Cell (118, 35).** -/
theorem cell118_35 (e : List (ZMod 25)) (heK : charOK (basisAt rK118) e = true)
    (h : ↥(reps (⟨35, by decide⟩ : Fin 148))) :
    species (reps (⟨35, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK118 e (h : Coordinate 1) T118_35 i :=
  species_entry_eq_sum rK118 ⟨35, by decide⟩ e heK h T118_35 hfix118_35 hinj118_35 hcardT118_35
    (fun i => conj_mem_of_fixedPoints (reps ⟨35, by decide⟩) (reps rK118) (T118_35 i) (hfix118_35 i) h)

/-! ## Cell (118, 40): |T| = 5 -/

def T118_40list : List Coordinates := [(0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0)]
def T118_40 : Fin 5 → Coordinate 1 := fun i => T118_40list.getD i.val (0,0,0,0,0)

theorem hfix118_40 : ∀ i, ((T118_40 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118) :=
  repsFix_of_siftB rK118 ⟨40, by decide⟩ T118_40 (by decide)

theorem hinj118_40 : Function.Injective
    (fun i => ((T118_40 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)) :=
  repsInj_of_reduceAux rK118 T118_40 (by decide)

theorem hcardT118_40 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK118 ⟨40, by decide⟩ R118 hpxR118 hcardq118 (by decide)).symm

/-- **Cell (118, 40).** -/
theorem cell118_40 (e : List (ZMod 25)) (heK : charOK (basisAt rK118) e = true)
    (h : ↥(reps (⟨40, by decide⟩ : Fin 148))) :
    species (reps (⟨40, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK118 e (h : Coordinate 1) T118_40 i :=
  species_entry_eq_sum rK118 ⟨40, by decide⟩ e heK h T118_40 hfix118_40 hinj118_40 hcardT118_40
    (fun i => conj_mem_of_fixedPoints (reps ⟨40, by decide⟩) (reps rK118) (T118_40 i) (hfix118_40 i) h)

/-! ## Cell (118, 45): |T| = 5 -/

def T118_45list : List Coordinates := [(0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0)]
def T118_45 : Fin 5 → Coordinate 1 := fun i => T118_45list.getD i.val (0,0,0,0,0)

theorem hfix118_45 : ∀ i, ((T118_45 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118) :=
  repsFix_of_siftB rK118 ⟨45, by decide⟩ T118_45 (by decide)

theorem hinj118_45 : Function.Injective
    (fun i => ((T118_45 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)) :=
  repsInj_of_reduceAux rK118 T118_45 (by decide)

theorem hcardT118_45 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK118 ⟨45, by decide⟩ R118 hpxR118 hcardq118 (by decide)).symm

/-- **Cell (118, 45).** -/
theorem cell118_45 (e : List (ZMod 25)) (heK : charOK (basisAt rK118) e = true)
    (h : ↥(reps (⟨45, by decide⟩ : Fin 148))) :
    species (reps (⟨45, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK118 e (h : Coordinate 1) T118_45 i :=
  species_entry_eq_sum rK118 ⟨45, by decide⟩ e heK h T118_45 hfix118_45 hinj118_45 hcardT118_45
    (fun i => conj_mem_of_fixedPoints (reps ⟨45, by decide⟩) (reps rK118) (T118_45 i) (hfix118_45 i) h)

/-! ## Cell (118, 50): |T| = 5 -/

def T118_50list : List Coordinates := [(0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0)]
def T118_50 : Fin 5 → Coordinate 1 := fun i => T118_50list.getD i.val (0,0,0,0,0)

theorem hfix118_50 : ∀ i, ((T118_50 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118) :=
  repsFix_of_siftB rK118 ⟨50, by decide⟩ T118_50 (by decide)

theorem hinj118_50 : Function.Injective
    (fun i => ((T118_50 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)) :=
  repsInj_of_reduceAux rK118 T118_50 (by decide)

theorem hcardT118_50 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK118 ⟨50, by decide⟩ R118 hpxR118 hcardq118 (by decide)).symm

/-- **Cell (118, 50).** -/
theorem cell118_50 (e : List (ZMod 25)) (heK : charOK (basisAt rK118) e = true)
    (h : ↥(reps (⟨50, by decide⟩ : Fin 148))) :
    species (reps (⟨50, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK118 e (h : Coordinate 1) T118_50 i :=
  species_entry_eq_sum rK118 ⟨50, by decide⟩ e heK h T118_50 hfix118_50 hinj118_50 hcardT118_50
    (fun i => conj_mem_of_fixedPoints (reps ⟨50, by decide⟩) (reps rK118) (T118_50 i) (hfix118_50 i) h)

/-! ## Cell (118, 53): |T| = 5 -/

def T118_53list : List Coordinates := [(0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0)]
def T118_53 : Fin 5 → Coordinate 1 := fun i => T118_53list.getD i.val (0,0,0,0,0)

theorem hfix118_53 : ∀ i, ((T118_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118) :=
  repsFix_of_siftB rK118 ⟨53, by decide⟩ T118_53 (by decide)

theorem hinj118_53 : Function.Injective
    (fun i => ((T118_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)) :=
  repsInj_of_reduceAux rK118 T118_53 (by decide)

theorem hcardT118_53 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK118 ⟨53, by decide⟩ R118 hpxR118 hcardq118 (by decide)).symm

/-- **Cell (118, 53).** -/
theorem cell118_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK118) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK118 e (h : Coordinate 1) T118_53 i :=
  species_entry_eq_sum rK118 ⟨53, by decide⟩ e heK h T118_53 hfix118_53 hinj118_53 hcardT118_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK118) (T118_53 i) (hfix118_53 i) h)

/-! ## Cell (118, 65): |T| = 5 -/

def T118_65list : List Coordinates := [(0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0)]
def T118_65 : Fin 5 → Coordinate 1 := fun i => T118_65list.getD i.val (0,0,0,0,0)

theorem hfix118_65 : ∀ i, ((T118_65 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118) :=
  repsFix_of_siftB rK118 ⟨65, by decide⟩ T118_65 (by decide)

theorem hinj118_65 : Function.Injective
    (fun i => ((T118_65 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)) :=
  repsInj_of_reduceAux rK118 T118_65 (by decide)

theorem hcardT118_65 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK118 ⟨65, by decide⟩ R118 hpxR118 hcardq118 (by decide)).symm

/-- **Cell (118, 65).** -/
theorem cell118_65 (e : List (ZMod 25)) (heK : charOK (basisAt rK118) e = true)
    (h : ↥(reps (⟨65, by decide⟩ : Fin 148))) :
    species (reps (⟨65, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK118 e (h : Coordinate 1) T118_65 i :=
  species_entry_eq_sum rK118 ⟨65, by decide⟩ e heK h T118_65 hfix118_65 hinj118_65 hcardT118_65
    (fun i => conj_mem_of_fixedPoints (reps ⟨65, by decide⟩) (reps rK118) (T118_65 i) (hfix118_65 i) h)

/-! ## Cell (118, 66): |T| = 5 -/

def T118_66list : List Coordinates := [(0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0)]
def T118_66 : Fin 5 → Coordinate 1 := fun i => T118_66list.getD i.val (0,0,0,0,0)

theorem hfix118_66 : ∀ i, ((T118_66 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118) :=
  repsFix_of_siftB rK118 ⟨66, by decide⟩ T118_66 (by decide)

theorem hinj118_66 : Function.Injective
    (fun i => ((T118_66 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)) :=
  repsInj_of_reduceAux rK118 T118_66 (by decide)

theorem hcardT118_66 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK118 ⟨66, by decide⟩ R118 hpxR118 hcardq118 (by decide)).symm

/-- **Cell (118, 66).** -/
theorem cell118_66 (e : List (ZMod 25)) (heK : charOK (basisAt rK118) e = true)
    (h : ↥(reps (⟨66, by decide⟩ : Fin 148))) :
    species (reps (⟨66, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK118 e (h : Coordinate 1) T118_66 i :=
  species_entry_eq_sum rK118 ⟨66, by decide⟩ e heK h T118_66 hfix118_66 hinj118_66 hcardT118_66
    (fun i => conj_mem_of_fixedPoints (reps ⟨66, by decide⟩) (reps rK118) (T118_66 i) (hfix118_66 i) h)

/-! ## Cell (118, 67): |T| = 5 -/

def T118_67list : List Coordinates := [(0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0)]
def T118_67 : Fin 5 → Coordinate 1 := fun i => T118_67list.getD i.val (0,0,0,0,0)

theorem hfix118_67 : ∀ i, ((T118_67 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118) :=
  repsFix_of_siftB rK118 ⟨67, by decide⟩ T118_67 (by decide)

theorem hinj118_67 : Function.Injective
    (fun i => ((T118_67 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)) :=
  repsInj_of_reduceAux rK118 T118_67 (by decide)

theorem hcardT118_67 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK118 ⟨67, by decide⟩ R118 hpxR118 hcardq118 (by decide)).symm

/-- **Cell (118, 67).** -/
theorem cell118_67 (e : List (ZMod 25)) (heK : charOK (basisAt rK118) e = true)
    (h : ↥(reps (⟨67, by decide⟩ : Fin 148))) :
    species (reps (⟨67, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK118 e (h : Coordinate 1) T118_67 i :=
  species_entry_eq_sum rK118 ⟨67, by decide⟩ e heK h T118_67 hfix118_67 hinj118_67 hcardT118_67
    (fun i => conj_mem_of_fixedPoints (reps ⟨67, by decide⟩) (reps rK118) (T118_67 i) (hfix118_67 i) h)

/-! ## Cell (118, 68): |T| = 5 -/

def T118_68list : List Coordinates := [(0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0)]
def T118_68 : Fin 5 → Coordinate 1 := fun i => T118_68list.getD i.val (0,0,0,0,0)

theorem hfix118_68 : ∀ i, ((T118_68 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118) :=
  repsFix_of_siftB rK118 ⟨68, by decide⟩ T118_68 (by decide)

theorem hinj118_68 : Function.Injective
    (fun i => ((T118_68 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)) :=
  repsInj_of_reduceAux rK118 T118_68 (by decide)

theorem hcardT118_68 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK118 ⟨68, by decide⟩ R118 hpxR118 hcardq118 (by decide)).symm

/-- **Cell (118, 68).** -/
theorem cell118_68 (e : List (ZMod 25)) (heK : charOK (basisAt rK118) e = true)
    (h : ↥(reps (⟨68, by decide⟩ : Fin 148))) :
    species (reps (⟨68, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK118 e (h : Coordinate 1) T118_68 i :=
  species_entry_eq_sum rK118 ⟨68, by decide⟩ e heK h T118_68 hfix118_68 hinj118_68 hcardT118_68
    (fun i => conj_mem_of_fixedPoints (reps ⟨68, by decide⟩) (reps rK118) (T118_68 i) (hfix118_68 i) h)

/-! ## Cell (118, 69): |T| = 5 -/

def T118_69list : List Coordinates := [(0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0)]
def T118_69 : Fin 5 → Coordinate 1 := fun i => T118_69list.getD i.val (0,0,0,0,0)

theorem hfix118_69 : ∀ i, ((T118_69 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118) :=
  repsFix_of_siftB rK118 ⟨69, by decide⟩ T118_69 (by decide)

theorem hinj118_69 : Function.Injective
    (fun i => ((T118_69 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)) :=
  repsInj_of_reduceAux rK118 T118_69 (by decide)

theorem hcardT118_69 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK118 ⟨69, by decide⟩ R118 hpxR118 hcardq118 (by decide)).symm

/-- **Cell (118, 69).** -/
theorem cell118_69 (e : List (ZMod 25)) (heK : charOK (basisAt rK118) e = true)
    (h : ↥(reps (⟨69, by decide⟩ : Fin 148))) :
    species (reps (⟨69, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK118 e (h : Coordinate 1) T118_69 i :=
  species_entry_eq_sum rK118 ⟨69, by decide⟩ e heK h T118_69 hfix118_69 hinj118_69 hcardT118_69
    (fun i => conj_mem_of_fixedPoints (reps ⟨69, by decide⟩) (reps rK118) (T118_69 i) (hfix118_69 i) h)

/-! ## Cell (118, 80): |T| = 5 -/

def T118_80list : List Coordinates := [(0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0)]
def T118_80 : Fin 5 → Coordinate 1 := fun i => T118_80list.getD i.val (0,0,0,0,0)

theorem hfix118_80 : ∀ i, ((T118_80 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118) :=
  repsFix_of_siftB rK118 ⟨80, by decide⟩ T118_80 (by decide)

theorem hinj118_80 : Function.Injective
    (fun i => ((T118_80 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)) :=
  repsInj_of_reduceAux rK118 T118_80 (by decide)

theorem hcardT118_80 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK118 ⟨80, by decide⟩ R118 hpxR118 hcardq118 (by decide)).symm

/-- **Cell (118, 80).** -/
theorem cell118_80 (e : List (ZMod 25)) (heK : charOK (basisAt rK118) e = true)
    (h : ↥(reps (⟨80, by decide⟩ : Fin 148))) :
    species (reps (⟨80, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK118 e (h : Coordinate 1) T118_80 i :=
  species_entry_eq_sum rK118 ⟨80, by decide⟩ e heK h T118_80 hfix118_80 hinj118_80 hcardT118_80
    (fun i => conj_mem_of_fixedPoints (reps ⟨80, by decide⟩) (reps rK118) (T118_80 i) (hfix118_80 i) h)

/-! ## Cell (118, 92): |T| = 5 -/

def T118_92list : List Coordinates := [(0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0)]
def T118_92 : Fin 5 → Coordinate 1 := fun i => T118_92list.getD i.val (0,0,0,0,0)

theorem hfix118_92 : ∀ i, ((T118_92 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118) :=
  repsFix_of_siftB rK118 ⟨92, by decide⟩ T118_92 (by decide)

theorem hinj118_92 : Function.Injective
    (fun i => ((T118_92 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)) :=
  repsInj_of_reduceAux rK118 T118_92 (by decide)

theorem hcardT118_92 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK118 ⟨92, by decide⟩ R118 hpxR118 hcardq118 (by decide)).symm

/-- **Cell (118, 92).** -/
theorem cell118_92 (e : List (ZMod 25)) (heK : charOK (basisAt rK118) e = true)
    (h : ↥(reps (⟨92, by decide⟩ : Fin 148))) :
    species (reps (⟨92, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK118 e (h : Coordinate 1) T118_92 i :=
  species_entry_eq_sum rK118 ⟨92, by decide⟩ e heK h T118_92 hfix118_92 hinj118_92 hcardT118_92
    (fun i => conj_mem_of_fixedPoints (reps ⟨92, by decide⟩) (reps rK118) (T118_92 i) (hfix118_92 i) h)

/-! ## Cell (118, 97): |T| = 5 -/

def T118_97list : List Coordinates := [(0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0)]
def T118_97 : Fin 5 → Coordinate 1 := fun i => T118_97list.getD i.val (0,0,0,0,0)

theorem hfix118_97 : ∀ i, ((T118_97 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118) :=
  repsFix_of_siftB rK118 ⟨97, by decide⟩ T118_97 (by decide)

theorem hinj118_97 : Function.Injective
    (fun i => ((T118_97 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)) :=
  repsInj_of_reduceAux rK118 T118_97 (by decide)

theorem hcardT118_97 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK118 ⟨97, by decide⟩ R118 hpxR118 hcardq118 (by decide)).symm

/-- **Cell (118, 97).** -/
theorem cell118_97 (e : List (ZMod 25)) (heK : charOK (basisAt rK118) e = true)
    (h : ↥(reps (⟨97, by decide⟩ : Fin 148))) :
    species (reps (⟨97, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK118 e (h : Coordinate 1) T118_97 i :=
  species_entry_eq_sum rK118 ⟨97, by decide⟩ e heK h T118_97 hfix118_97 hinj118_97 hcardT118_97
    (fun i => conj_mem_of_fixedPoints (reps ⟨97, by decide⟩) (reps rK118) (T118_97 i) (hfix118_97 i) h)

/-! ## Cell (118, 102): |T| = 5 -/

def T118_102list : List Coordinates := [(0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0)]
def T118_102 : Fin 5 → Coordinate 1 := fun i => T118_102list.getD i.val (0,0,0,0,0)

theorem hfix118_102 : ∀ i, ((T118_102 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118) :=
  repsFix_of_siftB rK118 ⟨102, by decide⟩ T118_102 (by decide)

theorem hinj118_102 : Function.Injective
    (fun i => ((T118_102 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)) :=
  repsInj_of_reduceAux rK118 T118_102 (by decide)

theorem hcardT118_102 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK118 ⟨102, by decide⟩ R118 hpxR118 hcardq118 (by decide)).symm

/-- **Cell (118, 102).** -/
theorem cell118_102 (e : List (ZMod 25)) (heK : charOK (basisAt rK118) e = true)
    (h : ↥(reps (⟨102, by decide⟩ : Fin 148))) :
    species (reps (⟨102, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK118 e (h : Coordinate 1) T118_102 i :=
  species_entry_eq_sum rK118 ⟨102, by decide⟩ e heK h T118_102 hfix118_102 hinj118_102 hcardT118_102
    (fun i => conj_mem_of_fixedPoints (reps ⟨102, by decide⟩) (reps rK118) (T118_102 i) (hfix118_102 i) h)

/-! ## Cell (118, 107): |T| = 5 -/

def T118_107list : List Coordinates := [(0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0)]
def T118_107 : Fin 5 → Coordinate 1 := fun i => T118_107list.getD i.val (0,0,0,0,0)

theorem hfix118_107 : ∀ i, ((T118_107 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118) :=
  repsFix_of_siftB rK118 ⟨107, by decide⟩ T118_107 (by decide)

theorem hinj118_107 : Function.Injective
    (fun i => ((T118_107 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)) :=
  repsInj_of_reduceAux rK118 T118_107 (by decide)

theorem hcardT118_107 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK118 ⟨107, by decide⟩ R118 hpxR118 hcardq118 (by decide)).symm

/-- **Cell (118, 107).** -/
theorem cell118_107 (e : List (ZMod 25)) (heK : charOK (basisAt rK118) e = true)
    (h : ↥(reps (⟨107, by decide⟩ : Fin 148))) :
    species (reps (⟨107, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK118 e (h : Coordinate 1) T118_107 i :=
  species_entry_eq_sum rK118 ⟨107, by decide⟩ e heK h T118_107 hfix118_107 hinj118_107 hcardT118_107
    (fun i => conj_mem_of_fixedPoints (reps ⟨107, by decide⟩) (reps rK118) (T118_107 i) (hfix118_107 i) h)

/-! ## Cell (118, 112): |T| = 5 -/

def T118_112list : List Coordinates := [(0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0)]
def T118_112 : Fin 5 → Coordinate 1 := fun i => T118_112list.getD i.val (0,0,0,0,0)

theorem hfix118_112 : ∀ i, ((T118_112 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118) :=
  repsFix_of_siftB rK118 ⟨112, by decide⟩ T118_112 (by decide)

theorem hinj118_112 : Function.Injective
    (fun i => ((T118_112 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)) :=
  repsInj_of_reduceAux rK118 T118_112 (by decide)

theorem hcardT118_112 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK118 ⟨112, by decide⟩ R118 hpxR118 hcardq118 (by decide)).symm

/-- **Cell (118, 112).** -/
theorem cell118_112 (e : List (ZMod 25)) (heK : charOK (basisAt rK118) e = true)
    (h : ↥(reps (⟨112, by decide⟩ : Fin 148))) :
    species (reps (⟨112, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK118 e (h : Coordinate 1) T118_112 i :=
  species_entry_eq_sum rK118 ⟨112, by decide⟩ e heK h T118_112 hfix118_112 hinj118_112 hcardT118_112
    (fun i => conj_mem_of_fixedPoints (reps ⟨112, by decide⟩) (reps rK118) (T118_112 i) (hfix118_112 i) h)

/-! ## Cell (118, 118): |T| = 5 -/

def T118_118list : List Coordinates := [(0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0)]
def T118_118 : Fin 5 → Coordinate 1 := fun i => T118_118list.getD i.val (0,0,0,0,0)

theorem hfix118_118 : ∀ i, ((T118_118 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118) :=
  repsFix_of_siftB rK118 ⟨118, by decide⟩ T118_118 (by decide)

theorem hinj118_118 : Function.Injective
    (fun i => ((T118_118 i : Coordinate 1) : Coordinate 1 ⧸ reps rK118)) :=
  repsInj_of_reduceAux rK118 T118_118 (by decide)

theorem hcardT118_118 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK118 ⟨118, by decide⟩ R118 hpxR118 hcardq118 (by decide)).symm

/-- **Cell (118, 118).** -/
theorem cell118_118 (e : List (ZMod 25)) (heK : charOK (basisAt rK118) e = true)
    (h : ↥(reps (⟨118, by decide⟩ : Fin 148))) :
    species (reps (⟨118, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK118 e (h : Coordinate 1) T118_118 i :=
  species_entry_eq_sum rK118 ⟨118, by decide⟩ e heK h T118_118 hfix118_118 hinj118_118 hcardT118_118
    (fun i => conj_mem_of_fixedPoints (reps ⟨118, by decide⟩) (reps rK118) (T118_118 i) (hfix118_118 i) h)

namespace Q2

def R118_2 : Fin 5 → Coordinate 2 := fun i => R118list.getD i.val (0,0,0,0,0)
theorem hpxR118_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK118) (R118_2 i)) := by decide
theorem hcardq118_2 : Nat.card (Coordinate 2 ⧸ reps rK118) = 5 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (118, 0) twin -/

def T118_0_2 : Fin 5 → Coordinate 2 := fun i => T118_0list.getD i.val (0,0,0,0,0)

theorem hfix118_0_2 : ∀ i, ((T118_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118) :=
  repsFix_of_siftB2 rK118 ⟨0, by decide⟩ T118_0_2 (by decide)

theorem hinj118_0_2 : Function.Injective
    (fun i => ((T118_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)) :=
  repsInj_of_reduceAux2 rK118 T118_0_2 (by decide)

theorem hcardT118_0_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK118 ⟨0, by decide⟩ R118_2 hpxR118_2 hcardq118_2 (by decide)).symm

/-- **Cell (118, 0) twin (q=2).** -/
theorem cell118_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK118) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec2 rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK118 e (h : Coordinate 2) T118_0_2 i :=
  species_entry_eq_sum rK118 ⟨0, by decide⟩ e heK h T118_0_2 hfix118_0_2 hinj118_0_2 hcardT118_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK118) (T118_0_2 i) (hfix118_0_2 i) h)

/-! ### Cell (118, 1) twin -/

def T118_1_2 : Fin 5 → Coordinate 2 := fun i => T118_1list.getD i.val (0,0,0,0,0)

theorem hfix118_1_2 : ∀ i, ((T118_1_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118) :=
  repsFix_of_siftB2 rK118 ⟨1, by decide⟩ T118_1_2 (by decide)

theorem hinj118_1_2 : Function.Injective
    (fun i => ((T118_1_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)) :=
  repsInj_of_reduceAux2 rK118 T118_1_2 (by decide)

theorem hcardT118_1_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK118 ⟨1, by decide⟩ R118_2 hpxR118_2 hcardq118_2 (by decide)).symm

/-- **Cell (118, 1) twin (q=2).** -/
theorem cell118_1_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK118) e = true)
    (h : ↥(reps (⟨1, by decide⟩ : Fin 148))) :
    species (reps (⟨1, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec2 rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK118 e (h : Coordinate 2) T118_1_2 i :=
  species_entry_eq_sum rK118 ⟨1, by decide⟩ e heK h T118_1_2 hfix118_1_2 hinj118_1_2 hcardT118_1_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨1, by decide⟩) (reps rK118) (T118_1_2 i) (hfix118_1_2 i) h)

/-! ### Cell (118, 6) twin -/

def T118_6_2 : Fin 5 → Coordinate 2 := fun i => T118_6list.getD i.val (0,0,0,0,0)

theorem hfix118_6_2 : ∀ i, ((T118_6_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118) :=
  repsFix_of_siftB2 rK118 ⟨6, by decide⟩ T118_6_2 (by decide)

theorem hinj118_6_2 : Function.Injective
    (fun i => ((T118_6_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)) :=
  repsInj_of_reduceAux2 rK118 T118_6_2 (by decide)

theorem hcardT118_6_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK118 ⟨6, by decide⟩ R118_2 hpxR118_2 hcardq118_2 (by decide)).symm

/-- **Cell (118, 6) twin (q=2).** -/
theorem cell118_6_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK118) e = true)
    (h : ↥(reps (⟨6, by decide⟩ : Fin 148))) :
    species (reps (⟨6, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec2 rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK118 e (h : Coordinate 2) T118_6_2 i :=
  species_entry_eq_sum rK118 ⟨6, by decide⟩ e heK h T118_6_2 hfix118_6_2 hinj118_6_2 hcardT118_6_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨6, by decide⟩) (reps rK118) (T118_6_2 i) (hfix118_6_2 i) h)

/-! ### Cell (118, 7) twin -/

def T118_7_2 : Fin 5 → Coordinate 2 := fun i => T118_7list.getD i.val (0,0,0,0,0)

theorem hfix118_7_2 : ∀ i, ((T118_7_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118) :=
  repsFix_of_siftB2 rK118 ⟨7, by decide⟩ T118_7_2 (by decide)

theorem hinj118_7_2 : Function.Injective
    (fun i => ((T118_7_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)) :=
  repsInj_of_reduceAux2 rK118 T118_7_2 (by decide)

theorem hcardT118_7_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK118 ⟨7, by decide⟩ R118_2 hpxR118_2 hcardq118_2 (by decide)).symm

/-- **Cell (118, 7) twin (q=2).** -/
theorem cell118_7_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK118) e = true)
    (h : ↥(reps (⟨7, by decide⟩ : Fin 148))) :
    species (reps (⟨7, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec2 rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK118 e (h : Coordinate 2) T118_7_2 i :=
  species_entry_eq_sum rK118 ⟨7, by decide⟩ e heK h T118_7_2 hfix118_7_2 hinj118_7_2 hcardT118_7_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨7, by decide⟩) (reps rK118) (T118_7_2 i) (hfix118_7_2 i) h)

/-! ### Cell (118, 8) twin -/

def T118_8_2 : Fin 5 → Coordinate 2 := fun i => T118_8list.getD i.val (0,0,0,0,0)

theorem hfix118_8_2 : ∀ i, ((T118_8_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118) :=
  repsFix_of_siftB2 rK118 ⟨8, by decide⟩ T118_8_2 (by decide)

theorem hinj118_8_2 : Function.Injective
    (fun i => ((T118_8_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)) :=
  repsInj_of_reduceAux2 rK118 T118_8_2 (by decide)

theorem hcardT118_8_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK118 ⟨8, by decide⟩ R118_2 hpxR118_2 hcardq118_2 (by decide)).symm

/-- **Cell (118, 8) twin (q=2).** -/
theorem cell118_8_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK118) e = true)
    (h : ↥(reps (⟨8, by decide⟩ : Fin 148))) :
    species (reps (⟨8, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec2 rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK118 e (h : Coordinate 2) T118_8_2 i :=
  species_entry_eq_sum rK118 ⟨8, by decide⟩ e heK h T118_8_2 hfix118_8_2 hinj118_8_2 hcardT118_8_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨8, by decide⟩) (reps rK118) (T118_8_2 i) (hfix118_8_2 i) h)

/-! ### Cell (118, 9) twin -/

def T118_9_2 : Fin 5 → Coordinate 2 := fun i => T118_9list.getD i.val (0,0,0,0,0)

theorem hfix118_9_2 : ∀ i, ((T118_9_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118) :=
  repsFix_of_siftB2 rK118 ⟨9, by decide⟩ T118_9_2 (by decide)

theorem hinj118_9_2 : Function.Injective
    (fun i => ((T118_9_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)) :=
  repsInj_of_reduceAux2 rK118 T118_9_2 (by decide)

theorem hcardT118_9_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK118 ⟨9, by decide⟩ R118_2 hpxR118_2 hcardq118_2 (by decide)).symm

/-- **Cell (118, 9) twin (q=2).** -/
theorem cell118_9_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK118) e = true)
    (h : ↥(reps (⟨9, by decide⟩ : Fin 148))) :
    species (reps (⟨9, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec2 rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK118 e (h : Coordinate 2) T118_9_2 i :=
  species_entry_eq_sum rK118 ⟨9, by decide⟩ e heK h T118_9_2 hfix118_9_2 hinj118_9_2 hcardT118_9_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨9, by decide⟩) (reps rK118) (T118_9_2 i) (hfix118_9_2 i) h)

/-! ### Cell (118, 10) twin -/

def T118_10_2 : Fin 5 → Coordinate 2 := fun i => T118_10list.getD i.val (0,0,0,0,0)

theorem hfix118_10_2 : ∀ i, ((T118_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118) :=
  repsFix_of_siftB2 rK118 ⟨10, by decide⟩ T118_10_2 (by decide)

theorem hinj118_10_2 : Function.Injective
    (fun i => ((T118_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)) :=
  repsInj_of_reduceAux2 rK118 T118_10_2 (by decide)

theorem hcardT118_10_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK118 ⟨10, by decide⟩ R118_2 hpxR118_2 hcardq118_2 (by decide)).symm

/-- **Cell (118, 10) twin (q=2).** -/
theorem cell118_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK118) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec2 rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK118 e (h : Coordinate 2) T118_10_2 i :=
  species_entry_eq_sum rK118 ⟨10, by decide⟩ e heK h T118_10_2 hfix118_10_2 hinj118_10_2 hcardT118_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK118) (T118_10_2 i) (hfix118_10_2 i) h)

/-! ### Cell (118, 12) twin -/

def T118_12_2 : Fin 5 → Coordinate 2 := fun i => T118_12list.getD i.val (0,0,0,0,0)

theorem hfix118_12_2 : ∀ i, ((T118_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118) :=
  repsFix_of_siftB2 rK118 ⟨12, by decide⟩ T118_12_2 (by decide)

theorem hinj118_12_2 : Function.Injective
    (fun i => ((T118_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)) :=
  repsInj_of_reduceAux2 rK118 T118_12_2 (by decide)

theorem hcardT118_12_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK118 ⟨12, by decide⟩ R118_2 hpxR118_2 hcardq118_2 (by decide)).symm

/-- **Cell (118, 12) twin (q=2).** -/
theorem cell118_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK118) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec2 rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK118 e (h : Coordinate 2) T118_12_2 i :=
  species_entry_eq_sum rK118 ⟨12, by decide⟩ e heK h T118_12_2 hfix118_12_2 hinj118_12_2 hcardT118_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK118) (T118_12_2 i) (hfix118_12_2 i) h)

/-! ### Cell (118, 13) twin -/

def T118_13_2 : Fin 5 → Coordinate 2 := fun i => T118_13list.getD i.val (0,0,0,0,0)

theorem hfix118_13_2 : ∀ i, ((T118_13_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118) :=
  repsFix_of_siftB2 rK118 ⟨13, by decide⟩ T118_13_2 (by decide)

theorem hinj118_13_2 : Function.Injective
    (fun i => ((T118_13_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)) :=
  repsInj_of_reduceAux2 rK118 T118_13_2 (by decide)

theorem hcardT118_13_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK118 ⟨13, by decide⟩ R118_2 hpxR118_2 hcardq118_2 (by decide)).symm

/-- **Cell (118, 13) twin (q=2).** -/
theorem cell118_13_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK118) e = true)
    (h : ↥(reps (⟨13, by decide⟩ : Fin 148))) :
    species (reps (⟨13, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec2 rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK118 e (h : Coordinate 2) T118_13_2 i :=
  species_entry_eq_sum rK118 ⟨13, by decide⟩ e heK h T118_13_2 hfix118_13_2 hinj118_13_2 hcardT118_13_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨13, by decide⟩) (reps rK118) (T118_13_2 i) (hfix118_13_2 i) h)

/-! ### Cell (118, 19) twin -/

def T118_19_2 : Fin 5 → Coordinate 2 := fun i => T118_19list.getD i.val (0,0,0,0,0)

theorem hfix118_19_2 : ∀ i, ((T118_19_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118) :=
  repsFix_of_siftB2 rK118 ⟨19, by decide⟩ T118_19_2 (by decide)

theorem hinj118_19_2 : Function.Injective
    (fun i => ((T118_19_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)) :=
  repsInj_of_reduceAux2 rK118 T118_19_2 (by decide)

theorem hcardT118_19_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK118 ⟨19, by decide⟩ R118_2 hpxR118_2 hcardq118_2 (by decide)).symm

/-- **Cell (118, 19) twin (q=2).** -/
theorem cell118_19_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK118) e = true)
    (h : ↥(reps (⟨19, by decide⟩ : Fin 148))) :
    species (reps (⟨19, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec2 rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK118 e (h : Coordinate 2) T118_19_2 i :=
  species_entry_eq_sum rK118 ⟨19, by decide⟩ e heK h T118_19_2 hfix118_19_2 hinj118_19_2 hcardT118_19_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨19, by decide⟩) (reps rK118) (T118_19_2 i) (hfix118_19_2 i) h)

/-! ### Cell (118, 24) twin -/

def T118_24_2 : Fin 5 → Coordinate 2 := fun i => T118_24list.getD i.val (0,0,0,0,0)

theorem hfix118_24_2 : ∀ i, ((T118_24_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118) :=
  repsFix_of_siftB2 rK118 ⟨24, by decide⟩ T118_24_2 (by decide)

theorem hinj118_24_2 : Function.Injective
    (fun i => ((T118_24_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)) :=
  repsInj_of_reduceAux2 rK118 T118_24_2 (by decide)

theorem hcardT118_24_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK118 ⟨24, by decide⟩ R118_2 hpxR118_2 hcardq118_2 (by decide)).symm

/-- **Cell (118, 24) twin (q=2).** -/
theorem cell118_24_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK118) e = true)
    (h : ↥(reps (⟨24, by decide⟩ : Fin 148))) :
    species (reps (⟨24, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec2 rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK118 e (h : Coordinate 2) T118_24_2 i :=
  species_entry_eq_sum rK118 ⟨24, by decide⟩ e heK h T118_24_2 hfix118_24_2 hinj118_24_2 hcardT118_24_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨24, by decide⟩) (reps rK118) (T118_24_2 i) (hfix118_24_2 i) h)

/-! ### Cell (118, 25) twin -/

def T118_25_2 : Fin 5 → Coordinate 2 := fun i => T118_25list.getD i.val (0,0,0,0,0)

theorem hfix118_25_2 : ∀ i, ((T118_25_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118) :=
  repsFix_of_siftB2 rK118 ⟨25, by decide⟩ T118_25_2 (by decide)

theorem hinj118_25_2 : Function.Injective
    (fun i => ((T118_25_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)) :=
  repsInj_of_reduceAux2 rK118 T118_25_2 (by decide)

theorem hcardT118_25_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK118 ⟨25, by decide⟩ R118_2 hpxR118_2 hcardq118_2 (by decide)).symm

/-- **Cell (118, 25) twin (q=2).** -/
theorem cell118_25_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK118) e = true)
    (h : ↥(reps (⟨25, by decide⟩ : Fin 148))) :
    species (reps (⟨25, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec2 rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK118 e (h : Coordinate 2) T118_25_2 i :=
  species_entry_eq_sum rK118 ⟨25, by decide⟩ e heK h T118_25_2 hfix118_25_2 hinj118_25_2 hcardT118_25_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨25, by decide⟩) (reps rK118) (T118_25_2 i) (hfix118_25_2 i) h)

/-! ### Cell (118, 26) twin -/

def T118_26_2 : Fin 5 → Coordinate 2 := fun i => T118_26list.getD i.val (0,0,0,0,0)

theorem hfix118_26_2 : ∀ i, ((T118_26_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118) :=
  repsFix_of_siftB2 rK118 ⟨26, by decide⟩ T118_26_2 (by decide)

theorem hinj118_26_2 : Function.Injective
    (fun i => ((T118_26_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)) :=
  repsInj_of_reduceAux2 rK118 T118_26_2 (by decide)

theorem hcardT118_26_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK118 ⟨26, by decide⟩ R118_2 hpxR118_2 hcardq118_2 (by decide)).symm

/-- **Cell (118, 26) twin (q=2).** -/
theorem cell118_26_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK118) e = true)
    (h : ↥(reps (⟨26, by decide⟩ : Fin 148))) :
    species (reps (⟨26, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec2 rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK118 e (h : Coordinate 2) T118_26_2 i :=
  species_entry_eq_sum rK118 ⟨26, by decide⟩ e heK h T118_26_2 hfix118_26_2 hinj118_26_2 hcardT118_26_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨26, by decide⟩) (reps rK118) (T118_26_2 i) (hfix118_26_2 i) h)

/-! ### Cell (118, 27) twin -/

def T118_27_2 : Fin 5 → Coordinate 2 := fun i => T118_27list.getD i.val (0,0,0,0,0)

theorem hfix118_27_2 : ∀ i, ((T118_27_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118) :=
  repsFix_of_siftB2 rK118 ⟨27, by decide⟩ T118_27_2 (by decide)

theorem hinj118_27_2 : Function.Injective
    (fun i => ((T118_27_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)) :=
  repsInj_of_reduceAux2 rK118 T118_27_2 (by decide)

theorem hcardT118_27_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK118 ⟨27, by decide⟩ R118_2 hpxR118_2 hcardq118_2 (by decide)).symm

/-- **Cell (118, 27) twin (q=2).** -/
theorem cell118_27_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK118) e = true)
    (h : ↥(reps (⟨27, by decide⟩ : Fin 148))) :
    species (reps (⟨27, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec2 rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK118 e (h : Coordinate 2) T118_27_2 i :=
  species_entry_eq_sum rK118 ⟨27, by decide⟩ e heK h T118_27_2 hfix118_27_2 hinj118_27_2 hcardT118_27_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨27, by decide⟩) (reps rK118) (T118_27_2 i) (hfix118_27_2 i) h)

/-! ### Cell (118, 30) twin -/

def T118_30_2 : Fin 5 → Coordinate 2 := fun i => T118_30list.getD i.val (0,0,0,0,0)

theorem hfix118_30_2 : ∀ i, ((T118_30_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118) :=
  repsFix_of_siftB2 rK118 ⟨30, by decide⟩ T118_30_2 (by decide)

theorem hinj118_30_2 : Function.Injective
    (fun i => ((T118_30_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)) :=
  repsInj_of_reduceAux2 rK118 T118_30_2 (by decide)

theorem hcardT118_30_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK118 ⟨30, by decide⟩ R118_2 hpxR118_2 hcardq118_2 (by decide)).symm

/-- **Cell (118, 30) twin (q=2).** -/
theorem cell118_30_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK118) e = true)
    (h : ↥(reps (⟨30, by decide⟩ : Fin 148))) :
    species (reps (⟨30, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec2 rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK118 e (h : Coordinate 2) T118_30_2 i :=
  species_entry_eq_sum rK118 ⟨30, by decide⟩ e heK h T118_30_2 hfix118_30_2 hinj118_30_2 hcardT118_30_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨30, by decide⟩) (reps rK118) (T118_30_2 i) (hfix118_30_2 i) h)

/-! ### Cell (118, 35) twin -/

def T118_35_2 : Fin 5 → Coordinate 2 := fun i => T118_35list.getD i.val (0,0,0,0,0)

theorem hfix118_35_2 : ∀ i, ((T118_35_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118) :=
  repsFix_of_siftB2 rK118 ⟨35, by decide⟩ T118_35_2 (by decide)

theorem hinj118_35_2 : Function.Injective
    (fun i => ((T118_35_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)) :=
  repsInj_of_reduceAux2 rK118 T118_35_2 (by decide)

theorem hcardT118_35_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK118 ⟨35, by decide⟩ R118_2 hpxR118_2 hcardq118_2 (by decide)).symm

/-- **Cell (118, 35) twin (q=2).** -/
theorem cell118_35_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK118) e = true)
    (h : ↥(reps (⟨35, by decide⟩ : Fin 148))) :
    species (reps (⟨35, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec2 rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK118 e (h : Coordinate 2) T118_35_2 i :=
  species_entry_eq_sum rK118 ⟨35, by decide⟩ e heK h T118_35_2 hfix118_35_2 hinj118_35_2 hcardT118_35_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨35, by decide⟩) (reps rK118) (T118_35_2 i) (hfix118_35_2 i) h)

/-! ### Cell (118, 40) twin -/

def T118_40_2 : Fin 5 → Coordinate 2 := fun i => T118_40list.getD i.val (0,0,0,0,0)

theorem hfix118_40_2 : ∀ i, ((T118_40_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118) :=
  repsFix_of_siftB2 rK118 ⟨40, by decide⟩ T118_40_2 (by decide)

theorem hinj118_40_2 : Function.Injective
    (fun i => ((T118_40_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)) :=
  repsInj_of_reduceAux2 rK118 T118_40_2 (by decide)

theorem hcardT118_40_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK118 ⟨40, by decide⟩ R118_2 hpxR118_2 hcardq118_2 (by decide)).symm

/-- **Cell (118, 40) twin (q=2).** -/
theorem cell118_40_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK118) e = true)
    (h : ↥(reps (⟨40, by decide⟩ : Fin 148))) :
    species (reps (⟨40, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec2 rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK118 e (h : Coordinate 2) T118_40_2 i :=
  species_entry_eq_sum rK118 ⟨40, by decide⟩ e heK h T118_40_2 hfix118_40_2 hinj118_40_2 hcardT118_40_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨40, by decide⟩) (reps rK118) (T118_40_2 i) (hfix118_40_2 i) h)

/-! ### Cell (118, 45) twin -/

def T118_45_2 : Fin 5 → Coordinate 2 := fun i => T118_45list.getD i.val (0,0,0,0,0)

theorem hfix118_45_2 : ∀ i, ((T118_45_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118) :=
  repsFix_of_siftB2 rK118 ⟨45, by decide⟩ T118_45_2 (by decide)

theorem hinj118_45_2 : Function.Injective
    (fun i => ((T118_45_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)) :=
  repsInj_of_reduceAux2 rK118 T118_45_2 (by decide)

theorem hcardT118_45_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK118 ⟨45, by decide⟩ R118_2 hpxR118_2 hcardq118_2 (by decide)).symm

/-- **Cell (118, 45) twin (q=2).** -/
theorem cell118_45_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK118) e = true)
    (h : ↥(reps (⟨45, by decide⟩ : Fin 148))) :
    species (reps (⟨45, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec2 rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK118 e (h : Coordinate 2) T118_45_2 i :=
  species_entry_eq_sum rK118 ⟨45, by decide⟩ e heK h T118_45_2 hfix118_45_2 hinj118_45_2 hcardT118_45_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨45, by decide⟩) (reps rK118) (T118_45_2 i) (hfix118_45_2 i) h)

/-! ### Cell (118, 50) twin -/

def T118_50_2 : Fin 5 → Coordinate 2 := fun i => T118_50list.getD i.val (0,0,0,0,0)

theorem hfix118_50_2 : ∀ i, ((T118_50_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118) :=
  repsFix_of_siftB2 rK118 ⟨50, by decide⟩ T118_50_2 (by decide)

theorem hinj118_50_2 : Function.Injective
    (fun i => ((T118_50_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)) :=
  repsInj_of_reduceAux2 rK118 T118_50_2 (by decide)

theorem hcardT118_50_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK118 ⟨50, by decide⟩ R118_2 hpxR118_2 hcardq118_2 (by decide)).symm

/-- **Cell (118, 50) twin (q=2).** -/
theorem cell118_50_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK118) e = true)
    (h : ↥(reps (⟨50, by decide⟩ : Fin 148))) :
    species (reps (⟨50, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec2 rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK118 e (h : Coordinate 2) T118_50_2 i :=
  species_entry_eq_sum rK118 ⟨50, by decide⟩ e heK h T118_50_2 hfix118_50_2 hinj118_50_2 hcardT118_50_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨50, by decide⟩) (reps rK118) (T118_50_2 i) (hfix118_50_2 i) h)

/-! ### Cell (118, 53) twin -/

def T118_53_2 : Fin 5 → Coordinate 2 := fun i => T118_53list.getD i.val (0,0,0,0,0)

theorem hfix118_53_2 : ∀ i, ((T118_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118) :=
  repsFix_of_siftB2 rK118 ⟨53, by decide⟩ T118_53_2 (by decide)

theorem hinj118_53_2 : Function.Injective
    (fun i => ((T118_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)) :=
  repsInj_of_reduceAux2 rK118 T118_53_2 (by decide)

theorem hcardT118_53_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK118 ⟨53, by decide⟩ R118_2 hpxR118_2 hcardq118_2 (by decide)).symm

/-- **Cell (118, 53) twin (q=2).** -/
theorem cell118_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK118) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec2 rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK118 e (h : Coordinate 2) T118_53_2 i :=
  species_entry_eq_sum rK118 ⟨53, by decide⟩ e heK h T118_53_2 hfix118_53_2 hinj118_53_2 hcardT118_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK118) (T118_53_2 i) (hfix118_53_2 i) h)

/-! ### Cell (118, 65) twin -/

def T118_65_2 : Fin 5 → Coordinate 2 := fun i => T118_65list.getD i.val (0,0,0,0,0)

theorem hfix118_65_2 : ∀ i, ((T118_65_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118) :=
  repsFix_of_siftB2 rK118 ⟨65, by decide⟩ T118_65_2 (by decide)

theorem hinj118_65_2 : Function.Injective
    (fun i => ((T118_65_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)) :=
  repsInj_of_reduceAux2 rK118 T118_65_2 (by decide)

theorem hcardT118_65_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK118 ⟨65, by decide⟩ R118_2 hpxR118_2 hcardq118_2 (by decide)).symm

/-- **Cell (118, 65) twin (q=2).** -/
theorem cell118_65_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK118) e = true)
    (h : ↥(reps (⟨65, by decide⟩ : Fin 148))) :
    species (reps (⟨65, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec2 rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK118 e (h : Coordinate 2) T118_65_2 i :=
  species_entry_eq_sum rK118 ⟨65, by decide⟩ e heK h T118_65_2 hfix118_65_2 hinj118_65_2 hcardT118_65_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨65, by decide⟩) (reps rK118) (T118_65_2 i) (hfix118_65_2 i) h)

/-! ### Cell (118, 66) twin -/

def T118_66_2 : Fin 5 → Coordinate 2 := fun i => T118_66list.getD i.val (0,0,0,0,0)

theorem hfix118_66_2 : ∀ i, ((T118_66_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118) :=
  repsFix_of_siftB2 rK118 ⟨66, by decide⟩ T118_66_2 (by decide)

theorem hinj118_66_2 : Function.Injective
    (fun i => ((T118_66_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)) :=
  repsInj_of_reduceAux2 rK118 T118_66_2 (by decide)

theorem hcardT118_66_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK118 ⟨66, by decide⟩ R118_2 hpxR118_2 hcardq118_2 (by decide)).symm

/-- **Cell (118, 66) twin (q=2).** -/
theorem cell118_66_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK118) e = true)
    (h : ↥(reps (⟨66, by decide⟩ : Fin 148))) :
    species (reps (⟨66, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec2 rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK118 e (h : Coordinate 2) T118_66_2 i :=
  species_entry_eq_sum rK118 ⟨66, by decide⟩ e heK h T118_66_2 hfix118_66_2 hinj118_66_2 hcardT118_66_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨66, by decide⟩) (reps rK118) (T118_66_2 i) (hfix118_66_2 i) h)

/-! ### Cell (118, 67) twin -/

def T118_67_2 : Fin 5 → Coordinate 2 := fun i => T118_67list.getD i.val (0,0,0,0,0)

theorem hfix118_67_2 : ∀ i, ((T118_67_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118) :=
  repsFix_of_siftB2 rK118 ⟨67, by decide⟩ T118_67_2 (by decide)

theorem hinj118_67_2 : Function.Injective
    (fun i => ((T118_67_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)) :=
  repsInj_of_reduceAux2 rK118 T118_67_2 (by decide)

theorem hcardT118_67_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK118 ⟨67, by decide⟩ R118_2 hpxR118_2 hcardq118_2 (by decide)).symm

/-- **Cell (118, 67) twin (q=2).** -/
theorem cell118_67_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK118) e = true)
    (h : ↥(reps (⟨67, by decide⟩ : Fin 148))) :
    species (reps (⟨67, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec2 rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK118 e (h : Coordinate 2) T118_67_2 i :=
  species_entry_eq_sum rK118 ⟨67, by decide⟩ e heK h T118_67_2 hfix118_67_2 hinj118_67_2 hcardT118_67_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨67, by decide⟩) (reps rK118) (T118_67_2 i) (hfix118_67_2 i) h)

/-! ### Cell (118, 68) twin -/

def T118_68_2 : Fin 5 → Coordinate 2 := fun i => T118_68list.getD i.val (0,0,0,0,0)

theorem hfix118_68_2 : ∀ i, ((T118_68_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118) :=
  repsFix_of_siftB2 rK118 ⟨68, by decide⟩ T118_68_2 (by decide)

theorem hinj118_68_2 : Function.Injective
    (fun i => ((T118_68_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)) :=
  repsInj_of_reduceAux2 rK118 T118_68_2 (by decide)

theorem hcardT118_68_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK118 ⟨68, by decide⟩ R118_2 hpxR118_2 hcardq118_2 (by decide)).symm

/-- **Cell (118, 68) twin (q=2).** -/
theorem cell118_68_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK118) e = true)
    (h : ↥(reps (⟨68, by decide⟩ : Fin 148))) :
    species (reps (⟨68, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec2 rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK118 e (h : Coordinate 2) T118_68_2 i :=
  species_entry_eq_sum rK118 ⟨68, by decide⟩ e heK h T118_68_2 hfix118_68_2 hinj118_68_2 hcardT118_68_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨68, by decide⟩) (reps rK118) (T118_68_2 i) (hfix118_68_2 i) h)

/-! ### Cell (118, 69) twin -/

def T118_69_2 : Fin 5 → Coordinate 2 := fun i => T118_69list.getD i.val (0,0,0,0,0)

theorem hfix118_69_2 : ∀ i, ((T118_69_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118) :=
  repsFix_of_siftB2 rK118 ⟨69, by decide⟩ T118_69_2 (by decide)

theorem hinj118_69_2 : Function.Injective
    (fun i => ((T118_69_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)) :=
  repsInj_of_reduceAux2 rK118 T118_69_2 (by decide)

theorem hcardT118_69_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK118 ⟨69, by decide⟩ R118_2 hpxR118_2 hcardq118_2 (by decide)).symm

/-- **Cell (118, 69) twin (q=2).** -/
theorem cell118_69_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK118) e = true)
    (h : ↥(reps (⟨69, by decide⟩ : Fin 148))) :
    species (reps (⟨69, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec2 rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK118 e (h : Coordinate 2) T118_69_2 i :=
  species_entry_eq_sum rK118 ⟨69, by decide⟩ e heK h T118_69_2 hfix118_69_2 hinj118_69_2 hcardT118_69_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨69, by decide⟩) (reps rK118) (T118_69_2 i) (hfix118_69_2 i) h)

/-! ### Cell (118, 80) twin -/

def T118_80_2 : Fin 5 → Coordinate 2 := fun i => T118_80list.getD i.val (0,0,0,0,0)

theorem hfix118_80_2 : ∀ i, ((T118_80_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118) :=
  repsFix_of_siftB2 rK118 ⟨80, by decide⟩ T118_80_2 (by decide)

theorem hinj118_80_2 : Function.Injective
    (fun i => ((T118_80_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)) :=
  repsInj_of_reduceAux2 rK118 T118_80_2 (by decide)

theorem hcardT118_80_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK118 ⟨80, by decide⟩ R118_2 hpxR118_2 hcardq118_2 (by decide)).symm

/-- **Cell (118, 80) twin (q=2).** -/
theorem cell118_80_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK118) e = true)
    (h : ↥(reps (⟨80, by decide⟩ : Fin 148))) :
    species (reps (⟨80, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec2 rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK118 e (h : Coordinate 2) T118_80_2 i :=
  species_entry_eq_sum rK118 ⟨80, by decide⟩ e heK h T118_80_2 hfix118_80_2 hinj118_80_2 hcardT118_80_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨80, by decide⟩) (reps rK118) (T118_80_2 i) (hfix118_80_2 i) h)

/-! ### Cell (118, 92) twin -/

def T118_92_2 : Fin 5 → Coordinate 2 := fun i => T118_92list.getD i.val (0,0,0,0,0)

theorem hfix118_92_2 : ∀ i, ((T118_92_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118) :=
  repsFix_of_siftB2 rK118 ⟨92, by decide⟩ T118_92_2 (by decide)

theorem hinj118_92_2 : Function.Injective
    (fun i => ((T118_92_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)) :=
  repsInj_of_reduceAux2 rK118 T118_92_2 (by decide)

theorem hcardT118_92_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK118 ⟨92, by decide⟩ R118_2 hpxR118_2 hcardq118_2 (by decide)).symm

/-- **Cell (118, 92) twin (q=2).** -/
theorem cell118_92_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK118) e = true)
    (h : ↥(reps (⟨92, by decide⟩ : Fin 148))) :
    species (reps (⟨92, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec2 rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK118 e (h : Coordinate 2) T118_92_2 i :=
  species_entry_eq_sum rK118 ⟨92, by decide⟩ e heK h T118_92_2 hfix118_92_2 hinj118_92_2 hcardT118_92_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨92, by decide⟩) (reps rK118) (T118_92_2 i) (hfix118_92_2 i) h)

/-! ### Cell (118, 97) twin -/

def T118_97_2 : Fin 5 → Coordinate 2 := fun i => T118_97list.getD i.val (0,0,0,0,0)

theorem hfix118_97_2 : ∀ i, ((T118_97_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118) :=
  repsFix_of_siftB2 rK118 ⟨97, by decide⟩ T118_97_2 (by decide)

theorem hinj118_97_2 : Function.Injective
    (fun i => ((T118_97_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)) :=
  repsInj_of_reduceAux2 rK118 T118_97_2 (by decide)

theorem hcardT118_97_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK118 ⟨97, by decide⟩ R118_2 hpxR118_2 hcardq118_2 (by decide)).symm

/-- **Cell (118, 97) twin (q=2).** -/
theorem cell118_97_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK118) e = true)
    (h : ↥(reps (⟨97, by decide⟩ : Fin 148))) :
    species (reps (⟨97, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec2 rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK118 e (h : Coordinate 2) T118_97_2 i :=
  species_entry_eq_sum rK118 ⟨97, by decide⟩ e heK h T118_97_2 hfix118_97_2 hinj118_97_2 hcardT118_97_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨97, by decide⟩) (reps rK118) (T118_97_2 i) (hfix118_97_2 i) h)

/-! ### Cell (118, 102) twin -/

def T118_102_2 : Fin 5 → Coordinate 2 := fun i => T118_102list.getD i.val (0,0,0,0,0)

theorem hfix118_102_2 : ∀ i, ((T118_102_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118) :=
  repsFix_of_siftB2 rK118 ⟨102, by decide⟩ T118_102_2 (by decide)

theorem hinj118_102_2 : Function.Injective
    (fun i => ((T118_102_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)) :=
  repsInj_of_reduceAux2 rK118 T118_102_2 (by decide)

theorem hcardT118_102_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK118 ⟨102, by decide⟩ R118_2 hpxR118_2 hcardq118_2 (by decide)).symm

/-- **Cell (118, 102) twin (q=2).** -/
theorem cell118_102_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK118) e = true)
    (h : ↥(reps (⟨102, by decide⟩ : Fin 148))) :
    species (reps (⟨102, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec2 rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK118 e (h : Coordinate 2) T118_102_2 i :=
  species_entry_eq_sum rK118 ⟨102, by decide⟩ e heK h T118_102_2 hfix118_102_2 hinj118_102_2 hcardT118_102_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨102, by decide⟩) (reps rK118) (T118_102_2 i) (hfix118_102_2 i) h)

/-! ### Cell (118, 107) twin -/

def T118_107_2 : Fin 5 → Coordinate 2 := fun i => T118_107list.getD i.val (0,0,0,0,0)

theorem hfix118_107_2 : ∀ i, ((T118_107_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118) :=
  repsFix_of_siftB2 rK118 ⟨107, by decide⟩ T118_107_2 (by decide)

theorem hinj118_107_2 : Function.Injective
    (fun i => ((T118_107_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)) :=
  repsInj_of_reduceAux2 rK118 T118_107_2 (by decide)

theorem hcardT118_107_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK118 ⟨107, by decide⟩ R118_2 hpxR118_2 hcardq118_2 (by decide)).symm

/-- **Cell (118, 107) twin (q=2).** -/
theorem cell118_107_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK118) e = true)
    (h : ↥(reps (⟨107, by decide⟩ : Fin 148))) :
    species (reps (⟨107, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec2 rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK118 e (h : Coordinate 2) T118_107_2 i :=
  species_entry_eq_sum rK118 ⟨107, by decide⟩ e heK h T118_107_2 hfix118_107_2 hinj118_107_2 hcardT118_107_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨107, by decide⟩) (reps rK118) (T118_107_2 i) (hfix118_107_2 i) h)

/-! ### Cell (118, 112) twin -/

def T118_112_2 : Fin 5 → Coordinate 2 := fun i => T118_112list.getD i.val (0,0,0,0,0)

theorem hfix118_112_2 : ∀ i, ((T118_112_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118) :=
  repsFix_of_siftB2 rK118 ⟨112, by decide⟩ T118_112_2 (by decide)

theorem hinj118_112_2 : Function.Injective
    (fun i => ((T118_112_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)) :=
  repsInj_of_reduceAux2 rK118 T118_112_2 (by decide)

theorem hcardT118_112_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK118 ⟨112, by decide⟩ R118_2 hpxR118_2 hcardq118_2 (by decide)).symm

/-- **Cell (118, 112) twin (q=2).** -/
theorem cell118_112_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK118) e = true)
    (h : ↥(reps (⟨112, by decide⟩ : Fin 148))) :
    species (reps (⟨112, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec2 rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK118 e (h : Coordinate 2) T118_112_2 i :=
  species_entry_eq_sum rK118 ⟨112, by decide⟩ e heK h T118_112_2 hfix118_112_2 hinj118_112_2 hcardT118_112_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨112, by decide⟩) (reps rK118) (T118_112_2 i) (hfix118_112_2 i) h)

/-! ### Cell (118, 118) twin -/

def T118_118_2 : Fin 5 → Coordinate 2 := fun i => T118_118list.getD i.val (0,0,0,0,0)

theorem hfix118_118_2 : ∀ i, ((T118_118_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)
    ∈ fixedPoints (reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118) :=
  repsFix_of_siftB2 rK118 ⟨118, by decide⟩ T118_118_2 (by decide)

theorem hinj118_118_2 : Function.Injective
    (fun i => ((T118_118_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK118)) :=
  repsInj_of_reduceAux2 rK118 T118_118_2 (by decide)

theorem hcardT118_118_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK118)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK118 ⟨118, by decide⟩ R118_2 hpxR118_2 hcardq118_2 (by decide)).symm

/-- **Cell (118, 118) twin (q=2).** -/
theorem cell118_118_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK118) e = true)
    (h : ↥(reps (⟨118, by decide⟩ : Fin 148))) :
    species (reps (⟨118, by decide⟩ : Fin 148)) h (basisElt (reps rK118) (charOfVec2 rK118 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK118 e (h : Coordinate 2) T118_118_2 i :=
  species_entry_eq_sum rK118 ⟨118, by decide⟩ e heK h T118_118_2 hfix118_118_2 hinj118_118_2 hcardT118_118_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨118, by decide⟩) (reps rK118) (T118_118_2 i) (hfix118_118_2 i) h)

end Q2

end LeanDring.P5Presentation
