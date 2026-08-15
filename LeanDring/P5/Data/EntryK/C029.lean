/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, K-strata data (5^4 stratum, rK 120-121): certified per-cell species-entry instantiations, both
twins.

Covers K-classes 120, 121 (order-5^4 K, |R|=5).  For each nonzero `H`-column
(`(G/K)^H ≠ ∅`), the full coset transversal `R120..` and each `H`-fixed
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

/-! # K-class rK = 120  (|G/K| = 5) -/

def rK120 : Fin 148 := ⟨120, by decide⟩

def R120list : List Coordinates := [(0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0)]
def R120 : Fin 5 → Coordinate 1 := fun i => R120list.getD i.val (0,0,0,0,0)

theorem hpxR120 : Function.Injective (fun i => reduceAux 1 (basisAt rK120) (R120 i)) := by decide
theorem hcardq120 : Nat.card (Coordinate 1 ⧸ reps rK120) = 5 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (120, 0): |T| = 5 -/

def T120_0list : List Coordinates := [(0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0)]
def T120_0 : Fin 5 → Coordinate 1 := fun i => T120_0list.getD i.val (0,0,0,0,0)

theorem hfix120_0 : ∀ i, ((T120_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120) :=
  repsFix_of_siftB rK120 ⟨0, by decide⟩ T120_0 (by decide)

theorem hinj120_0 : Function.Injective
    (fun i => ((T120_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)) :=
  repsInj_of_reduceAux rK120 T120_0 (by decide)

theorem hcardT120_0 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK120 ⟨0, by decide⟩ R120 hpxR120 hcardq120 (by decide)).symm

/-- **Cell (120, 0).** -/
theorem cell120_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK120) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK120 e (h : Coordinate 1) T120_0 i :=
  species_entry_eq_sum rK120 ⟨0, by decide⟩ e heK h T120_0 hfix120_0 hinj120_0 hcardT120_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK120) (T120_0 i) (hfix120_0 i) h)

/-! ## Cell (120, 1): |T| = 5 -/

def T120_1list : List Coordinates := [(0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0)]
def T120_1 : Fin 5 → Coordinate 1 := fun i => T120_1list.getD i.val (0,0,0,0,0)

theorem hfix120_1 : ∀ i, ((T120_1 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120) :=
  repsFix_of_siftB rK120 ⟨1, by decide⟩ T120_1 (by decide)

theorem hinj120_1 : Function.Injective
    (fun i => ((T120_1 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)) :=
  repsInj_of_reduceAux rK120 T120_1 (by decide)

theorem hcardT120_1 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK120 ⟨1, by decide⟩ R120 hpxR120 hcardq120 (by decide)).symm

/-- **Cell (120, 1).** -/
theorem cell120_1 (e : List (ZMod 25)) (heK : charOK (basisAt rK120) e = true)
    (h : ↥(reps (⟨1, by decide⟩ : Fin 148))) :
    species (reps (⟨1, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK120 e (h : Coordinate 1) T120_1 i :=
  species_entry_eq_sum rK120 ⟨1, by decide⟩ e heK h T120_1 hfix120_1 hinj120_1 hcardT120_1
    (fun i => conj_mem_of_fixedPoints (reps ⟨1, by decide⟩) (reps rK120) (T120_1 i) (hfix120_1 i) h)

/-! ## Cell (120, 6): |T| = 5 -/

def T120_6list : List Coordinates := [(0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0)]
def T120_6 : Fin 5 → Coordinate 1 := fun i => T120_6list.getD i.val (0,0,0,0,0)

theorem hfix120_6 : ∀ i, ((T120_6 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120) :=
  repsFix_of_siftB rK120 ⟨6, by decide⟩ T120_6 (by decide)

theorem hinj120_6 : Function.Injective
    (fun i => ((T120_6 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)) :=
  repsInj_of_reduceAux rK120 T120_6 (by decide)

theorem hcardT120_6 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK120 ⟨6, by decide⟩ R120 hpxR120 hcardq120 (by decide)).symm

/-- **Cell (120, 6).** -/
theorem cell120_6 (e : List (ZMod 25)) (heK : charOK (basisAt rK120) e = true)
    (h : ↥(reps (⟨6, by decide⟩ : Fin 148))) :
    species (reps (⟨6, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK120 e (h : Coordinate 1) T120_6 i :=
  species_entry_eq_sum rK120 ⟨6, by decide⟩ e heK h T120_6 hfix120_6 hinj120_6 hcardT120_6
    (fun i => conj_mem_of_fixedPoints (reps ⟨6, by decide⟩) (reps rK120) (T120_6 i) (hfix120_6 i) h)

/-! ## Cell (120, 7): |T| = 5 -/

def T120_7list : List Coordinates := [(0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0)]
def T120_7 : Fin 5 → Coordinate 1 := fun i => T120_7list.getD i.val (0,0,0,0,0)

theorem hfix120_7 : ∀ i, ((T120_7 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120) :=
  repsFix_of_siftB rK120 ⟨7, by decide⟩ T120_7 (by decide)

theorem hinj120_7 : Function.Injective
    (fun i => ((T120_7 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)) :=
  repsInj_of_reduceAux rK120 T120_7 (by decide)

theorem hcardT120_7 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK120 ⟨7, by decide⟩ R120 hpxR120 hcardq120 (by decide)).symm

/-- **Cell (120, 7).** -/
theorem cell120_7 (e : List (ZMod 25)) (heK : charOK (basisAt rK120) e = true)
    (h : ↥(reps (⟨7, by decide⟩ : Fin 148))) :
    species (reps (⟨7, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK120 e (h : Coordinate 1) T120_7 i :=
  species_entry_eq_sum rK120 ⟨7, by decide⟩ e heK h T120_7 hfix120_7 hinj120_7 hcardT120_7
    (fun i => conj_mem_of_fixedPoints (reps ⟨7, by decide⟩) (reps rK120) (T120_7 i) (hfix120_7 i) h)

/-! ## Cell (120, 8): |T| = 5 -/

def T120_8list : List Coordinates := [(0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0)]
def T120_8 : Fin 5 → Coordinate 1 := fun i => T120_8list.getD i.val (0,0,0,0,0)

theorem hfix120_8 : ∀ i, ((T120_8 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120) :=
  repsFix_of_siftB rK120 ⟨8, by decide⟩ T120_8 (by decide)

theorem hinj120_8 : Function.Injective
    (fun i => ((T120_8 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)) :=
  repsInj_of_reduceAux rK120 T120_8 (by decide)

theorem hcardT120_8 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK120 ⟨8, by decide⟩ R120 hpxR120 hcardq120 (by decide)).symm

/-- **Cell (120, 8).** -/
theorem cell120_8 (e : List (ZMod 25)) (heK : charOK (basisAt rK120) e = true)
    (h : ↥(reps (⟨8, by decide⟩ : Fin 148))) :
    species (reps (⟨8, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK120 e (h : Coordinate 1) T120_8 i :=
  species_entry_eq_sum rK120 ⟨8, by decide⟩ e heK h T120_8 hfix120_8 hinj120_8 hcardT120_8
    (fun i => conj_mem_of_fixedPoints (reps ⟨8, by decide⟩) (reps rK120) (T120_8 i) (hfix120_8 i) h)

/-! ## Cell (120, 9): |T| = 5 -/

def T120_9list : List Coordinates := [(0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0)]
def T120_9 : Fin 5 → Coordinate 1 := fun i => T120_9list.getD i.val (0,0,0,0,0)

theorem hfix120_9 : ∀ i, ((T120_9 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120) :=
  repsFix_of_siftB rK120 ⟨9, by decide⟩ T120_9 (by decide)

theorem hinj120_9 : Function.Injective
    (fun i => ((T120_9 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)) :=
  repsInj_of_reduceAux rK120 T120_9 (by decide)

theorem hcardT120_9 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK120 ⟨9, by decide⟩ R120 hpxR120 hcardq120 (by decide)).symm

/-- **Cell (120, 9).** -/
theorem cell120_9 (e : List (ZMod 25)) (heK : charOK (basisAt rK120) e = true)
    (h : ↥(reps (⟨9, by decide⟩ : Fin 148))) :
    species (reps (⟨9, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK120 e (h : Coordinate 1) T120_9 i :=
  species_entry_eq_sum rK120 ⟨9, by decide⟩ e heK h T120_9 hfix120_9 hinj120_9 hcardT120_9
    (fun i => conj_mem_of_fixedPoints (reps ⟨9, by decide⟩) (reps rK120) (T120_9 i) (hfix120_9 i) h)

/-! ## Cell (120, 10): |T| = 5 -/

def T120_10list : List Coordinates := [(0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0)]
def T120_10 : Fin 5 → Coordinate 1 := fun i => T120_10list.getD i.val (0,0,0,0,0)

theorem hfix120_10 : ∀ i, ((T120_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120) :=
  repsFix_of_siftB rK120 ⟨10, by decide⟩ T120_10 (by decide)

theorem hinj120_10 : Function.Injective
    (fun i => ((T120_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)) :=
  repsInj_of_reduceAux rK120 T120_10 (by decide)

theorem hcardT120_10 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK120 ⟨10, by decide⟩ R120 hpxR120 hcardq120 (by decide)).symm

/-- **Cell (120, 10).** -/
theorem cell120_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK120) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK120 e (h : Coordinate 1) T120_10 i :=
  species_entry_eq_sum rK120 ⟨10, by decide⟩ e heK h T120_10 hfix120_10 hinj120_10 hcardT120_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK120) (T120_10 i) (hfix120_10 i) h)

/-! ## Cell (120, 12): |T| = 5 -/

def T120_12list : List Coordinates := [(0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0)]
def T120_12 : Fin 5 → Coordinate 1 := fun i => T120_12list.getD i.val (0,0,0,0,0)

theorem hfix120_12 : ∀ i, ((T120_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120) :=
  repsFix_of_siftB rK120 ⟨12, by decide⟩ T120_12 (by decide)

theorem hinj120_12 : Function.Injective
    (fun i => ((T120_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)) :=
  repsInj_of_reduceAux rK120 T120_12 (by decide)

theorem hcardT120_12 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK120 ⟨12, by decide⟩ R120 hpxR120 hcardq120 (by decide)).symm

/-- **Cell (120, 12).** -/
theorem cell120_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK120) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK120 e (h : Coordinate 1) T120_12 i :=
  species_entry_eq_sum rK120 ⟨12, by decide⟩ e heK h T120_12 hfix120_12 hinj120_12 hcardT120_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK120) (T120_12 i) (hfix120_12 i) h)

/-! ## Cell (120, 13): |T| = 5 -/

def T120_13list : List Coordinates := [(0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0)]
def T120_13 : Fin 5 → Coordinate 1 := fun i => T120_13list.getD i.val (0,0,0,0,0)

theorem hfix120_13 : ∀ i, ((T120_13 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120) :=
  repsFix_of_siftB rK120 ⟨13, by decide⟩ T120_13 (by decide)

theorem hinj120_13 : Function.Injective
    (fun i => ((T120_13 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)) :=
  repsInj_of_reduceAux rK120 T120_13 (by decide)

theorem hcardT120_13 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK120 ⟨13, by decide⟩ R120 hpxR120 hcardq120 (by decide)).symm

/-- **Cell (120, 13).** -/
theorem cell120_13 (e : List (ZMod 25)) (heK : charOK (basisAt rK120) e = true)
    (h : ↥(reps (⟨13, by decide⟩ : Fin 148))) :
    species (reps (⟨13, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK120 e (h : Coordinate 1) T120_13 i :=
  species_entry_eq_sum rK120 ⟨13, by decide⟩ e heK h T120_13 hfix120_13 hinj120_13 hcardT120_13
    (fun i => conj_mem_of_fixedPoints (reps ⟨13, by decide⟩) (reps rK120) (T120_13 i) (hfix120_13 i) h)

/-! ## Cell (120, 19): |T| = 5 -/

def T120_19list : List Coordinates := [(0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0)]
def T120_19 : Fin 5 → Coordinate 1 := fun i => T120_19list.getD i.val (0,0,0,0,0)

theorem hfix120_19 : ∀ i, ((T120_19 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120) :=
  repsFix_of_siftB rK120 ⟨19, by decide⟩ T120_19 (by decide)

theorem hinj120_19 : Function.Injective
    (fun i => ((T120_19 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)) :=
  repsInj_of_reduceAux rK120 T120_19 (by decide)

theorem hcardT120_19 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK120 ⟨19, by decide⟩ R120 hpxR120 hcardq120 (by decide)).symm

/-- **Cell (120, 19).** -/
theorem cell120_19 (e : List (ZMod 25)) (heK : charOK (basisAt rK120) e = true)
    (h : ↥(reps (⟨19, by decide⟩ : Fin 148))) :
    species (reps (⟨19, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK120 e (h : Coordinate 1) T120_19 i :=
  species_entry_eq_sum rK120 ⟨19, by decide⟩ e heK h T120_19 hfix120_19 hinj120_19 hcardT120_19
    (fun i => conj_mem_of_fixedPoints (reps ⟨19, by decide⟩) (reps rK120) (T120_19 i) (hfix120_19 i) h)

/-! ## Cell (120, 24): |T| = 5 -/

def T120_24list : List Coordinates := [(0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0)]
def T120_24 : Fin 5 → Coordinate 1 := fun i => T120_24list.getD i.val (0,0,0,0,0)

theorem hfix120_24 : ∀ i, ((T120_24 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120) :=
  repsFix_of_siftB rK120 ⟨24, by decide⟩ T120_24 (by decide)

theorem hinj120_24 : Function.Injective
    (fun i => ((T120_24 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)) :=
  repsInj_of_reduceAux rK120 T120_24 (by decide)

theorem hcardT120_24 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK120 ⟨24, by decide⟩ R120 hpxR120 hcardq120 (by decide)).symm

/-- **Cell (120, 24).** -/
theorem cell120_24 (e : List (ZMod 25)) (heK : charOK (basisAt rK120) e = true)
    (h : ↥(reps (⟨24, by decide⟩ : Fin 148))) :
    species (reps (⟨24, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK120 e (h : Coordinate 1) T120_24 i :=
  species_entry_eq_sum rK120 ⟨24, by decide⟩ e heK h T120_24 hfix120_24 hinj120_24 hcardT120_24
    (fun i => conj_mem_of_fixedPoints (reps ⟨24, by decide⟩) (reps rK120) (T120_24 i) (hfix120_24 i) h)

/-! ## Cell (120, 25): |T| = 5 -/

def T120_25list : List Coordinates := [(0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0)]
def T120_25 : Fin 5 → Coordinate 1 := fun i => T120_25list.getD i.val (0,0,0,0,0)

theorem hfix120_25 : ∀ i, ((T120_25 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120) :=
  repsFix_of_siftB rK120 ⟨25, by decide⟩ T120_25 (by decide)

theorem hinj120_25 : Function.Injective
    (fun i => ((T120_25 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)) :=
  repsInj_of_reduceAux rK120 T120_25 (by decide)

theorem hcardT120_25 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK120 ⟨25, by decide⟩ R120 hpxR120 hcardq120 (by decide)).symm

/-- **Cell (120, 25).** -/
theorem cell120_25 (e : List (ZMod 25)) (heK : charOK (basisAt rK120) e = true)
    (h : ↥(reps (⟨25, by decide⟩ : Fin 148))) :
    species (reps (⟨25, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK120 e (h : Coordinate 1) T120_25 i :=
  species_entry_eq_sum rK120 ⟨25, by decide⟩ e heK h T120_25 hfix120_25 hinj120_25 hcardT120_25
    (fun i => conj_mem_of_fixedPoints (reps ⟨25, by decide⟩) (reps rK120) (T120_25 i) (hfix120_25 i) h)

/-! ## Cell (120, 26): |T| = 5 -/

def T120_26list : List Coordinates := [(0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0)]
def T120_26 : Fin 5 → Coordinate 1 := fun i => T120_26list.getD i.val (0,0,0,0,0)

theorem hfix120_26 : ∀ i, ((T120_26 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120) :=
  repsFix_of_siftB rK120 ⟨26, by decide⟩ T120_26 (by decide)

theorem hinj120_26 : Function.Injective
    (fun i => ((T120_26 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)) :=
  repsInj_of_reduceAux rK120 T120_26 (by decide)

theorem hcardT120_26 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK120 ⟨26, by decide⟩ R120 hpxR120 hcardq120 (by decide)).symm

/-- **Cell (120, 26).** -/
theorem cell120_26 (e : List (ZMod 25)) (heK : charOK (basisAt rK120) e = true)
    (h : ↥(reps (⟨26, by decide⟩ : Fin 148))) :
    species (reps (⟨26, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK120 e (h : Coordinate 1) T120_26 i :=
  species_entry_eq_sum rK120 ⟨26, by decide⟩ e heK h T120_26 hfix120_26 hinj120_26 hcardT120_26
    (fun i => conj_mem_of_fixedPoints (reps ⟨26, by decide⟩) (reps rK120) (T120_26 i) (hfix120_26 i) h)

/-! ## Cell (120, 27): |T| = 5 -/

def T120_27list : List Coordinates := [(0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0)]
def T120_27 : Fin 5 → Coordinate 1 := fun i => T120_27list.getD i.val (0,0,0,0,0)

theorem hfix120_27 : ∀ i, ((T120_27 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120) :=
  repsFix_of_siftB rK120 ⟨27, by decide⟩ T120_27 (by decide)

theorem hinj120_27 : Function.Injective
    (fun i => ((T120_27 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)) :=
  repsInj_of_reduceAux rK120 T120_27 (by decide)

theorem hcardT120_27 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK120 ⟨27, by decide⟩ R120 hpxR120 hcardq120 (by decide)).symm

/-- **Cell (120, 27).** -/
theorem cell120_27 (e : List (ZMod 25)) (heK : charOK (basisAt rK120) e = true)
    (h : ↥(reps (⟨27, by decide⟩ : Fin 148))) :
    species (reps (⟨27, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK120 e (h : Coordinate 1) T120_27 i :=
  species_entry_eq_sum rK120 ⟨27, by decide⟩ e heK h T120_27 hfix120_27 hinj120_27 hcardT120_27
    (fun i => conj_mem_of_fixedPoints (reps ⟨27, by decide⟩) (reps rK120) (T120_27 i) (hfix120_27 i) h)

/-! ## Cell (120, 32): |T| = 5 -/

def T120_32list : List Coordinates := [(0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0)]
def T120_32 : Fin 5 → Coordinate 1 := fun i => T120_32list.getD i.val (0,0,0,0,0)

theorem hfix120_32 : ∀ i, ((T120_32 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120) :=
  repsFix_of_siftB rK120 ⟨32, by decide⟩ T120_32 (by decide)

theorem hinj120_32 : Function.Injective
    (fun i => ((T120_32 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)) :=
  repsInj_of_reduceAux rK120 T120_32 (by decide)

theorem hcardT120_32 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK120 ⟨32, by decide⟩ R120 hpxR120 hcardq120 (by decide)).symm

/-- **Cell (120, 32).** -/
theorem cell120_32 (e : List (ZMod 25)) (heK : charOK (basisAt rK120) e = true)
    (h : ↥(reps (⟨32, by decide⟩ : Fin 148))) :
    species (reps (⟨32, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK120 e (h : Coordinate 1) T120_32 i :=
  species_entry_eq_sum rK120 ⟨32, by decide⟩ e heK h T120_32 hfix120_32 hinj120_32 hcardT120_32
    (fun i => conj_mem_of_fixedPoints (reps ⟨32, by decide⟩) (reps rK120) (T120_32 i) (hfix120_32 i) h)

/-! ## Cell (120, 37): |T| = 5 -/

def T120_37list : List Coordinates := [(0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0)]
def T120_37 : Fin 5 → Coordinate 1 := fun i => T120_37list.getD i.val (0,0,0,0,0)

theorem hfix120_37 : ∀ i, ((T120_37 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120) :=
  repsFix_of_siftB rK120 ⟨37, by decide⟩ T120_37 (by decide)

theorem hinj120_37 : Function.Injective
    (fun i => ((T120_37 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)) :=
  repsInj_of_reduceAux rK120 T120_37 (by decide)

theorem hcardT120_37 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK120 ⟨37, by decide⟩ R120 hpxR120 hcardq120 (by decide)).symm

/-- **Cell (120, 37).** -/
theorem cell120_37 (e : List (ZMod 25)) (heK : charOK (basisAt rK120) e = true)
    (h : ↥(reps (⟨37, by decide⟩ : Fin 148))) :
    species (reps (⟨37, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK120 e (h : Coordinate 1) T120_37 i :=
  species_entry_eq_sum rK120 ⟨37, by decide⟩ e heK h T120_37 hfix120_37 hinj120_37 hcardT120_37
    (fun i => conj_mem_of_fixedPoints (reps ⟨37, by decide⟩) (reps rK120) (T120_37 i) (hfix120_37 i) h)

/-! ## Cell (120, 42): |T| = 5 -/

def T120_42list : List Coordinates := [(0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0)]
def T120_42 : Fin 5 → Coordinate 1 := fun i => T120_42list.getD i.val (0,0,0,0,0)

theorem hfix120_42 : ∀ i, ((T120_42 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120) :=
  repsFix_of_siftB rK120 ⟨42, by decide⟩ T120_42 (by decide)

theorem hinj120_42 : Function.Injective
    (fun i => ((T120_42 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)) :=
  repsInj_of_reduceAux rK120 T120_42 (by decide)

theorem hcardT120_42 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK120 ⟨42, by decide⟩ R120 hpxR120 hcardq120 (by decide)).symm

/-- **Cell (120, 42).** -/
theorem cell120_42 (e : List (ZMod 25)) (heK : charOK (basisAt rK120) e = true)
    (h : ↥(reps (⟨42, by decide⟩ : Fin 148))) :
    species (reps (⟨42, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK120 e (h : Coordinate 1) T120_42 i :=
  species_entry_eq_sum rK120 ⟨42, by decide⟩ e heK h T120_42 hfix120_42 hinj120_42 hcardT120_42
    (fun i => conj_mem_of_fixedPoints (reps ⟨42, by decide⟩) (reps rK120) (T120_42 i) (hfix120_42 i) h)

/-! ## Cell (120, 47): |T| = 5 -/

def T120_47list : List Coordinates := [(0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0)]
def T120_47 : Fin 5 → Coordinate 1 := fun i => T120_47list.getD i.val (0,0,0,0,0)

theorem hfix120_47 : ∀ i, ((T120_47 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120) :=
  repsFix_of_siftB rK120 ⟨47, by decide⟩ T120_47 (by decide)

theorem hinj120_47 : Function.Injective
    (fun i => ((T120_47 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)) :=
  repsInj_of_reduceAux rK120 T120_47 (by decide)

theorem hcardT120_47 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK120 ⟨47, by decide⟩ R120 hpxR120 hcardq120 (by decide)).symm

/-- **Cell (120, 47).** -/
theorem cell120_47 (e : List (ZMod 25)) (heK : charOK (basisAt rK120) e = true)
    (h : ↥(reps (⟨47, by decide⟩ : Fin 148))) :
    species (reps (⟨47, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK120 e (h : Coordinate 1) T120_47 i :=
  species_entry_eq_sum rK120 ⟨47, by decide⟩ e heK h T120_47 hfix120_47 hinj120_47 hcardT120_47
    (fun i => conj_mem_of_fixedPoints (reps ⟨47, by decide⟩) (reps rK120) (T120_47 i) (hfix120_47 i) h)

/-! ## Cell (120, 52): |T| = 5 -/

def T120_52list : List Coordinates := [(0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0)]
def T120_52 : Fin 5 → Coordinate 1 := fun i => T120_52list.getD i.val (0,0,0,0,0)

theorem hfix120_52 : ∀ i, ((T120_52 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120) :=
  repsFix_of_siftB rK120 ⟨52, by decide⟩ T120_52 (by decide)

theorem hinj120_52 : Function.Injective
    (fun i => ((T120_52 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)) :=
  repsInj_of_reduceAux rK120 T120_52 (by decide)

theorem hcardT120_52 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK120 ⟨52, by decide⟩ R120 hpxR120 hcardq120 (by decide)).symm

/-- **Cell (120, 52).** -/
theorem cell120_52 (e : List (ZMod 25)) (heK : charOK (basisAt rK120) e = true)
    (h : ↥(reps (⟨52, by decide⟩ : Fin 148))) :
    species (reps (⟨52, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK120 e (h : Coordinate 1) T120_52 i :=
  species_entry_eq_sum rK120 ⟨52, by decide⟩ e heK h T120_52 hfix120_52 hinj120_52 hcardT120_52
    (fun i => conj_mem_of_fixedPoints (reps ⟨52, by decide⟩) (reps rK120) (T120_52 i) (hfix120_52 i) h)

/-! ## Cell (120, 53): |T| = 5 -/

def T120_53list : List Coordinates := [(0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0)]
def T120_53 : Fin 5 → Coordinate 1 := fun i => T120_53list.getD i.val (0,0,0,0,0)

theorem hfix120_53 : ∀ i, ((T120_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120) :=
  repsFix_of_siftB rK120 ⟨53, by decide⟩ T120_53 (by decide)

theorem hinj120_53 : Function.Injective
    (fun i => ((T120_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)) :=
  repsInj_of_reduceAux rK120 T120_53 (by decide)

theorem hcardT120_53 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK120 ⟨53, by decide⟩ R120 hpxR120 hcardq120 (by decide)).symm

/-- **Cell (120, 53).** -/
theorem cell120_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK120) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK120 e (h : Coordinate 1) T120_53 i :=
  species_entry_eq_sum rK120 ⟨53, by decide⟩ e heK h T120_53 hfix120_53 hinj120_53 hcardT120_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK120) (T120_53 i) (hfix120_53 i) h)

/-! ## Cell (120, 75): |T| = 5 -/

def T120_75list : List Coordinates := [(0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0)]
def T120_75 : Fin 5 → Coordinate 1 := fun i => T120_75list.getD i.val (0,0,0,0,0)

theorem hfix120_75 : ∀ i, ((T120_75 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120) :=
  repsFix_of_siftB rK120 ⟨75, by decide⟩ T120_75 (by decide)

theorem hinj120_75 : Function.Injective
    (fun i => ((T120_75 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)) :=
  repsInj_of_reduceAux rK120 T120_75 (by decide)

theorem hcardT120_75 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK120 ⟨75, by decide⟩ R120 hpxR120 hcardq120 (by decide)).symm

/-- **Cell (120, 75).** -/
theorem cell120_75 (e : List (ZMod 25)) (heK : charOK (basisAt rK120) e = true)
    (h : ↥(reps (⟨75, by decide⟩ : Fin 148))) :
    species (reps (⟨75, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK120 e (h : Coordinate 1) T120_75 i :=
  species_entry_eq_sum rK120 ⟨75, by decide⟩ e heK h T120_75 hfix120_75 hinj120_75 hcardT120_75
    (fun i => conj_mem_of_fixedPoints (reps ⟨75, by decide⟩) (reps rK120) (T120_75 i) (hfix120_75 i) h)

/-! ## Cell (120, 76): |T| = 5 -/

def T120_76list : List Coordinates := [(0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0)]
def T120_76 : Fin 5 → Coordinate 1 := fun i => T120_76list.getD i.val (0,0,0,0,0)

theorem hfix120_76 : ∀ i, ((T120_76 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120) :=
  repsFix_of_siftB rK120 ⟨76, by decide⟩ T120_76 (by decide)

theorem hinj120_76 : Function.Injective
    (fun i => ((T120_76 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)) :=
  repsInj_of_reduceAux rK120 T120_76 (by decide)

theorem hcardT120_76 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK120 ⟨76, by decide⟩ R120 hpxR120 hcardq120 (by decide)).symm

/-- **Cell (120, 76).** -/
theorem cell120_76 (e : List (ZMod 25)) (heK : charOK (basisAt rK120) e = true)
    (h : ↥(reps (⟨76, by decide⟩ : Fin 148))) :
    species (reps (⟨76, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK120 e (h : Coordinate 1) T120_76 i :=
  species_entry_eq_sum rK120 ⟨76, by decide⟩ e heK h T120_76 hfix120_76 hinj120_76 hcardT120_76
    (fun i => conj_mem_of_fixedPoints (reps ⟨76, by decide⟩) (reps rK120) (T120_76 i) (hfix120_76 i) h)

/-! ## Cell (120, 77): |T| = 5 -/

def T120_77list : List Coordinates := [(0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0)]
def T120_77 : Fin 5 → Coordinate 1 := fun i => T120_77list.getD i.val (0,0,0,0,0)

theorem hfix120_77 : ∀ i, ((T120_77 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120) :=
  repsFix_of_siftB rK120 ⟨77, by decide⟩ T120_77 (by decide)

theorem hinj120_77 : Function.Injective
    (fun i => ((T120_77 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)) :=
  repsInj_of_reduceAux rK120 T120_77 (by decide)

theorem hcardT120_77 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK120 ⟨77, by decide⟩ R120 hpxR120 hcardq120 (by decide)).symm

/-- **Cell (120, 77).** -/
theorem cell120_77 (e : List (ZMod 25)) (heK : charOK (basisAt rK120) e = true)
    (h : ↥(reps (⟨77, by decide⟩ : Fin 148))) :
    species (reps (⟨77, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK120 e (h : Coordinate 1) T120_77 i :=
  species_entry_eq_sum rK120 ⟨77, by decide⟩ e heK h T120_77 hfix120_77 hinj120_77 hcardT120_77
    (fun i => conj_mem_of_fixedPoints (reps ⟨77, by decide⟩) (reps rK120) (T120_77 i) (hfix120_77 i) h)

/-! ## Cell (120, 78): |T| = 5 -/

def T120_78list : List Coordinates := [(0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0)]
def T120_78 : Fin 5 → Coordinate 1 := fun i => T120_78list.getD i.val (0,0,0,0,0)

theorem hfix120_78 : ∀ i, ((T120_78 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120) :=
  repsFix_of_siftB rK120 ⟨78, by decide⟩ T120_78 (by decide)

theorem hinj120_78 : Function.Injective
    (fun i => ((T120_78 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)) :=
  repsInj_of_reduceAux rK120 T120_78 (by decide)

theorem hcardT120_78 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK120 ⟨78, by decide⟩ R120 hpxR120 hcardq120 (by decide)).symm

/-- **Cell (120, 78).** -/
theorem cell120_78 (e : List (ZMod 25)) (heK : charOK (basisAt rK120) e = true)
    (h : ↥(reps (⟨78, by decide⟩ : Fin 148))) :
    species (reps (⟨78, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK120 e (h : Coordinate 1) T120_78 i :=
  species_entry_eq_sum rK120 ⟨78, by decide⟩ e heK h T120_78 hfix120_78 hinj120_78 hcardT120_78
    (fun i => conj_mem_of_fixedPoints (reps ⟨78, by decide⟩) (reps rK120) (T120_78 i) (hfix120_78 i) h)

/-! ## Cell (120, 79): |T| = 5 -/

def T120_79list : List Coordinates := [(0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0)]
def T120_79 : Fin 5 → Coordinate 1 := fun i => T120_79list.getD i.val (0,0,0,0,0)

theorem hfix120_79 : ∀ i, ((T120_79 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120) :=
  repsFix_of_siftB rK120 ⟨79, by decide⟩ T120_79 (by decide)

theorem hinj120_79 : Function.Injective
    (fun i => ((T120_79 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)) :=
  repsInj_of_reduceAux rK120 T120_79 (by decide)

theorem hcardT120_79 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK120 ⟨79, by decide⟩ R120 hpxR120 hcardq120 (by decide)).symm

/-- **Cell (120, 79).** -/
theorem cell120_79 (e : List (ZMod 25)) (heK : charOK (basisAt rK120) e = true)
    (h : ↥(reps (⟨79, by decide⟩ : Fin 148))) :
    species (reps (⟨79, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK120 e (h : Coordinate 1) T120_79 i :=
  species_entry_eq_sum rK120 ⟨79, by decide⟩ e heK h T120_79 hfix120_79 hinj120_79 hcardT120_79
    (fun i => conj_mem_of_fixedPoints (reps ⟨79, by decide⟩) (reps rK120) (T120_79 i) (hfix120_79 i) h)

/-! ## Cell (120, 80): |T| = 5 -/

def T120_80list : List Coordinates := [(0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0)]
def T120_80 : Fin 5 → Coordinate 1 := fun i => T120_80list.getD i.val (0,0,0,0,0)

theorem hfix120_80 : ∀ i, ((T120_80 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120) :=
  repsFix_of_siftB rK120 ⟨80, by decide⟩ T120_80 (by decide)

theorem hinj120_80 : Function.Injective
    (fun i => ((T120_80 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)) :=
  repsInj_of_reduceAux rK120 T120_80 (by decide)

theorem hcardT120_80 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK120 ⟨80, by decide⟩ R120 hpxR120 hcardq120 (by decide)).symm

/-- **Cell (120, 80).** -/
theorem cell120_80 (e : List (ZMod 25)) (heK : charOK (basisAt rK120) e = true)
    (h : ↥(reps (⟨80, by decide⟩ : Fin 148))) :
    species (reps (⟨80, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK120 e (h : Coordinate 1) T120_80 i :=
  species_entry_eq_sum rK120 ⟨80, by decide⟩ e heK h T120_80 hfix120_80 hinj120_80 hcardT120_80
    (fun i => conj_mem_of_fixedPoints (reps ⟨80, by decide⟩) (reps rK120) (T120_80 i) (hfix120_80 i) h)

/-! ## Cell (120, 94): |T| = 5 -/

def T120_94list : List Coordinates := [(0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0)]
def T120_94 : Fin 5 → Coordinate 1 := fun i => T120_94list.getD i.val (0,0,0,0,0)

theorem hfix120_94 : ∀ i, ((T120_94 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120) :=
  repsFix_of_siftB rK120 ⟨94, by decide⟩ T120_94 (by decide)

theorem hinj120_94 : Function.Injective
    (fun i => ((T120_94 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)) :=
  repsInj_of_reduceAux rK120 T120_94 (by decide)

theorem hcardT120_94 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK120 ⟨94, by decide⟩ R120 hpxR120 hcardq120 (by decide)).symm

/-- **Cell (120, 94).** -/
theorem cell120_94 (e : List (ZMod 25)) (heK : charOK (basisAt rK120) e = true)
    (h : ↥(reps (⟨94, by decide⟩ : Fin 148))) :
    species (reps (⟨94, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK120 e (h : Coordinate 1) T120_94 i :=
  species_entry_eq_sum rK120 ⟨94, by decide⟩ e heK h T120_94 hfix120_94 hinj120_94 hcardT120_94
    (fun i => conj_mem_of_fixedPoints (reps ⟨94, by decide⟩) (reps rK120) (T120_94 i) (hfix120_94 i) h)

/-! ## Cell (120, 99): |T| = 5 -/

def T120_99list : List Coordinates := [(0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0)]
def T120_99 : Fin 5 → Coordinate 1 := fun i => T120_99list.getD i.val (0,0,0,0,0)

theorem hfix120_99 : ∀ i, ((T120_99 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120) :=
  repsFix_of_siftB rK120 ⟨99, by decide⟩ T120_99 (by decide)

theorem hinj120_99 : Function.Injective
    (fun i => ((T120_99 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)) :=
  repsInj_of_reduceAux rK120 T120_99 (by decide)

theorem hcardT120_99 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK120 ⟨99, by decide⟩ R120 hpxR120 hcardq120 (by decide)).symm

/-- **Cell (120, 99).** -/
theorem cell120_99 (e : List (ZMod 25)) (heK : charOK (basisAt rK120) e = true)
    (h : ↥(reps (⟨99, by decide⟩ : Fin 148))) :
    species (reps (⟨99, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK120 e (h : Coordinate 1) T120_99 i :=
  species_entry_eq_sum rK120 ⟨99, by decide⟩ e heK h T120_99 hfix120_99 hinj120_99 hcardT120_99
    (fun i => conj_mem_of_fixedPoints (reps ⟨99, by decide⟩) (reps rK120) (T120_99 i) (hfix120_99 i) h)

/-! ## Cell (120, 104): |T| = 5 -/

def T120_104list : List Coordinates := [(0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0)]
def T120_104 : Fin 5 → Coordinate 1 := fun i => T120_104list.getD i.val (0,0,0,0,0)

theorem hfix120_104 : ∀ i, ((T120_104 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120) :=
  repsFix_of_siftB rK120 ⟨104, by decide⟩ T120_104 (by decide)

theorem hinj120_104 : Function.Injective
    (fun i => ((T120_104 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)) :=
  repsInj_of_reduceAux rK120 T120_104 (by decide)

theorem hcardT120_104 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK120 ⟨104, by decide⟩ R120 hpxR120 hcardq120 (by decide)).symm

/-- **Cell (120, 104).** -/
theorem cell120_104 (e : List (ZMod 25)) (heK : charOK (basisAt rK120) e = true)
    (h : ↥(reps (⟨104, by decide⟩ : Fin 148))) :
    species (reps (⟨104, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK120 e (h : Coordinate 1) T120_104 i :=
  species_entry_eq_sum rK120 ⟨104, by decide⟩ e heK h T120_104 hfix120_104 hinj120_104 hcardT120_104
    (fun i => conj_mem_of_fixedPoints (reps ⟨104, by decide⟩) (reps rK120) (T120_104 i) (hfix120_104 i) h)

/-! ## Cell (120, 109): |T| = 5 -/

def T120_109list : List Coordinates := [(0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0)]
def T120_109 : Fin 5 → Coordinate 1 := fun i => T120_109list.getD i.val (0,0,0,0,0)

theorem hfix120_109 : ∀ i, ((T120_109 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120) :=
  repsFix_of_siftB rK120 ⟨109, by decide⟩ T120_109 (by decide)

theorem hinj120_109 : Function.Injective
    (fun i => ((T120_109 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)) :=
  repsInj_of_reduceAux rK120 T120_109 (by decide)

theorem hcardT120_109 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK120 ⟨109, by decide⟩ R120 hpxR120 hcardq120 (by decide)).symm

/-- **Cell (120, 109).** -/
theorem cell120_109 (e : List (ZMod 25)) (heK : charOK (basisAt rK120) e = true)
    (h : ↥(reps (⟨109, by decide⟩ : Fin 148))) :
    species (reps (⟨109, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK120 e (h : Coordinate 1) T120_109 i :=
  species_entry_eq_sum rK120 ⟨109, by decide⟩ e heK h T120_109 hfix120_109 hinj120_109 hcardT120_109
    (fun i => conj_mem_of_fixedPoints (reps ⟨109, by decide⟩) (reps rK120) (T120_109 i) (hfix120_109 i) h)

/-! ## Cell (120, 114): |T| = 5 -/

def T120_114list : List Coordinates := [(0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0)]
def T120_114 : Fin 5 → Coordinate 1 := fun i => T120_114list.getD i.val (0,0,0,0,0)

theorem hfix120_114 : ∀ i, ((T120_114 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120) :=
  repsFix_of_siftB rK120 ⟨114, by decide⟩ T120_114 (by decide)

theorem hinj120_114 : Function.Injective
    (fun i => ((T120_114 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)) :=
  repsInj_of_reduceAux rK120 T120_114 (by decide)

theorem hcardT120_114 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK120 ⟨114, by decide⟩ R120 hpxR120 hcardq120 (by decide)).symm

/-- **Cell (120, 114).** -/
theorem cell120_114 (e : List (ZMod 25)) (heK : charOK (basisAt rK120) e = true)
    (h : ↥(reps (⟨114, by decide⟩ : Fin 148))) :
    species (reps (⟨114, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK120 e (h : Coordinate 1) T120_114 i :=
  species_entry_eq_sum rK120 ⟨114, by decide⟩ e heK h T120_114 hfix120_114 hinj120_114 hcardT120_114
    (fun i => conj_mem_of_fixedPoints (reps ⟨114, by decide⟩) (reps rK120) (T120_114 i) (hfix120_114 i) h)

/-! ## Cell (120, 120): |T| = 5 -/

def T120_120list : List Coordinates := [(0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0)]
def T120_120 : Fin 5 → Coordinate 1 := fun i => T120_120list.getD i.val (0,0,0,0,0)

theorem hfix120_120 : ∀ i, ((T120_120 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120) :=
  repsFix_of_siftB rK120 ⟨120, by decide⟩ T120_120 (by decide)

theorem hinj120_120 : Function.Injective
    (fun i => ((T120_120 i : Coordinate 1) : Coordinate 1 ⧸ reps rK120)) :=
  repsInj_of_reduceAux rK120 T120_120 (by decide)

theorem hcardT120_120 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK120 ⟨120, by decide⟩ R120 hpxR120 hcardq120 (by decide)).symm

/-- **Cell (120, 120).** -/
theorem cell120_120 (e : List (ZMod 25)) (heK : charOK (basisAt rK120) e = true)
    (h : ↥(reps (⟨120, by decide⟩ : Fin 148))) :
    species (reps (⟨120, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK120 e (h : Coordinate 1) T120_120 i :=
  species_entry_eq_sum rK120 ⟨120, by decide⟩ e heK h T120_120 hfix120_120 hinj120_120 hcardT120_120
    (fun i => conj_mem_of_fixedPoints (reps ⟨120, by decide⟩) (reps rK120) (T120_120 i) (hfix120_120 i) h)

namespace Q2

def R120_2 : Fin 5 → Coordinate 2 := fun i => R120list.getD i.val (0,0,0,0,0)
theorem hpxR120_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK120) (R120_2 i)) := by decide
theorem hcardq120_2 : Nat.card (Coordinate 2 ⧸ reps rK120) = 5 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (120, 0) twin -/

def T120_0_2 : Fin 5 → Coordinate 2 := fun i => T120_0list.getD i.val (0,0,0,0,0)

theorem hfix120_0_2 : ∀ i, ((T120_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120) :=
  repsFix_of_siftB2 rK120 ⟨0, by decide⟩ T120_0_2 (by decide)

theorem hinj120_0_2 : Function.Injective
    (fun i => ((T120_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)) :=
  repsInj_of_reduceAux2 rK120 T120_0_2 (by decide)

theorem hcardT120_0_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK120 ⟨0, by decide⟩ R120_2 hpxR120_2 hcardq120_2 (by decide)).symm

/-- **Cell (120, 0) twin (q=2).** -/
theorem cell120_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK120) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec2 rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK120 e (h : Coordinate 2) T120_0_2 i :=
  species_entry_eq_sum rK120 ⟨0, by decide⟩ e heK h T120_0_2 hfix120_0_2 hinj120_0_2 hcardT120_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK120) (T120_0_2 i) (hfix120_0_2 i) h)

/-! ### Cell (120, 1) twin -/

def T120_1_2 : Fin 5 → Coordinate 2 := fun i => T120_1list.getD i.val (0,0,0,0,0)

theorem hfix120_1_2 : ∀ i, ((T120_1_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120) :=
  repsFix_of_siftB2 rK120 ⟨1, by decide⟩ T120_1_2 (by decide)

theorem hinj120_1_2 : Function.Injective
    (fun i => ((T120_1_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)) :=
  repsInj_of_reduceAux2 rK120 T120_1_2 (by decide)

theorem hcardT120_1_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK120 ⟨1, by decide⟩ R120_2 hpxR120_2 hcardq120_2 (by decide)).symm

/-- **Cell (120, 1) twin (q=2).** -/
theorem cell120_1_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK120) e = true)
    (h : ↥(reps (⟨1, by decide⟩ : Fin 148))) :
    species (reps (⟨1, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec2 rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK120 e (h : Coordinate 2) T120_1_2 i :=
  species_entry_eq_sum rK120 ⟨1, by decide⟩ e heK h T120_1_2 hfix120_1_2 hinj120_1_2 hcardT120_1_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨1, by decide⟩) (reps rK120) (T120_1_2 i) (hfix120_1_2 i) h)

/-! ### Cell (120, 6) twin -/

def T120_6_2 : Fin 5 → Coordinate 2 := fun i => T120_6list.getD i.val (0,0,0,0,0)

theorem hfix120_6_2 : ∀ i, ((T120_6_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120) :=
  repsFix_of_siftB2 rK120 ⟨6, by decide⟩ T120_6_2 (by decide)

theorem hinj120_6_2 : Function.Injective
    (fun i => ((T120_6_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)) :=
  repsInj_of_reduceAux2 rK120 T120_6_2 (by decide)

theorem hcardT120_6_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK120 ⟨6, by decide⟩ R120_2 hpxR120_2 hcardq120_2 (by decide)).symm

/-- **Cell (120, 6) twin (q=2).** -/
theorem cell120_6_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK120) e = true)
    (h : ↥(reps (⟨6, by decide⟩ : Fin 148))) :
    species (reps (⟨6, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec2 rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK120 e (h : Coordinate 2) T120_6_2 i :=
  species_entry_eq_sum rK120 ⟨6, by decide⟩ e heK h T120_6_2 hfix120_6_2 hinj120_6_2 hcardT120_6_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨6, by decide⟩) (reps rK120) (T120_6_2 i) (hfix120_6_2 i) h)

/-! ### Cell (120, 7) twin -/

def T120_7_2 : Fin 5 → Coordinate 2 := fun i => T120_7list.getD i.val (0,0,0,0,0)

theorem hfix120_7_2 : ∀ i, ((T120_7_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120) :=
  repsFix_of_siftB2 rK120 ⟨7, by decide⟩ T120_7_2 (by decide)

theorem hinj120_7_2 : Function.Injective
    (fun i => ((T120_7_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)) :=
  repsInj_of_reduceAux2 rK120 T120_7_2 (by decide)

theorem hcardT120_7_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK120 ⟨7, by decide⟩ R120_2 hpxR120_2 hcardq120_2 (by decide)).symm

/-- **Cell (120, 7) twin (q=2).** -/
theorem cell120_7_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK120) e = true)
    (h : ↥(reps (⟨7, by decide⟩ : Fin 148))) :
    species (reps (⟨7, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec2 rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK120 e (h : Coordinate 2) T120_7_2 i :=
  species_entry_eq_sum rK120 ⟨7, by decide⟩ e heK h T120_7_2 hfix120_7_2 hinj120_7_2 hcardT120_7_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨7, by decide⟩) (reps rK120) (T120_7_2 i) (hfix120_7_2 i) h)

/-! ### Cell (120, 8) twin -/

def T120_8_2 : Fin 5 → Coordinate 2 := fun i => T120_8list.getD i.val (0,0,0,0,0)

theorem hfix120_8_2 : ∀ i, ((T120_8_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120) :=
  repsFix_of_siftB2 rK120 ⟨8, by decide⟩ T120_8_2 (by decide)

theorem hinj120_8_2 : Function.Injective
    (fun i => ((T120_8_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)) :=
  repsInj_of_reduceAux2 rK120 T120_8_2 (by decide)

theorem hcardT120_8_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK120 ⟨8, by decide⟩ R120_2 hpxR120_2 hcardq120_2 (by decide)).symm

/-- **Cell (120, 8) twin (q=2).** -/
theorem cell120_8_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK120) e = true)
    (h : ↥(reps (⟨8, by decide⟩ : Fin 148))) :
    species (reps (⟨8, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec2 rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK120 e (h : Coordinate 2) T120_8_2 i :=
  species_entry_eq_sum rK120 ⟨8, by decide⟩ e heK h T120_8_2 hfix120_8_2 hinj120_8_2 hcardT120_8_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨8, by decide⟩) (reps rK120) (T120_8_2 i) (hfix120_8_2 i) h)

/-! ### Cell (120, 9) twin -/

def T120_9_2 : Fin 5 → Coordinate 2 := fun i => T120_9list.getD i.val (0,0,0,0,0)

theorem hfix120_9_2 : ∀ i, ((T120_9_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120) :=
  repsFix_of_siftB2 rK120 ⟨9, by decide⟩ T120_9_2 (by decide)

theorem hinj120_9_2 : Function.Injective
    (fun i => ((T120_9_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)) :=
  repsInj_of_reduceAux2 rK120 T120_9_2 (by decide)

theorem hcardT120_9_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK120 ⟨9, by decide⟩ R120_2 hpxR120_2 hcardq120_2 (by decide)).symm

/-- **Cell (120, 9) twin (q=2).** -/
theorem cell120_9_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK120) e = true)
    (h : ↥(reps (⟨9, by decide⟩ : Fin 148))) :
    species (reps (⟨9, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec2 rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK120 e (h : Coordinate 2) T120_9_2 i :=
  species_entry_eq_sum rK120 ⟨9, by decide⟩ e heK h T120_9_2 hfix120_9_2 hinj120_9_2 hcardT120_9_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨9, by decide⟩) (reps rK120) (T120_9_2 i) (hfix120_9_2 i) h)

/-! ### Cell (120, 10) twin -/

def T120_10_2 : Fin 5 → Coordinate 2 := fun i => T120_10list.getD i.val (0,0,0,0,0)

theorem hfix120_10_2 : ∀ i, ((T120_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120) :=
  repsFix_of_siftB2 rK120 ⟨10, by decide⟩ T120_10_2 (by decide)

theorem hinj120_10_2 : Function.Injective
    (fun i => ((T120_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)) :=
  repsInj_of_reduceAux2 rK120 T120_10_2 (by decide)

theorem hcardT120_10_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK120 ⟨10, by decide⟩ R120_2 hpxR120_2 hcardq120_2 (by decide)).symm

/-- **Cell (120, 10) twin (q=2).** -/
theorem cell120_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK120) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec2 rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK120 e (h : Coordinate 2) T120_10_2 i :=
  species_entry_eq_sum rK120 ⟨10, by decide⟩ e heK h T120_10_2 hfix120_10_2 hinj120_10_2 hcardT120_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK120) (T120_10_2 i) (hfix120_10_2 i) h)

/-! ### Cell (120, 12) twin -/

def T120_12_2 : Fin 5 → Coordinate 2 := fun i => T120_12list.getD i.val (0,0,0,0,0)

theorem hfix120_12_2 : ∀ i, ((T120_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120) :=
  repsFix_of_siftB2 rK120 ⟨12, by decide⟩ T120_12_2 (by decide)

theorem hinj120_12_2 : Function.Injective
    (fun i => ((T120_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)) :=
  repsInj_of_reduceAux2 rK120 T120_12_2 (by decide)

theorem hcardT120_12_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK120 ⟨12, by decide⟩ R120_2 hpxR120_2 hcardq120_2 (by decide)).symm

/-- **Cell (120, 12) twin (q=2).** -/
theorem cell120_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK120) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec2 rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK120 e (h : Coordinate 2) T120_12_2 i :=
  species_entry_eq_sum rK120 ⟨12, by decide⟩ e heK h T120_12_2 hfix120_12_2 hinj120_12_2 hcardT120_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK120) (T120_12_2 i) (hfix120_12_2 i) h)

/-! ### Cell (120, 13) twin -/

def T120_13_2 : Fin 5 → Coordinate 2 := fun i => T120_13list.getD i.val (0,0,0,0,0)

theorem hfix120_13_2 : ∀ i, ((T120_13_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120) :=
  repsFix_of_siftB2 rK120 ⟨13, by decide⟩ T120_13_2 (by decide)

theorem hinj120_13_2 : Function.Injective
    (fun i => ((T120_13_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)) :=
  repsInj_of_reduceAux2 rK120 T120_13_2 (by decide)

theorem hcardT120_13_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK120 ⟨13, by decide⟩ R120_2 hpxR120_2 hcardq120_2 (by decide)).symm

/-- **Cell (120, 13) twin (q=2).** -/
theorem cell120_13_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK120) e = true)
    (h : ↥(reps (⟨13, by decide⟩ : Fin 148))) :
    species (reps (⟨13, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec2 rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK120 e (h : Coordinate 2) T120_13_2 i :=
  species_entry_eq_sum rK120 ⟨13, by decide⟩ e heK h T120_13_2 hfix120_13_2 hinj120_13_2 hcardT120_13_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨13, by decide⟩) (reps rK120) (T120_13_2 i) (hfix120_13_2 i) h)

/-! ### Cell (120, 19) twin -/

def T120_19_2 : Fin 5 → Coordinate 2 := fun i => T120_19list.getD i.val (0,0,0,0,0)

theorem hfix120_19_2 : ∀ i, ((T120_19_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120) :=
  repsFix_of_siftB2 rK120 ⟨19, by decide⟩ T120_19_2 (by decide)

theorem hinj120_19_2 : Function.Injective
    (fun i => ((T120_19_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)) :=
  repsInj_of_reduceAux2 rK120 T120_19_2 (by decide)

theorem hcardT120_19_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK120 ⟨19, by decide⟩ R120_2 hpxR120_2 hcardq120_2 (by decide)).symm

/-- **Cell (120, 19) twin (q=2).** -/
theorem cell120_19_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK120) e = true)
    (h : ↥(reps (⟨19, by decide⟩ : Fin 148))) :
    species (reps (⟨19, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec2 rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK120 e (h : Coordinate 2) T120_19_2 i :=
  species_entry_eq_sum rK120 ⟨19, by decide⟩ e heK h T120_19_2 hfix120_19_2 hinj120_19_2 hcardT120_19_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨19, by decide⟩) (reps rK120) (T120_19_2 i) (hfix120_19_2 i) h)

/-! ### Cell (120, 24) twin -/

def T120_24_2 : Fin 5 → Coordinate 2 := fun i => T120_24list.getD i.val (0,0,0,0,0)

theorem hfix120_24_2 : ∀ i, ((T120_24_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120) :=
  repsFix_of_siftB2 rK120 ⟨24, by decide⟩ T120_24_2 (by decide)

theorem hinj120_24_2 : Function.Injective
    (fun i => ((T120_24_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)) :=
  repsInj_of_reduceAux2 rK120 T120_24_2 (by decide)

theorem hcardT120_24_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK120 ⟨24, by decide⟩ R120_2 hpxR120_2 hcardq120_2 (by decide)).symm

/-- **Cell (120, 24) twin (q=2).** -/
theorem cell120_24_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK120) e = true)
    (h : ↥(reps (⟨24, by decide⟩ : Fin 148))) :
    species (reps (⟨24, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec2 rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK120 e (h : Coordinate 2) T120_24_2 i :=
  species_entry_eq_sum rK120 ⟨24, by decide⟩ e heK h T120_24_2 hfix120_24_2 hinj120_24_2 hcardT120_24_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨24, by decide⟩) (reps rK120) (T120_24_2 i) (hfix120_24_2 i) h)

/-! ### Cell (120, 25) twin -/

def T120_25_2 : Fin 5 → Coordinate 2 := fun i => T120_25list.getD i.val (0,0,0,0,0)

theorem hfix120_25_2 : ∀ i, ((T120_25_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120) :=
  repsFix_of_siftB2 rK120 ⟨25, by decide⟩ T120_25_2 (by decide)

theorem hinj120_25_2 : Function.Injective
    (fun i => ((T120_25_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)) :=
  repsInj_of_reduceAux2 rK120 T120_25_2 (by decide)

theorem hcardT120_25_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK120 ⟨25, by decide⟩ R120_2 hpxR120_2 hcardq120_2 (by decide)).symm

/-- **Cell (120, 25) twin (q=2).** -/
theorem cell120_25_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK120) e = true)
    (h : ↥(reps (⟨25, by decide⟩ : Fin 148))) :
    species (reps (⟨25, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec2 rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK120 e (h : Coordinate 2) T120_25_2 i :=
  species_entry_eq_sum rK120 ⟨25, by decide⟩ e heK h T120_25_2 hfix120_25_2 hinj120_25_2 hcardT120_25_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨25, by decide⟩) (reps rK120) (T120_25_2 i) (hfix120_25_2 i) h)

/-! ### Cell (120, 26) twin -/

def T120_26_2 : Fin 5 → Coordinate 2 := fun i => T120_26list.getD i.val (0,0,0,0,0)

theorem hfix120_26_2 : ∀ i, ((T120_26_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120) :=
  repsFix_of_siftB2 rK120 ⟨26, by decide⟩ T120_26_2 (by decide)

theorem hinj120_26_2 : Function.Injective
    (fun i => ((T120_26_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)) :=
  repsInj_of_reduceAux2 rK120 T120_26_2 (by decide)

theorem hcardT120_26_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK120 ⟨26, by decide⟩ R120_2 hpxR120_2 hcardq120_2 (by decide)).symm

/-- **Cell (120, 26) twin (q=2).** -/
theorem cell120_26_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK120) e = true)
    (h : ↥(reps (⟨26, by decide⟩ : Fin 148))) :
    species (reps (⟨26, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec2 rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK120 e (h : Coordinate 2) T120_26_2 i :=
  species_entry_eq_sum rK120 ⟨26, by decide⟩ e heK h T120_26_2 hfix120_26_2 hinj120_26_2 hcardT120_26_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨26, by decide⟩) (reps rK120) (T120_26_2 i) (hfix120_26_2 i) h)

/-! ### Cell (120, 27) twin -/

def T120_27_2 : Fin 5 → Coordinate 2 := fun i => T120_27list.getD i.val (0,0,0,0,0)

theorem hfix120_27_2 : ∀ i, ((T120_27_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120) :=
  repsFix_of_siftB2 rK120 ⟨27, by decide⟩ T120_27_2 (by decide)

theorem hinj120_27_2 : Function.Injective
    (fun i => ((T120_27_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)) :=
  repsInj_of_reduceAux2 rK120 T120_27_2 (by decide)

theorem hcardT120_27_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK120 ⟨27, by decide⟩ R120_2 hpxR120_2 hcardq120_2 (by decide)).symm

/-- **Cell (120, 27) twin (q=2).** -/
theorem cell120_27_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK120) e = true)
    (h : ↥(reps (⟨27, by decide⟩ : Fin 148))) :
    species (reps (⟨27, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec2 rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK120 e (h : Coordinate 2) T120_27_2 i :=
  species_entry_eq_sum rK120 ⟨27, by decide⟩ e heK h T120_27_2 hfix120_27_2 hinj120_27_2 hcardT120_27_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨27, by decide⟩) (reps rK120) (T120_27_2 i) (hfix120_27_2 i) h)

/-! ### Cell (120, 32) twin -/

def T120_32_2 : Fin 5 → Coordinate 2 := fun i => T120_32list.getD i.val (0,0,0,0,0)

theorem hfix120_32_2 : ∀ i, ((T120_32_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120) :=
  repsFix_of_siftB2 rK120 ⟨32, by decide⟩ T120_32_2 (by decide)

theorem hinj120_32_2 : Function.Injective
    (fun i => ((T120_32_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)) :=
  repsInj_of_reduceAux2 rK120 T120_32_2 (by decide)

theorem hcardT120_32_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK120 ⟨32, by decide⟩ R120_2 hpxR120_2 hcardq120_2 (by decide)).symm

/-- **Cell (120, 32) twin (q=2).** -/
theorem cell120_32_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK120) e = true)
    (h : ↥(reps (⟨32, by decide⟩ : Fin 148))) :
    species (reps (⟨32, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec2 rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK120 e (h : Coordinate 2) T120_32_2 i :=
  species_entry_eq_sum rK120 ⟨32, by decide⟩ e heK h T120_32_2 hfix120_32_2 hinj120_32_2 hcardT120_32_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨32, by decide⟩) (reps rK120) (T120_32_2 i) (hfix120_32_2 i) h)

/-! ### Cell (120, 37) twin -/

def T120_37_2 : Fin 5 → Coordinate 2 := fun i => T120_37list.getD i.val (0,0,0,0,0)

theorem hfix120_37_2 : ∀ i, ((T120_37_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120) :=
  repsFix_of_siftB2 rK120 ⟨37, by decide⟩ T120_37_2 (by decide)

theorem hinj120_37_2 : Function.Injective
    (fun i => ((T120_37_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)) :=
  repsInj_of_reduceAux2 rK120 T120_37_2 (by decide)

theorem hcardT120_37_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK120 ⟨37, by decide⟩ R120_2 hpxR120_2 hcardq120_2 (by decide)).symm

/-- **Cell (120, 37) twin (q=2).** -/
theorem cell120_37_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK120) e = true)
    (h : ↥(reps (⟨37, by decide⟩ : Fin 148))) :
    species (reps (⟨37, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec2 rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK120 e (h : Coordinate 2) T120_37_2 i :=
  species_entry_eq_sum rK120 ⟨37, by decide⟩ e heK h T120_37_2 hfix120_37_2 hinj120_37_2 hcardT120_37_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨37, by decide⟩) (reps rK120) (T120_37_2 i) (hfix120_37_2 i) h)

/-! ### Cell (120, 42) twin -/

def T120_42_2 : Fin 5 → Coordinate 2 := fun i => T120_42list.getD i.val (0,0,0,0,0)

theorem hfix120_42_2 : ∀ i, ((T120_42_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120) :=
  repsFix_of_siftB2 rK120 ⟨42, by decide⟩ T120_42_2 (by decide)

theorem hinj120_42_2 : Function.Injective
    (fun i => ((T120_42_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)) :=
  repsInj_of_reduceAux2 rK120 T120_42_2 (by decide)

theorem hcardT120_42_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK120 ⟨42, by decide⟩ R120_2 hpxR120_2 hcardq120_2 (by decide)).symm

/-- **Cell (120, 42) twin (q=2).** -/
theorem cell120_42_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK120) e = true)
    (h : ↥(reps (⟨42, by decide⟩ : Fin 148))) :
    species (reps (⟨42, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec2 rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK120 e (h : Coordinate 2) T120_42_2 i :=
  species_entry_eq_sum rK120 ⟨42, by decide⟩ e heK h T120_42_2 hfix120_42_2 hinj120_42_2 hcardT120_42_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨42, by decide⟩) (reps rK120) (T120_42_2 i) (hfix120_42_2 i) h)

/-! ### Cell (120, 47) twin -/

def T120_47_2 : Fin 5 → Coordinate 2 := fun i => T120_47list.getD i.val (0,0,0,0,0)

theorem hfix120_47_2 : ∀ i, ((T120_47_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120) :=
  repsFix_of_siftB2 rK120 ⟨47, by decide⟩ T120_47_2 (by decide)

theorem hinj120_47_2 : Function.Injective
    (fun i => ((T120_47_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)) :=
  repsInj_of_reduceAux2 rK120 T120_47_2 (by decide)

theorem hcardT120_47_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK120 ⟨47, by decide⟩ R120_2 hpxR120_2 hcardq120_2 (by decide)).symm

/-- **Cell (120, 47) twin (q=2).** -/
theorem cell120_47_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK120) e = true)
    (h : ↥(reps (⟨47, by decide⟩ : Fin 148))) :
    species (reps (⟨47, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec2 rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK120 e (h : Coordinate 2) T120_47_2 i :=
  species_entry_eq_sum rK120 ⟨47, by decide⟩ e heK h T120_47_2 hfix120_47_2 hinj120_47_2 hcardT120_47_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨47, by decide⟩) (reps rK120) (T120_47_2 i) (hfix120_47_2 i) h)

/-! ### Cell (120, 52) twin -/

def T120_52_2 : Fin 5 → Coordinate 2 := fun i => T120_52list.getD i.val (0,0,0,0,0)

theorem hfix120_52_2 : ∀ i, ((T120_52_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120) :=
  repsFix_of_siftB2 rK120 ⟨52, by decide⟩ T120_52_2 (by decide)

theorem hinj120_52_2 : Function.Injective
    (fun i => ((T120_52_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)) :=
  repsInj_of_reduceAux2 rK120 T120_52_2 (by decide)

theorem hcardT120_52_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK120 ⟨52, by decide⟩ R120_2 hpxR120_2 hcardq120_2 (by decide)).symm

/-- **Cell (120, 52) twin (q=2).** -/
theorem cell120_52_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK120) e = true)
    (h : ↥(reps (⟨52, by decide⟩ : Fin 148))) :
    species (reps (⟨52, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec2 rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK120 e (h : Coordinate 2) T120_52_2 i :=
  species_entry_eq_sum rK120 ⟨52, by decide⟩ e heK h T120_52_2 hfix120_52_2 hinj120_52_2 hcardT120_52_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨52, by decide⟩) (reps rK120) (T120_52_2 i) (hfix120_52_2 i) h)

/-! ### Cell (120, 53) twin -/

def T120_53_2 : Fin 5 → Coordinate 2 := fun i => T120_53list.getD i.val (0,0,0,0,0)

theorem hfix120_53_2 : ∀ i, ((T120_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120) :=
  repsFix_of_siftB2 rK120 ⟨53, by decide⟩ T120_53_2 (by decide)

theorem hinj120_53_2 : Function.Injective
    (fun i => ((T120_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)) :=
  repsInj_of_reduceAux2 rK120 T120_53_2 (by decide)

theorem hcardT120_53_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK120 ⟨53, by decide⟩ R120_2 hpxR120_2 hcardq120_2 (by decide)).symm

/-- **Cell (120, 53) twin (q=2).** -/
theorem cell120_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK120) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec2 rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK120 e (h : Coordinate 2) T120_53_2 i :=
  species_entry_eq_sum rK120 ⟨53, by decide⟩ e heK h T120_53_2 hfix120_53_2 hinj120_53_2 hcardT120_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK120) (T120_53_2 i) (hfix120_53_2 i) h)

/-! ### Cell (120, 75) twin -/

def T120_75_2 : Fin 5 → Coordinate 2 := fun i => T120_75list.getD i.val (0,0,0,0,0)

theorem hfix120_75_2 : ∀ i, ((T120_75_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120) :=
  repsFix_of_siftB2 rK120 ⟨75, by decide⟩ T120_75_2 (by decide)

theorem hinj120_75_2 : Function.Injective
    (fun i => ((T120_75_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)) :=
  repsInj_of_reduceAux2 rK120 T120_75_2 (by decide)

theorem hcardT120_75_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK120 ⟨75, by decide⟩ R120_2 hpxR120_2 hcardq120_2 (by decide)).symm

/-- **Cell (120, 75) twin (q=2).** -/
theorem cell120_75_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK120) e = true)
    (h : ↥(reps (⟨75, by decide⟩ : Fin 148))) :
    species (reps (⟨75, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec2 rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK120 e (h : Coordinate 2) T120_75_2 i :=
  species_entry_eq_sum rK120 ⟨75, by decide⟩ e heK h T120_75_2 hfix120_75_2 hinj120_75_2 hcardT120_75_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨75, by decide⟩) (reps rK120) (T120_75_2 i) (hfix120_75_2 i) h)

/-! ### Cell (120, 76) twin -/

def T120_76_2 : Fin 5 → Coordinate 2 := fun i => T120_76list.getD i.val (0,0,0,0,0)

theorem hfix120_76_2 : ∀ i, ((T120_76_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120) :=
  repsFix_of_siftB2 rK120 ⟨76, by decide⟩ T120_76_2 (by decide)

theorem hinj120_76_2 : Function.Injective
    (fun i => ((T120_76_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)) :=
  repsInj_of_reduceAux2 rK120 T120_76_2 (by decide)

theorem hcardT120_76_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK120 ⟨76, by decide⟩ R120_2 hpxR120_2 hcardq120_2 (by decide)).symm

/-- **Cell (120, 76) twin (q=2).** -/
theorem cell120_76_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK120) e = true)
    (h : ↥(reps (⟨76, by decide⟩ : Fin 148))) :
    species (reps (⟨76, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec2 rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK120 e (h : Coordinate 2) T120_76_2 i :=
  species_entry_eq_sum rK120 ⟨76, by decide⟩ e heK h T120_76_2 hfix120_76_2 hinj120_76_2 hcardT120_76_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨76, by decide⟩) (reps rK120) (T120_76_2 i) (hfix120_76_2 i) h)

/-! ### Cell (120, 77) twin -/

def T120_77_2 : Fin 5 → Coordinate 2 := fun i => T120_77list.getD i.val (0,0,0,0,0)

theorem hfix120_77_2 : ∀ i, ((T120_77_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120) :=
  repsFix_of_siftB2 rK120 ⟨77, by decide⟩ T120_77_2 (by decide)

theorem hinj120_77_2 : Function.Injective
    (fun i => ((T120_77_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)) :=
  repsInj_of_reduceAux2 rK120 T120_77_2 (by decide)

theorem hcardT120_77_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK120 ⟨77, by decide⟩ R120_2 hpxR120_2 hcardq120_2 (by decide)).symm

/-- **Cell (120, 77) twin (q=2).** -/
theorem cell120_77_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK120) e = true)
    (h : ↥(reps (⟨77, by decide⟩ : Fin 148))) :
    species (reps (⟨77, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec2 rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK120 e (h : Coordinate 2) T120_77_2 i :=
  species_entry_eq_sum rK120 ⟨77, by decide⟩ e heK h T120_77_2 hfix120_77_2 hinj120_77_2 hcardT120_77_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨77, by decide⟩) (reps rK120) (T120_77_2 i) (hfix120_77_2 i) h)

/-! ### Cell (120, 78) twin -/

def T120_78_2 : Fin 5 → Coordinate 2 := fun i => T120_78list.getD i.val (0,0,0,0,0)

theorem hfix120_78_2 : ∀ i, ((T120_78_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120) :=
  repsFix_of_siftB2 rK120 ⟨78, by decide⟩ T120_78_2 (by decide)

theorem hinj120_78_2 : Function.Injective
    (fun i => ((T120_78_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)) :=
  repsInj_of_reduceAux2 rK120 T120_78_2 (by decide)

theorem hcardT120_78_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK120 ⟨78, by decide⟩ R120_2 hpxR120_2 hcardq120_2 (by decide)).symm

/-- **Cell (120, 78) twin (q=2).** -/
theorem cell120_78_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK120) e = true)
    (h : ↥(reps (⟨78, by decide⟩ : Fin 148))) :
    species (reps (⟨78, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec2 rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK120 e (h : Coordinate 2) T120_78_2 i :=
  species_entry_eq_sum rK120 ⟨78, by decide⟩ e heK h T120_78_2 hfix120_78_2 hinj120_78_2 hcardT120_78_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨78, by decide⟩) (reps rK120) (T120_78_2 i) (hfix120_78_2 i) h)

/-! ### Cell (120, 79) twin -/

def T120_79_2 : Fin 5 → Coordinate 2 := fun i => T120_79list.getD i.val (0,0,0,0,0)

theorem hfix120_79_2 : ∀ i, ((T120_79_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120) :=
  repsFix_of_siftB2 rK120 ⟨79, by decide⟩ T120_79_2 (by decide)

theorem hinj120_79_2 : Function.Injective
    (fun i => ((T120_79_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)) :=
  repsInj_of_reduceAux2 rK120 T120_79_2 (by decide)

theorem hcardT120_79_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK120 ⟨79, by decide⟩ R120_2 hpxR120_2 hcardq120_2 (by decide)).symm

/-- **Cell (120, 79) twin (q=2).** -/
theorem cell120_79_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK120) e = true)
    (h : ↥(reps (⟨79, by decide⟩ : Fin 148))) :
    species (reps (⟨79, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec2 rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK120 e (h : Coordinate 2) T120_79_2 i :=
  species_entry_eq_sum rK120 ⟨79, by decide⟩ e heK h T120_79_2 hfix120_79_2 hinj120_79_2 hcardT120_79_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨79, by decide⟩) (reps rK120) (T120_79_2 i) (hfix120_79_2 i) h)

/-! ### Cell (120, 80) twin -/

def T120_80_2 : Fin 5 → Coordinate 2 := fun i => T120_80list.getD i.val (0,0,0,0,0)

theorem hfix120_80_2 : ∀ i, ((T120_80_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120) :=
  repsFix_of_siftB2 rK120 ⟨80, by decide⟩ T120_80_2 (by decide)

theorem hinj120_80_2 : Function.Injective
    (fun i => ((T120_80_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)) :=
  repsInj_of_reduceAux2 rK120 T120_80_2 (by decide)

theorem hcardT120_80_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK120 ⟨80, by decide⟩ R120_2 hpxR120_2 hcardq120_2 (by decide)).symm

/-- **Cell (120, 80) twin (q=2).** -/
theorem cell120_80_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK120) e = true)
    (h : ↥(reps (⟨80, by decide⟩ : Fin 148))) :
    species (reps (⟨80, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec2 rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK120 e (h : Coordinate 2) T120_80_2 i :=
  species_entry_eq_sum rK120 ⟨80, by decide⟩ e heK h T120_80_2 hfix120_80_2 hinj120_80_2 hcardT120_80_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨80, by decide⟩) (reps rK120) (T120_80_2 i) (hfix120_80_2 i) h)

/-! ### Cell (120, 94) twin -/

def T120_94_2 : Fin 5 → Coordinate 2 := fun i => T120_94list.getD i.val (0,0,0,0,0)

theorem hfix120_94_2 : ∀ i, ((T120_94_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120) :=
  repsFix_of_siftB2 rK120 ⟨94, by decide⟩ T120_94_2 (by decide)

theorem hinj120_94_2 : Function.Injective
    (fun i => ((T120_94_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)) :=
  repsInj_of_reduceAux2 rK120 T120_94_2 (by decide)

theorem hcardT120_94_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK120 ⟨94, by decide⟩ R120_2 hpxR120_2 hcardq120_2 (by decide)).symm

/-- **Cell (120, 94) twin (q=2).** -/
theorem cell120_94_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK120) e = true)
    (h : ↥(reps (⟨94, by decide⟩ : Fin 148))) :
    species (reps (⟨94, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec2 rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK120 e (h : Coordinate 2) T120_94_2 i :=
  species_entry_eq_sum rK120 ⟨94, by decide⟩ e heK h T120_94_2 hfix120_94_2 hinj120_94_2 hcardT120_94_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨94, by decide⟩) (reps rK120) (T120_94_2 i) (hfix120_94_2 i) h)

/-! ### Cell (120, 99) twin -/

def T120_99_2 : Fin 5 → Coordinate 2 := fun i => T120_99list.getD i.val (0,0,0,0,0)

theorem hfix120_99_2 : ∀ i, ((T120_99_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120) :=
  repsFix_of_siftB2 rK120 ⟨99, by decide⟩ T120_99_2 (by decide)

theorem hinj120_99_2 : Function.Injective
    (fun i => ((T120_99_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)) :=
  repsInj_of_reduceAux2 rK120 T120_99_2 (by decide)

theorem hcardT120_99_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK120 ⟨99, by decide⟩ R120_2 hpxR120_2 hcardq120_2 (by decide)).symm

/-- **Cell (120, 99) twin (q=2).** -/
theorem cell120_99_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK120) e = true)
    (h : ↥(reps (⟨99, by decide⟩ : Fin 148))) :
    species (reps (⟨99, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec2 rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK120 e (h : Coordinate 2) T120_99_2 i :=
  species_entry_eq_sum rK120 ⟨99, by decide⟩ e heK h T120_99_2 hfix120_99_2 hinj120_99_2 hcardT120_99_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨99, by decide⟩) (reps rK120) (T120_99_2 i) (hfix120_99_2 i) h)

/-! ### Cell (120, 104) twin -/

def T120_104_2 : Fin 5 → Coordinate 2 := fun i => T120_104list.getD i.val (0,0,0,0,0)

theorem hfix120_104_2 : ∀ i, ((T120_104_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120) :=
  repsFix_of_siftB2 rK120 ⟨104, by decide⟩ T120_104_2 (by decide)

theorem hinj120_104_2 : Function.Injective
    (fun i => ((T120_104_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)) :=
  repsInj_of_reduceAux2 rK120 T120_104_2 (by decide)

theorem hcardT120_104_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK120 ⟨104, by decide⟩ R120_2 hpxR120_2 hcardq120_2 (by decide)).symm

/-- **Cell (120, 104) twin (q=2).** -/
theorem cell120_104_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK120) e = true)
    (h : ↥(reps (⟨104, by decide⟩ : Fin 148))) :
    species (reps (⟨104, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec2 rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK120 e (h : Coordinate 2) T120_104_2 i :=
  species_entry_eq_sum rK120 ⟨104, by decide⟩ e heK h T120_104_2 hfix120_104_2 hinj120_104_2 hcardT120_104_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨104, by decide⟩) (reps rK120) (T120_104_2 i) (hfix120_104_2 i) h)

/-! ### Cell (120, 109) twin -/

def T120_109_2 : Fin 5 → Coordinate 2 := fun i => T120_109list.getD i.val (0,0,0,0,0)

theorem hfix120_109_2 : ∀ i, ((T120_109_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120) :=
  repsFix_of_siftB2 rK120 ⟨109, by decide⟩ T120_109_2 (by decide)

theorem hinj120_109_2 : Function.Injective
    (fun i => ((T120_109_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)) :=
  repsInj_of_reduceAux2 rK120 T120_109_2 (by decide)

theorem hcardT120_109_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK120 ⟨109, by decide⟩ R120_2 hpxR120_2 hcardq120_2 (by decide)).symm

/-- **Cell (120, 109) twin (q=2).** -/
theorem cell120_109_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK120) e = true)
    (h : ↥(reps (⟨109, by decide⟩ : Fin 148))) :
    species (reps (⟨109, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec2 rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK120 e (h : Coordinate 2) T120_109_2 i :=
  species_entry_eq_sum rK120 ⟨109, by decide⟩ e heK h T120_109_2 hfix120_109_2 hinj120_109_2 hcardT120_109_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨109, by decide⟩) (reps rK120) (T120_109_2 i) (hfix120_109_2 i) h)

/-! ### Cell (120, 114) twin -/

def T120_114_2 : Fin 5 → Coordinate 2 := fun i => T120_114list.getD i.val (0,0,0,0,0)

theorem hfix120_114_2 : ∀ i, ((T120_114_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120) :=
  repsFix_of_siftB2 rK120 ⟨114, by decide⟩ T120_114_2 (by decide)

theorem hinj120_114_2 : Function.Injective
    (fun i => ((T120_114_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)) :=
  repsInj_of_reduceAux2 rK120 T120_114_2 (by decide)

theorem hcardT120_114_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK120 ⟨114, by decide⟩ R120_2 hpxR120_2 hcardq120_2 (by decide)).symm

/-- **Cell (120, 114) twin (q=2).** -/
theorem cell120_114_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK120) e = true)
    (h : ↥(reps (⟨114, by decide⟩ : Fin 148))) :
    species (reps (⟨114, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec2 rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK120 e (h : Coordinate 2) T120_114_2 i :=
  species_entry_eq_sum rK120 ⟨114, by decide⟩ e heK h T120_114_2 hfix120_114_2 hinj120_114_2 hcardT120_114_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨114, by decide⟩) (reps rK120) (T120_114_2 i) (hfix120_114_2 i) h)

/-! ### Cell (120, 120) twin -/

def T120_120_2 : Fin 5 → Coordinate 2 := fun i => T120_120list.getD i.val (0,0,0,0,0)

theorem hfix120_120_2 : ∀ i, ((T120_120_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)
    ∈ fixedPoints (reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120) :=
  repsFix_of_siftB2 rK120 ⟨120, by decide⟩ T120_120_2 (by decide)

theorem hinj120_120_2 : Function.Injective
    (fun i => ((T120_120_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK120)) :=
  repsInj_of_reduceAux2 rK120 T120_120_2 (by decide)

theorem hcardT120_120_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK120)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK120 ⟨120, by decide⟩ R120_2 hpxR120_2 hcardq120_2 (by decide)).symm

/-- **Cell (120, 120) twin (q=2).** -/
theorem cell120_120_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK120) e = true)
    (h : ↥(reps (⟨120, by decide⟩ : Fin 148))) :
    species (reps (⟨120, by decide⟩ : Fin 148)) h (basisElt (reps rK120) (charOfVec2 rK120 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK120 e (h : Coordinate 2) T120_120_2 i :=
  species_entry_eq_sum rK120 ⟨120, by decide⟩ e heK h T120_120_2 hfix120_120_2 hinj120_120_2 hcardT120_120_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨120, by decide⟩) (reps rK120) (T120_120_2 i) (hfix120_120_2 i) h)

end Q2

/-! # K-class rK = 121  (|G/K| = 5) -/

def rK121 : Fin 148 := ⟨121, by decide⟩

def R121list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def R121 : Fin 5 → Coordinate 1 := fun i => R121list.getD i.val (0,0,0,0,0)

theorem hpxR121 : Function.Injective (fun i => reduceAux 1 (basisAt rK121) (R121 i)) := by decide
theorem hcardq121 : Nat.card (Coordinate 1 ⧸ reps rK121) = 5 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (121, 0): |T| = 5 -/

def T121_0list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T121_0 : Fin 5 → Coordinate 1 := fun i => T121_0list.getD i.val (0,0,0,0,0)

theorem hfix121_0 : ∀ i, ((T121_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK121)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121) :=
  repsFix_of_siftB rK121 ⟨0, by decide⟩ T121_0 (by decide)

theorem hinj121_0 : Function.Injective
    (fun i => ((T121_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK121)) :=
  repsInj_of_reduceAux rK121 T121_0 (by decide)

theorem hcardT121_0 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK121 ⟨0, by decide⟩ R121 hpxR121 hcardq121 (by decide)).symm

/-- **Cell (121, 0).** -/
theorem cell121_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK121) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK121) (charOfVec rK121 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK121 e (h : Coordinate 1) T121_0 i :=
  species_entry_eq_sum rK121 ⟨0, by decide⟩ e heK h T121_0 hfix121_0 hinj121_0 hcardT121_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK121) (T121_0 i) (hfix121_0 i) h)

/-! ## Cell (121, 2): |T| = 5 -/

def T121_2list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T121_2 : Fin 5 → Coordinate 1 := fun i => T121_2list.getD i.val (0,0,0,0,0)

theorem hfix121_2 : ∀ i, ((T121_2 i : Coordinate 1) : Coordinate 1 ⧸ reps rK121)
    ∈ fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121) :=
  repsFix_of_siftB rK121 ⟨2, by decide⟩ T121_2 (by decide)

theorem hinj121_2 : Function.Injective
    (fun i => ((T121_2 i : Coordinate 1) : Coordinate 1 ⧸ reps rK121)) :=
  repsInj_of_reduceAux rK121 T121_2 (by decide)

theorem hcardT121_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK121 ⟨2, by decide⟩ R121 hpxR121 hcardq121 (by decide)).symm

/-- **Cell (121, 2).** -/
theorem cell121_2 (e : List (ZMod 25)) (heK : charOK (basisAt rK121) e = true)
    (h : ↥(reps (⟨2, by decide⟩ : Fin 148))) :
    species (reps (⟨2, by decide⟩ : Fin 148)) h (basisElt (reps rK121) (charOfVec rK121 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK121 e (h : Coordinate 1) T121_2 i :=
  species_entry_eq_sum rK121 ⟨2, by decide⟩ e heK h T121_2 hfix121_2 hinj121_2 hcardT121_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨2, by decide⟩) (reps rK121) (T121_2 i) (hfix121_2 i) h)

/-! ## Cell (121, 10): |T| = 5 -/

def T121_10list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T121_10 : Fin 5 → Coordinate 1 := fun i => T121_10list.getD i.val (0,0,0,0,0)

theorem hfix121_10 : ∀ i, ((T121_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK121)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121) :=
  repsFix_of_siftB rK121 ⟨10, by decide⟩ T121_10 (by decide)

theorem hinj121_10 : Function.Injective
    (fun i => ((T121_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK121)) :=
  repsInj_of_reduceAux rK121 T121_10 (by decide)

theorem hcardT121_10 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK121 ⟨10, by decide⟩ R121 hpxR121 hcardq121 (by decide)).symm

/-- **Cell (121, 10).** -/
theorem cell121_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK121) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK121) (charOfVec rK121 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK121 e (h : Coordinate 1) T121_10 i :=
  species_entry_eq_sum rK121 ⟨10, by decide⟩ e heK h T121_10 hfix121_10 hinj121_10 hcardT121_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK121) (T121_10 i) (hfix121_10 i) h)

/-! ## Cell (121, 12): |T| = 5 -/

def T121_12list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T121_12 : Fin 5 → Coordinate 1 := fun i => T121_12list.getD i.val (0,0,0,0,0)

theorem hfix121_12 : ∀ i, ((T121_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK121)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121) :=
  repsFix_of_siftB rK121 ⟨12, by decide⟩ T121_12 (by decide)

theorem hinj121_12 : Function.Injective
    (fun i => ((T121_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK121)) :=
  repsInj_of_reduceAux rK121 T121_12 (by decide)

theorem hcardT121_12 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK121 ⟨12, by decide⟩ R121 hpxR121 hcardq121 (by decide)).symm

/-- **Cell (121, 12).** -/
theorem cell121_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK121) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK121) (charOfVec rK121 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK121 e (h : Coordinate 1) T121_12 i :=
  species_entry_eq_sum rK121 ⟨12, by decide⟩ e heK h T121_12 hfix121_12 hinj121_12 hcardT121_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK121) (T121_12 i) (hfix121_12 i) h)

/-! ## Cell (121, 20): |T| = 5 -/

def T121_20list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T121_20 : Fin 5 → Coordinate 1 := fun i => T121_20list.getD i.val (0,0,0,0,0)

theorem hfix121_20 : ∀ i, ((T121_20 i : Coordinate 1) : Coordinate 1 ⧸ reps rK121)
    ∈ fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121) :=
  repsFix_of_siftB rK121 ⟨20, by decide⟩ T121_20 (by decide)

theorem hinj121_20 : Function.Injective
    (fun i => ((T121_20 i : Coordinate 1) : Coordinate 1 ⧸ reps rK121)) :=
  repsInj_of_reduceAux rK121 T121_20 (by decide)

theorem hcardT121_20 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK121 ⟨20, by decide⟩ R121 hpxR121 hcardq121 (by decide)).symm

/-- **Cell (121, 20).** -/
theorem cell121_20 (e : List (ZMod 25)) (heK : charOK (basisAt rK121) e = true)
    (h : ↥(reps (⟨20, by decide⟩ : Fin 148))) :
    species (reps (⟨20, by decide⟩ : Fin 148)) h (basisElt (reps rK121) (charOfVec rK121 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK121 e (h : Coordinate 1) T121_20 i :=
  species_entry_eq_sum rK121 ⟨20, by decide⟩ e heK h T121_20 hfix121_20 hinj121_20 hcardT121_20
    (fun i => conj_mem_of_fixedPoints (reps ⟨20, by decide⟩) (reps rK121) (T121_20 i) (hfix121_20 i) h)

/-! ## Cell (121, 32): |T| = 5 -/

def T121_32list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T121_32 : Fin 5 → Coordinate 1 := fun i => T121_32list.getD i.val (0,0,0,0,0)

theorem hfix121_32 : ∀ i, ((T121_32 i : Coordinate 1) : Coordinate 1 ⧸ reps rK121)
    ∈ fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121) :=
  repsFix_of_siftB rK121 ⟨32, by decide⟩ T121_32 (by decide)

theorem hinj121_32 : Function.Injective
    (fun i => ((T121_32 i : Coordinate 1) : Coordinate 1 ⧸ reps rK121)) :=
  repsInj_of_reduceAux rK121 T121_32 (by decide)

theorem hcardT121_32 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK121 ⟨32, by decide⟩ R121 hpxR121 hcardq121 (by decide)).symm

/-- **Cell (121, 32).** -/
theorem cell121_32 (e : List (ZMod 25)) (heK : charOK (basisAt rK121) e = true)
    (h : ↥(reps (⟨32, by decide⟩ : Fin 148))) :
    species (reps (⟨32, by decide⟩ : Fin 148)) h (basisElt (reps rK121) (charOfVec rK121 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK121 e (h : Coordinate 1) T121_32 i :=
  species_entry_eq_sum rK121 ⟨32, by decide⟩ e heK h T121_32 hfix121_32 hinj121_32 hcardT121_32
    (fun i => conj_mem_of_fixedPoints (reps ⟨32, by decide⟩) (reps rK121) (T121_32 i) (hfix121_32 i) h)

/-! ## Cell (121, 35): |T| = 5 -/

def T121_35list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T121_35 : Fin 5 → Coordinate 1 := fun i => T121_35list.getD i.val (0,0,0,0,0)

theorem hfix121_35 : ∀ i, ((T121_35 i : Coordinate 1) : Coordinate 1 ⧸ reps rK121)
    ∈ fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121) :=
  repsFix_of_siftB rK121 ⟨35, by decide⟩ T121_35 (by decide)

theorem hinj121_35 : Function.Injective
    (fun i => ((T121_35 i : Coordinate 1) : Coordinate 1 ⧸ reps rK121)) :=
  repsInj_of_reduceAux rK121 T121_35 (by decide)

theorem hcardT121_35 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK121 ⟨35, by decide⟩ R121 hpxR121 hcardq121 (by decide)).symm

/-- **Cell (121, 35).** -/
theorem cell121_35 (e : List (ZMod 25)) (heK : charOK (basisAt rK121) e = true)
    (h : ↥(reps (⟨35, by decide⟩ : Fin 148))) :
    species (reps (⟨35, by decide⟩ : Fin 148)) h (basisElt (reps rK121) (charOfVec rK121 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK121 e (h : Coordinate 1) T121_35 i :=
  species_entry_eq_sum rK121 ⟨35, by decide⟩ e heK h T121_35 hfix121_35 hinj121_35 hcardT121_35
    (fun i => conj_mem_of_fixedPoints (reps ⟨35, by decide⟩) (reps rK121) (T121_35 i) (hfix121_35 i) h)

/-! ## Cell (121, 41): |T| = 5 -/

def T121_41list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T121_41 : Fin 5 → Coordinate 1 := fun i => T121_41list.getD i.val (0,0,0,0,0)

theorem hfix121_41 : ∀ i, ((T121_41 i : Coordinate 1) : Coordinate 1 ⧸ reps rK121)
    ∈ fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121) :=
  repsFix_of_siftB rK121 ⟨41, by decide⟩ T121_41 (by decide)

theorem hinj121_41 : Function.Injective
    (fun i => ((T121_41 i : Coordinate 1) : Coordinate 1 ⧸ reps rK121)) :=
  repsInj_of_reduceAux rK121 T121_41 (by decide)

theorem hcardT121_41 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK121 ⟨41, by decide⟩ R121 hpxR121 hcardq121 (by decide)).symm

/-- **Cell (121, 41).** -/
theorem cell121_41 (e : List (ZMod 25)) (heK : charOK (basisAt rK121) e = true)
    (h : ↥(reps (⟨41, by decide⟩ : Fin 148))) :
    species (reps (⟨41, by decide⟩ : Fin 148)) h (basisElt (reps rK121) (charOfVec rK121 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK121 e (h : Coordinate 1) T121_41 i :=
  species_entry_eq_sum rK121 ⟨41, by decide⟩ e heK h T121_41 hfix121_41 hinj121_41 hcardT121_41
    (fun i => conj_mem_of_fixedPoints (reps ⟨41, by decide⟩) (reps rK121) (T121_41 i) (hfix121_41 i) h)

/-! ## Cell (121, 44): |T| = 5 -/

def T121_44list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T121_44 : Fin 5 → Coordinate 1 := fun i => T121_44list.getD i.val (0,0,0,0,0)

theorem hfix121_44 : ∀ i, ((T121_44 i : Coordinate 1) : Coordinate 1 ⧸ reps rK121)
    ∈ fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121) :=
  repsFix_of_siftB rK121 ⟨44, by decide⟩ T121_44 (by decide)

theorem hinj121_44 : Function.Injective
    (fun i => ((T121_44 i : Coordinate 1) : Coordinate 1 ⧸ reps rK121)) :=
  repsInj_of_reduceAux rK121 T121_44 (by decide)

theorem hcardT121_44 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK121 ⟨44, by decide⟩ R121 hpxR121 hcardq121 (by decide)).symm

/-- **Cell (121, 44).** -/
theorem cell121_44 (e : List (ZMod 25)) (heK : charOK (basisAt rK121) e = true)
    (h : ↥(reps (⟨44, by decide⟩ : Fin 148))) :
    species (reps (⟨44, by decide⟩ : Fin 148)) h (basisElt (reps rK121) (charOfVec rK121 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK121 e (h : Coordinate 1) T121_44 i :=
  species_entry_eq_sum rK121 ⟨44, by decide⟩ e heK h T121_44 hfix121_44 hinj121_44 hcardT121_44
    (fun i => conj_mem_of_fixedPoints (reps ⟨44, by decide⟩) (reps rK121) (T121_44 i) (hfix121_44 i) h)

/-! ## Cell (121, 48): |T| = 5 -/

def T121_48list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T121_48 : Fin 5 → Coordinate 1 := fun i => T121_48list.getD i.val (0,0,0,0,0)

theorem hfix121_48 : ∀ i, ((T121_48 i : Coordinate 1) : Coordinate 1 ⧸ reps rK121)
    ∈ fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121) :=
  repsFix_of_siftB rK121 ⟨48, by decide⟩ T121_48 (by decide)

theorem hinj121_48 : Function.Injective
    (fun i => ((T121_48 i : Coordinate 1) : Coordinate 1 ⧸ reps rK121)) :=
  repsInj_of_reduceAux rK121 T121_48 (by decide)

theorem hcardT121_48 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK121 ⟨48, by decide⟩ R121 hpxR121 hcardq121 (by decide)).symm

/-- **Cell (121, 48).** -/
theorem cell121_48 (e : List (ZMod 25)) (heK : charOK (basisAt rK121) e = true)
    (h : ↥(reps (⟨48, by decide⟩ : Fin 148))) :
    species (reps (⟨48, by decide⟩ : Fin 148)) h (basisElt (reps rK121) (charOfVec rK121 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK121 e (h : Coordinate 1) T121_48 i :=
  species_entry_eq_sum rK121 ⟨48, by decide⟩ e heK h T121_48 hfix121_48 hinj121_48 hcardT121_48
    (fun i => conj_mem_of_fixedPoints (reps ⟨48, by decide⟩) (reps rK121) (T121_48 i) (hfix121_48 i) h)

/-! ## Cell (121, 53): |T| = 5 -/

def T121_53list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T121_53 : Fin 5 → Coordinate 1 := fun i => T121_53list.getD i.val (0,0,0,0,0)

theorem hfix121_53 : ∀ i, ((T121_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK121)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121) :=
  repsFix_of_siftB rK121 ⟨53, by decide⟩ T121_53 (by decide)

theorem hinj121_53 : Function.Injective
    (fun i => ((T121_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK121)) :=
  repsInj_of_reduceAux rK121 T121_53 (by decide)

theorem hcardT121_53 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK121 ⟨53, by decide⟩ R121 hpxR121 hcardq121 (by decide)).symm

/-- **Cell (121, 53).** -/
theorem cell121_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK121) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK121) (charOfVec rK121 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK121 e (h : Coordinate 1) T121_53 i :=
  species_entry_eq_sum rK121 ⟨53, by decide⟩ e heK h T121_53 hfix121_53 hinj121_53 hcardT121_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK121) (T121_53 i) (hfix121_53 i) h)

/-! ## Cell (121, 81): |T| = 5 -/

def T121_81list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T121_81 : Fin 5 → Coordinate 1 := fun i => T121_81list.getD i.val (0,0,0,0,0)

theorem hfix121_81 : ∀ i, ((T121_81 i : Coordinate 1) : Coordinate 1 ⧸ reps rK121)
    ∈ fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121) :=
  repsFix_of_siftB rK121 ⟨81, by decide⟩ T121_81 (by decide)

theorem hinj121_81 : Function.Injective
    (fun i => ((T121_81 i : Coordinate 1) : Coordinate 1 ⧸ reps rK121)) :=
  repsInj_of_reduceAux rK121 T121_81 (by decide)

theorem hcardT121_81 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK121 ⟨81, by decide⟩ R121 hpxR121 hcardq121 (by decide)).symm

/-- **Cell (121, 81).** -/
theorem cell121_81 (e : List (ZMod 25)) (heK : charOK (basisAt rK121) e = true)
    (h : ↥(reps (⟨81, by decide⟩ : Fin 148))) :
    species (reps (⟨81, by decide⟩ : Fin 148)) h (basisElt (reps rK121) (charOfVec rK121 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK121 e (h : Coordinate 1) T121_81 i :=
  species_entry_eq_sum rK121 ⟨81, by decide⟩ e heK h T121_81 hfix121_81 hinj121_81 hcardT121_81
    (fun i => conj_mem_of_fixedPoints (reps ⟨81, by decide⟩) (reps rK121) (T121_81 i) (hfix121_81 i) h)

/-! ## Cell (121, 94): |T| = 5 -/

def T121_94list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T121_94 : Fin 5 → Coordinate 1 := fun i => T121_94list.getD i.val (0,0,0,0,0)

theorem hfix121_94 : ∀ i, ((T121_94 i : Coordinate 1) : Coordinate 1 ⧸ reps rK121)
    ∈ fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121) :=
  repsFix_of_siftB rK121 ⟨94, by decide⟩ T121_94 (by decide)

theorem hinj121_94 : Function.Injective
    (fun i => ((T121_94 i : Coordinate 1) : Coordinate 1 ⧸ reps rK121)) :=
  repsInj_of_reduceAux rK121 T121_94 (by decide)

theorem hcardT121_94 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK121 ⟨94, by decide⟩ R121 hpxR121 hcardq121 (by decide)).symm

/-- **Cell (121, 94).** -/
theorem cell121_94 (e : List (ZMod 25)) (heK : charOK (basisAt rK121) e = true)
    (h : ↥(reps (⟨94, by decide⟩ : Fin 148))) :
    species (reps (⟨94, by decide⟩ : Fin 148)) h (basisElt (reps rK121) (charOfVec rK121 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK121 e (h : Coordinate 1) T121_94 i :=
  species_entry_eq_sum rK121 ⟨94, by decide⟩ e heK h T121_94 hfix121_94 hinj121_94 hcardT121_94
    (fun i => conj_mem_of_fixedPoints (reps ⟨94, by decide⟩) (reps rK121) (T121_94 i) (hfix121_94 i) h)

/-! ## Cell (121, 97): |T| = 5 -/

def T121_97list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T121_97 : Fin 5 → Coordinate 1 := fun i => T121_97list.getD i.val (0,0,0,0,0)

theorem hfix121_97 : ∀ i, ((T121_97 i : Coordinate 1) : Coordinate 1 ⧸ reps rK121)
    ∈ fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121) :=
  repsFix_of_siftB rK121 ⟨97, by decide⟩ T121_97 (by decide)

theorem hinj121_97 : Function.Injective
    (fun i => ((T121_97 i : Coordinate 1) : Coordinate 1 ⧸ reps rK121)) :=
  repsInj_of_reduceAux rK121 T121_97 (by decide)

theorem hcardT121_97 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK121 ⟨97, by decide⟩ R121 hpxR121 hcardq121 (by decide)).symm

/-- **Cell (121, 97).** -/
theorem cell121_97 (e : List (ZMod 25)) (heK : charOK (basisAt rK121) e = true)
    (h : ↥(reps (⟨97, by decide⟩ : Fin 148))) :
    species (reps (⟨97, by decide⟩ : Fin 148)) h (basisElt (reps rK121) (charOfVec rK121 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK121 e (h : Coordinate 1) T121_97 i :=
  species_entry_eq_sum rK121 ⟨97, by decide⟩ e heK h T121_97 hfix121_97 hinj121_97 hcardT121_97
    (fun i => conj_mem_of_fixedPoints (reps ⟨97, by decide⟩) (reps rK121) (T121_97 i) (hfix121_97 i) h)

/-! ## Cell (121, 103): |T| = 5 -/

def T121_103list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T121_103 : Fin 5 → Coordinate 1 := fun i => T121_103list.getD i.val (0,0,0,0,0)

theorem hfix121_103 : ∀ i, ((T121_103 i : Coordinate 1) : Coordinate 1 ⧸ reps rK121)
    ∈ fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121) :=
  repsFix_of_siftB rK121 ⟨103, by decide⟩ T121_103 (by decide)

theorem hinj121_103 : Function.Injective
    (fun i => ((T121_103 i : Coordinate 1) : Coordinate 1 ⧸ reps rK121)) :=
  repsInj_of_reduceAux rK121 T121_103 (by decide)

theorem hcardT121_103 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK121 ⟨103, by decide⟩ R121 hpxR121 hcardq121 (by decide)).symm

/-- **Cell (121, 103).** -/
theorem cell121_103 (e : List (ZMod 25)) (heK : charOK (basisAt rK121) e = true)
    (h : ↥(reps (⟨103, by decide⟩ : Fin 148))) :
    species (reps (⟨103, by decide⟩ : Fin 148)) h (basisElt (reps rK121) (charOfVec rK121 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK121 e (h : Coordinate 1) T121_103 i :=
  species_entry_eq_sum rK121 ⟨103, by decide⟩ e heK h T121_103 hfix121_103 hinj121_103 hcardT121_103
    (fun i => conj_mem_of_fixedPoints (reps ⟨103, by decide⟩) (reps rK121) (T121_103 i) (hfix121_103 i) h)

/-! ## Cell (121, 106): |T| = 5 -/

def T121_106list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T121_106 : Fin 5 → Coordinate 1 := fun i => T121_106list.getD i.val (0,0,0,0,0)

theorem hfix121_106 : ∀ i, ((T121_106 i : Coordinate 1) : Coordinate 1 ⧸ reps rK121)
    ∈ fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121) :=
  repsFix_of_siftB rK121 ⟨106, by decide⟩ T121_106 (by decide)

theorem hinj121_106 : Function.Injective
    (fun i => ((T121_106 i : Coordinate 1) : Coordinate 1 ⧸ reps rK121)) :=
  repsInj_of_reduceAux rK121 T121_106 (by decide)

theorem hcardT121_106 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK121 ⟨106, by decide⟩ R121 hpxR121 hcardq121 (by decide)).symm

/-- **Cell (121, 106).** -/
theorem cell121_106 (e : List (ZMod 25)) (heK : charOK (basisAt rK121) e = true)
    (h : ↥(reps (⟨106, by decide⟩ : Fin 148))) :
    species (reps (⟨106, by decide⟩ : Fin 148)) h (basisElt (reps rK121) (charOfVec rK121 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK121 e (h : Coordinate 1) T121_106 i :=
  species_entry_eq_sum rK121 ⟨106, by decide⟩ e heK h T121_106 hfix121_106 hinj121_106 hcardT121_106
    (fun i => conj_mem_of_fixedPoints (reps ⟨106, by decide⟩) (reps rK121) (T121_106 i) (hfix121_106 i) h)

/-! ## Cell (121, 110): |T| = 5 -/

def T121_110list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T121_110 : Fin 5 → Coordinate 1 := fun i => T121_110list.getD i.val (0,0,0,0,0)

theorem hfix121_110 : ∀ i, ((T121_110 i : Coordinate 1) : Coordinate 1 ⧸ reps rK121)
    ∈ fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121) :=
  repsFix_of_siftB rK121 ⟨110, by decide⟩ T121_110 (by decide)

theorem hinj121_110 : Function.Injective
    (fun i => ((T121_110 i : Coordinate 1) : Coordinate 1 ⧸ reps rK121)) :=
  repsInj_of_reduceAux rK121 T121_110 (by decide)

theorem hcardT121_110 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK121 ⟨110, by decide⟩ R121 hpxR121 hcardq121 (by decide)).symm

/-- **Cell (121, 110).** -/
theorem cell121_110 (e : List (ZMod 25)) (heK : charOK (basisAt rK121) e = true)
    (h : ↥(reps (⟨110, by decide⟩ : Fin 148))) :
    species (reps (⟨110, by decide⟩ : Fin 148)) h (basisElt (reps rK121) (charOfVec rK121 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK121 e (h : Coordinate 1) T121_110 i :=
  species_entry_eq_sum rK121 ⟨110, by decide⟩ e heK h T121_110 hfix121_110 hinj121_110 hcardT121_110
    (fun i => conj_mem_of_fixedPoints (reps ⟨110, by decide⟩) (reps rK121) (T121_110 i) (hfix121_110 i) h)

/-! ## Cell (121, 121): |T| = 5 -/

def T121_121list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T121_121 : Fin 5 → Coordinate 1 := fun i => T121_121list.getD i.val (0,0,0,0,0)

theorem hfix121_121 : ∀ i, ((T121_121 i : Coordinate 1) : Coordinate 1 ⧸ reps rK121)
    ∈ fixedPoints (reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121) :=
  repsFix_of_siftB rK121 ⟨121, by decide⟩ T121_121 (by decide)

theorem hinj121_121 : Function.Injective
    (fun i => ((T121_121 i : Coordinate 1) : Coordinate 1 ⧸ reps rK121)) :=
  repsInj_of_reduceAux rK121 T121_121 (by decide)

theorem hcardT121_121 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK121 ⟨121, by decide⟩ R121 hpxR121 hcardq121 (by decide)).symm

/-- **Cell (121, 121).** -/
theorem cell121_121 (e : List (ZMod 25)) (heK : charOK (basisAt rK121) e = true)
    (h : ↥(reps (⟨121, by decide⟩ : Fin 148))) :
    species (reps (⟨121, by decide⟩ : Fin 148)) h (basisElt (reps rK121) (charOfVec rK121 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK121 e (h : Coordinate 1) T121_121 i :=
  species_entry_eq_sum rK121 ⟨121, by decide⟩ e heK h T121_121 hfix121_121 hinj121_121 hcardT121_121
    (fun i => conj_mem_of_fixedPoints (reps ⟨121, by decide⟩) (reps rK121) (T121_121 i) (hfix121_121 i) h)

namespace Q2

def R121_2 : Fin 5 → Coordinate 2 := fun i => R121list.getD i.val (0,0,0,0,0)
theorem hpxR121_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK121) (R121_2 i)) := by decide
theorem hcardq121_2 : Nat.card (Coordinate 2 ⧸ reps rK121) = 5 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (121, 0) twin -/

def T121_0_2 : Fin 5 → Coordinate 2 := fun i => T121_0list.getD i.val (0,0,0,0,0)

theorem hfix121_0_2 : ∀ i, ((T121_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK121)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK121) :=
  repsFix_of_siftB2 rK121 ⟨0, by decide⟩ T121_0_2 (by decide)

theorem hinj121_0_2 : Function.Injective
    (fun i => ((T121_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK121)) :=
  repsInj_of_reduceAux2 rK121 T121_0_2 (by decide)

theorem hcardT121_0_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK121)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK121 ⟨0, by decide⟩ R121_2 hpxR121_2 hcardq121_2 (by decide)).symm

/-- **Cell (121, 0) twin (q=2).** -/
theorem cell121_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK121) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK121) (charOfVec2 rK121 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK121 e (h : Coordinate 2) T121_0_2 i :=
  species_entry_eq_sum rK121 ⟨0, by decide⟩ e heK h T121_0_2 hfix121_0_2 hinj121_0_2 hcardT121_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK121) (T121_0_2 i) (hfix121_0_2 i) h)

/-! ### Cell (121, 2) twin -/

def T121_2_2 : Fin 5 → Coordinate 2 := fun i => T121_2list.getD i.val (0,0,0,0,0)

theorem hfix121_2_2 : ∀ i, ((T121_2_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK121)
    ∈ fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK121) :=
  repsFix_of_siftB2 rK121 ⟨2, by decide⟩ T121_2_2 (by decide)

theorem hinj121_2_2 : Function.Injective
    (fun i => ((T121_2_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK121)) :=
  repsInj_of_reduceAux2 rK121 T121_2_2 (by decide)

theorem hcardT121_2_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK121)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK121 ⟨2, by decide⟩ R121_2 hpxR121_2 hcardq121_2 (by decide)).symm

/-- **Cell (121, 2) twin (q=2).** -/
theorem cell121_2_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK121) e = true)
    (h : ↥(reps (⟨2, by decide⟩ : Fin 148))) :
    species (reps (⟨2, by decide⟩ : Fin 148)) h (basisElt (reps rK121) (charOfVec2 rK121 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK121 e (h : Coordinate 2) T121_2_2 i :=
  species_entry_eq_sum rK121 ⟨2, by decide⟩ e heK h T121_2_2 hfix121_2_2 hinj121_2_2 hcardT121_2_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨2, by decide⟩) (reps rK121) (T121_2_2 i) (hfix121_2_2 i) h)

/-! ### Cell (121, 10) twin -/

def T121_10_2 : Fin 5 → Coordinate 2 := fun i => T121_10list.getD i.val (0,0,0,0,0)

theorem hfix121_10_2 : ∀ i, ((T121_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK121)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK121) :=
  repsFix_of_siftB2 rK121 ⟨10, by decide⟩ T121_10_2 (by decide)

theorem hinj121_10_2 : Function.Injective
    (fun i => ((T121_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK121)) :=
  repsInj_of_reduceAux2 rK121 T121_10_2 (by decide)

theorem hcardT121_10_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK121)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK121 ⟨10, by decide⟩ R121_2 hpxR121_2 hcardq121_2 (by decide)).symm

/-- **Cell (121, 10) twin (q=2).** -/
theorem cell121_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK121) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK121) (charOfVec2 rK121 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK121 e (h : Coordinate 2) T121_10_2 i :=
  species_entry_eq_sum rK121 ⟨10, by decide⟩ e heK h T121_10_2 hfix121_10_2 hinj121_10_2 hcardT121_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK121) (T121_10_2 i) (hfix121_10_2 i) h)

/-! ### Cell (121, 12) twin -/

def T121_12_2 : Fin 5 → Coordinate 2 := fun i => T121_12list.getD i.val (0,0,0,0,0)

theorem hfix121_12_2 : ∀ i, ((T121_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK121)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK121) :=
  repsFix_of_siftB2 rK121 ⟨12, by decide⟩ T121_12_2 (by decide)

theorem hinj121_12_2 : Function.Injective
    (fun i => ((T121_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK121)) :=
  repsInj_of_reduceAux2 rK121 T121_12_2 (by decide)

theorem hcardT121_12_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK121)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK121 ⟨12, by decide⟩ R121_2 hpxR121_2 hcardq121_2 (by decide)).symm

/-- **Cell (121, 12) twin (q=2).** -/
theorem cell121_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK121) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK121) (charOfVec2 rK121 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK121 e (h : Coordinate 2) T121_12_2 i :=
  species_entry_eq_sum rK121 ⟨12, by decide⟩ e heK h T121_12_2 hfix121_12_2 hinj121_12_2 hcardT121_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK121) (T121_12_2 i) (hfix121_12_2 i) h)

/-! ### Cell (121, 20) twin -/

def T121_20_2 : Fin 5 → Coordinate 2 := fun i => T121_20list.getD i.val (0,0,0,0,0)

theorem hfix121_20_2 : ∀ i, ((T121_20_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK121)
    ∈ fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK121) :=
  repsFix_of_siftB2 rK121 ⟨20, by decide⟩ T121_20_2 (by decide)

theorem hinj121_20_2 : Function.Injective
    (fun i => ((T121_20_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK121)) :=
  repsInj_of_reduceAux2 rK121 T121_20_2 (by decide)

theorem hcardT121_20_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK121)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK121 ⟨20, by decide⟩ R121_2 hpxR121_2 hcardq121_2 (by decide)).symm

/-- **Cell (121, 20) twin (q=2).** -/
theorem cell121_20_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK121) e = true)
    (h : ↥(reps (⟨20, by decide⟩ : Fin 148))) :
    species (reps (⟨20, by decide⟩ : Fin 148)) h (basisElt (reps rK121) (charOfVec2 rK121 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK121 e (h : Coordinate 2) T121_20_2 i :=
  species_entry_eq_sum rK121 ⟨20, by decide⟩ e heK h T121_20_2 hfix121_20_2 hinj121_20_2 hcardT121_20_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨20, by decide⟩) (reps rK121) (T121_20_2 i) (hfix121_20_2 i) h)

/-! ### Cell (121, 32) twin -/

def T121_32_2 : Fin 5 → Coordinate 2 := fun i => T121_32list.getD i.val (0,0,0,0,0)

theorem hfix121_32_2 : ∀ i, ((T121_32_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK121)
    ∈ fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK121) :=
  repsFix_of_siftB2 rK121 ⟨32, by decide⟩ T121_32_2 (by decide)

theorem hinj121_32_2 : Function.Injective
    (fun i => ((T121_32_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK121)) :=
  repsInj_of_reduceAux2 rK121 T121_32_2 (by decide)

theorem hcardT121_32_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK121)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK121 ⟨32, by decide⟩ R121_2 hpxR121_2 hcardq121_2 (by decide)).symm

/-- **Cell (121, 32) twin (q=2).** -/
theorem cell121_32_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK121) e = true)
    (h : ↥(reps (⟨32, by decide⟩ : Fin 148))) :
    species (reps (⟨32, by decide⟩ : Fin 148)) h (basisElt (reps rK121) (charOfVec2 rK121 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK121 e (h : Coordinate 2) T121_32_2 i :=
  species_entry_eq_sum rK121 ⟨32, by decide⟩ e heK h T121_32_2 hfix121_32_2 hinj121_32_2 hcardT121_32_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨32, by decide⟩) (reps rK121) (T121_32_2 i) (hfix121_32_2 i) h)

/-! ### Cell (121, 35) twin -/

def T121_35_2 : Fin 5 → Coordinate 2 := fun i => T121_35list.getD i.val (0,0,0,0,0)

theorem hfix121_35_2 : ∀ i, ((T121_35_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK121)
    ∈ fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK121) :=
  repsFix_of_siftB2 rK121 ⟨35, by decide⟩ T121_35_2 (by decide)

theorem hinj121_35_2 : Function.Injective
    (fun i => ((T121_35_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK121)) :=
  repsInj_of_reduceAux2 rK121 T121_35_2 (by decide)

theorem hcardT121_35_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK121)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK121 ⟨35, by decide⟩ R121_2 hpxR121_2 hcardq121_2 (by decide)).symm

/-- **Cell (121, 35) twin (q=2).** -/
theorem cell121_35_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK121) e = true)
    (h : ↥(reps (⟨35, by decide⟩ : Fin 148))) :
    species (reps (⟨35, by decide⟩ : Fin 148)) h (basisElt (reps rK121) (charOfVec2 rK121 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK121 e (h : Coordinate 2) T121_35_2 i :=
  species_entry_eq_sum rK121 ⟨35, by decide⟩ e heK h T121_35_2 hfix121_35_2 hinj121_35_2 hcardT121_35_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨35, by decide⟩) (reps rK121) (T121_35_2 i) (hfix121_35_2 i) h)

/-! ### Cell (121, 41) twin -/

def T121_41_2 : Fin 5 → Coordinate 2 := fun i => T121_41list.getD i.val (0,0,0,0,0)

theorem hfix121_41_2 : ∀ i, ((T121_41_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK121)
    ∈ fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK121) :=
  repsFix_of_siftB2 rK121 ⟨41, by decide⟩ T121_41_2 (by decide)

theorem hinj121_41_2 : Function.Injective
    (fun i => ((T121_41_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK121)) :=
  repsInj_of_reduceAux2 rK121 T121_41_2 (by decide)

theorem hcardT121_41_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK121)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK121 ⟨41, by decide⟩ R121_2 hpxR121_2 hcardq121_2 (by decide)).symm

/-- **Cell (121, 41) twin (q=2).** -/
theorem cell121_41_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK121) e = true)
    (h : ↥(reps (⟨41, by decide⟩ : Fin 148))) :
    species (reps (⟨41, by decide⟩ : Fin 148)) h (basisElt (reps rK121) (charOfVec2 rK121 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK121 e (h : Coordinate 2) T121_41_2 i :=
  species_entry_eq_sum rK121 ⟨41, by decide⟩ e heK h T121_41_2 hfix121_41_2 hinj121_41_2 hcardT121_41_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨41, by decide⟩) (reps rK121) (T121_41_2 i) (hfix121_41_2 i) h)

/-! ### Cell (121, 44) twin -/

def T121_44_2 : Fin 5 → Coordinate 2 := fun i => T121_44list.getD i.val (0,0,0,0,0)

theorem hfix121_44_2 : ∀ i, ((T121_44_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK121)
    ∈ fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK121) :=
  repsFix_of_siftB2 rK121 ⟨44, by decide⟩ T121_44_2 (by decide)

theorem hinj121_44_2 : Function.Injective
    (fun i => ((T121_44_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK121)) :=
  repsInj_of_reduceAux2 rK121 T121_44_2 (by decide)

theorem hcardT121_44_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK121)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK121 ⟨44, by decide⟩ R121_2 hpxR121_2 hcardq121_2 (by decide)).symm

/-- **Cell (121, 44) twin (q=2).** -/
theorem cell121_44_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK121) e = true)
    (h : ↥(reps (⟨44, by decide⟩ : Fin 148))) :
    species (reps (⟨44, by decide⟩ : Fin 148)) h (basisElt (reps rK121) (charOfVec2 rK121 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK121 e (h : Coordinate 2) T121_44_2 i :=
  species_entry_eq_sum rK121 ⟨44, by decide⟩ e heK h T121_44_2 hfix121_44_2 hinj121_44_2 hcardT121_44_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨44, by decide⟩) (reps rK121) (T121_44_2 i) (hfix121_44_2 i) h)

/-! ### Cell (121, 48) twin -/

def T121_48_2 : Fin 5 → Coordinate 2 := fun i => T121_48list.getD i.val (0,0,0,0,0)

theorem hfix121_48_2 : ∀ i, ((T121_48_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK121)
    ∈ fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK121) :=
  repsFix_of_siftB2 rK121 ⟨48, by decide⟩ T121_48_2 (by decide)

theorem hinj121_48_2 : Function.Injective
    (fun i => ((T121_48_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK121)) :=
  repsInj_of_reduceAux2 rK121 T121_48_2 (by decide)

theorem hcardT121_48_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK121)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK121 ⟨48, by decide⟩ R121_2 hpxR121_2 hcardq121_2 (by decide)).symm

/-- **Cell (121, 48) twin (q=2).** -/
theorem cell121_48_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK121) e = true)
    (h : ↥(reps (⟨48, by decide⟩ : Fin 148))) :
    species (reps (⟨48, by decide⟩ : Fin 148)) h (basisElt (reps rK121) (charOfVec2 rK121 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK121 e (h : Coordinate 2) T121_48_2 i :=
  species_entry_eq_sum rK121 ⟨48, by decide⟩ e heK h T121_48_2 hfix121_48_2 hinj121_48_2 hcardT121_48_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨48, by decide⟩) (reps rK121) (T121_48_2 i) (hfix121_48_2 i) h)

/-! ### Cell (121, 53) twin -/

def T121_53_2 : Fin 5 → Coordinate 2 := fun i => T121_53list.getD i.val (0,0,0,0,0)

theorem hfix121_53_2 : ∀ i, ((T121_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK121)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK121) :=
  repsFix_of_siftB2 rK121 ⟨53, by decide⟩ T121_53_2 (by decide)

theorem hinj121_53_2 : Function.Injective
    (fun i => ((T121_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK121)) :=
  repsInj_of_reduceAux2 rK121 T121_53_2 (by decide)

theorem hcardT121_53_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK121)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK121 ⟨53, by decide⟩ R121_2 hpxR121_2 hcardq121_2 (by decide)).symm

/-- **Cell (121, 53) twin (q=2).** -/
theorem cell121_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK121) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK121) (charOfVec2 rK121 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK121 e (h : Coordinate 2) T121_53_2 i :=
  species_entry_eq_sum rK121 ⟨53, by decide⟩ e heK h T121_53_2 hfix121_53_2 hinj121_53_2 hcardT121_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK121) (T121_53_2 i) (hfix121_53_2 i) h)

/-! ### Cell (121, 81) twin -/

def T121_81_2 : Fin 5 → Coordinate 2 := fun i => T121_81list.getD i.val (0,0,0,0,0)

theorem hfix121_81_2 : ∀ i, ((T121_81_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK121)
    ∈ fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK121) :=
  repsFix_of_siftB2 rK121 ⟨81, by decide⟩ T121_81_2 (by decide)

theorem hinj121_81_2 : Function.Injective
    (fun i => ((T121_81_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK121)) :=
  repsInj_of_reduceAux2 rK121 T121_81_2 (by decide)

theorem hcardT121_81_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK121)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK121 ⟨81, by decide⟩ R121_2 hpxR121_2 hcardq121_2 (by decide)).symm

/-- **Cell (121, 81) twin (q=2).** -/
theorem cell121_81_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK121) e = true)
    (h : ↥(reps (⟨81, by decide⟩ : Fin 148))) :
    species (reps (⟨81, by decide⟩ : Fin 148)) h (basisElt (reps rK121) (charOfVec2 rK121 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK121 e (h : Coordinate 2) T121_81_2 i :=
  species_entry_eq_sum rK121 ⟨81, by decide⟩ e heK h T121_81_2 hfix121_81_2 hinj121_81_2 hcardT121_81_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨81, by decide⟩) (reps rK121) (T121_81_2 i) (hfix121_81_2 i) h)

/-! ### Cell (121, 94) twin -/

def T121_94_2 : Fin 5 → Coordinate 2 := fun i => T121_94list.getD i.val (0,0,0,0,0)

theorem hfix121_94_2 : ∀ i, ((T121_94_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK121)
    ∈ fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK121) :=
  repsFix_of_siftB2 rK121 ⟨94, by decide⟩ T121_94_2 (by decide)

theorem hinj121_94_2 : Function.Injective
    (fun i => ((T121_94_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK121)) :=
  repsInj_of_reduceAux2 rK121 T121_94_2 (by decide)

theorem hcardT121_94_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK121)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK121 ⟨94, by decide⟩ R121_2 hpxR121_2 hcardq121_2 (by decide)).symm

/-- **Cell (121, 94) twin (q=2).** -/
theorem cell121_94_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK121) e = true)
    (h : ↥(reps (⟨94, by decide⟩ : Fin 148))) :
    species (reps (⟨94, by decide⟩ : Fin 148)) h (basisElt (reps rK121) (charOfVec2 rK121 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK121 e (h : Coordinate 2) T121_94_2 i :=
  species_entry_eq_sum rK121 ⟨94, by decide⟩ e heK h T121_94_2 hfix121_94_2 hinj121_94_2 hcardT121_94_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨94, by decide⟩) (reps rK121) (T121_94_2 i) (hfix121_94_2 i) h)

/-! ### Cell (121, 97) twin -/

def T121_97_2 : Fin 5 → Coordinate 2 := fun i => T121_97list.getD i.val (0,0,0,0,0)

theorem hfix121_97_2 : ∀ i, ((T121_97_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK121)
    ∈ fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK121) :=
  repsFix_of_siftB2 rK121 ⟨97, by decide⟩ T121_97_2 (by decide)

theorem hinj121_97_2 : Function.Injective
    (fun i => ((T121_97_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK121)) :=
  repsInj_of_reduceAux2 rK121 T121_97_2 (by decide)

theorem hcardT121_97_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK121)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK121 ⟨97, by decide⟩ R121_2 hpxR121_2 hcardq121_2 (by decide)).symm

/-- **Cell (121, 97) twin (q=2).** -/
theorem cell121_97_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK121) e = true)
    (h : ↥(reps (⟨97, by decide⟩ : Fin 148))) :
    species (reps (⟨97, by decide⟩ : Fin 148)) h (basisElt (reps rK121) (charOfVec2 rK121 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK121 e (h : Coordinate 2) T121_97_2 i :=
  species_entry_eq_sum rK121 ⟨97, by decide⟩ e heK h T121_97_2 hfix121_97_2 hinj121_97_2 hcardT121_97_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨97, by decide⟩) (reps rK121) (T121_97_2 i) (hfix121_97_2 i) h)

/-! ### Cell (121, 103) twin -/

def T121_103_2 : Fin 5 → Coordinate 2 := fun i => T121_103list.getD i.val (0,0,0,0,0)

theorem hfix121_103_2 : ∀ i, ((T121_103_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK121)
    ∈ fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK121) :=
  repsFix_of_siftB2 rK121 ⟨103, by decide⟩ T121_103_2 (by decide)

theorem hinj121_103_2 : Function.Injective
    (fun i => ((T121_103_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK121)) :=
  repsInj_of_reduceAux2 rK121 T121_103_2 (by decide)

theorem hcardT121_103_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK121)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK121 ⟨103, by decide⟩ R121_2 hpxR121_2 hcardq121_2 (by decide)).symm

/-- **Cell (121, 103) twin (q=2).** -/
theorem cell121_103_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK121) e = true)
    (h : ↥(reps (⟨103, by decide⟩ : Fin 148))) :
    species (reps (⟨103, by decide⟩ : Fin 148)) h (basisElt (reps rK121) (charOfVec2 rK121 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK121 e (h : Coordinate 2) T121_103_2 i :=
  species_entry_eq_sum rK121 ⟨103, by decide⟩ e heK h T121_103_2 hfix121_103_2 hinj121_103_2 hcardT121_103_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨103, by decide⟩) (reps rK121) (T121_103_2 i) (hfix121_103_2 i) h)

/-! ### Cell (121, 106) twin -/

def T121_106_2 : Fin 5 → Coordinate 2 := fun i => T121_106list.getD i.val (0,0,0,0,0)

theorem hfix121_106_2 : ∀ i, ((T121_106_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK121)
    ∈ fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK121) :=
  repsFix_of_siftB2 rK121 ⟨106, by decide⟩ T121_106_2 (by decide)

theorem hinj121_106_2 : Function.Injective
    (fun i => ((T121_106_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK121)) :=
  repsInj_of_reduceAux2 rK121 T121_106_2 (by decide)

theorem hcardT121_106_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK121)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK121 ⟨106, by decide⟩ R121_2 hpxR121_2 hcardq121_2 (by decide)).symm

/-- **Cell (121, 106) twin (q=2).** -/
theorem cell121_106_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK121) e = true)
    (h : ↥(reps (⟨106, by decide⟩ : Fin 148))) :
    species (reps (⟨106, by decide⟩ : Fin 148)) h (basisElt (reps rK121) (charOfVec2 rK121 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK121 e (h : Coordinate 2) T121_106_2 i :=
  species_entry_eq_sum rK121 ⟨106, by decide⟩ e heK h T121_106_2 hfix121_106_2 hinj121_106_2 hcardT121_106_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨106, by decide⟩) (reps rK121) (T121_106_2 i) (hfix121_106_2 i) h)

/-! ### Cell (121, 110) twin -/

def T121_110_2 : Fin 5 → Coordinate 2 := fun i => T121_110list.getD i.val (0,0,0,0,0)

theorem hfix121_110_2 : ∀ i, ((T121_110_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK121)
    ∈ fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK121) :=
  repsFix_of_siftB2 rK121 ⟨110, by decide⟩ T121_110_2 (by decide)

theorem hinj121_110_2 : Function.Injective
    (fun i => ((T121_110_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK121)) :=
  repsInj_of_reduceAux2 rK121 T121_110_2 (by decide)

theorem hcardT121_110_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK121)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK121 ⟨110, by decide⟩ R121_2 hpxR121_2 hcardq121_2 (by decide)).symm

/-- **Cell (121, 110) twin (q=2).** -/
theorem cell121_110_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK121) e = true)
    (h : ↥(reps (⟨110, by decide⟩ : Fin 148))) :
    species (reps (⟨110, by decide⟩ : Fin 148)) h (basisElt (reps rK121) (charOfVec2 rK121 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK121 e (h : Coordinate 2) T121_110_2 i :=
  species_entry_eq_sum rK121 ⟨110, by decide⟩ e heK h T121_110_2 hfix121_110_2 hinj121_110_2 hcardT121_110_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨110, by decide⟩) (reps rK121) (T121_110_2 i) (hfix121_110_2 i) h)

/-! ### Cell (121, 121) twin -/

def T121_121_2 : Fin 5 → Coordinate 2 := fun i => T121_121list.getD i.val (0,0,0,0,0)

theorem hfix121_121_2 : ∀ i, ((T121_121_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK121)
    ∈ fixedPoints (reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK121) :=
  repsFix_of_siftB2 rK121 ⟨121, by decide⟩ T121_121_2 (by decide)

theorem hinj121_121_2 : Function.Injective
    (fun i => ((T121_121_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK121)) :=
  repsInj_of_reduceAux2 rK121 T121_121_2 (by decide)

theorem hcardT121_121_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK121)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK121 ⟨121, by decide⟩ R121_2 hpxR121_2 hcardq121_2 (by decide)).symm

/-- **Cell (121, 121) twin (q=2).** -/
theorem cell121_121_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK121) e = true)
    (h : ↥(reps (⟨121, by decide⟩ : Fin 148))) :
    species (reps (⟨121, by decide⟩ : Fin 148)) h (basisElt (reps rK121) (charOfVec2 rK121 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK121 e (h : Coordinate 2) T121_121_2 i :=
  species_entry_eq_sum rK121 ⟨121, by decide⟩ e heK h T121_121_2 hfix121_121_2 hinj121_121_2 hcardT121_121_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨121, by decide⟩) (reps rK121) (T121_121_2 i) (hfix121_121_2 i) h)

end Q2

end LeanDring.P5Presentation
