/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, K-strata data (5^4 stratum, rK 117-117): certified per-cell species-entry instantiations, both
twins.

Covers K-classes 117 (order-5^4 K, |R|=5).  For each nonzero `H`-column
(`(G/K)^H ≠ ∅`), the full coset transversal `R117..` and each `H`-fixed
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

/-! # K-class rK = 117  (|G/K| = 5) -/

def rK117 : Fin 148 := ⟨117, by decide⟩

def R117list : List Coordinates := [(0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0)]
def R117 : Fin 5 → Coordinate 1 := fun i => R117list.getD i.val (0,0,0,0,0)

theorem hpxR117 : Function.Injective (fun i => reduceAux 1 (basisAt rK117) (R117 i)) := by decide
theorem hcardq117 : Nat.card (Coordinate 1 ⧸ reps rK117) = 5 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (117, 0): |T| = 5 -/

def T117_0list : List Coordinates := [(0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0)]
def T117_0 : Fin 5 → Coordinate 1 := fun i => T117_0list.getD i.val (0,0,0,0,0)

theorem hfix117_0 : ∀ i, ((T117_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117) :=
  repsFix_of_siftB rK117 ⟨0, by decide⟩ T117_0 (by decide)

theorem hinj117_0 : Function.Injective
    (fun i => ((T117_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)) :=
  repsInj_of_reduceAux rK117 T117_0 (by decide)

theorem hcardT117_0 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK117 ⟨0, by decide⟩ R117 hpxR117 hcardq117 (by decide)).symm

/-- **Cell (117, 0).** -/
theorem cell117_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK117) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK117 e (h : Coordinate 1) T117_0 i :=
  species_entry_eq_sum rK117 ⟨0, by decide⟩ e heK h T117_0 hfix117_0 hinj117_0 hcardT117_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK117) (T117_0 i) (hfix117_0 i) h)

/-! ## Cell (117, 1): |T| = 5 -/

def T117_1list : List Coordinates := [(0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0)]
def T117_1 : Fin 5 → Coordinate 1 := fun i => T117_1list.getD i.val (0,0,0,0,0)

theorem hfix117_1 : ∀ i, ((T117_1 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117) :=
  repsFix_of_siftB rK117 ⟨1, by decide⟩ T117_1 (by decide)

theorem hinj117_1 : Function.Injective
    (fun i => ((T117_1 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)) :=
  repsInj_of_reduceAux rK117 T117_1 (by decide)

theorem hcardT117_1 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK117 ⟨1, by decide⟩ R117 hpxR117 hcardq117 (by decide)).symm

/-- **Cell (117, 1).** -/
theorem cell117_1 (e : List (ZMod 25)) (heK : charOK (basisAt rK117) e = true)
    (h : ↥(reps (⟨1, by decide⟩ : Fin 148))) :
    species (reps (⟨1, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK117 e (h : Coordinate 1) T117_1 i :=
  species_entry_eq_sum rK117 ⟨1, by decide⟩ e heK h T117_1 hfix117_1 hinj117_1 hcardT117_1
    (fun i => conj_mem_of_fixedPoints (reps ⟨1, by decide⟩) (reps rK117) (T117_1 i) (hfix117_1 i) h)

/-! ## Cell (117, 6): |T| = 5 -/

def T117_6list : List Coordinates := [(0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0)]
def T117_6 : Fin 5 → Coordinate 1 := fun i => T117_6list.getD i.val (0,0,0,0,0)

theorem hfix117_6 : ∀ i, ((T117_6 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117) :=
  repsFix_of_siftB rK117 ⟨6, by decide⟩ T117_6 (by decide)

theorem hinj117_6 : Function.Injective
    (fun i => ((T117_6 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)) :=
  repsInj_of_reduceAux rK117 T117_6 (by decide)

theorem hcardT117_6 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK117 ⟨6, by decide⟩ R117 hpxR117 hcardq117 (by decide)).symm

/-- **Cell (117, 6).** -/
theorem cell117_6 (e : List (ZMod 25)) (heK : charOK (basisAt rK117) e = true)
    (h : ↥(reps (⟨6, by decide⟩ : Fin 148))) :
    species (reps (⟨6, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK117 e (h : Coordinate 1) T117_6 i :=
  species_entry_eq_sum rK117 ⟨6, by decide⟩ e heK h T117_6 hfix117_6 hinj117_6 hcardT117_6
    (fun i => conj_mem_of_fixedPoints (reps ⟨6, by decide⟩) (reps rK117) (T117_6 i) (hfix117_6 i) h)

/-! ## Cell (117, 7): |T| = 5 -/

def T117_7list : List Coordinates := [(0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0)]
def T117_7 : Fin 5 → Coordinate 1 := fun i => T117_7list.getD i.val (0,0,0,0,0)

theorem hfix117_7 : ∀ i, ((T117_7 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117) :=
  repsFix_of_siftB rK117 ⟨7, by decide⟩ T117_7 (by decide)

theorem hinj117_7 : Function.Injective
    (fun i => ((T117_7 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)) :=
  repsInj_of_reduceAux rK117 T117_7 (by decide)

theorem hcardT117_7 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK117 ⟨7, by decide⟩ R117 hpxR117 hcardq117 (by decide)).symm

/-- **Cell (117, 7).** -/
theorem cell117_7 (e : List (ZMod 25)) (heK : charOK (basisAt rK117) e = true)
    (h : ↥(reps (⟨7, by decide⟩ : Fin 148))) :
    species (reps (⟨7, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK117 e (h : Coordinate 1) T117_7 i :=
  species_entry_eq_sum rK117 ⟨7, by decide⟩ e heK h T117_7 hfix117_7 hinj117_7 hcardT117_7
    (fun i => conj_mem_of_fixedPoints (reps ⟨7, by decide⟩) (reps rK117) (T117_7 i) (hfix117_7 i) h)

/-! ## Cell (117, 8): |T| = 5 -/

def T117_8list : List Coordinates := [(0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0)]
def T117_8 : Fin 5 → Coordinate 1 := fun i => T117_8list.getD i.val (0,0,0,0,0)

theorem hfix117_8 : ∀ i, ((T117_8 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117) :=
  repsFix_of_siftB rK117 ⟨8, by decide⟩ T117_8 (by decide)

theorem hinj117_8 : Function.Injective
    (fun i => ((T117_8 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)) :=
  repsInj_of_reduceAux rK117 T117_8 (by decide)

theorem hcardT117_8 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK117 ⟨8, by decide⟩ R117 hpxR117 hcardq117 (by decide)).symm

/-- **Cell (117, 8).** -/
theorem cell117_8 (e : List (ZMod 25)) (heK : charOK (basisAt rK117) e = true)
    (h : ↥(reps (⟨8, by decide⟩ : Fin 148))) :
    species (reps (⟨8, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK117 e (h : Coordinate 1) T117_8 i :=
  species_entry_eq_sum rK117 ⟨8, by decide⟩ e heK h T117_8 hfix117_8 hinj117_8 hcardT117_8
    (fun i => conj_mem_of_fixedPoints (reps ⟨8, by decide⟩) (reps rK117) (T117_8 i) (hfix117_8 i) h)

/-! ## Cell (117, 9): |T| = 5 -/

def T117_9list : List Coordinates := [(0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0)]
def T117_9 : Fin 5 → Coordinate 1 := fun i => T117_9list.getD i.val (0,0,0,0,0)

theorem hfix117_9 : ∀ i, ((T117_9 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117) :=
  repsFix_of_siftB rK117 ⟨9, by decide⟩ T117_9 (by decide)

theorem hinj117_9 : Function.Injective
    (fun i => ((T117_9 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)) :=
  repsInj_of_reduceAux rK117 T117_9 (by decide)

theorem hcardT117_9 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK117 ⟨9, by decide⟩ R117 hpxR117 hcardq117 (by decide)).symm

/-- **Cell (117, 9).** -/
theorem cell117_9 (e : List (ZMod 25)) (heK : charOK (basisAt rK117) e = true)
    (h : ↥(reps (⟨9, by decide⟩ : Fin 148))) :
    species (reps (⟨9, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK117 e (h : Coordinate 1) T117_9 i :=
  species_entry_eq_sum rK117 ⟨9, by decide⟩ e heK h T117_9 hfix117_9 hinj117_9 hcardT117_9
    (fun i => conj_mem_of_fixedPoints (reps ⟨9, by decide⟩) (reps rK117) (T117_9 i) (hfix117_9 i) h)

/-! ## Cell (117, 10): |T| = 5 -/

def T117_10list : List Coordinates := [(0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0)]
def T117_10 : Fin 5 → Coordinate 1 := fun i => T117_10list.getD i.val (0,0,0,0,0)

theorem hfix117_10 : ∀ i, ((T117_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117) :=
  repsFix_of_siftB rK117 ⟨10, by decide⟩ T117_10 (by decide)

theorem hinj117_10 : Function.Injective
    (fun i => ((T117_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)) :=
  repsInj_of_reduceAux rK117 T117_10 (by decide)

theorem hcardT117_10 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK117 ⟨10, by decide⟩ R117 hpxR117 hcardq117 (by decide)).symm

/-- **Cell (117, 10).** -/
theorem cell117_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK117) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK117 e (h : Coordinate 1) T117_10 i :=
  species_entry_eq_sum rK117 ⟨10, by decide⟩ e heK h T117_10 hfix117_10 hinj117_10 hcardT117_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK117) (T117_10 i) (hfix117_10 i) h)

/-! ## Cell (117, 12): |T| = 5 -/

def T117_12list : List Coordinates := [(0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0)]
def T117_12 : Fin 5 → Coordinate 1 := fun i => T117_12list.getD i.val (0,0,0,0,0)

theorem hfix117_12 : ∀ i, ((T117_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117) :=
  repsFix_of_siftB rK117 ⟨12, by decide⟩ T117_12 (by decide)

theorem hinj117_12 : Function.Injective
    (fun i => ((T117_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)) :=
  repsInj_of_reduceAux rK117 T117_12 (by decide)

theorem hcardT117_12 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK117 ⟨12, by decide⟩ R117 hpxR117 hcardq117 (by decide)).symm

/-- **Cell (117, 12).** -/
theorem cell117_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK117) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK117 e (h : Coordinate 1) T117_12 i :=
  species_entry_eq_sum rK117 ⟨12, by decide⟩ e heK h T117_12 hfix117_12 hinj117_12 hcardT117_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK117) (T117_12 i) (hfix117_12 i) h)

/-! ## Cell (117, 13): |T| = 5 -/

def T117_13list : List Coordinates := [(0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0)]
def T117_13 : Fin 5 → Coordinate 1 := fun i => T117_13list.getD i.val (0,0,0,0,0)

theorem hfix117_13 : ∀ i, ((T117_13 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117) :=
  repsFix_of_siftB rK117 ⟨13, by decide⟩ T117_13 (by decide)

theorem hinj117_13 : Function.Injective
    (fun i => ((T117_13 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)) :=
  repsInj_of_reduceAux rK117 T117_13 (by decide)

theorem hcardT117_13 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK117 ⟨13, by decide⟩ R117 hpxR117 hcardq117 (by decide)).symm

/-- **Cell (117, 13).** -/
theorem cell117_13 (e : List (ZMod 25)) (heK : charOK (basisAt rK117) e = true)
    (h : ↥(reps (⟨13, by decide⟩ : Fin 148))) :
    species (reps (⟨13, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK117 e (h : Coordinate 1) T117_13 i :=
  species_entry_eq_sum rK117 ⟨13, by decide⟩ e heK h T117_13 hfix117_13 hinj117_13 hcardT117_13
    (fun i => conj_mem_of_fixedPoints (reps ⟨13, by decide⟩) (reps rK117) (T117_13 i) (hfix117_13 i) h)

/-! ## Cell (117, 19): |T| = 5 -/

def T117_19list : List Coordinates := [(0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0)]
def T117_19 : Fin 5 → Coordinate 1 := fun i => T117_19list.getD i.val (0,0,0,0,0)

theorem hfix117_19 : ∀ i, ((T117_19 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117) :=
  repsFix_of_siftB rK117 ⟨19, by decide⟩ T117_19 (by decide)

theorem hinj117_19 : Function.Injective
    (fun i => ((T117_19 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)) :=
  repsInj_of_reduceAux rK117 T117_19 (by decide)

theorem hcardT117_19 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK117 ⟨19, by decide⟩ R117 hpxR117 hcardq117 (by decide)).symm

/-- **Cell (117, 19).** -/
theorem cell117_19 (e : List (ZMod 25)) (heK : charOK (basisAt rK117) e = true)
    (h : ↥(reps (⟨19, by decide⟩ : Fin 148))) :
    species (reps (⟨19, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK117 e (h : Coordinate 1) T117_19 i :=
  species_entry_eq_sum rK117 ⟨19, by decide⟩ e heK h T117_19 hfix117_19 hinj117_19 hcardT117_19
    (fun i => conj_mem_of_fixedPoints (reps ⟨19, by decide⟩) (reps rK117) (T117_19 i) (hfix117_19 i) h)

/-! ## Cell (117, 24): |T| = 5 -/

def T117_24list : List Coordinates := [(0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0)]
def T117_24 : Fin 5 → Coordinate 1 := fun i => T117_24list.getD i.val (0,0,0,0,0)

theorem hfix117_24 : ∀ i, ((T117_24 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117) :=
  repsFix_of_siftB rK117 ⟨24, by decide⟩ T117_24 (by decide)

theorem hinj117_24 : Function.Injective
    (fun i => ((T117_24 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)) :=
  repsInj_of_reduceAux rK117 T117_24 (by decide)

theorem hcardT117_24 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK117 ⟨24, by decide⟩ R117 hpxR117 hcardq117 (by decide)).symm

/-- **Cell (117, 24).** -/
theorem cell117_24 (e : List (ZMod 25)) (heK : charOK (basisAt rK117) e = true)
    (h : ↥(reps (⟨24, by decide⟩ : Fin 148))) :
    species (reps (⟨24, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK117 e (h : Coordinate 1) T117_24 i :=
  species_entry_eq_sum rK117 ⟨24, by decide⟩ e heK h T117_24 hfix117_24 hinj117_24 hcardT117_24
    (fun i => conj_mem_of_fixedPoints (reps ⟨24, by decide⟩) (reps rK117) (T117_24 i) (hfix117_24 i) h)

/-! ## Cell (117, 25): |T| = 5 -/

def T117_25list : List Coordinates := [(0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0)]
def T117_25 : Fin 5 → Coordinate 1 := fun i => T117_25list.getD i.val (0,0,0,0,0)

theorem hfix117_25 : ∀ i, ((T117_25 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117) :=
  repsFix_of_siftB rK117 ⟨25, by decide⟩ T117_25 (by decide)

theorem hinj117_25 : Function.Injective
    (fun i => ((T117_25 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)) :=
  repsInj_of_reduceAux rK117 T117_25 (by decide)

theorem hcardT117_25 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK117 ⟨25, by decide⟩ R117 hpxR117 hcardq117 (by decide)).symm

/-- **Cell (117, 25).** -/
theorem cell117_25 (e : List (ZMod 25)) (heK : charOK (basisAt rK117) e = true)
    (h : ↥(reps (⟨25, by decide⟩ : Fin 148))) :
    species (reps (⟨25, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK117 e (h : Coordinate 1) T117_25 i :=
  species_entry_eq_sum rK117 ⟨25, by decide⟩ e heK h T117_25 hfix117_25 hinj117_25 hcardT117_25
    (fun i => conj_mem_of_fixedPoints (reps ⟨25, by decide⟩) (reps rK117) (T117_25 i) (hfix117_25 i) h)

/-! ## Cell (117, 26): |T| = 5 -/

def T117_26list : List Coordinates := [(0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0)]
def T117_26 : Fin 5 → Coordinate 1 := fun i => T117_26list.getD i.val (0,0,0,0,0)

theorem hfix117_26 : ∀ i, ((T117_26 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117) :=
  repsFix_of_siftB rK117 ⟨26, by decide⟩ T117_26 (by decide)

theorem hinj117_26 : Function.Injective
    (fun i => ((T117_26 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)) :=
  repsInj_of_reduceAux rK117 T117_26 (by decide)

theorem hcardT117_26 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK117 ⟨26, by decide⟩ R117 hpxR117 hcardq117 (by decide)).symm

/-- **Cell (117, 26).** -/
theorem cell117_26 (e : List (ZMod 25)) (heK : charOK (basisAt rK117) e = true)
    (h : ↥(reps (⟨26, by decide⟩ : Fin 148))) :
    species (reps (⟨26, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK117 e (h : Coordinate 1) T117_26 i :=
  species_entry_eq_sum rK117 ⟨26, by decide⟩ e heK h T117_26 hfix117_26 hinj117_26 hcardT117_26
    (fun i => conj_mem_of_fixedPoints (reps ⟨26, by decide⟩) (reps rK117) (T117_26 i) (hfix117_26 i) h)

/-! ## Cell (117, 27): |T| = 5 -/

def T117_27list : List Coordinates := [(0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0)]
def T117_27 : Fin 5 → Coordinate 1 := fun i => T117_27list.getD i.val (0,0,0,0,0)

theorem hfix117_27 : ∀ i, ((T117_27 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117) :=
  repsFix_of_siftB rK117 ⟨27, by decide⟩ T117_27 (by decide)

theorem hinj117_27 : Function.Injective
    (fun i => ((T117_27 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)) :=
  repsInj_of_reduceAux rK117 T117_27 (by decide)

theorem hcardT117_27 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK117 ⟨27, by decide⟩ R117 hpxR117 hcardq117 (by decide)).symm

/-- **Cell (117, 27).** -/
theorem cell117_27 (e : List (ZMod 25)) (heK : charOK (basisAt rK117) e = true)
    (h : ↥(reps (⟨27, by decide⟩ : Fin 148))) :
    species (reps (⟨27, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK117 e (h : Coordinate 1) T117_27 i :=
  species_entry_eq_sum rK117 ⟨27, by decide⟩ e heK h T117_27 hfix117_27 hinj117_27 hcardT117_27
    (fun i => conj_mem_of_fixedPoints (reps ⟨27, by decide⟩) (reps rK117) (T117_27 i) (hfix117_27 i) h)

/-! ## Cell (117, 29): |T| = 5 -/

def T117_29list : List Coordinates := [(0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0)]
def T117_29 : Fin 5 → Coordinate 1 := fun i => T117_29list.getD i.val (0,0,0,0,0)

theorem hfix117_29 : ∀ i, ((T117_29 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117) :=
  repsFix_of_siftB rK117 ⟨29, by decide⟩ T117_29 (by decide)

theorem hinj117_29 : Function.Injective
    (fun i => ((T117_29 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)) :=
  repsInj_of_reduceAux rK117 T117_29 (by decide)

theorem hcardT117_29 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK117 ⟨29, by decide⟩ R117 hpxR117 hcardq117 (by decide)).symm

/-- **Cell (117, 29).** -/
theorem cell117_29 (e : List (ZMod 25)) (heK : charOK (basisAt rK117) e = true)
    (h : ↥(reps (⟨29, by decide⟩ : Fin 148))) :
    species (reps (⟨29, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK117 e (h : Coordinate 1) T117_29 i :=
  species_entry_eq_sum rK117 ⟨29, by decide⟩ e heK h T117_29 hfix117_29 hinj117_29 hcardT117_29
    (fun i => conj_mem_of_fixedPoints (reps ⟨29, by decide⟩) (reps rK117) (T117_29 i) (hfix117_29 i) h)

/-! ## Cell (117, 34): |T| = 5 -/

def T117_34list : List Coordinates := [(0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0)]
def T117_34 : Fin 5 → Coordinate 1 := fun i => T117_34list.getD i.val (0,0,0,0,0)

theorem hfix117_34 : ∀ i, ((T117_34 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117) :=
  repsFix_of_siftB rK117 ⟨34, by decide⟩ T117_34 (by decide)

theorem hinj117_34 : Function.Injective
    (fun i => ((T117_34 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)) :=
  repsInj_of_reduceAux rK117 T117_34 (by decide)

theorem hcardT117_34 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK117 ⟨34, by decide⟩ R117 hpxR117 hcardq117 (by decide)).symm

/-- **Cell (117, 34).** -/
theorem cell117_34 (e : List (ZMod 25)) (heK : charOK (basisAt rK117) e = true)
    (h : ↥(reps (⟨34, by decide⟩ : Fin 148))) :
    species (reps (⟨34, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK117 e (h : Coordinate 1) T117_34 i :=
  species_entry_eq_sum rK117 ⟨34, by decide⟩ e heK h T117_34 hfix117_34 hinj117_34 hcardT117_34
    (fun i => conj_mem_of_fixedPoints (reps ⟨34, by decide⟩) (reps rK117) (T117_34 i) (hfix117_34 i) h)

/-! ## Cell (117, 39): |T| = 5 -/

def T117_39list : List Coordinates := [(0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0)]
def T117_39 : Fin 5 → Coordinate 1 := fun i => T117_39list.getD i.val (0,0,0,0,0)

theorem hfix117_39 : ∀ i, ((T117_39 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117) :=
  repsFix_of_siftB rK117 ⟨39, by decide⟩ T117_39 (by decide)

theorem hinj117_39 : Function.Injective
    (fun i => ((T117_39 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)) :=
  repsInj_of_reduceAux rK117 T117_39 (by decide)

theorem hcardT117_39 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK117 ⟨39, by decide⟩ R117 hpxR117 hcardq117 (by decide)).symm

/-- **Cell (117, 39).** -/
theorem cell117_39 (e : List (ZMod 25)) (heK : charOK (basisAt rK117) e = true)
    (h : ↥(reps (⟨39, by decide⟩ : Fin 148))) :
    species (reps (⟨39, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK117 e (h : Coordinate 1) T117_39 i :=
  species_entry_eq_sum rK117 ⟨39, by decide⟩ e heK h T117_39 hfix117_39 hinj117_39 hcardT117_39
    (fun i => conj_mem_of_fixedPoints (reps ⟨39, by decide⟩) (reps rK117) (T117_39 i) (hfix117_39 i) h)

/-! ## Cell (117, 44): |T| = 5 -/

def T117_44list : List Coordinates := [(0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0)]
def T117_44 : Fin 5 → Coordinate 1 := fun i => T117_44list.getD i.val (0,0,0,0,0)

theorem hfix117_44 : ∀ i, ((T117_44 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117) :=
  repsFix_of_siftB rK117 ⟨44, by decide⟩ T117_44 (by decide)

theorem hinj117_44 : Function.Injective
    (fun i => ((T117_44 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)) :=
  repsInj_of_reduceAux rK117 T117_44 (by decide)

theorem hcardT117_44 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK117 ⟨44, by decide⟩ R117 hpxR117 hcardq117 (by decide)).symm

/-- **Cell (117, 44).** -/
theorem cell117_44 (e : List (ZMod 25)) (heK : charOK (basisAt rK117) e = true)
    (h : ↥(reps (⟨44, by decide⟩ : Fin 148))) :
    species (reps (⟨44, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK117 e (h : Coordinate 1) T117_44 i :=
  species_entry_eq_sum rK117 ⟨44, by decide⟩ e heK h T117_44 hfix117_44 hinj117_44 hcardT117_44
    (fun i => conj_mem_of_fixedPoints (reps ⟨44, by decide⟩) (reps rK117) (T117_44 i) (hfix117_44 i) h)

/-! ## Cell (117, 49): |T| = 5 -/

def T117_49list : List Coordinates := [(0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0)]
def T117_49 : Fin 5 → Coordinate 1 := fun i => T117_49list.getD i.val (0,0,0,0,0)

theorem hfix117_49 : ∀ i, ((T117_49 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117) :=
  repsFix_of_siftB rK117 ⟨49, by decide⟩ T117_49 (by decide)

theorem hinj117_49 : Function.Injective
    (fun i => ((T117_49 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)) :=
  repsInj_of_reduceAux rK117 T117_49 (by decide)

theorem hcardT117_49 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK117 ⟨49, by decide⟩ R117 hpxR117 hcardq117 (by decide)).symm

/-- **Cell (117, 49).** -/
theorem cell117_49 (e : List (ZMod 25)) (heK : charOK (basisAt rK117) e = true)
    (h : ↥(reps (⟨49, by decide⟩ : Fin 148))) :
    species (reps (⟨49, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK117 e (h : Coordinate 1) T117_49 i :=
  species_entry_eq_sum rK117 ⟨49, by decide⟩ e heK h T117_49 hfix117_49 hinj117_49 hcardT117_49
    (fun i => conj_mem_of_fixedPoints (reps ⟨49, by decide⟩) (reps rK117) (T117_49 i) (hfix117_49 i) h)

/-! ## Cell (117, 53): |T| = 5 -/

def T117_53list : List Coordinates := [(0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0)]
def T117_53 : Fin 5 → Coordinate 1 := fun i => T117_53list.getD i.val (0,0,0,0,0)

theorem hfix117_53 : ∀ i, ((T117_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117) :=
  repsFix_of_siftB rK117 ⟨53, by decide⟩ T117_53 (by decide)

theorem hinj117_53 : Function.Injective
    (fun i => ((T117_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)) :=
  repsInj_of_reduceAux rK117 T117_53 (by decide)

theorem hcardT117_53 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK117 ⟨53, by decide⟩ R117 hpxR117 hcardq117 (by decide)).symm

/-- **Cell (117, 53).** -/
theorem cell117_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK117) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK117 e (h : Coordinate 1) T117_53 i :=
  species_entry_eq_sum rK117 ⟨53, by decide⟩ e heK h T117_53 hfix117_53 hinj117_53 hcardT117_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK117) (T117_53 i) (hfix117_53 i) h)

/-! ## Cell (117, 60): |T| = 5 -/

def T117_60list : List Coordinates := [(0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0)]
def T117_60 : Fin 5 → Coordinate 1 := fun i => T117_60list.getD i.val (0,0,0,0,0)

theorem hfix117_60 : ∀ i, ((T117_60 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117) :=
  repsFix_of_siftB rK117 ⟨60, by decide⟩ T117_60 (by decide)

theorem hinj117_60 : Function.Injective
    (fun i => ((T117_60 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)) :=
  repsInj_of_reduceAux rK117 T117_60 (by decide)

theorem hcardT117_60 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK117 ⟨60, by decide⟩ R117 hpxR117 hcardq117 (by decide)).symm

/-- **Cell (117, 60).** -/
theorem cell117_60 (e : List (ZMod 25)) (heK : charOK (basisAt rK117) e = true)
    (h : ↥(reps (⟨60, by decide⟩ : Fin 148))) :
    species (reps (⟨60, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK117 e (h : Coordinate 1) T117_60 i :=
  species_entry_eq_sum rK117 ⟨60, by decide⟩ e heK h T117_60 hfix117_60 hinj117_60 hcardT117_60
    (fun i => conj_mem_of_fixedPoints (reps ⟨60, by decide⟩) (reps rK117) (T117_60 i) (hfix117_60 i) h)

/-! ## Cell (117, 61): |T| = 5 -/

def T117_61list : List Coordinates := [(0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0)]
def T117_61 : Fin 5 → Coordinate 1 := fun i => T117_61list.getD i.val (0,0,0,0,0)

theorem hfix117_61 : ∀ i, ((T117_61 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117) :=
  repsFix_of_siftB rK117 ⟨61, by decide⟩ T117_61 (by decide)

theorem hinj117_61 : Function.Injective
    (fun i => ((T117_61 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)) :=
  repsInj_of_reduceAux rK117 T117_61 (by decide)

theorem hcardT117_61 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK117 ⟨61, by decide⟩ R117 hpxR117 hcardq117 (by decide)).symm

/-- **Cell (117, 61).** -/
theorem cell117_61 (e : List (ZMod 25)) (heK : charOK (basisAt rK117) e = true)
    (h : ↥(reps (⟨61, by decide⟩ : Fin 148))) :
    species (reps (⟨61, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK117 e (h : Coordinate 1) T117_61 i :=
  species_entry_eq_sum rK117 ⟨61, by decide⟩ e heK h T117_61 hfix117_61 hinj117_61 hcardT117_61
    (fun i => conj_mem_of_fixedPoints (reps ⟨61, by decide⟩) (reps rK117) (T117_61 i) (hfix117_61 i) h)

/-! ## Cell (117, 62): |T| = 5 -/

def T117_62list : List Coordinates := [(0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0)]
def T117_62 : Fin 5 → Coordinate 1 := fun i => T117_62list.getD i.val (0,0,0,0,0)

theorem hfix117_62 : ∀ i, ((T117_62 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117) :=
  repsFix_of_siftB rK117 ⟨62, by decide⟩ T117_62 (by decide)

theorem hinj117_62 : Function.Injective
    (fun i => ((T117_62 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)) :=
  repsInj_of_reduceAux rK117 T117_62 (by decide)

theorem hcardT117_62 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK117 ⟨62, by decide⟩ R117 hpxR117 hcardq117 (by decide)).symm

/-- **Cell (117, 62).** -/
theorem cell117_62 (e : List (ZMod 25)) (heK : charOK (basisAt rK117) e = true)
    (h : ↥(reps (⟨62, by decide⟩ : Fin 148))) :
    species (reps (⟨62, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK117 e (h : Coordinate 1) T117_62 i :=
  species_entry_eq_sum rK117 ⟨62, by decide⟩ e heK h T117_62 hfix117_62 hinj117_62 hcardT117_62
    (fun i => conj_mem_of_fixedPoints (reps ⟨62, by decide⟩) (reps rK117) (T117_62 i) (hfix117_62 i) h)

/-! ## Cell (117, 63): |T| = 5 -/

def T117_63list : List Coordinates := [(0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0)]
def T117_63 : Fin 5 → Coordinate 1 := fun i => T117_63list.getD i.val (0,0,0,0,0)

theorem hfix117_63 : ∀ i, ((T117_63 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117) :=
  repsFix_of_siftB rK117 ⟨63, by decide⟩ T117_63 (by decide)

theorem hinj117_63 : Function.Injective
    (fun i => ((T117_63 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)) :=
  repsInj_of_reduceAux rK117 T117_63 (by decide)

theorem hcardT117_63 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK117 ⟨63, by decide⟩ R117 hpxR117 hcardq117 (by decide)).symm

/-- **Cell (117, 63).** -/
theorem cell117_63 (e : List (ZMod 25)) (heK : charOK (basisAt rK117) e = true)
    (h : ↥(reps (⟨63, by decide⟩ : Fin 148))) :
    species (reps (⟨63, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK117 e (h : Coordinate 1) T117_63 i :=
  species_entry_eq_sum rK117 ⟨63, by decide⟩ e heK h T117_63 hfix117_63 hinj117_63 hcardT117_63
    (fun i => conj_mem_of_fixedPoints (reps ⟨63, by decide⟩) (reps rK117) (T117_63 i) (hfix117_63 i) h)

/-! ## Cell (117, 64): |T| = 5 -/

def T117_64list : List Coordinates := [(0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0)]
def T117_64 : Fin 5 → Coordinate 1 := fun i => T117_64list.getD i.val (0,0,0,0,0)

theorem hfix117_64 : ∀ i, ((T117_64 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117) :=
  repsFix_of_siftB rK117 ⟨64, by decide⟩ T117_64 (by decide)

theorem hinj117_64 : Function.Injective
    (fun i => ((T117_64 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)) :=
  repsInj_of_reduceAux rK117 T117_64 (by decide)

theorem hcardT117_64 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK117 ⟨64, by decide⟩ R117 hpxR117 hcardq117 (by decide)).symm

/-- **Cell (117, 64).** -/
theorem cell117_64 (e : List (ZMod 25)) (heK : charOK (basisAt rK117) e = true)
    (h : ↥(reps (⟨64, by decide⟩ : Fin 148))) :
    species (reps (⟨64, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK117 e (h : Coordinate 1) T117_64 i :=
  species_entry_eq_sum rK117 ⟨64, by decide⟩ e heK h T117_64 hfix117_64 hinj117_64 hcardT117_64
    (fun i => conj_mem_of_fixedPoints (reps ⟨64, by decide⟩) (reps rK117) (T117_64 i) (hfix117_64 i) h)

/-! ## Cell (117, 80): |T| = 5 -/

def T117_80list : List Coordinates := [(0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0)]
def T117_80 : Fin 5 → Coordinate 1 := fun i => T117_80list.getD i.val (0,0,0,0,0)

theorem hfix117_80 : ∀ i, ((T117_80 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117) :=
  repsFix_of_siftB rK117 ⟨80, by decide⟩ T117_80 (by decide)

theorem hinj117_80 : Function.Injective
    (fun i => ((T117_80 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)) :=
  repsInj_of_reduceAux rK117 T117_80 (by decide)

theorem hcardT117_80 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK117 ⟨80, by decide⟩ R117 hpxR117 hcardq117 (by decide)).symm

/-- **Cell (117, 80).** -/
theorem cell117_80 (e : List (ZMod 25)) (heK : charOK (basisAt rK117) e = true)
    (h : ↥(reps (⟨80, by decide⟩ : Fin 148))) :
    species (reps (⟨80, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK117 e (h : Coordinate 1) T117_80 i :=
  species_entry_eq_sum rK117 ⟨80, by decide⟩ e heK h T117_80 hfix117_80 hinj117_80 hcardT117_80
    (fun i => conj_mem_of_fixedPoints (reps ⟨80, by decide⟩) (reps rK117) (T117_80 i) (hfix117_80 i) h)

/-! ## Cell (117, 91): |T| = 5 -/

def T117_91list : List Coordinates := [(0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0)]
def T117_91 : Fin 5 → Coordinate 1 := fun i => T117_91list.getD i.val (0,0,0,0,0)

theorem hfix117_91 : ∀ i, ((T117_91 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117) :=
  repsFix_of_siftB rK117 ⟨91, by decide⟩ T117_91 (by decide)

theorem hinj117_91 : Function.Injective
    (fun i => ((T117_91 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)) :=
  repsInj_of_reduceAux rK117 T117_91 (by decide)

theorem hcardT117_91 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK117 ⟨91, by decide⟩ R117 hpxR117 hcardq117 (by decide)).symm

/-- **Cell (117, 91).** -/
theorem cell117_91 (e : List (ZMod 25)) (heK : charOK (basisAt rK117) e = true)
    (h : ↥(reps (⟨91, by decide⟩ : Fin 148))) :
    species (reps (⟨91, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK117 e (h : Coordinate 1) T117_91 i :=
  species_entry_eq_sum rK117 ⟨91, by decide⟩ e heK h T117_91 hfix117_91 hinj117_91 hcardT117_91
    (fun i => conj_mem_of_fixedPoints (reps ⟨91, by decide⟩) (reps rK117) (T117_91 i) (hfix117_91 i) h)

/-! ## Cell (117, 96): |T| = 5 -/

def T117_96list : List Coordinates := [(0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0)]
def T117_96 : Fin 5 → Coordinate 1 := fun i => T117_96list.getD i.val (0,0,0,0,0)

theorem hfix117_96 : ∀ i, ((T117_96 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117) :=
  repsFix_of_siftB rK117 ⟨96, by decide⟩ T117_96 (by decide)

theorem hinj117_96 : Function.Injective
    (fun i => ((T117_96 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)) :=
  repsInj_of_reduceAux rK117 T117_96 (by decide)

theorem hcardT117_96 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK117 ⟨96, by decide⟩ R117 hpxR117 hcardq117 (by decide)).symm

/-- **Cell (117, 96).** -/
theorem cell117_96 (e : List (ZMod 25)) (heK : charOK (basisAt rK117) e = true)
    (h : ↥(reps (⟨96, by decide⟩ : Fin 148))) :
    species (reps (⟨96, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK117 e (h : Coordinate 1) T117_96 i :=
  species_entry_eq_sum rK117 ⟨96, by decide⟩ e heK h T117_96 hfix117_96 hinj117_96 hcardT117_96
    (fun i => conj_mem_of_fixedPoints (reps ⟨96, by decide⟩) (reps rK117) (T117_96 i) (hfix117_96 i) h)

/-! ## Cell (117, 101): |T| = 5 -/

def T117_101list : List Coordinates := [(0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0)]
def T117_101 : Fin 5 → Coordinate 1 := fun i => T117_101list.getD i.val (0,0,0,0,0)

theorem hfix117_101 : ∀ i, ((T117_101 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117) :=
  repsFix_of_siftB rK117 ⟨101, by decide⟩ T117_101 (by decide)

theorem hinj117_101 : Function.Injective
    (fun i => ((T117_101 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)) :=
  repsInj_of_reduceAux rK117 T117_101 (by decide)

theorem hcardT117_101 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK117 ⟨101, by decide⟩ R117 hpxR117 hcardq117 (by decide)).symm

/-- **Cell (117, 101).** -/
theorem cell117_101 (e : List (ZMod 25)) (heK : charOK (basisAt rK117) e = true)
    (h : ↥(reps (⟨101, by decide⟩ : Fin 148))) :
    species (reps (⟨101, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK117 e (h : Coordinate 1) T117_101 i :=
  species_entry_eq_sum rK117 ⟨101, by decide⟩ e heK h T117_101 hfix117_101 hinj117_101 hcardT117_101
    (fun i => conj_mem_of_fixedPoints (reps ⟨101, by decide⟩) (reps rK117) (T117_101 i) (hfix117_101 i) h)

/-! ## Cell (117, 106): |T| = 5 -/

def T117_106list : List Coordinates := [(0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0)]
def T117_106 : Fin 5 → Coordinate 1 := fun i => T117_106list.getD i.val (0,0,0,0,0)

theorem hfix117_106 : ∀ i, ((T117_106 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117) :=
  repsFix_of_siftB rK117 ⟨106, by decide⟩ T117_106 (by decide)

theorem hinj117_106 : Function.Injective
    (fun i => ((T117_106 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)) :=
  repsInj_of_reduceAux rK117 T117_106 (by decide)

theorem hcardT117_106 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK117 ⟨106, by decide⟩ R117 hpxR117 hcardq117 (by decide)).symm

/-- **Cell (117, 106).** -/
theorem cell117_106 (e : List (ZMod 25)) (heK : charOK (basisAt rK117) e = true)
    (h : ↥(reps (⟨106, by decide⟩ : Fin 148))) :
    species (reps (⟨106, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK117 e (h : Coordinate 1) T117_106 i :=
  species_entry_eq_sum rK117 ⟨106, by decide⟩ e heK h T117_106 hfix117_106 hinj117_106 hcardT117_106
    (fun i => conj_mem_of_fixedPoints (reps ⟨106, by decide⟩) (reps rK117) (T117_106 i) (hfix117_106 i) h)

/-! ## Cell (117, 111): |T| = 5 -/

def T117_111list : List Coordinates := [(0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0)]
def T117_111 : Fin 5 → Coordinate 1 := fun i => T117_111list.getD i.val (0,0,0,0,0)

theorem hfix117_111 : ∀ i, ((T117_111 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117) :=
  repsFix_of_siftB rK117 ⟨111, by decide⟩ T117_111 (by decide)

theorem hinj117_111 : Function.Injective
    (fun i => ((T117_111 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)) :=
  repsInj_of_reduceAux rK117 T117_111 (by decide)

theorem hcardT117_111 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK117 ⟨111, by decide⟩ R117 hpxR117 hcardq117 (by decide)).symm

/-- **Cell (117, 111).** -/
theorem cell117_111 (e : List (ZMod 25)) (heK : charOK (basisAt rK117) e = true)
    (h : ↥(reps (⟨111, by decide⟩ : Fin 148))) :
    species (reps (⟨111, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK117 e (h : Coordinate 1) T117_111 i :=
  species_entry_eq_sum rK117 ⟨111, by decide⟩ e heK h T117_111 hfix117_111 hinj117_111 hcardT117_111
    (fun i => conj_mem_of_fixedPoints (reps ⟨111, by decide⟩) (reps rK117) (T117_111 i) (hfix117_111 i) h)

/-! ## Cell (117, 117): |T| = 5 -/

def T117_117list : List Coordinates := [(0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0)]
def T117_117 : Fin 5 → Coordinate 1 := fun i => T117_117list.getD i.val (0,0,0,0,0)

theorem hfix117_117 : ∀ i, ((T117_117 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117) :=
  repsFix_of_siftB rK117 ⟨117, by decide⟩ T117_117 (by decide)

theorem hinj117_117 : Function.Injective
    (fun i => ((T117_117 i : Coordinate 1) : Coordinate 1 ⧸ reps rK117)) :=
  repsInj_of_reduceAux rK117 T117_117 (by decide)

theorem hcardT117_117 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK117 ⟨117, by decide⟩ R117 hpxR117 hcardq117 (by decide)).symm

/-- **Cell (117, 117).** -/
theorem cell117_117 (e : List (ZMod 25)) (heK : charOK (basisAt rK117) e = true)
    (h : ↥(reps (⟨117, by decide⟩ : Fin 148))) :
    species (reps (⟨117, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK117 e (h : Coordinate 1) T117_117 i :=
  species_entry_eq_sum rK117 ⟨117, by decide⟩ e heK h T117_117 hfix117_117 hinj117_117 hcardT117_117
    (fun i => conj_mem_of_fixedPoints (reps ⟨117, by decide⟩) (reps rK117) (T117_117 i) (hfix117_117 i) h)

namespace Q2

def R117_2 : Fin 5 → Coordinate 2 := fun i => R117list.getD i.val (0,0,0,0,0)
theorem hpxR117_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK117) (R117_2 i)) := by decide
theorem hcardq117_2 : Nat.card (Coordinate 2 ⧸ reps rK117) = 5 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (117, 0) twin -/

def T117_0_2 : Fin 5 → Coordinate 2 := fun i => T117_0list.getD i.val (0,0,0,0,0)

theorem hfix117_0_2 : ∀ i, ((T117_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117) :=
  repsFix_of_siftB2 rK117 ⟨0, by decide⟩ T117_0_2 (by decide)

theorem hinj117_0_2 : Function.Injective
    (fun i => ((T117_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)) :=
  repsInj_of_reduceAux2 rK117 T117_0_2 (by decide)

theorem hcardT117_0_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK117 ⟨0, by decide⟩ R117_2 hpxR117_2 hcardq117_2 (by decide)).symm

/-- **Cell (117, 0) twin (q=2).** -/
theorem cell117_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK117) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec2 rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK117 e (h : Coordinate 2) T117_0_2 i :=
  species_entry_eq_sum rK117 ⟨0, by decide⟩ e heK h T117_0_2 hfix117_0_2 hinj117_0_2 hcardT117_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK117) (T117_0_2 i) (hfix117_0_2 i) h)

/-! ### Cell (117, 1) twin -/

def T117_1_2 : Fin 5 → Coordinate 2 := fun i => T117_1list.getD i.val (0,0,0,0,0)

theorem hfix117_1_2 : ∀ i, ((T117_1_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117) :=
  repsFix_of_siftB2 rK117 ⟨1, by decide⟩ T117_1_2 (by decide)

theorem hinj117_1_2 : Function.Injective
    (fun i => ((T117_1_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)) :=
  repsInj_of_reduceAux2 rK117 T117_1_2 (by decide)

theorem hcardT117_1_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK117 ⟨1, by decide⟩ R117_2 hpxR117_2 hcardq117_2 (by decide)).symm

/-- **Cell (117, 1) twin (q=2).** -/
theorem cell117_1_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK117) e = true)
    (h : ↥(reps (⟨1, by decide⟩ : Fin 148))) :
    species (reps (⟨1, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec2 rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK117 e (h : Coordinate 2) T117_1_2 i :=
  species_entry_eq_sum rK117 ⟨1, by decide⟩ e heK h T117_1_2 hfix117_1_2 hinj117_1_2 hcardT117_1_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨1, by decide⟩) (reps rK117) (T117_1_2 i) (hfix117_1_2 i) h)

/-! ### Cell (117, 6) twin -/

def T117_6_2 : Fin 5 → Coordinate 2 := fun i => T117_6list.getD i.val (0,0,0,0,0)

theorem hfix117_6_2 : ∀ i, ((T117_6_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117) :=
  repsFix_of_siftB2 rK117 ⟨6, by decide⟩ T117_6_2 (by decide)

theorem hinj117_6_2 : Function.Injective
    (fun i => ((T117_6_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)) :=
  repsInj_of_reduceAux2 rK117 T117_6_2 (by decide)

theorem hcardT117_6_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK117 ⟨6, by decide⟩ R117_2 hpxR117_2 hcardq117_2 (by decide)).symm

/-- **Cell (117, 6) twin (q=2).** -/
theorem cell117_6_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK117) e = true)
    (h : ↥(reps (⟨6, by decide⟩ : Fin 148))) :
    species (reps (⟨6, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec2 rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK117 e (h : Coordinate 2) T117_6_2 i :=
  species_entry_eq_sum rK117 ⟨6, by decide⟩ e heK h T117_6_2 hfix117_6_2 hinj117_6_2 hcardT117_6_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨6, by decide⟩) (reps rK117) (T117_6_2 i) (hfix117_6_2 i) h)

/-! ### Cell (117, 7) twin -/

def T117_7_2 : Fin 5 → Coordinate 2 := fun i => T117_7list.getD i.val (0,0,0,0,0)

theorem hfix117_7_2 : ∀ i, ((T117_7_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117) :=
  repsFix_of_siftB2 rK117 ⟨7, by decide⟩ T117_7_2 (by decide)

theorem hinj117_7_2 : Function.Injective
    (fun i => ((T117_7_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)) :=
  repsInj_of_reduceAux2 rK117 T117_7_2 (by decide)

theorem hcardT117_7_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK117 ⟨7, by decide⟩ R117_2 hpxR117_2 hcardq117_2 (by decide)).symm

/-- **Cell (117, 7) twin (q=2).** -/
theorem cell117_7_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK117) e = true)
    (h : ↥(reps (⟨7, by decide⟩ : Fin 148))) :
    species (reps (⟨7, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec2 rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK117 e (h : Coordinate 2) T117_7_2 i :=
  species_entry_eq_sum rK117 ⟨7, by decide⟩ e heK h T117_7_2 hfix117_7_2 hinj117_7_2 hcardT117_7_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨7, by decide⟩) (reps rK117) (T117_7_2 i) (hfix117_7_2 i) h)

/-! ### Cell (117, 8) twin -/

def T117_8_2 : Fin 5 → Coordinate 2 := fun i => T117_8list.getD i.val (0,0,0,0,0)

theorem hfix117_8_2 : ∀ i, ((T117_8_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117) :=
  repsFix_of_siftB2 rK117 ⟨8, by decide⟩ T117_8_2 (by decide)

theorem hinj117_8_2 : Function.Injective
    (fun i => ((T117_8_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)) :=
  repsInj_of_reduceAux2 rK117 T117_8_2 (by decide)

theorem hcardT117_8_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK117 ⟨8, by decide⟩ R117_2 hpxR117_2 hcardq117_2 (by decide)).symm

/-- **Cell (117, 8) twin (q=2).** -/
theorem cell117_8_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK117) e = true)
    (h : ↥(reps (⟨8, by decide⟩ : Fin 148))) :
    species (reps (⟨8, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec2 rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK117 e (h : Coordinate 2) T117_8_2 i :=
  species_entry_eq_sum rK117 ⟨8, by decide⟩ e heK h T117_8_2 hfix117_8_2 hinj117_8_2 hcardT117_8_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨8, by decide⟩) (reps rK117) (T117_8_2 i) (hfix117_8_2 i) h)

/-! ### Cell (117, 9) twin -/

def T117_9_2 : Fin 5 → Coordinate 2 := fun i => T117_9list.getD i.val (0,0,0,0,0)

theorem hfix117_9_2 : ∀ i, ((T117_9_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117) :=
  repsFix_of_siftB2 rK117 ⟨9, by decide⟩ T117_9_2 (by decide)

theorem hinj117_9_2 : Function.Injective
    (fun i => ((T117_9_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)) :=
  repsInj_of_reduceAux2 rK117 T117_9_2 (by decide)

theorem hcardT117_9_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK117 ⟨9, by decide⟩ R117_2 hpxR117_2 hcardq117_2 (by decide)).symm

/-- **Cell (117, 9) twin (q=2).** -/
theorem cell117_9_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK117) e = true)
    (h : ↥(reps (⟨9, by decide⟩ : Fin 148))) :
    species (reps (⟨9, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec2 rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK117 e (h : Coordinate 2) T117_9_2 i :=
  species_entry_eq_sum rK117 ⟨9, by decide⟩ e heK h T117_9_2 hfix117_9_2 hinj117_9_2 hcardT117_9_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨9, by decide⟩) (reps rK117) (T117_9_2 i) (hfix117_9_2 i) h)

/-! ### Cell (117, 10) twin -/

def T117_10_2 : Fin 5 → Coordinate 2 := fun i => T117_10list.getD i.val (0,0,0,0,0)

theorem hfix117_10_2 : ∀ i, ((T117_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117) :=
  repsFix_of_siftB2 rK117 ⟨10, by decide⟩ T117_10_2 (by decide)

theorem hinj117_10_2 : Function.Injective
    (fun i => ((T117_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)) :=
  repsInj_of_reduceAux2 rK117 T117_10_2 (by decide)

theorem hcardT117_10_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK117 ⟨10, by decide⟩ R117_2 hpxR117_2 hcardq117_2 (by decide)).symm

/-- **Cell (117, 10) twin (q=2).** -/
theorem cell117_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK117) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec2 rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK117 e (h : Coordinate 2) T117_10_2 i :=
  species_entry_eq_sum rK117 ⟨10, by decide⟩ e heK h T117_10_2 hfix117_10_2 hinj117_10_2 hcardT117_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK117) (T117_10_2 i) (hfix117_10_2 i) h)

/-! ### Cell (117, 12) twin -/

def T117_12_2 : Fin 5 → Coordinate 2 := fun i => T117_12list.getD i.val (0,0,0,0,0)

theorem hfix117_12_2 : ∀ i, ((T117_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117) :=
  repsFix_of_siftB2 rK117 ⟨12, by decide⟩ T117_12_2 (by decide)

theorem hinj117_12_2 : Function.Injective
    (fun i => ((T117_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)) :=
  repsInj_of_reduceAux2 rK117 T117_12_2 (by decide)

theorem hcardT117_12_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK117 ⟨12, by decide⟩ R117_2 hpxR117_2 hcardq117_2 (by decide)).symm

/-- **Cell (117, 12) twin (q=2).** -/
theorem cell117_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK117) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec2 rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK117 e (h : Coordinate 2) T117_12_2 i :=
  species_entry_eq_sum rK117 ⟨12, by decide⟩ e heK h T117_12_2 hfix117_12_2 hinj117_12_2 hcardT117_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK117) (T117_12_2 i) (hfix117_12_2 i) h)

/-! ### Cell (117, 13) twin -/

def T117_13_2 : Fin 5 → Coordinate 2 := fun i => T117_13list.getD i.val (0,0,0,0,0)

theorem hfix117_13_2 : ∀ i, ((T117_13_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117) :=
  repsFix_of_siftB2 rK117 ⟨13, by decide⟩ T117_13_2 (by decide)

theorem hinj117_13_2 : Function.Injective
    (fun i => ((T117_13_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)) :=
  repsInj_of_reduceAux2 rK117 T117_13_2 (by decide)

theorem hcardT117_13_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK117 ⟨13, by decide⟩ R117_2 hpxR117_2 hcardq117_2 (by decide)).symm

/-- **Cell (117, 13) twin (q=2).** -/
theorem cell117_13_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK117) e = true)
    (h : ↥(reps (⟨13, by decide⟩ : Fin 148))) :
    species (reps (⟨13, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec2 rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK117 e (h : Coordinate 2) T117_13_2 i :=
  species_entry_eq_sum rK117 ⟨13, by decide⟩ e heK h T117_13_2 hfix117_13_2 hinj117_13_2 hcardT117_13_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨13, by decide⟩) (reps rK117) (T117_13_2 i) (hfix117_13_2 i) h)

/-! ### Cell (117, 19) twin -/

def T117_19_2 : Fin 5 → Coordinate 2 := fun i => T117_19list.getD i.val (0,0,0,0,0)

theorem hfix117_19_2 : ∀ i, ((T117_19_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117) :=
  repsFix_of_siftB2 rK117 ⟨19, by decide⟩ T117_19_2 (by decide)

theorem hinj117_19_2 : Function.Injective
    (fun i => ((T117_19_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)) :=
  repsInj_of_reduceAux2 rK117 T117_19_2 (by decide)

theorem hcardT117_19_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK117 ⟨19, by decide⟩ R117_2 hpxR117_2 hcardq117_2 (by decide)).symm

/-- **Cell (117, 19) twin (q=2).** -/
theorem cell117_19_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK117) e = true)
    (h : ↥(reps (⟨19, by decide⟩ : Fin 148))) :
    species (reps (⟨19, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec2 rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK117 e (h : Coordinate 2) T117_19_2 i :=
  species_entry_eq_sum rK117 ⟨19, by decide⟩ e heK h T117_19_2 hfix117_19_2 hinj117_19_2 hcardT117_19_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨19, by decide⟩) (reps rK117) (T117_19_2 i) (hfix117_19_2 i) h)

/-! ### Cell (117, 24) twin -/

def T117_24_2 : Fin 5 → Coordinate 2 := fun i => T117_24list.getD i.val (0,0,0,0,0)

theorem hfix117_24_2 : ∀ i, ((T117_24_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117) :=
  repsFix_of_siftB2 rK117 ⟨24, by decide⟩ T117_24_2 (by decide)

theorem hinj117_24_2 : Function.Injective
    (fun i => ((T117_24_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)) :=
  repsInj_of_reduceAux2 rK117 T117_24_2 (by decide)

theorem hcardT117_24_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK117 ⟨24, by decide⟩ R117_2 hpxR117_2 hcardq117_2 (by decide)).symm

/-- **Cell (117, 24) twin (q=2).** -/
theorem cell117_24_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK117) e = true)
    (h : ↥(reps (⟨24, by decide⟩ : Fin 148))) :
    species (reps (⟨24, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec2 rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK117 e (h : Coordinate 2) T117_24_2 i :=
  species_entry_eq_sum rK117 ⟨24, by decide⟩ e heK h T117_24_2 hfix117_24_2 hinj117_24_2 hcardT117_24_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨24, by decide⟩) (reps rK117) (T117_24_2 i) (hfix117_24_2 i) h)

/-! ### Cell (117, 25) twin -/

def T117_25_2 : Fin 5 → Coordinate 2 := fun i => T117_25list.getD i.val (0,0,0,0,0)

theorem hfix117_25_2 : ∀ i, ((T117_25_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117) :=
  repsFix_of_siftB2 rK117 ⟨25, by decide⟩ T117_25_2 (by decide)

theorem hinj117_25_2 : Function.Injective
    (fun i => ((T117_25_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)) :=
  repsInj_of_reduceAux2 rK117 T117_25_2 (by decide)

theorem hcardT117_25_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK117 ⟨25, by decide⟩ R117_2 hpxR117_2 hcardq117_2 (by decide)).symm

/-- **Cell (117, 25) twin (q=2).** -/
theorem cell117_25_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK117) e = true)
    (h : ↥(reps (⟨25, by decide⟩ : Fin 148))) :
    species (reps (⟨25, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec2 rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK117 e (h : Coordinate 2) T117_25_2 i :=
  species_entry_eq_sum rK117 ⟨25, by decide⟩ e heK h T117_25_2 hfix117_25_2 hinj117_25_2 hcardT117_25_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨25, by decide⟩) (reps rK117) (T117_25_2 i) (hfix117_25_2 i) h)

/-! ### Cell (117, 26) twin -/

def T117_26_2 : Fin 5 → Coordinate 2 := fun i => T117_26list.getD i.val (0,0,0,0,0)

theorem hfix117_26_2 : ∀ i, ((T117_26_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117) :=
  repsFix_of_siftB2 rK117 ⟨26, by decide⟩ T117_26_2 (by decide)

theorem hinj117_26_2 : Function.Injective
    (fun i => ((T117_26_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)) :=
  repsInj_of_reduceAux2 rK117 T117_26_2 (by decide)

theorem hcardT117_26_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK117 ⟨26, by decide⟩ R117_2 hpxR117_2 hcardq117_2 (by decide)).symm

/-- **Cell (117, 26) twin (q=2).** -/
theorem cell117_26_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK117) e = true)
    (h : ↥(reps (⟨26, by decide⟩ : Fin 148))) :
    species (reps (⟨26, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec2 rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK117 e (h : Coordinate 2) T117_26_2 i :=
  species_entry_eq_sum rK117 ⟨26, by decide⟩ e heK h T117_26_2 hfix117_26_2 hinj117_26_2 hcardT117_26_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨26, by decide⟩) (reps rK117) (T117_26_2 i) (hfix117_26_2 i) h)

/-! ### Cell (117, 27) twin -/

def T117_27_2 : Fin 5 → Coordinate 2 := fun i => T117_27list.getD i.val (0,0,0,0,0)

theorem hfix117_27_2 : ∀ i, ((T117_27_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117) :=
  repsFix_of_siftB2 rK117 ⟨27, by decide⟩ T117_27_2 (by decide)

theorem hinj117_27_2 : Function.Injective
    (fun i => ((T117_27_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)) :=
  repsInj_of_reduceAux2 rK117 T117_27_2 (by decide)

theorem hcardT117_27_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK117 ⟨27, by decide⟩ R117_2 hpxR117_2 hcardq117_2 (by decide)).symm

/-- **Cell (117, 27) twin (q=2).** -/
theorem cell117_27_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK117) e = true)
    (h : ↥(reps (⟨27, by decide⟩ : Fin 148))) :
    species (reps (⟨27, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec2 rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK117 e (h : Coordinate 2) T117_27_2 i :=
  species_entry_eq_sum rK117 ⟨27, by decide⟩ e heK h T117_27_2 hfix117_27_2 hinj117_27_2 hcardT117_27_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨27, by decide⟩) (reps rK117) (T117_27_2 i) (hfix117_27_2 i) h)

/-! ### Cell (117, 29) twin -/

def T117_29_2 : Fin 5 → Coordinate 2 := fun i => T117_29list.getD i.val (0,0,0,0,0)

theorem hfix117_29_2 : ∀ i, ((T117_29_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117) :=
  repsFix_of_siftB2 rK117 ⟨29, by decide⟩ T117_29_2 (by decide)

theorem hinj117_29_2 : Function.Injective
    (fun i => ((T117_29_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)) :=
  repsInj_of_reduceAux2 rK117 T117_29_2 (by decide)

theorem hcardT117_29_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK117 ⟨29, by decide⟩ R117_2 hpxR117_2 hcardq117_2 (by decide)).symm

/-- **Cell (117, 29) twin (q=2).** -/
theorem cell117_29_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK117) e = true)
    (h : ↥(reps (⟨29, by decide⟩ : Fin 148))) :
    species (reps (⟨29, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec2 rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK117 e (h : Coordinate 2) T117_29_2 i :=
  species_entry_eq_sum rK117 ⟨29, by decide⟩ e heK h T117_29_2 hfix117_29_2 hinj117_29_2 hcardT117_29_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨29, by decide⟩) (reps rK117) (T117_29_2 i) (hfix117_29_2 i) h)

/-! ### Cell (117, 34) twin -/

def T117_34_2 : Fin 5 → Coordinate 2 := fun i => T117_34list.getD i.val (0,0,0,0,0)

theorem hfix117_34_2 : ∀ i, ((T117_34_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117) :=
  repsFix_of_siftB2 rK117 ⟨34, by decide⟩ T117_34_2 (by decide)

theorem hinj117_34_2 : Function.Injective
    (fun i => ((T117_34_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)) :=
  repsInj_of_reduceAux2 rK117 T117_34_2 (by decide)

theorem hcardT117_34_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK117 ⟨34, by decide⟩ R117_2 hpxR117_2 hcardq117_2 (by decide)).symm

/-- **Cell (117, 34) twin (q=2).** -/
theorem cell117_34_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK117) e = true)
    (h : ↥(reps (⟨34, by decide⟩ : Fin 148))) :
    species (reps (⟨34, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec2 rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK117 e (h : Coordinate 2) T117_34_2 i :=
  species_entry_eq_sum rK117 ⟨34, by decide⟩ e heK h T117_34_2 hfix117_34_2 hinj117_34_2 hcardT117_34_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨34, by decide⟩) (reps rK117) (T117_34_2 i) (hfix117_34_2 i) h)

/-! ### Cell (117, 39) twin -/

def T117_39_2 : Fin 5 → Coordinate 2 := fun i => T117_39list.getD i.val (0,0,0,0,0)

theorem hfix117_39_2 : ∀ i, ((T117_39_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117) :=
  repsFix_of_siftB2 rK117 ⟨39, by decide⟩ T117_39_2 (by decide)

theorem hinj117_39_2 : Function.Injective
    (fun i => ((T117_39_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)) :=
  repsInj_of_reduceAux2 rK117 T117_39_2 (by decide)

theorem hcardT117_39_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK117 ⟨39, by decide⟩ R117_2 hpxR117_2 hcardq117_2 (by decide)).symm

/-- **Cell (117, 39) twin (q=2).** -/
theorem cell117_39_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK117) e = true)
    (h : ↥(reps (⟨39, by decide⟩ : Fin 148))) :
    species (reps (⟨39, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec2 rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK117 e (h : Coordinate 2) T117_39_2 i :=
  species_entry_eq_sum rK117 ⟨39, by decide⟩ e heK h T117_39_2 hfix117_39_2 hinj117_39_2 hcardT117_39_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨39, by decide⟩) (reps rK117) (T117_39_2 i) (hfix117_39_2 i) h)

/-! ### Cell (117, 44) twin -/

def T117_44_2 : Fin 5 → Coordinate 2 := fun i => T117_44list.getD i.val (0,0,0,0,0)

theorem hfix117_44_2 : ∀ i, ((T117_44_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117) :=
  repsFix_of_siftB2 rK117 ⟨44, by decide⟩ T117_44_2 (by decide)

theorem hinj117_44_2 : Function.Injective
    (fun i => ((T117_44_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)) :=
  repsInj_of_reduceAux2 rK117 T117_44_2 (by decide)

theorem hcardT117_44_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK117 ⟨44, by decide⟩ R117_2 hpxR117_2 hcardq117_2 (by decide)).symm

/-- **Cell (117, 44) twin (q=2).** -/
theorem cell117_44_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK117) e = true)
    (h : ↥(reps (⟨44, by decide⟩ : Fin 148))) :
    species (reps (⟨44, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec2 rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK117 e (h : Coordinate 2) T117_44_2 i :=
  species_entry_eq_sum rK117 ⟨44, by decide⟩ e heK h T117_44_2 hfix117_44_2 hinj117_44_2 hcardT117_44_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨44, by decide⟩) (reps rK117) (T117_44_2 i) (hfix117_44_2 i) h)

/-! ### Cell (117, 49) twin -/

def T117_49_2 : Fin 5 → Coordinate 2 := fun i => T117_49list.getD i.val (0,0,0,0,0)

theorem hfix117_49_2 : ∀ i, ((T117_49_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117) :=
  repsFix_of_siftB2 rK117 ⟨49, by decide⟩ T117_49_2 (by decide)

theorem hinj117_49_2 : Function.Injective
    (fun i => ((T117_49_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)) :=
  repsInj_of_reduceAux2 rK117 T117_49_2 (by decide)

theorem hcardT117_49_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK117 ⟨49, by decide⟩ R117_2 hpxR117_2 hcardq117_2 (by decide)).symm

/-- **Cell (117, 49) twin (q=2).** -/
theorem cell117_49_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK117) e = true)
    (h : ↥(reps (⟨49, by decide⟩ : Fin 148))) :
    species (reps (⟨49, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec2 rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK117 e (h : Coordinate 2) T117_49_2 i :=
  species_entry_eq_sum rK117 ⟨49, by decide⟩ e heK h T117_49_2 hfix117_49_2 hinj117_49_2 hcardT117_49_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨49, by decide⟩) (reps rK117) (T117_49_2 i) (hfix117_49_2 i) h)

/-! ### Cell (117, 53) twin -/

def T117_53_2 : Fin 5 → Coordinate 2 := fun i => T117_53list.getD i.val (0,0,0,0,0)

theorem hfix117_53_2 : ∀ i, ((T117_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117) :=
  repsFix_of_siftB2 rK117 ⟨53, by decide⟩ T117_53_2 (by decide)

theorem hinj117_53_2 : Function.Injective
    (fun i => ((T117_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)) :=
  repsInj_of_reduceAux2 rK117 T117_53_2 (by decide)

theorem hcardT117_53_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK117 ⟨53, by decide⟩ R117_2 hpxR117_2 hcardq117_2 (by decide)).symm

/-- **Cell (117, 53) twin (q=2).** -/
theorem cell117_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK117) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec2 rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK117 e (h : Coordinate 2) T117_53_2 i :=
  species_entry_eq_sum rK117 ⟨53, by decide⟩ e heK h T117_53_2 hfix117_53_2 hinj117_53_2 hcardT117_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK117) (T117_53_2 i) (hfix117_53_2 i) h)

/-! ### Cell (117, 60) twin -/

def T117_60_2 : Fin 5 → Coordinate 2 := fun i => T117_60list.getD i.val (0,0,0,0,0)

theorem hfix117_60_2 : ∀ i, ((T117_60_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117) :=
  repsFix_of_siftB2 rK117 ⟨60, by decide⟩ T117_60_2 (by decide)

theorem hinj117_60_2 : Function.Injective
    (fun i => ((T117_60_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)) :=
  repsInj_of_reduceAux2 rK117 T117_60_2 (by decide)

theorem hcardT117_60_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK117 ⟨60, by decide⟩ R117_2 hpxR117_2 hcardq117_2 (by decide)).symm

/-- **Cell (117, 60) twin (q=2).** -/
theorem cell117_60_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK117) e = true)
    (h : ↥(reps (⟨60, by decide⟩ : Fin 148))) :
    species (reps (⟨60, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec2 rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK117 e (h : Coordinate 2) T117_60_2 i :=
  species_entry_eq_sum rK117 ⟨60, by decide⟩ e heK h T117_60_2 hfix117_60_2 hinj117_60_2 hcardT117_60_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨60, by decide⟩) (reps rK117) (T117_60_2 i) (hfix117_60_2 i) h)

/-! ### Cell (117, 61) twin -/

def T117_61_2 : Fin 5 → Coordinate 2 := fun i => T117_61list.getD i.val (0,0,0,0,0)

theorem hfix117_61_2 : ∀ i, ((T117_61_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117) :=
  repsFix_of_siftB2 rK117 ⟨61, by decide⟩ T117_61_2 (by decide)

theorem hinj117_61_2 : Function.Injective
    (fun i => ((T117_61_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)) :=
  repsInj_of_reduceAux2 rK117 T117_61_2 (by decide)

theorem hcardT117_61_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK117 ⟨61, by decide⟩ R117_2 hpxR117_2 hcardq117_2 (by decide)).symm

/-- **Cell (117, 61) twin (q=2).** -/
theorem cell117_61_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK117) e = true)
    (h : ↥(reps (⟨61, by decide⟩ : Fin 148))) :
    species (reps (⟨61, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec2 rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK117 e (h : Coordinate 2) T117_61_2 i :=
  species_entry_eq_sum rK117 ⟨61, by decide⟩ e heK h T117_61_2 hfix117_61_2 hinj117_61_2 hcardT117_61_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨61, by decide⟩) (reps rK117) (T117_61_2 i) (hfix117_61_2 i) h)

/-! ### Cell (117, 62) twin -/

def T117_62_2 : Fin 5 → Coordinate 2 := fun i => T117_62list.getD i.val (0,0,0,0,0)

theorem hfix117_62_2 : ∀ i, ((T117_62_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117) :=
  repsFix_of_siftB2 rK117 ⟨62, by decide⟩ T117_62_2 (by decide)

theorem hinj117_62_2 : Function.Injective
    (fun i => ((T117_62_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)) :=
  repsInj_of_reduceAux2 rK117 T117_62_2 (by decide)

theorem hcardT117_62_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK117 ⟨62, by decide⟩ R117_2 hpxR117_2 hcardq117_2 (by decide)).symm

/-- **Cell (117, 62) twin (q=2).** -/
theorem cell117_62_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK117) e = true)
    (h : ↥(reps (⟨62, by decide⟩ : Fin 148))) :
    species (reps (⟨62, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec2 rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK117 e (h : Coordinate 2) T117_62_2 i :=
  species_entry_eq_sum rK117 ⟨62, by decide⟩ e heK h T117_62_2 hfix117_62_2 hinj117_62_2 hcardT117_62_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨62, by decide⟩) (reps rK117) (T117_62_2 i) (hfix117_62_2 i) h)

/-! ### Cell (117, 63) twin -/

def T117_63_2 : Fin 5 → Coordinate 2 := fun i => T117_63list.getD i.val (0,0,0,0,0)

theorem hfix117_63_2 : ∀ i, ((T117_63_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117) :=
  repsFix_of_siftB2 rK117 ⟨63, by decide⟩ T117_63_2 (by decide)

theorem hinj117_63_2 : Function.Injective
    (fun i => ((T117_63_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)) :=
  repsInj_of_reduceAux2 rK117 T117_63_2 (by decide)

theorem hcardT117_63_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK117 ⟨63, by decide⟩ R117_2 hpxR117_2 hcardq117_2 (by decide)).symm

/-- **Cell (117, 63) twin (q=2).** -/
theorem cell117_63_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK117) e = true)
    (h : ↥(reps (⟨63, by decide⟩ : Fin 148))) :
    species (reps (⟨63, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec2 rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK117 e (h : Coordinate 2) T117_63_2 i :=
  species_entry_eq_sum rK117 ⟨63, by decide⟩ e heK h T117_63_2 hfix117_63_2 hinj117_63_2 hcardT117_63_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨63, by decide⟩) (reps rK117) (T117_63_2 i) (hfix117_63_2 i) h)

/-! ### Cell (117, 64) twin -/

def T117_64_2 : Fin 5 → Coordinate 2 := fun i => T117_64list.getD i.val (0,0,0,0,0)

theorem hfix117_64_2 : ∀ i, ((T117_64_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117) :=
  repsFix_of_siftB2 rK117 ⟨64, by decide⟩ T117_64_2 (by decide)

theorem hinj117_64_2 : Function.Injective
    (fun i => ((T117_64_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)) :=
  repsInj_of_reduceAux2 rK117 T117_64_2 (by decide)

theorem hcardT117_64_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK117 ⟨64, by decide⟩ R117_2 hpxR117_2 hcardq117_2 (by decide)).symm

/-- **Cell (117, 64) twin (q=2).** -/
theorem cell117_64_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK117) e = true)
    (h : ↥(reps (⟨64, by decide⟩ : Fin 148))) :
    species (reps (⟨64, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec2 rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK117 e (h : Coordinate 2) T117_64_2 i :=
  species_entry_eq_sum rK117 ⟨64, by decide⟩ e heK h T117_64_2 hfix117_64_2 hinj117_64_2 hcardT117_64_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨64, by decide⟩) (reps rK117) (T117_64_2 i) (hfix117_64_2 i) h)

/-! ### Cell (117, 80) twin -/

def T117_80_2 : Fin 5 → Coordinate 2 := fun i => T117_80list.getD i.val (0,0,0,0,0)

theorem hfix117_80_2 : ∀ i, ((T117_80_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117) :=
  repsFix_of_siftB2 rK117 ⟨80, by decide⟩ T117_80_2 (by decide)

theorem hinj117_80_2 : Function.Injective
    (fun i => ((T117_80_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)) :=
  repsInj_of_reduceAux2 rK117 T117_80_2 (by decide)

theorem hcardT117_80_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK117 ⟨80, by decide⟩ R117_2 hpxR117_2 hcardq117_2 (by decide)).symm

/-- **Cell (117, 80) twin (q=2).** -/
theorem cell117_80_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK117) e = true)
    (h : ↥(reps (⟨80, by decide⟩ : Fin 148))) :
    species (reps (⟨80, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec2 rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK117 e (h : Coordinate 2) T117_80_2 i :=
  species_entry_eq_sum rK117 ⟨80, by decide⟩ e heK h T117_80_2 hfix117_80_2 hinj117_80_2 hcardT117_80_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨80, by decide⟩) (reps rK117) (T117_80_2 i) (hfix117_80_2 i) h)

/-! ### Cell (117, 91) twin -/

def T117_91_2 : Fin 5 → Coordinate 2 := fun i => T117_91list.getD i.val (0,0,0,0,0)

theorem hfix117_91_2 : ∀ i, ((T117_91_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117) :=
  repsFix_of_siftB2 rK117 ⟨91, by decide⟩ T117_91_2 (by decide)

theorem hinj117_91_2 : Function.Injective
    (fun i => ((T117_91_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)) :=
  repsInj_of_reduceAux2 rK117 T117_91_2 (by decide)

theorem hcardT117_91_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK117 ⟨91, by decide⟩ R117_2 hpxR117_2 hcardq117_2 (by decide)).symm

/-- **Cell (117, 91) twin (q=2).** -/
theorem cell117_91_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK117) e = true)
    (h : ↥(reps (⟨91, by decide⟩ : Fin 148))) :
    species (reps (⟨91, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec2 rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK117 e (h : Coordinate 2) T117_91_2 i :=
  species_entry_eq_sum rK117 ⟨91, by decide⟩ e heK h T117_91_2 hfix117_91_2 hinj117_91_2 hcardT117_91_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨91, by decide⟩) (reps rK117) (T117_91_2 i) (hfix117_91_2 i) h)

/-! ### Cell (117, 96) twin -/

def T117_96_2 : Fin 5 → Coordinate 2 := fun i => T117_96list.getD i.val (0,0,0,0,0)

theorem hfix117_96_2 : ∀ i, ((T117_96_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117) :=
  repsFix_of_siftB2 rK117 ⟨96, by decide⟩ T117_96_2 (by decide)

theorem hinj117_96_2 : Function.Injective
    (fun i => ((T117_96_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)) :=
  repsInj_of_reduceAux2 rK117 T117_96_2 (by decide)

theorem hcardT117_96_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK117 ⟨96, by decide⟩ R117_2 hpxR117_2 hcardq117_2 (by decide)).symm

/-- **Cell (117, 96) twin (q=2).** -/
theorem cell117_96_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK117) e = true)
    (h : ↥(reps (⟨96, by decide⟩ : Fin 148))) :
    species (reps (⟨96, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec2 rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK117 e (h : Coordinate 2) T117_96_2 i :=
  species_entry_eq_sum rK117 ⟨96, by decide⟩ e heK h T117_96_2 hfix117_96_2 hinj117_96_2 hcardT117_96_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨96, by decide⟩) (reps rK117) (T117_96_2 i) (hfix117_96_2 i) h)

/-! ### Cell (117, 101) twin -/

def T117_101_2 : Fin 5 → Coordinate 2 := fun i => T117_101list.getD i.val (0,0,0,0,0)

theorem hfix117_101_2 : ∀ i, ((T117_101_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117) :=
  repsFix_of_siftB2 rK117 ⟨101, by decide⟩ T117_101_2 (by decide)

theorem hinj117_101_2 : Function.Injective
    (fun i => ((T117_101_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)) :=
  repsInj_of_reduceAux2 rK117 T117_101_2 (by decide)

theorem hcardT117_101_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK117 ⟨101, by decide⟩ R117_2 hpxR117_2 hcardq117_2 (by decide)).symm

/-- **Cell (117, 101) twin (q=2).** -/
theorem cell117_101_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK117) e = true)
    (h : ↥(reps (⟨101, by decide⟩ : Fin 148))) :
    species (reps (⟨101, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec2 rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK117 e (h : Coordinate 2) T117_101_2 i :=
  species_entry_eq_sum rK117 ⟨101, by decide⟩ e heK h T117_101_2 hfix117_101_2 hinj117_101_2 hcardT117_101_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨101, by decide⟩) (reps rK117) (T117_101_2 i) (hfix117_101_2 i) h)

/-! ### Cell (117, 106) twin -/

def T117_106_2 : Fin 5 → Coordinate 2 := fun i => T117_106list.getD i.val (0,0,0,0,0)

theorem hfix117_106_2 : ∀ i, ((T117_106_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117) :=
  repsFix_of_siftB2 rK117 ⟨106, by decide⟩ T117_106_2 (by decide)

theorem hinj117_106_2 : Function.Injective
    (fun i => ((T117_106_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)) :=
  repsInj_of_reduceAux2 rK117 T117_106_2 (by decide)

theorem hcardT117_106_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK117 ⟨106, by decide⟩ R117_2 hpxR117_2 hcardq117_2 (by decide)).symm

/-- **Cell (117, 106) twin (q=2).** -/
theorem cell117_106_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK117) e = true)
    (h : ↥(reps (⟨106, by decide⟩ : Fin 148))) :
    species (reps (⟨106, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec2 rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK117 e (h : Coordinate 2) T117_106_2 i :=
  species_entry_eq_sum rK117 ⟨106, by decide⟩ e heK h T117_106_2 hfix117_106_2 hinj117_106_2 hcardT117_106_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨106, by decide⟩) (reps rK117) (T117_106_2 i) (hfix117_106_2 i) h)

/-! ### Cell (117, 111) twin -/

def T117_111_2 : Fin 5 → Coordinate 2 := fun i => T117_111list.getD i.val (0,0,0,0,0)

theorem hfix117_111_2 : ∀ i, ((T117_111_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117) :=
  repsFix_of_siftB2 rK117 ⟨111, by decide⟩ T117_111_2 (by decide)

theorem hinj117_111_2 : Function.Injective
    (fun i => ((T117_111_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)) :=
  repsInj_of_reduceAux2 rK117 T117_111_2 (by decide)

theorem hcardT117_111_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK117 ⟨111, by decide⟩ R117_2 hpxR117_2 hcardq117_2 (by decide)).symm

/-- **Cell (117, 111) twin (q=2).** -/
theorem cell117_111_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK117) e = true)
    (h : ↥(reps (⟨111, by decide⟩ : Fin 148))) :
    species (reps (⟨111, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec2 rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK117 e (h : Coordinate 2) T117_111_2 i :=
  species_entry_eq_sum rK117 ⟨111, by decide⟩ e heK h T117_111_2 hfix117_111_2 hinj117_111_2 hcardT117_111_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨111, by decide⟩) (reps rK117) (T117_111_2 i) (hfix117_111_2 i) h)

/-! ### Cell (117, 117) twin -/

def T117_117_2 : Fin 5 → Coordinate 2 := fun i => T117_117list.getD i.val (0,0,0,0,0)

theorem hfix117_117_2 : ∀ i, ((T117_117_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)
    ∈ fixedPoints (reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117) :=
  repsFix_of_siftB2 rK117 ⟨117, by decide⟩ T117_117_2 (by decide)

theorem hinj117_117_2 : Function.Injective
    (fun i => ((T117_117_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK117)) :=
  repsInj_of_reduceAux2 rK117 T117_117_2 (by decide)

theorem hcardT117_117_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK117)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK117 ⟨117, by decide⟩ R117_2 hpxR117_2 hcardq117_2 (by decide)).symm

/-- **Cell (117, 117) twin (q=2).** -/
theorem cell117_117_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK117) e = true)
    (h : ↥(reps (⟨117, by decide⟩ : Fin 148))) :
    species (reps (⟨117, by decide⟩ : Fin 148)) h (basisElt (reps rK117) (charOfVec2 rK117 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK117 e (h : Coordinate 2) T117_117_2 i :=
  species_entry_eq_sum rK117 ⟨117, by decide⟩ e heK h T117_117_2 hfix117_117_2 hinj117_117_2 hcardT117_117_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨117, by decide⟩) (reps rK117) (T117_117_2 i) (hfix117_117_2 i) h)

end Q2

end LeanDring.P5Presentation
