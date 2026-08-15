/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, K-strata data (5^4 stratum, rK 122-123): certified per-cell species-entry instantiations, both
twins.

Covers K-classes 122, 123 (order-5^4 K, |R|=5).  For each nonzero `H`-column
(`(G/K)^H ≠ ∅`), the full coset transversal `R122..` and each `H`-fixed
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

/-! # K-class rK = 122  (|G/K| = 5) -/

def rK122 : Fin 148 := ⟨122, by decide⟩

def R122list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def R122 : Fin 5 → Coordinate 1 := fun i => R122list.getD i.val (0,0,0,0,0)

theorem hpxR122 : Function.Injective (fun i => reduceAux 1 (basisAt rK122) (R122 i)) := by decide
theorem hcardq122 : Nat.card (Coordinate 1 ⧸ reps rK122) = 5 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (122, 0): |T| = 5 -/

def T122_0list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T122_0 : Fin 5 → Coordinate 1 := fun i => T122_0list.getD i.val (0,0,0,0,0)

theorem hfix122_0 : ∀ i, ((T122_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK122)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122) :=
  repsFix_of_siftB rK122 ⟨0, by decide⟩ T122_0 (by decide)

theorem hinj122_0 : Function.Injective
    (fun i => ((T122_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK122)) :=
  repsInj_of_reduceAux rK122 T122_0 (by decide)

theorem hcardT122_0 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK122 ⟨0, by decide⟩ R122 hpxR122 hcardq122 (by decide)).symm

/-- **Cell (122, 0).** -/
theorem cell122_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK122) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK122) (charOfVec rK122 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK122 e (h : Coordinate 1) T122_0 i :=
  species_entry_eq_sum rK122 ⟨0, by decide⟩ e heK h T122_0 hfix122_0 hinj122_0 hcardT122_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK122) (T122_0 i) (hfix122_0 i) h)

/-! ## Cell (122, 2): |T| = 5 -/

def T122_2list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T122_2 : Fin 5 → Coordinate 1 := fun i => T122_2list.getD i.val (0,0,0,0,0)

theorem hfix122_2 : ∀ i, ((T122_2 i : Coordinate 1) : Coordinate 1 ⧸ reps rK122)
    ∈ fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122) :=
  repsFix_of_siftB rK122 ⟨2, by decide⟩ T122_2 (by decide)

theorem hinj122_2 : Function.Injective
    (fun i => ((T122_2 i : Coordinate 1) : Coordinate 1 ⧸ reps rK122)) :=
  repsInj_of_reduceAux rK122 T122_2 (by decide)

theorem hcardT122_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK122 ⟨2, by decide⟩ R122 hpxR122 hcardq122 (by decide)).symm

/-- **Cell (122, 2).** -/
theorem cell122_2 (e : List (ZMod 25)) (heK : charOK (basisAt rK122) e = true)
    (h : ↥(reps (⟨2, by decide⟩ : Fin 148))) :
    species (reps (⟨2, by decide⟩ : Fin 148)) h (basisElt (reps rK122) (charOfVec rK122 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK122 e (h : Coordinate 1) T122_2 i :=
  species_entry_eq_sum rK122 ⟨2, by decide⟩ e heK h T122_2 hfix122_2 hinj122_2 hcardT122_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨2, by decide⟩) (reps rK122) (T122_2 i) (hfix122_2 i) h)

/-! ## Cell (122, 10): |T| = 5 -/

def T122_10list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T122_10 : Fin 5 → Coordinate 1 := fun i => T122_10list.getD i.val (0,0,0,0,0)

theorem hfix122_10 : ∀ i, ((T122_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK122)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122) :=
  repsFix_of_siftB rK122 ⟨10, by decide⟩ T122_10 (by decide)

theorem hinj122_10 : Function.Injective
    (fun i => ((T122_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK122)) :=
  repsInj_of_reduceAux rK122 T122_10 (by decide)

theorem hcardT122_10 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK122 ⟨10, by decide⟩ R122 hpxR122 hcardq122 (by decide)).symm

/-- **Cell (122, 10).** -/
theorem cell122_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK122) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK122) (charOfVec rK122 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK122 e (h : Coordinate 1) T122_10 i :=
  species_entry_eq_sum rK122 ⟨10, by decide⟩ e heK h T122_10 hfix122_10 hinj122_10 hcardT122_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK122) (T122_10 i) (hfix122_10 i) h)

/-! ## Cell (122, 12): |T| = 5 -/

def T122_12list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T122_12 : Fin 5 → Coordinate 1 := fun i => T122_12list.getD i.val (0,0,0,0,0)

theorem hfix122_12 : ∀ i, ((T122_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK122)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122) :=
  repsFix_of_siftB rK122 ⟨12, by decide⟩ T122_12 (by decide)

theorem hinj122_12 : Function.Injective
    (fun i => ((T122_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK122)) :=
  repsInj_of_reduceAux rK122 T122_12 (by decide)

theorem hcardT122_12 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK122 ⟨12, by decide⟩ R122 hpxR122 hcardq122 (by decide)).symm

/-- **Cell (122, 12).** -/
theorem cell122_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK122) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK122) (charOfVec rK122 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK122 e (h : Coordinate 1) T122_12 i :=
  species_entry_eq_sum rK122 ⟨12, by decide⟩ e heK h T122_12 hfix122_12 hinj122_12 hcardT122_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK122) (T122_12 i) (hfix122_12 i) h)

/-! ## Cell (122, 20): |T| = 5 -/

def T122_20list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T122_20 : Fin 5 → Coordinate 1 := fun i => T122_20list.getD i.val (0,0,0,0,0)

theorem hfix122_20 : ∀ i, ((T122_20 i : Coordinate 1) : Coordinate 1 ⧸ reps rK122)
    ∈ fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122) :=
  repsFix_of_siftB rK122 ⟨20, by decide⟩ T122_20 (by decide)

theorem hinj122_20 : Function.Injective
    (fun i => ((T122_20 i : Coordinate 1) : Coordinate 1 ⧸ reps rK122)) :=
  repsInj_of_reduceAux rK122 T122_20 (by decide)

theorem hcardT122_20 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK122 ⟨20, by decide⟩ R122 hpxR122 hcardq122 (by decide)).symm

/-- **Cell (122, 20).** -/
theorem cell122_20 (e : List (ZMod 25)) (heK : charOK (basisAt rK122) e = true)
    (h : ↥(reps (⟨20, by decide⟩ : Fin 148))) :
    species (reps (⟨20, by decide⟩ : Fin 148)) h (basisElt (reps rK122) (charOfVec rK122 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK122 e (h : Coordinate 1) T122_20 i :=
  species_entry_eq_sum rK122 ⟨20, by decide⟩ e heK h T122_20 hfix122_20 hinj122_20 hcardT122_20
    (fun i => conj_mem_of_fixedPoints (reps ⟨20, by decide⟩) (reps rK122) (T122_20 i) (hfix122_20 i) h)

/-! ## Cell (122, 28): |T| = 5 -/

def T122_28list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T122_28 : Fin 5 → Coordinate 1 := fun i => T122_28list.getD i.val (0,0,0,0,0)

theorem hfix122_28 : ∀ i, ((T122_28 i : Coordinate 1) : Coordinate 1 ⧸ reps rK122)
    ∈ fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122) :=
  repsFix_of_siftB rK122 ⟨28, by decide⟩ T122_28 (by decide)

theorem hinj122_28 : Function.Injective
    (fun i => ((T122_28 i : Coordinate 1) : Coordinate 1 ⧸ reps rK122)) :=
  repsInj_of_reduceAux rK122 T122_28 (by decide)

theorem hcardT122_28 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK122 ⟨28, by decide⟩ R122 hpxR122 hcardq122 (by decide)).symm

/-- **Cell (122, 28).** -/
theorem cell122_28 (e : List (ZMod 25)) (heK : charOK (basisAt rK122) e = true)
    (h : ↥(reps (⟨28, by decide⟩ : Fin 148))) :
    species (reps (⟨28, by decide⟩ : Fin 148)) h (basisElt (reps rK122) (charOfVec rK122 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK122 e (h : Coordinate 1) T122_28 i :=
  species_entry_eq_sum rK122 ⟨28, by decide⟩ e heK h T122_28 hfix122_28 hinj122_28 hcardT122_28
    (fun i => conj_mem_of_fixedPoints (reps ⟨28, by decide⟩) (reps rK122) (T122_28 i) (hfix122_28 i) h)

/-! ## Cell (122, 36): |T| = 5 -/

def T122_36list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T122_36 : Fin 5 → Coordinate 1 := fun i => T122_36list.getD i.val (0,0,0,0,0)

theorem hfix122_36 : ∀ i, ((T122_36 i : Coordinate 1) : Coordinate 1 ⧸ reps rK122)
    ∈ fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122) :=
  repsFix_of_siftB rK122 ⟨36, by decide⟩ T122_36 (by decide)

theorem hinj122_36 : Function.Injective
    (fun i => ((T122_36 i : Coordinate 1) : Coordinate 1 ⧸ reps rK122)) :=
  repsInj_of_reduceAux rK122 T122_36 (by decide)

theorem hcardT122_36 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK122 ⟨36, by decide⟩ R122 hpxR122 hcardq122 (by decide)).symm

/-- **Cell (122, 36).** -/
theorem cell122_36 (e : List (ZMod 25)) (heK : charOK (basisAt rK122) e = true)
    (h : ↥(reps (⟨36, by decide⟩ : Fin 148))) :
    species (reps (⟨36, by decide⟩ : Fin 148)) h (basisElt (reps rK122) (charOfVec rK122 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK122 e (h : Coordinate 1) T122_36 i :=
  species_entry_eq_sum rK122 ⟨36, by decide⟩ e heK h T122_36 hfix122_36 hinj122_36 hcardT122_36
    (fun i => conj_mem_of_fixedPoints (reps ⟨36, by decide⟩) (reps rK122) (T122_36 i) (hfix122_36 i) h)

/-! ## Cell (122, 42): |T| = 5 -/

def T122_42list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T122_42 : Fin 5 → Coordinate 1 := fun i => T122_42list.getD i.val (0,0,0,0,0)

theorem hfix122_42 : ∀ i, ((T122_42 i : Coordinate 1) : Coordinate 1 ⧸ reps rK122)
    ∈ fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122) :=
  repsFix_of_siftB rK122 ⟨42, by decide⟩ T122_42 (by decide)

theorem hinj122_42 : Function.Injective
    (fun i => ((T122_42 i : Coordinate 1) : Coordinate 1 ⧸ reps rK122)) :=
  repsInj_of_reduceAux rK122 T122_42 (by decide)

theorem hcardT122_42 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK122 ⟨42, by decide⟩ R122 hpxR122 hcardq122 (by decide)).symm

/-- **Cell (122, 42).** -/
theorem cell122_42 (e : List (ZMod 25)) (heK : charOK (basisAt rK122) e = true)
    (h : ↥(reps (⟨42, by decide⟩ : Fin 148))) :
    species (reps (⟨42, by decide⟩ : Fin 148)) h (basisElt (reps rK122) (charOfVec rK122 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK122 e (h : Coordinate 1) T122_42 i :=
  species_entry_eq_sum rK122 ⟨42, by decide⟩ e heK h T122_42 hfix122_42 hinj122_42 hcardT122_42
    (fun i => conj_mem_of_fixedPoints (reps ⟨42, by decide⟩) (reps rK122) (T122_42 i) (hfix122_42 i) h)

/-! ## Cell (122, 45): |T| = 5 -/

def T122_45list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T122_45 : Fin 5 → Coordinate 1 := fun i => T122_45list.getD i.val (0,0,0,0,0)

theorem hfix122_45 : ∀ i, ((T122_45 i : Coordinate 1) : Coordinate 1 ⧸ reps rK122)
    ∈ fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122) :=
  repsFix_of_siftB rK122 ⟨45, by decide⟩ T122_45 (by decide)

theorem hinj122_45 : Function.Injective
    (fun i => ((T122_45 i : Coordinate 1) : Coordinate 1 ⧸ reps rK122)) :=
  repsInj_of_reduceAux rK122 T122_45 (by decide)

theorem hcardT122_45 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK122 ⟨45, by decide⟩ R122 hpxR122 hcardq122 (by decide)).symm

/-- **Cell (122, 45).** -/
theorem cell122_45 (e : List (ZMod 25)) (heK : charOK (basisAt rK122) e = true)
    (h : ↥(reps (⟨45, by decide⟩ : Fin 148))) :
    species (reps (⟨45, by decide⟩ : Fin 148)) h (basisElt (reps rK122) (charOfVec rK122 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK122 e (h : Coordinate 1) T122_45 i :=
  species_entry_eq_sum rK122 ⟨45, by decide⟩ e heK h T122_45 hfix122_45 hinj122_45 hcardT122_45
    (fun i => conj_mem_of_fixedPoints (reps ⟨45, by decide⟩) (reps rK122) (T122_45 i) (hfix122_45 i) h)

/-! ## Cell (122, 49): |T| = 5 -/

def T122_49list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T122_49 : Fin 5 → Coordinate 1 := fun i => T122_49list.getD i.val (0,0,0,0,0)

theorem hfix122_49 : ∀ i, ((T122_49 i : Coordinate 1) : Coordinate 1 ⧸ reps rK122)
    ∈ fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122) :=
  repsFix_of_siftB rK122 ⟨49, by decide⟩ T122_49 (by decide)

theorem hinj122_49 : Function.Injective
    (fun i => ((T122_49 i : Coordinate 1) : Coordinate 1 ⧸ reps rK122)) :=
  repsInj_of_reduceAux rK122 T122_49 (by decide)

theorem hcardT122_49 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK122 ⟨49, by decide⟩ R122 hpxR122 hcardq122 (by decide)).symm

/-- **Cell (122, 49).** -/
theorem cell122_49 (e : List (ZMod 25)) (heK : charOK (basisAt rK122) e = true)
    (h : ↥(reps (⟨49, by decide⟩ : Fin 148))) :
    species (reps (⟨49, by decide⟩ : Fin 148)) h (basisElt (reps rK122) (charOfVec rK122 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK122 e (h : Coordinate 1) T122_49 i :=
  species_entry_eq_sum rK122 ⟨49, by decide⟩ e heK h T122_49 hfix122_49 hinj122_49 hcardT122_49
    (fun i => conj_mem_of_fixedPoints (reps ⟨49, by decide⟩) (reps rK122) (T122_49 i) (hfix122_49 i) h)

/-! ## Cell (122, 53): |T| = 5 -/

def T122_53list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T122_53 : Fin 5 → Coordinate 1 := fun i => T122_53list.getD i.val (0,0,0,0,0)

theorem hfix122_53 : ∀ i, ((T122_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK122)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122) :=
  repsFix_of_siftB rK122 ⟨53, by decide⟩ T122_53 (by decide)

theorem hinj122_53 : Function.Injective
    (fun i => ((T122_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK122)) :=
  repsInj_of_reduceAux rK122 T122_53 (by decide)

theorem hcardT122_53 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK122 ⟨53, by decide⟩ R122 hpxR122 hcardq122 (by decide)).symm

/-- **Cell (122, 53).** -/
theorem cell122_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK122) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK122) (charOfVec rK122 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK122 e (h : Coordinate 1) T122_53 i :=
  species_entry_eq_sum rK122 ⟨53, by decide⟩ e heK h T122_53 hfix122_53 hinj122_53 hcardT122_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK122) (T122_53 i) (hfix122_53 i) h)

/-! ## Cell (122, 81): |T| = 5 -/

def T122_81list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T122_81 : Fin 5 → Coordinate 1 := fun i => T122_81list.getD i.val (0,0,0,0,0)

theorem hfix122_81 : ∀ i, ((T122_81 i : Coordinate 1) : Coordinate 1 ⧸ reps rK122)
    ∈ fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122) :=
  repsFix_of_siftB rK122 ⟨81, by decide⟩ T122_81 (by decide)

theorem hinj122_81 : Function.Injective
    (fun i => ((T122_81 i : Coordinate 1) : Coordinate 1 ⧸ reps rK122)) :=
  repsInj_of_reduceAux rK122 T122_81 (by decide)

theorem hcardT122_81 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK122 ⟨81, by decide⟩ R122 hpxR122 hcardq122 (by decide)).symm

/-- **Cell (122, 81).** -/
theorem cell122_81 (e : List (ZMod 25)) (heK : charOK (basisAt rK122) e = true)
    (h : ↥(reps (⟨81, by decide⟩ : Fin 148))) :
    species (reps (⟨81, by decide⟩ : Fin 148)) h (basisElt (reps rK122) (charOfVec rK122 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK122 e (h : Coordinate 1) T122_81 i :=
  species_entry_eq_sum rK122 ⟨81, by decide⟩ e heK h T122_81 hfix122_81 hinj122_81 hcardT122_81
    (fun i => conj_mem_of_fixedPoints (reps ⟨81, by decide⟩) (reps rK122) (T122_81 i) (hfix122_81 i) h)

/-! ## Cell (122, 90): |T| = 5 -/

def T122_90list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T122_90 : Fin 5 → Coordinate 1 := fun i => T122_90list.getD i.val (0,0,0,0,0)

theorem hfix122_90 : ∀ i, ((T122_90 i : Coordinate 1) : Coordinate 1 ⧸ reps rK122)
    ∈ fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122) :=
  repsFix_of_siftB rK122 ⟨90, by decide⟩ T122_90 (by decide)

theorem hinj122_90 : Function.Injective
    (fun i => ((T122_90 i : Coordinate 1) : Coordinate 1 ⧸ reps rK122)) :=
  repsInj_of_reduceAux rK122 T122_90 (by decide)

theorem hcardT122_90 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK122 ⟨90, by decide⟩ R122 hpxR122 hcardq122 (by decide)).symm

/-- **Cell (122, 90).** -/
theorem cell122_90 (e : List (ZMod 25)) (heK : charOK (basisAt rK122) e = true)
    (h : ↥(reps (⟨90, by decide⟩ : Fin 148))) :
    species (reps (⟨90, by decide⟩ : Fin 148)) h (basisElt (reps rK122) (charOfVec rK122 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK122 e (h : Coordinate 1) T122_90 i :=
  species_entry_eq_sum rK122 ⟨90, by decide⟩ e heK h T122_90 hfix122_90 hinj122_90 hcardT122_90
    (fun i => conj_mem_of_fixedPoints (reps ⟨90, by decide⟩) (reps rK122) (T122_90 i) (hfix122_90 i) h)

/-! ## Cell (122, 98): |T| = 5 -/

def T122_98list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T122_98 : Fin 5 → Coordinate 1 := fun i => T122_98list.getD i.val (0,0,0,0,0)

theorem hfix122_98 : ∀ i, ((T122_98 i : Coordinate 1) : Coordinate 1 ⧸ reps rK122)
    ∈ fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122) :=
  repsFix_of_siftB rK122 ⟨98, by decide⟩ T122_98 (by decide)

theorem hinj122_98 : Function.Injective
    (fun i => ((T122_98 i : Coordinate 1) : Coordinate 1 ⧸ reps rK122)) :=
  repsInj_of_reduceAux rK122 T122_98 (by decide)

theorem hcardT122_98 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK122 ⟨98, by decide⟩ R122 hpxR122 hcardq122 (by decide)).symm

/-- **Cell (122, 98).** -/
theorem cell122_98 (e : List (ZMod 25)) (heK : charOK (basisAt rK122) e = true)
    (h : ↥(reps (⟨98, by decide⟩ : Fin 148))) :
    species (reps (⟨98, by decide⟩ : Fin 148)) h (basisElt (reps rK122) (charOfVec rK122 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK122 e (h : Coordinate 1) T122_98 i :=
  species_entry_eq_sum rK122 ⟨98, by decide⟩ e heK h T122_98 hfix122_98 hinj122_98 hcardT122_98
    (fun i => conj_mem_of_fixedPoints (reps ⟨98, by decide⟩) (reps rK122) (T122_98 i) (hfix122_98 i) h)

/-! ## Cell (122, 104): |T| = 5 -/

def T122_104list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T122_104 : Fin 5 → Coordinate 1 := fun i => T122_104list.getD i.val (0,0,0,0,0)

theorem hfix122_104 : ∀ i, ((T122_104 i : Coordinate 1) : Coordinate 1 ⧸ reps rK122)
    ∈ fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122) :=
  repsFix_of_siftB rK122 ⟨104, by decide⟩ T122_104 (by decide)

theorem hinj122_104 : Function.Injective
    (fun i => ((T122_104 i : Coordinate 1) : Coordinate 1 ⧸ reps rK122)) :=
  repsInj_of_reduceAux rK122 T122_104 (by decide)

theorem hcardT122_104 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK122 ⟨104, by decide⟩ R122 hpxR122 hcardq122 (by decide)).symm

/-- **Cell (122, 104).** -/
theorem cell122_104 (e : List (ZMod 25)) (heK : charOK (basisAt rK122) e = true)
    (h : ↥(reps (⟨104, by decide⟩ : Fin 148))) :
    species (reps (⟨104, by decide⟩ : Fin 148)) h (basisElt (reps rK122) (charOfVec rK122 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK122 e (h : Coordinate 1) T122_104 i :=
  species_entry_eq_sum rK122 ⟨104, by decide⟩ e heK h T122_104 hfix122_104 hinj122_104 hcardT122_104
    (fun i => conj_mem_of_fixedPoints (reps ⟨104, by decide⟩) (reps rK122) (T122_104 i) (hfix122_104 i) h)

/-! ## Cell (122, 107): |T| = 5 -/

def T122_107list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T122_107 : Fin 5 → Coordinate 1 := fun i => T122_107list.getD i.val (0,0,0,0,0)

theorem hfix122_107 : ∀ i, ((T122_107 i : Coordinate 1) : Coordinate 1 ⧸ reps rK122)
    ∈ fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122) :=
  repsFix_of_siftB rK122 ⟨107, by decide⟩ T122_107 (by decide)

theorem hinj122_107 : Function.Injective
    (fun i => ((T122_107 i : Coordinate 1) : Coordinate 1 ⧸ reps rK122)) :=
  repsInj_of_reduceAux rK122 T122_107 (by decide)

theorem hcardT122_107 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK122 ⟨107, by decide⟩ R122 hpxR122 hcardq122 (by decide)).symm

/-- **Cell (122, 107).** -/
theorem cell122_107 (e : List (ZMod 25)) (heK : charOK (basisAt rK122) e = true)
    (h : ↥(reps (⟨107, by decide⟩ : Fin 148))) :
    species (reps (⟨107, by decide⟩ : Fin 148)) h (basisElt (reps rK122) (charOfVec rK122 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK122 e (h : Coordinate 1) T122_107 i :=
  species_entry_eq_sum rK122 ⟨107, by decide⟩ e heK h T122_107 hfix122_107 hinj122_107 hcardT122_107
    (fun i => conj_mem_of_fixedPoints (reps ⟨107, by decide⟩) (reps rK122) (T122_107 i) (hfix122_107 i) h)

/-! ## Cell (122, 111): |T| = 5 -/

def T122_111list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T122_111 : Fin 5 → Coordinate 1 := fun i => T122_111list.getD i.val (0,0,0,0,0)

theorem hfix122_111 : ∀ i, ((T122_111 i : Coordinate 1) : Coordinate 1 ⧸ reps rK122)
    ∈ fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122) :=
  repsFix_of_siftB rK122 ⟨111, by decide⟩ T122_111 (by decide)

theorem hinj122_111 : Function.Injective
    (fun i => ((T122_111 i : Coordinate 1) : Coordinate 1 ⧸ reps rK122)) :=
  repsInj_of_reduceAux rK122 T122_111 (by decide)

theorem hcardT122_111 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK122 ⟨111, by decide⟩ R122 hpxR122 hcardq122 (by decide)).symm

/-- **Cell (122, 111).** -/
theorem cell122_111 (e : List (ZMod 25)) (heK : charOK (basisAt rK122) e = true)
    (h : ↥(reps (⟨111, by decide⟩ : Fin 148))) :
    species (reps (⟨111, by decide⟩ : Fin 148)) h (basisElt (reps rK122) (charOfVec rK122 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK122 e (h : Coordinate 1) T122_111 i :=
  species_entry_eq_sum rK122 ⟨111, by decide⟩ e heK h T122_111 hfix122_111 hinj122_111 hcardT122_111
    (fun i => conj_mem_of_fixedPoints (reps ⟨111, by decide⟩) (reps rK122) (T122_111 i) (hfix122_111 i) h)

/-! ## Cell (122, 122): |T| = 5 -/

def T122_122list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T122_122 : Fin 5 → Coordinate 1 := fun i => T122_122list.getD i.val (0,0,0,0,0)

theorem hfix122_122 : ∀ i, ((T122_122 i : Coordinate 1) : Coordinate 1 ⧸ reps rK122)
    ∈ fixedPoints (reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122) :=
  repsFix_of_siftB rK122 ⟨122, by decide⟩ T122_122 (by decide)

theorem hinj122_122 : Function.Injective
    (fun i => ((T122_122 i : Coordinate 1) : Coordinate 1 ⧸ reps rK122)) :=
  repsInj_of_reduceAux rK122 T122_122 (by decide)

theorem hcardT122_122 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK122 ⟨122, by decide⟩ R122 hpxR122 hcardq122 (by decide)).symm

/-- **Cell (122, 122).** -/
theorem cell122_122 (e : List (ZMod 25)) (heK : charOK (basisAt rK122) e = true)
    (h : ↥(reps (⟨122, by decide⟩ : Fin 148))) :
    species (reps (⟨122, by decide⟩ : Fin 148)) h (basisElt (reps rK122) (charOfVec rK122 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK122 e (h : Coordinate 1) T122_122 i :=
  species_entry_eq_sum rK122 ⟨122, by decide⟩ e heK h T122_122 hfix122_122 hinj122_122 hcardT122_122
    (fun i => conj_mem_of_fixedPoints (reps ⟨122, by decide⟩) (reps rK122) (T122_122 i) (hfix122_122 i) h)

namespace Q2

def R122_2 : Fin 5 → Coordinate 2 := fun i => R122list.getD i.val (0,0,0,0,0)
theorem hpxR122_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK122) (R122_2 i)) := by decide
theorem hcardq122_2 : Nat.card (Coordinate 2 ⧸ reps rK122) = 5 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (122, 0) twin -/

def T122_0_2 : Fin 5 → Coordinate 2 := fun i => T122_0list.getD i.val (0,0,0,0,0)

theorem hfix122_0_2 : ∀ i, ((T122_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK122)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK122) :=
  repsFix_of_siftB2 rK122 ⟨0, by decide⟩ T122_0_2 (by decide)

theorem hinj122_0_2 : Function.Injective
    (fun i => ((T122_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK122)) :=
  repsInj_of_reduceAux2 rK122 T122_0_2 (by decide)

theorem hcardT122_0_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK122)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK122 ⟨0, by decide⟩ R122_2 hpxR122_2 hcardq122_2 (by decide)).symm

/-- **Cell (122, 0) twin (q=2).** -/
theorem cell122_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK122) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK122) (charOfVec2 rK122 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK122 e (h : Coordinate 2) T122_0_2 i :=
  species_entry_eq_sum rK122 ⟨0, by decide⟩ e heK h T122_0_2 hfix122_0_2 hinj122_0_2 hcardT122_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK122) (T122_0_2 i) (hfix122_0_2 i) h)

/-! ### Cell (122, 2) twin -/

def T122_2_2 : Fin 5 → Coordinate 2 := fun i => T122_2list.getD i.val (0,0,0,0,0)

theorem hfix122_2_2 : ∀ i, ((T122_2_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK122)
    ∈ fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK122) :=
  repsFix_of_siftB2 rK122 ⟨2, by decide⟩ T122_2_2 (by decide)

theorem hinj122_2_2 : Function.Injective
    (fun i => ((T122_2_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK122)) :=
  repsInj_of_reduceAux2 rK122 T122_2_2 (by decide)

theorem hcardT122_2_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK122)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK122 ⟨2, by decide⟩ R122_2 hpxR122_2 hcardq122_2 (by decide)).symm

/-- **Cell (122, 2) twin (q=2).** -/
theorem cell122_2_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK122) e = true)
    (h : ↥(reps (⟨2, by decide⟩ : Fin 148))) :
    species (reps (⟨2, by decide⟩ : Fin 148)) h (basisElt (reps rK122) (charOfVec2 rK122 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK122 e (h : Coordinate 2) T122_2_2 i :=
  species_entry_eq_sum rK122 ⟨2, by decide⟩ e heK h T122_2_2 hfix122_2_2 hinj122_2_2 hcardT122_2_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨2, by decide⟩) (reps rK122) (T122_2_2 i) (hfix122_2_2 i) h)

/-! ### Cell (122, 10) twin -/

def T122_10_2 : Fin 5 → Coordinate 2 := fun i => T122_10list.getD i.val (0,0,0,0,0)

theorem hfix122_10_2 : ∀ i, ((T122_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK122)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK122) :=
  repsFix_of_siftB2 rK122 ⟨10, by decide⟩ T122_10_2 (by decide)

theorem hinj122_10_2 : Function.Injective
    (fun i => ((T122_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK122)) :=
  repsInj_of_reduceAux2 rK122 T122_10_2 (by decide)

theorem hcardT122_10_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK122)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK122 ⟨10, by decide⟩ R122_2 hpxR122_2 hcardq122_2 (by decide)).symm

/-- **Cell (122, 10) twin (q=2).** -/
theorem cell122_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK122) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK122) (charOfVec2 rK122 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK122 e (h : Coordinate 2) T122_10_2 i :=
  species_entry_eq_sum rK122 ⟨10, by decide⟩ e heK h T122_10_2 hfix122_10_2 hinj122_10_2 hcardT122_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK122) (T122_10_2 i) (hfix122_10_2 i) h)

/-! ### Cell (122, 12) twin -/

def T122_12_2 : Fin 5 → Coordinate 2 := fun i => T122_12list.getD i.val (0,0,0,0,0)

theorem hfix122_12_2 : ∀ i, ((T122_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK122)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK122) :=
  repsFix_of_siftB2 rK122 ⟨12, by decide⟩ T122_12_2 (by decide)

theorem hinj122_12_2 : Function.Injective
    (fun i => ((T122_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK122)) :=
  repsInj_of_reduceAux2 rK122 T122_12_2 (by decide)

theorem hcardT122_12_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK122)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK122 ⟨12, by decide⟩ R122_2 hpxR122_2 hcardq122_2 (by decide)).symm

/-- **Cell (122, 12) twin (q=2).** -/
theorem cell122_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK122) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK122) (charOfVec2 rK122 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK122 e (h : Coordinate 2) T122_12_2 i :=
  species_entry_eq_sum rK122 ⟨12, by decide⟩ e heK h T122_12_2 hfix122_12_2 hinj122_12_2 hcardT122_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK122) (T122_12_2 i) (hfix122_12_2 i) h)

/-! ### Cell (122, 20) twin -/

def T122_20_2 : Fin 5 → Coordinate 2 := fun i => T122_20list.getD i.val (0,0,0,0,0)

theorem hfix122_20_2 : ∀ i, ((T122_20_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK122)
    ∈ fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK122) :=
  repsFix_of_siftB2 rK122 ⟨20, by decide⟩ T122_20_2 (by decide)

theorem hinj122_20_2 : Function.Injective
    (fun i => ((T122_20_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK122)) :=
  repsInj_of_reduceAux2 rK122 T122_20_2 (by decide)

theorem hcardT122_20_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK122)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK122 ⟨20, by decide⟩ R122_2 hpxR122_2 hcardq122_2 (by decide)).symm

/-- **Cell (122, 20) twin (q=2).** -/
theorem cell122_20_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK122) e = true)
    (h : ↥(reps (⟨20, by decide⟩ : Fin 148))) :
    species (reps (⟨20, by decide⟩ : Fin 148)) h (basisElt (reps rK122) (charOfVec2 rK122 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK122 e (h : Coordinate 2) T122_20_2 i :=
  species_entry_eq_sum rK122 ⟨20, by decide⟩ e heK h T122_20_2 hfix122_20_2 hinj122_20_2 hcardT122_20_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨20, by decide⟩) (reps rK122) (T122_20_2 i) (hfix122_20_2 i) h)

/-! ### Cell (122, 28) twin -/

def T122_28_2 : Fin 5 → Coordinate 2 := fun i => T122_28list.getD i.val (0,0,0,0,0)

theorem hfix122_28_2 : ∀ i, ((T122_28_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK122)
    ∈ fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK122) :=
  repsFix_of_siftB2 rK122 ⟨28, by decide⟩ T122_28_2 (by decide)

theorem hinj122_28_2 : Function.Injective
    (fun i => ((T122_28_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK122)) :=
  repsInj_of_reduceAux2 rK122 T122_28_2 (by decide)

theorem hcardT122_28_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK122)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK122 ⟨28, by decide⟩ R122_2 hpxR122_2 hcardq122_2 (by decide)).symm

/-- **Cell (122, 28) twin (q=2).** -/
theorem cell122_28_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK122) e = true)
    (h : ↥(reps (⟨28, by decide⟩ : Fin 148))) :
    species (reps (⟨28, by decide⟩ : Fin 148)) h (basisElt (reps rK122) (charOfVec2 rK122 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK122 e (h : Coordinate 2) T122_28_2 i :=
  species_entry_eq_sum rK122 ⟨28, by decide⟩ e heK h T122_28_2 hfix122_28_2 hinj122_28_2 hcardT122_28_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨28, by decide⟩) (reps rK122) (T122_28_2 i) (hfix122_28_2 i) h)

/-! ### Cell (122, 36) twin -/

def T122_36_2 : Fin 5 → Coordinate 2 := fun i => T122_36list.getD i.val (0,0,0,0,0)

theorem hfix122_36_2 : ∀ i, ((T122_36_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK122)
    ∈ fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK122) :=
  repsFix_of_siftB2 rK122 ⟨36, by decide⟩ T122_36_2 (by decide)

theorem hinj122_36_2 : Function.Injective
    (fun i => ((T122_36_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK122)) :=
  repsInj_of_reduceAux2 rK122 T122_36_2 (by decide)

theorem hcardT122_36_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK122)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK122 ⟨36, by decide⟩ R122_2 hpxR122_2 hcardq122_2 (by decide)).symm

/-- **Cell (122, 36) twin (q=2).** -/
theorem cell122_36_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK122) e = true)
    (h : ↥(reps (⟨36, by decide⟩ : Fin 148))) :
    species (reps (⟨36, by decide⟩ : Fin 148)) h (basisElt (reps rK122) (charOfVec2 rK122 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK122 e (h : Coordinate 2) T122_36_2 i :=
  species_entry_eq_sum rK122 ⟨36, by decide⟩ e heK h T122_36_2 hfix122_36_2 hinj122_36_2 hcardT122_36_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨36, by decide⟩) (reps rK122) (T122_36_2 i) (hfix122_36_2 i) h)

/-! ### Cell (122, 42) twin -/

def T122_42_2 : Fin 5 → Coordinate 2 := fun i => T122_42list.getD i.val (0,0,0,0,0)

theorem hfix122_42_2 : ∀ i, ((T122_42_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK122)
    ∈ fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK122) :=
  repsFix_of_siftB2 rK122 ⟨42, by decide⟩ T122_42_2 (by decide)

theorem hinj122_42_2 : Function.Injective
    (fun i => ((T122_42_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK122)) :=
  repsInj_of_reduceAux2 rK122 T122_42_2 (by decide)

theorem hcardT122_42_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK122)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK122 ⟨42, by decide⟩ R122_2 hpxR122_2 hcardq122_2 (by decide)).symm

/-- **Cell (122, 42) twin (q=2).** -/
theorem cell122_42_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK122) e = true)
    (h : ↥(reps (⟨42, by decide⟩ : Fin 148))) :
    species (reps (⟨42, by decide⟩ : Fin 148)) h (basisElt (reps rK122) (charOfVec2 rK122 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK122 e (h : Coordinate 2) T122_42_2 i :=
  species_entry_eq_sum rK122 ⟨42, by decide⟩ e heK h T122_42_2 hfix122_42_2 hinj122_42_2 hcardT122_42_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨42, by decide⟩) (reps rK122) (T122_42_2 i) (hfix122_42_2 i) h)

/-! ### Cell (122, 45) twin -/

def T122_45_2 : Fin 5 → Coordinate 2 := fun i => T122_45list.getD i.val (0,0,0,0,0)

theorem hfix122_45_2 : ∀ i, ((T122_45_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK122)
    ∈ fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK122) :=
  repsFix_of_siftB2 rK122 ⟨45, by decide⟩ T122_45_2 (by decide)

theorem hinj122_45_2 : Function.Injective
    (fun i => ((T122_45_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK122)) :=
  repsInj_of_reduceAux2 rK122 T122_45_2 (by decide)

theorem hcardT122_45_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK122)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK122 ⟨45, by decide⟩ R122_2 hpxR122_2 hcardq122_2 (by decide)).symm

/-- **Cell (122, 45) twin (q=2).** -/
theorem cell122_45_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK122) e = true)
    (h : ↥(reps (⟨45, by decide⟩ : Fin 148))) :
    species (reps (⟨45, by decide⟩ : Fin 148)) h (basisElt (reps rK122) (charOfVec2 rK122 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK122 e (h : Coordinate 2) T122_45_2 i :=
  species_entry_eq_sum rK122 ⟨45, by decide⟩ e heK h T122_45_2 hfix122_45_2 hinj122_45_2 hcardT122_45_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨45, by decide⟩) (reps rK122) (T122_45_2 i) (hfix122_45_2 i) h)

/-! ### Cell (122, 49) twin -/

def T122_49_2 : Fin 5 → Coordinate 2 := fun i => T122_49list.getD i.val (0,0,0,0,0)

theorem hfix122_49_2 : ∀ i, ((T122_49_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK122)
    ∈ fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK122) :=
  repsFix_of_siftB2 rK122 ⟨49, by decide⟩ T122_49_2 (by decide)

theorem hinj122_49_2 : Function.Injective
    (fun i => ((T122_49_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK122)) :=
  repsInj_of_reduceAux2 rK122 T122_49_2 (by decide)

theorem hcardT122_49_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK122)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK122 ⟨49, by decide⟩ R122_2 hpxR122_2 hcardq122_2 (by decide)).symm

/-- **Cell (122, 49) twin (q=2).** -/
theorem cell122_49_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK122) e = true)
    (h : ↥(reps (⟨49, by decide⟩ : Fin 148))) :
    species (reps (⟨49, by decide⟩ : Fin 148)) h (basisElt (reps rK122) (charOfVec2 rK122 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK122 e (h : Coordinate 2) T122_49_2 i :=
  species_entry_eq_sum rK122 ⟨49, by decide⟩ e heK h T122_49_2 hfix122_49_2 hinj122_49_2 hcardT122_49_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨49, by decide⟩) (reps rK122) (T122_49_2 i) (hfix122_49_2 i) h)

/-! ### Cell (122, 53) twin -/

def T122_53_2 : Fin 5 → Coordinate 2 := fun i => T122_53list.getD i.val (0,0,0,0,0)

theorem hfix122_53_2 : ∀ i, ((T122_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK122)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK122) :=
  repsFix_of_siftB2 rK122 ⟨53, by decide⟩ T122_53_2 (by decide)

theorem hinj122_53_2 : Function.Injective
    (fun i => ((T122_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK122)) :=
  repsInj_of_reduceAux2 rK122 T122_53_2 (by decide)

theorem hcardT122_53_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK122)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK122 ⟨53, by decide⟩ R122_2 hpxR122_2 hcardq122_2 (by decide)).symm

/-- **Cell (122, 53) twin (q=2).** -/
theorem cell122_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK122) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK122) (charOfVec2 rK122 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK122 e (h : Coordinate 2) T122_53_2 i :=
  species_entry_eq_sum rK122 ⟨53, by decide⟩ e heK h T122_53_2 hfix122_53_2 hinj122_53_2 hcardT122_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK122) (T122_53_2 i) (hfix122_53_2 i) h)

/-! ### Cell (122, 81) twin -/

def T122_81_2 : Fin 5 → Coordinate 2 := fun i => T122_81list.getD i.val (0,0,0,0,0)

theorem hfix122_81_2 : ∀ i, ((T122_81_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK122)
    ∈ fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK122) :=
  repsFix_of_siftB2 rK122 ⟨81, by decide⟩ T122_81_2 (by decide)

theorem hinj122_81_2 : Function.Injective
    (fun i => ((T122_81_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK122)) :=
  repsInj_of_reduceAux2 rK122 T122_81_2 (by decide)

theorem hcardT122_81_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK122)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK122 ⟨81, by decide⟩ R122_2 hpxR122_2 hcardq122_2 (by decide)).symm

/-- **Cell (122, 81) twin (q=2).** -/
theorem cell122_81_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK122) e = true)
    (h : ↥(reps (⟨81, by decide⟩ : Fin 148))) :
    species (reps (⟨81, by decide⟩ : Fin 148)) h (basisElt (reps rK122) (charOfVec2 rK122 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK122 e (h : Coordinate 2) T122_81_2 i :=
  species_entry_eq_sum rK122 ⟨81, by decide⟩ e heK h T122_81_2 hfix122_81_2 hinj122_81_2 hcardT122_81_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨81, by decide⟩) (reps rK122) (T122_81_2 i) (hfix122_81_2 i) h)

/-! ### Cell (122, 90) twin -/

def T122_90_2 : Fin 5 → Coordinate 2 := fun i => T122_90list.getD i.val (0,0,0,0,0)

theorem hfix122_90_2 : ∀ i, ((T122_90_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK122)
    ∈ fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK122) :=
  repsFix_of_siftB2 rK122 ⟨90, by decide⟩ T122_90_2 (by decide)

theorem hinj122_90_2 : Function.Injective
    (fun i => ((T122_90_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK122)) :=
  repsInj_of_reduceAux2 rK122 T122_90_2 (by decide)

theorem hcardT122_90_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK122)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK122 ⟨90, by decide⟩ R122_2 hpxR122_2 hcardq122_2 (by decide)).symm

/-- **Cell (122, 90) twin (q=2).** -/
theorem cell122_90_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK122) e = true)
    (h : ↥(reps (⟨90, by decide⟩ : Fin 148))) :
    species (reps (⟨90, by decide⟩ : Fin 148)) h (basisElt (reps rK122) (charOfVec2 rK122 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK122 e (h : Coordinate 2) T122_90_2 i :=
  species_entry_eq_sum rK122 ⟨90, by decide⟩ e heK h T122_90_2 hfix122_90_2 hinj122_90_2 hcardT122_90_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨90, by decide⟩) (reps rK122) (T122_90_2 i) (hfix122_90_2 i) h)

/-! ### Cell (122, 98) twin -/

def T122_98_2 : Fin 5 → Coordinate 2 := fun i => T122_98list.getD i.val (0,0,0,0,0)

theorem hfix122_98_2 : ∀ i, ((T122_98_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK122)
    ∈ fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK122) :=
  repsFix_of_siftB2 rK122 ⟨98, by decide⟩ T122_98_2 (by decide)

theorem hinj122_98_2 : Function.Injective
    (fun i => ((T122_98_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK122)) :=
  repsInj_of_reduceAux2 rK122 T122_98_2 (by decide)

theorem hcardT122_98_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK122)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK122 ⟨98, by decide⟩ R122_2 hpxR122_2 hcardq122_2 (by decide)).symm

/-- **Cell (122, 98) twin (q=2).** -/
theorem cell122_98_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK122) e = true)
    (h : ↥(reps (⟨98, by decide⟩ : Fin 148))) :
    species (reps (⟨98, by decide⟩ : Fin 148)) h (basisElt (reps rK122) (charOfVec2 rK122 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK122 e (h : Coordinate 2) T122_98_2 i :=
  species_entry_eq_sum rK122 ⟨98, by decide⟩ e heK h T122_98_2 hfix122_98_2 hinj122_98_2 hcardT122_98_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨98, by decide⟩) (reps rK122) (T122_98_2 i) (hfix122_98_2 i) h)

/-! ### Cell (122, 104) twin -/

def T122_104_2 : Fin 5 → Coordinate 2 := fun i => T122_104list.getD i.val (0,0,0,0,0)

theorem hfix122_104_2 : ∀ i, ((T122_104_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK122)
    ∈ fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK122) :=
  repsFix_of_siftB2 rK122 ⟨104, by decide⟩ T122_104_2 (by decide)

theorem hinj122_104_2 : Function.Injective
    (fun i => ((T122_104_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK122)) :=
  repsInj_of_reduceAux2 rK122 T122_104_2 (by decide)

theorem hcardT122_104_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK122)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK122 ⟨104, by decide⟩ R122_2 hpxR122_2 hcardq122_2 (by decide)).symm

/-- **Cell (122, 104) twin (q=2).** -/
theorem cell122_104_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK122) e = true)
    (h : ↥(reps (⟨104, by decide⟩ : Fin 148))) :
    species (reps (⟨104, by decide⟩ : Fin 148)) h (basisElt (reps rK122) (charOfVec2 rK122 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK122 e (h : Coordinate 2) T122_104_2 i :=
  species_entry_eq_sum rK122 ⟨104, by decide⟩ e heK h T122_104_2 hfix122_104_2 hinj122_104_2 hcardT122_104_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨104, by decide⟩) (reps rK122) (T122_104_2 i) (hfix122_104_2 i) h)

/-! ### Cell (122, 107) twin -/

def T122_107_2 : Fin 5 → Coordinate 2 := fun i => T122_107list.getD i.val (0,0,0,0,0)

theorem hfix122_107_2 : ∀ i, ((T122_107_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK122)
    ∈ fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK122) :=
  repsFix_of_siftB2 rK122 ⟨107, by decide⟩ T122_107_2 (by decide)

theorem hinj122_107_2 : Function.Injective
    (fun i => ((T122_107_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK122)) :=
  repsInj_of_reduceAux2 rK122 T122_107_2 (by decide)

theorem hcardT122_107_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK122)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK122 ⟨107, by decide⟩ R122_2 hpxR122_2 hcardq122_2 (by decide)).symm

/-- **Cell (122, 107) twin (q=2).** -/
theorem cell122_107_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK122) e = true)
    (h : ↥(reps (⟨107, by decide⟩ : Fin 148))) :
    species (reps (⟨107, by decide⟩ : Fin 148)) h (basisElt (reps rK122) (charOfVec2 rK122 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK122 e (h : Coordinate 2) T122_107_2 i :=
  species_entry_eq_sum rK122 ⟨107, by decide⟩ e heK h T122_107_2 hfix122_107_2 hinj122_107_2 hcardT122_107_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨107, by decide⟩) (reps rK122) (T122_107_2 i) (hfix122_107_2 i) h)

/-! ### Cell (122, 111) twin -/

def T122_111_2 : Fin 5 → Coordinate 2 := fun i => T122_111list.getD i.val (0,0,0,0,0)

theorem hfix122_111_2 : ∀ i, ((T122_111_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK122)
    ∈ fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK122) :=
  repsFix_of_siftB2 rK122 ⟨111, by decide⟩ T122_111_2 (by decide)

theorem hinj122_111_2 : Function.Injective
    (fun i => ((T122_111_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK122)) :=
  repsInj_of_reduceAux2 rK122 T122_111_2 (by decide)

theorem hcardT122_111_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK122)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK122 ⟨111, by decide⟩ R122_2 hpxR122_2 hcardq122_2 (by decide)).symm

/-- **Cell (122, 111) twin (q=2).** -/
theorem cell122_111_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK122) e = true)
    (h : ↥(reps (⟨111, by decide⟩ : Fin 148))) :
    species (reps (⟨111, by decide⟩ : Fin 148)) h (basisElt (reps rK122) (charOfVec2 rK122 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK122 e (h : Coordinate 2) T122_111_2 i :=
  species_entry_eq_sum rK122 ⟨111, by decide⟩ e heK h T122_111_2 hfix122_111_2 hinj122_111_2 hcardT122_111_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨111, by decide⟩) (reps rK122) (T122_111_2 i) (hfix122_111_2 i) h)

/-! ### Cell (122, 122) twin -/

def T122_122_2 : Fin 5 → Coordinate 2 := fun i => T122_122list.getD i.val (0,0,0,0,0)

theorem hfix122_122_2 : ∀ i, ((T122_122_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK122)
    ∈ fixedPoints (reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK122) :=
  repsFix_of_siftB2 rK122 ⟨122, by decide⟩ T122_122_2 (by decide)

theorem hinj122_122_2 : Function.Injective
    (fun i => ((T122_122_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK122)) :=
  repsInj_of_reduceAux2 rK122 T122_122_2 (by decide)

theorem hcardT122_122_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK122)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK122 ⟨122, by decide⟩ R122_2 hpxR122_2 hcardq122_2 (by decide)).symm

/-- **Cell (122, 122) twin (q=2).** -/
theorem cell122_122_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK122) e = true)
    (h : ↥(reps (⟨122, by decide⟩ : Fin 148))) :
    species (reps (⟨122, by decide⟩ : Fin 148)) h (basisElt (reps rK122) (charOfVec2 rK122 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK122 e (h : Coordinate 2) T122_122_2 i :=
  species_entry_eq_sum rK122 ⟨122, by decide⟩ e heK h T122_122_2 hfix122_122_2 hinj122_122_2 hcardT122_122_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨122, by decide⟩) (reps rK122) (T122_122_2 i) (hfix122_122_2 i) h)

end Q2

/-! # K-class rK = 123  (|G/K| = 5) -/

def rK123 : Fin 148 := ⟨123, by decide⟩

def R123list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def R123 : Fin 5 → Coordinate 1 := fun i => R123list.getD i.val (0,0,0,0,0)

theorem hpxR123 : Function.Injective (fun i => reduceAux 1 (basisAt rK123) (R123 i)) := by decide
theorem hcardq123 : Nat.card (Coordinate 1 ⧸ reps rK123) = 5 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (123, 0): |T| = 5 -/

def T123_0list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T123_0 : Fin 5 → Coordinate 1 := fun i => T123_0list.getD i.val (0,0,0,0,0)

theorem hfix123_0 : ∀ i, ((T123_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK123)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123) :=
  repsFix_of_siftB rK123 ⟨0, by decide⟩ T123_0 (by decide)

theorem hinj123_0 : Function.Injective
    (fun i => ((T123_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK123)) :=
  repsInj_of_reduceAux rK123 T123_0 (by decide)

theorem hcardT123_0 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK123 ⟨0, by decide⟩ R123 hpxR123 hcardq123 (by decide)).symm

/-- **Cell (123, 0).** -/
theorem cell123_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK123) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK123) (charOfVec rK123 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK123 e (h : Coordinate 1) T123_0 i :=
  species_entry_eq_sum rK123 ⟨0, by decide⟩ e heK h T123_0 hfix123_0 hinj123_0 hcardT123_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK123) (T123_0 i) (hfix123_0 i) h)

/-! ## Cell (123, 2): |T| = 5 -/

def T123_2list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T123_2 : Fin 5 → Coordinate 1 := fun i => T123_2list.getD i.val (0,0,0,0,0)

theorem hfix123_2 : ∀ i, ((T123_2 i : Coordinate 1) : Coordinate 1 ⧸ reps rK123)
    ∈ fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123) :=
  repsFix_of_siftB rK123 ⟨2, by decide⟩ T123_2 (by decide)

theorem hinj123_2 : Function.Injective
    (fun i => ((T123_2 i : Coordinate 1) : Coordinate 1 ⧸ reps rK123)) :=
  repsInj_of_reduceAux rK123 T123_2 (by decide)

theorem hcardT123_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK123 ⟨2, by decide⟩ R123 hpxR123 hcardq123 (by decide)).symm

/-- **Cell (123, 2).** -/
theorem cell123_2 (e : List (ZMod 25)) (heK : charOK (basisAt rK123) e = true)
    (h : ↥(reps (⟨2, by decide⟩ : Fin 148))) :
    species (reps (⟨2, by decide⟩ : Fin 148)) h (basisElt (reps rK123) (charOfVec rK123 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK123 e (h : Coordinate 1) T123_2 i :=
  species_entry_eq_sum rK123 ⟨2, by decide⟩ e heK h T123_2 hfix123_2 hinj123_2 hcardT123_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨2, by decide⟩) (reps rK123) (T123_2 i) (hfix123_2 i) h)

/-! ## Cell (123, 10): |T| = 5 -/

def T123_10list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T123_10 : Fin 5 → Coordinate 1 := fun i => T123_10list.getD i.val (0,0,0,0,0)

theorem hfix123_10 : ∀ i, ((T123_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK123)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123) :=
  repsFix_of_siftB rK123 ⟨10, by decide⟩ T123_10 (by decide)

theorem hinj123_10 : Function.Injective
    (fun i => ((T123_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK123)) :=
  repsInj_of_reduceAux rK123 T123_10 (by decide)

theorem hcardT123_10 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK123 ⟨10, by decide⟩ R123 hpxR123 hcardq123 (by decide)).symm

/-- **Cell (123, 10).** -/
theorem cell123_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK123) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK123) (charOfVec rK123 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK123 e (h : Coordinate 1) T123_10 i :=
  species_entry_eq_sum rK123 ⟨10, by decide⟩ e heK h T123_10 hfix123_10 hinj123_10 hcardT123_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK123) (T123_10 i) (hfix123_10 i) h)

/-! ## Cell (123, 12): |T| = 5 -/

def T123_12list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T123_12 : Fin 5 → Coordinate 1 := fun i => T123_12list.getD i.val (0,0,0,0,0)

theorem hfix123_12 : ∀ i, ((T123_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK123)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123) :=
  repsFix_of_siftB rK123 ⟨12, by decide⟩ T123_12 (by decide)

theorem hinj123_12 : Function.Injective
    (fun i => ((T123_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK123)) :=
  repsInj_of_reduceAux rK123 T123_12 (by decide)

theorem hcardT123_12 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK123 ⟨12, by decide⟩ R123 hpxR123 hcardq123 (by decide)).symm

/-- **Cell (123, 12).** -/
theorem cell123_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK123) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK123) (charOfVec rK123 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK123 e (h : Coordinate 1) T123_12 i :=
  species_entry_eq_sum rK123 ⟨12, by decide⟩ e heK h T123_12 hfix123_12 hinj123_12 hcardT123_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK123) (T123_12 i) (hfix123_12 i) h)

/-! ## Cell (123, 20): |T| = 5 -/

def T123_20list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T123_20 : Fin 5 → Coordinate 1 := fun i => T123_20list.getD i.val (0,0,0,0,0)

theorem hfix123_20 : ∀ i, ((T123_20 i : Coordinate 1) : Coordinate 1 ⧸ reps rK123)
    ∈ fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123) :=
  repsFix_of_siftB rK123 ⟨20, by decide⟩ T123_20 (by decide)

theorem hinj123_20 : Function.Injective
    (fun i => ((T123_20 i : Coordinate 1) : Coordinate 1 ⧸ reps rK123)) :=
  repsInj_of_reduceAux rK123 T123_20 (by decide)

theorem hcardT123_20 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK123 ⟨20, by decide⟩ R123 hpxR123 hcardq123 (by decide)).symm

/-- **Cell (123, 20).** -/
theorem cell123_20 (e : List (ZMod 25)) (heK : charOK (basisAt rK123) e = true)
    (h : ↥(reps (⟨20, by decide⟩ : Fin 148))) :
    species (reps (⟨20, by decide⟩ : Fin 148)) h (basisElt (reps rK123) (charOfVec rK123 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK123 e (h : Coordinate 1) T123_20 i :=
  species_entry_eq_sum rK123 ⟨20, by decide⟩ e heK h T123_20 hfix123_20 hinj123_20 hcardT123_20
    (fun i => conj_mem_of_fixedPoints (reps ⟨20, by decide⟩) (reps rK123) (T123_20 i) (hfix123_20 i) h)

/-! ## Cell (123, 29): |T| = 5 -/

def T123_29list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T123_29 : Fin 5 → Coordinate 1 := fun i => T123_29list.getD i.val (0,0,0,0,0)

theorem hfix123_29 : ∀ i, ((T123_29 i : Coordinate 1) : Coordinate 1 ⧸ reps rK123)
    ∈ fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123) :=
  repsFix_of_siftB rK123 ⟨29, by decide⟩ T123_29 (by decide)

theorem hinj123_29 : Function.Injective
    (fun i => ((T123_29 i : Coordinate 1) : Coordinate 1 ⧸ reps rK123)) :=
  repsInj_of_reduceAux rK123 T123_29 (by decide)

theorem hcardT123_29 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK123 ⟨29, by decide⟩ R123 hpxR123 hcardq123 (by decide)).symm

/-- **Cell (123, 29).** -/
theorem cell123_29 (e : List (ZMod 25)) (heK : charOK (basisAt rK123) e = true)
    (h : ↥(reps (⟨29, by decide⟩ : Fin 148))) :
    species (reps (⟨29, by decide⟩ : Fin 148)) h (basisElt (reps rK123) (charOfVec rK123 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK123 e (h : Coordinate 1) T123_29 i :=
  species_entry_eq_sum rK123 ⟨29, by decide⟩ e heK h T123_29 hfix123_29 hinj123_29 hcardT123_29
    (fun i => conj_mem_of_fixedPoints (reps ⟨29, by decide⟩) (reps rK123) (T123_29 i) (hfix123_29 i) h)

/-! ## Cell (123, 37): |T| = 5 -/

def T123_37list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T123_37 : Fin 5 → Coordinate 1 := fun i => T123_37list.getD i.val (0,0,0,0,0)

theorem hfix123_37 : ∀ i, ((T123_37 i : Coordinate 1) : Coordinate 1 ⧸ reps rK123)
    ∈ fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123) :=
  repsFix_of_siftB rK123 ⟨37, by decide⟩ T123_37 (by decide)

theorem hinj123_37 : Function.Injective
    (fun i => ((T123_37 i : Coordinate 1) : Coordinate 1 ⧸ reps rK123)) :=
  repsInj_of_reduceAux rK123 T123_37 (by decide)

theorem hcardT123_37 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK123 ⟨37, by decide⟩ R123 hpxR123 hcardq123 (by decide)).symm

/-- **Cell (123, 37).** -/
theorem cell123_37 (e : List (ZMod 25)) (heK : charOK (basisAt rK123) e = true)
    (h : ↥(reps (⟨37, by decide⟩ : Fin 148))) :
    species (reps (⟨37, by decide⟩ : Fin 148)) h (basisElt (reps rK123) (charOfVec rK123 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK123 e (h : Coordinate 1) T123_37 i :=
  species_entry_eq_sum rK123 ⟨37, by decide⟩ e heK h T123_37 hfix123_37 hinj123_37 hcardT123_37
    (fun i => conj_mem_of_fixedPoints (reps ⟨37, by decide⟩) (reps rK123) (T123_37 i) (hfix123_37 i) h)

/-! ## Cell (123, 38): |T| = 5 -/

def T123_38list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T123_38 : Fin 5 → Coordinate 1 := fun i => T123_38list.getD i.val (0,0,0,0,0)

theorem hfix123_38 : ∀ i, ((T123_38 i : Coordinate 1) : Coordinate 1 ⧸ reps rK123)
    ∈ fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123) :=
  repsFix_of_siftB rK123 ⟨38, by decide⟩ T123_38 (by decide)

theorem hinj123_38 : Function.Injective
    (fun i => ((T123_38 i : Coordinate 1) : Coordinate 1 ⧸ reps rK123)) :=
  repsInj_of_reduceAux rK123 T123_38 (by decide)

theorem hcardT123_38 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK123 ⟨38, by decide⟩ R123 hpxR123 hcardq123 (by decide)).symm

/-- **Cell (123, 38).** -/
theorem cell123_38 (e : List (ZMod 25)) (heK : charOK (basisAt rK123) e = true)
    (h : ↥(reps (⟨38, by decide⟩ : Fin 148))) :
    species (reps (⟨38, by decide⟩ : Fin 148)) h (basisElt (reps rK123) (charOfVec rK123 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK123 e (h : Coordinate 1) T123_38 i :=
  species_entry_eq_sum rK123 ⟨38, by decide⟩ e heK h T123_38 hfix123_38 hinj123_38 hcardT123_38
    (fun i => conj_mem_of_fixedPoints (reps ⟨38, by decide⟩) (reps rK123) (T123_38 i) (hfix123_38 i) h)

/-! ## Cell (123, 46): |T| = 5 -/

def T123_46list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T123_46 : Fin 5 → Coordinate 1 := fun i => T123_46list.getD i.val (0,0,0,0,0)

theorem hfix123_46 : ∀ i, ((T123_46 i : Coordinate 1) : Coordinate 1 ⧸ reps rK123)
    ∈ fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123) :=
  repsFix_of_siftB rK123 ⟨46, by decide⟩ T123_46 (by decide)

theorem hinj123_46 : Function.Injective
    (fun i => ((T123_46 i : Coordinate 1) : Coordinate 1 ⧸ reps rK123)) :=
  repsInj_of_reduceAux rK123 T123_46 (by decide)

theorem hcardT123_46 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK123 ⟨46, by decide⟩ R123 hpxR123 hcardq123 (by decide)).symm

/-- **Cell (123, 46).** -/
theorem cell123_46 (e : List (ZMod 25)) (heK : charOK (basisAt rK123) e = true)
    (h : ↥(reps (⟨46, by decide⟩ : Fin 148))) :
    species (reps (⟨46, by decide⟩ : Fin 148)) h (basisElt (reps rK123) (charOfVec rK123 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK123 e (h : Coordinate 1) T123_46 i :=
  species_entry_eq_sum rK123 ⟨46, by decide⟩ e heK h T123_46 hfix123_46 hinj123_46 hcardT123_46
    (fun i => conj_mem_of_fixedPoints (reps ⟨46, by decide⟩) (reps rK123) (T123_46 i) (hfix123_46 i) h)

/-! ## Cell (123, 50): |T| = 5 -/

def T123_50list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T123_50 : Fin 5 → Coordinate 1 := fun i => T123_50list.getD i.val (0,0,0,0,0)

theorem hfix123_50 : ∀ i, ((T123_50 i : Coordinate 1) : Coordinate 1 ⧸ reps rK123)
    ∈ fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123) :=
  repsFix_of_siftB rK123 ⟨50, by decide⟩ T123_50 (by decide)

theorem hinj123_50 : Function.Injective
    (fun i => ((T123_50 i : Coordinate 1) : Coordinate 1 ⧸ reps rK123)) :=
  repsInj_of_reduceAux rK123 T123_50 (by decide)

theorem hcardT123_50 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK123 ⟨50, by decide⟩ R123 hpxR123 hcardq123 (by decide)).symm

/-- **Cell (123, 50).** -/
theorem cell123_50 (e : List (ZMod 25)) (heK : charOK (basisAt rK123) e = true)
    (h : ↥(reps (⟨50, by decide⟩ : Fin 148))) :
    species (reps (⟨50, by decide⟩ : Fin 148)) h (basisElt (reps rK123) (charOfVec rK123 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK123 e (h : Coordinate 1) T123_50 i :=
  species_entry_eq_sum rK123 ⟨50, by decide⟩ e heK h T123_50 hfix123_50 hinj123_50 hcardT123_50
    (fun i => conj_mem_of_fixedPoints (reps ⟨50, by decide⟩) (reps rK123) (T123_50 i) (hfix123_50 i) h)

/-! ## Cell (123, 53): |T| = 5 -/

def T123_53list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T123_53 : Fin 5 → Coordinate 1 := fun i => T123_53list.getD i.val (0,0,0,0,0)

theorem hfix123_53 : ∀ i, ((T123_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK123)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123) :=
  repsFix_of_siftB rK123 ⟨53, by decide⟩ T123_53 (by decide)

theorem hinj123_53 : Function.Injective
    (fun i => ((T123_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK123)) :=
  repsInj_of_reduceAux rK123 T123_53 (by decide)

theorem hcardT123_53 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK123 ⟨53, by decide⟩ R123 hpxR123 hcardq123 (by decide)).symm

/-- **Cell (123, 53).** -/
theorem cell123_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK123) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK123) (charOfVec rK123 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK123 e (h : Coordinate 1) T123_53 i :=
  species_entry_eq_sum rK123 ⟨53, by decide⟩ e heK h T123_53 hfix123_53 hinj123_53 hcardT123_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK123) (T123_53 i) (hfix123_53 i) h)

/-! ## Cell (123, 81): |T| = 5 -/

def T123_81list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T123_81 : Fin 5 → Coordinate 1 := fun i => T123_81list.getD i.val (0,0,0,0,0)

theorem hfix123_81 : ∀ i, ((T123_81 i : Coordinate 1) : Coordinate 1 ⧸ reps rK123)
    ∈ fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123) :=
  repsFix_of_siftB rK123 ⟨81, by decide⟩ T123_81 (by decide)

theorem hinj123_81 : Function.Injective
    (fun i => ((T123_81 i : Coordinate 1) : Coordinate 1 ⧸ reps rK123)) :=
  repsInj_of_reduceAux rK123 T123_81 (by decide)

theorem hcardT123_81 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK123 ⟨81, by decide⟩ R123 hpxR123 hcardq123 (by decide)).symm

/-- **Cell (123, 81).** -/
theorem cell123_81 (e : List (ZMod 25)) (heK : charOK (basisAt rK123) e = true)
    (h : ↥(reps (⟨81, by decide⟩ : Fin 148))) :
    species (reps (⟨81, by decide⟩ : Fin 148)) h (basisElt (reps rK123) (charOfVec rK123 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK123 e (h : Coordinate 1) T123_81 i :=
  species_entry_eq_sum rK123 ⟨81, by decide⟩ e heK h T123_81 hfix123_81 hinj123_81 hcardT123_81
    (fun i => conj_mem_of_fixedPoints (reps ⟨81, by decide⟩) (reps rK123) (T123_81 i) (hfix123_81 i) h)

/-! ## Cell (123, 91): |T| = 5 -/

def T123_91list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T123_91 : Fin 5 → Coordinate 1 := fun i => T123_91list.getD i.val (0,0,0,0,0)

theorem hfix123_91 : ∀ i, ((T123_91 i : Coordinate 1) : Coordinate 1 ⧸ reps rK123)
    ∈ fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123) :=
  repsFix_of_siftB rK123 ⟨91, by decide⟩ T123_91 (by decide)

theorem hinj123_91 : Function.Injective
    (fun i => ((T123_91 i : Coordinate 1) : Coordinate 1 ⧸ reps rK123)) :=
  repsInj_of_reduceAux rK123 T123_91 (by decide)

theorem hcardT123_91 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK123 ⟨91, by decide⟩ R123 hpxR123 hcardq123 (by decide)).symm

/-- **Cell (123, 91).** -/
theorem cell123_91 (e : List (ZMod 25)) (heK : charOK (basisAt rK123) e = true)
    (h : ↥(reps (⟨91, by decide⟩ : Fin 148))) :
    species (reps (⟨91, by decide⟩ : Fin 148)) h (basisElt (reps rK123) (charOfVec rK123 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK123 e (h : Coordinate 1) T123_91 i :=
  species_entry_eq_sum rK123 ⟨91, by decide⟩ e heK h T123_91 hfix123_91 hinj123_91 hcardT123_91
    (fun i => conj_mem_of_fixedPoints (reps ⟨91, by decide⟩) (reps rK123) (T123_91 i) (hfix123_91 i) h)

/-! ## Cell (123, 99): |T| = 5 -/

def T123_99list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T123_99 : Fin 5 → Coordinate 1 := fun i => T123_99list.getD i.val (0,0,0,0,0)

theorem hfix123_99 : ∀ i, ((T123_99 i : Coordinate 1) : Coordinate 1 ⧸ reps rK123)
    ∈ fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123) :=
  repsFix_of_siftB rK123 ⟨99, by decide⟩ T123_99 (by decide)

theorem hinj123_99 : Function.Injective
    (fun i => ((T123_99 i : Coordinate 1) : Coordinate 1 ⧸ reps rK123)) :=
  repsInj_of_reduceAux rK123 T123_99 (by decide)

theorem hcardT123_99 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK123 ⟨99, by decide⟩ R123 hpxR123 hcardq123 (by decide)).symm

/-- **Cell (123, 99).** -/
theorem cell123_99 (e : List (ZMod 25)) (heK : charOK (basisAt rK123) e = true)
    (h : ↥(reps (⟨99, by decide⟩ : Fin 148))) :
    species (reps (⟨99, by decide⟩ : Fin 148)) h (basisElt (reps rK123) (charOfVec rK123 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK123 e (h : Coordinate 1) T123_99 i :=
  species_entry_eq_sum rK123 ⟨99, by decide⟩ e heK h T123_99 hfix123_99 hinj123_99 hcardT123_99
    (fun i => conj_mem_of_fixedPoints (reps ⟨99, by decide⟩) (reps rK123) (T123_99 i) (hfix123_99 i) h)

/-! ## Cell (123, 100): |T| = 5 -/

def T123_100list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T123_100 : Fin 5 → Coordinate 1 := fun i => T123_100list.getD i.val (0,0,0,0,0)

theorem hfix123_100 : ∀ i, ((T123_100 i : Coordinate 1) : Coordinate 1 ⧸ reps rK123)
    ∈ fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123) :=
  repsFix_of_siftB rK123 ⟨100, by decide⟩ T123_100 (by decide)

theorem hinj123_100 : Function.Injective
    (fun i => ((T123_100 i : Coordinate 1) : Coordinate 1 ⧸ reps rK123)) :=
  repsInj_of_reduceAux rK123 T123_100 (by decide)

theorem hcardT123_100 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK123 ⟨100, by decide⟩ R123 hpxR123 hcardq123 (by decide)).symm

/-- **Cell (123, 100).** -/
theorem cell123_100 (e : List (ZMod 25)) (heK : charOK (basisAt rK123) e = true)
    (h : ↥(reps (⟨100, by decide⟩ : Fin 148))) :
    species (reps (⟨100, by decide⟩ : Fin 148)) h (basisElt (reps rK123) (charOfVec rK123 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK123 e (h : Coordinate 1) T123_100 i :=
  species_entry_eq_sum rK123 ⟨100, by decide⟩ e heK h T123_100 hfix123_100 hinj123_100 hcardT123_100
    (fun i => conj_mem_of_fixedPoints (reps ⟨100, by decide⟩) (reps rK123) (T123_100 i) (hfix123_100 i) h)

/-! ## Cell (123, 108): |T| = 5 -/

def T123_108list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T123_108 : Fin 5 → Coordinate 1 := fun i => T123_108list.getD i.val (0,0,0,0,0)

theorem hfix123_108 : ∀ i, ((T123_108 i : Coordinate 1) : Coordinate 1 ⧸ reps rK123)
    ∈ fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123) :=
  repsFix_of_siftB rK123 ⟨108, by decide⟩ T123_108 (by decide)

theorem hinj123_108 : Function.Injective
    (fun i => ((T123_108 i : Coordinate 1) : Coordinate 1 ⧸ reps rK123)) :=
  repsInj_of_reduceAux rK123 T123_108 (by decide)

theorem hcardT123_108 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK123 ⟨108, by decide⟩ R123 hpxR123 hcardq123 (by decide)).symm

/-- **Cell (123, 108).** -/
theorem cell123_108 (e : List (ZMod 25)) (heK : charOK (basisAt rK123) e = true)
    (h : ↥(reps (⟨108, by decide⟩ : Fin 148))) :
    species (reps (⟨108, by decide⟩ : Fin 148)) h (basisElt (reps rK123) (charOfVec rK123 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK123 e (h : Coordinate 1) T123_108 i :=
  species_entry_eq_sum rK123 ⟨108, by decide⟩ e heK h T123_108 hfix123_108 hinj123_108 hcardT123_108
    (fun i => conj_mem_of_fixedPoints (reps ⟨108, by decide⟩) (reps rK123) (T123_108 i) (hfix123_108 i) h)

/-! ## Cell (123, 112): |T| = 5 -/

def T123_112list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T123_112 : Fin 5 → Coordinate 1 := fun i => T123_112list.getD i.val (0,0,0,0,0)

theorem hfix123_112 : ∀ i, ((T123_112 i : Coordinate 1) : Coordinate 1 ⧸ reps rK123)
    ∈ fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123) :=
  repsFix_of_siftB rK123 ⟨112, by decide⟩ T123_112 (by decide)

theorem hinj123_112 : Function.Injective
    (fun i => ((T123_112 i : Coordinate 1) : Coordinate 1 ⧸ reps rK123)) :=
  repsInj_of_reduceAux rK123 T123_112 (by decide)

theorem hcardT123_112 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK123 ⟨112, by decide⟩ R123 hpxR123 hcardq123 (by decide)).symm

/-- **Cell (123, 112).** -/
theorem cell123_112 (e : List (ZMod 25)) (heK : charOK (basisAt rK123) e = true)
    (h : ↥(reps (⟨112, by decide⟩ : Fin 148))) :
    species (reps (⟨112, by decide⟩ : Fin 148)) h (basisElt (reps rK123) (charOfVec rK123 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK123 e (h : Coordinate 1) T123_112 i :=
  species_entry_eq_sum rK123 ⟨112, by decide⟩ e heK h T123_112 hfix123_112 hinj123_112 hcardT123_112
    (fun i => conj_mem_of_fixedPoints (reps ⟨112, by decide⟩) (reps rK123) (T123_112 i) (hfix123_112 i) h)

/-! ## Cell (123, 123): |T| = 5 -/

def T123_123list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T123_123 : Fin 5 → Coordinate 1 := fun i => T123_123list.getD i.val (0,0,0,0,0)

theorem hfix123_123 : ∀ i, ((T123_123 i : Coordinate 1) : Coordinate 1 ⧸ reps rK123)
    ∈ fixedPoints (reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123) :=
  repsFix_of_siftB rK123 ⟨123, by decide⟩ T123_123 (by decide)

theorem hinj123_123 : Function.Injective
    (fun i => ((T123_123 i : Coordinate 1) : Coordinate 1 ⧸ reps rK123)) :=
  repsInj_of_reduceAux rK123 T123_123 (by decide)

theorem hcardT123_123 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK123 ⟨123, by decide⟩ R123 hpxR123 hcardq123 (by decide)).symm

/-- **Cell (123, 123).** -/
theorem cell123_123 (e : List (ZMod 25)) (heK : charOK (basisAt rK123) e = true)
    (h : ↥(reps (⟨123, by decide⟩ : Fin 148))) :
    species (reps (⟨123, by decide⟩ : Fin 148)) h (basisElt (reps rK123) (charOfVec rK123 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK123 e (h : Coordinate 1) T123_123 i :=
  species_entry_eq_sum rK123 ⟨123, by decide⟩ e heK h T123_123 hfix123_123 hinj123_123 hcardT123_123
    (fun i => conj_mem_of_fixedPoints (reps ⟨123, by decide⟩) (reps rK123) (T123_123 i) (hfix123_123 i) h)

namespace Q2

def R123_2 : Fin 5 → Coordinate 2 := fun i => R123list.getD i.val (0,0,0,0,0)
theorem hpxR123_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK123) (R123_2 i)) := by decide
theorem hcardq123_2 : Nat.card (Coordinate 2 ⧸ reps rK123) = 5 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (123, 0) twin -/

def T123_0_2 : Fin 5 → Coordinate 2 := fun i => T123_0list.getD i.val (0,0,0,0,0)

theorem hfix123_0_2 : ∀ i, ((T123_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK123)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK123) :=
  repsFix_of_siftB2 rK123 ⟨0, by decide⟩ T123_0_2 (by decide)

theorem hinj123_0_2 : Function.Injective
    (fun i => ((T123_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK123)) :=
  repsInj_of_reduceAux2 rK123 T123_0_2 (by decide)

theorem hcardT123_0_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK123)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK123 ⟨0, by decide⟩ R123_2 hpxR123_2 hcardq123_2 (by decide)).symm

/-- **Cell (123, 0) twin (q=2).** -/
theorem cell123_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK123) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK123) (charOfVec2 rK123 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK123 e (h : Coordinate 2) T123_0_2 i :=
  species_entry_eq_sum rK123 ⟨0, by decide⟩ e heK h T123_0_2 hfix123_0_2 hinj123_0_2 hcardT123_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK123) (T123_0_2 i) (hfix123_0_2 i) h)

/-! ### Cell (123, 2) twin -/

def T123_2_2 : Fin 5 → Coordinate 2 := fun i => T123_2list.getD i.val (0,0,0,0,0)

theorem hfix123_2_2 : ∀ i, ((T123_2_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK123)
    ∈ fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK123) :=
  repsFix_of_siftB2 rK123 ⟨2, by decide⟩ T123_2_2 (by decide)

theorem hinj123_2_2 : Function.Injective
    (fun i => ((T123_2_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK123)) :=
  repsInj_of_reduceAux2 rK123 T123_2_2 (by decide)

theorem hcardT123_2_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK123)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK123 ⟨2, by decide⟩ R123_2 hpxR123_2 hcardq123_2 (by decide)).symm

/-- **Cell (123, 2) twin (q=2).** -/
theorem cell123_2_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK123) e = true)
    (h : ↥(reps (⟨2, by decide⟩ : Fin 148))) :
    species (reps (⟨2, by decide⟩ : Fin 148)) h (basisElt (reps rK123) (charOfVec2 rK123 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK123 e (h : Coordinate 2) T123_2_2 i :=
  species_entry_eq_sum rK123 ⟨2, by decide⟩ e heK h T123_2_2 hfix123_2_2 hinj123_2_2 hcardT123_2_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨2, by decide⟩) (reps rK123) (T123_2_2 i) (hfix123_2_2 i) h)

/-! ### Cell (123, 10) twin -/

def T123_10_2 : Fin 5 → Coordinate 2 := fun i => T123_10list.getD i.val (0,0,0,0,0)

theorem hfix123_10_2 : ∀ i, ((T123_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK123)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK123) :=
  repsFix_of_siftB2 rK123 ⟨10, by decide⟩ T123_10_2 (by decide)

theorem hinj123_10_2 : Function.Injective
    (fun i => ((T123_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK123)) :=
  repsInj_of_reduceAux2 rK123 T123_10_2 (by decide)

theorem hcardT123_10_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK123)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK123 ⟨10, by decide⟩ R123_2 hpxR123_2 hcardq123_2 (by decide)).symm

/-- **Cell (123, 10) twin (q=2).** -/
theorem cell123_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK123) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK123) (charOfVec2 rK123 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK123 e (h : Coordinate 2) T123_10_2 i :=
  species_entry_eq_sum rK123 ⟨10, by decide⟩ e heK h T123_10_2 hfix123_10_2 hinj123_10_2 hcardT123_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK123) (T123_10_2 i) (hfix123_10_2 i) h)

/-! ### Cell (123, 12) twin -/

def T123_12_2 : Fin 5 → Coordinate 2 := fun i => T123_12list.getD i.val (0,0,0,0,0)

theorem hfix123_12_2 : ∀ i, ((T123_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK123)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK123) :=
  repsFix_of_siftB2 rK123 ⟨12, by decide⟩ T123_12_2 (by decide)

theorem hinj123_12_2 : Function.Injective
    (fun i => ((T123_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK123)) :=
  repsInj_of_reduceAux2 rK123 T123_12_2 (by decide)

theorem hcardT123_12_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK123)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK123 ⟨12, by decide⟩ R123_2 hpxR123_2 hcardq123_2 (by decide)).symm

/-- **Cell (123, 12) twin (q=2).** -/
theorem cell123_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK123) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK123) (charOfVec2 rK123 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK123 e (h : Coordinate 2) T123_12_2 i :=
  species_entry_eq_sum rK123 ⟨12, by decide⟩ e heK h T123_12_2 hfix123_12_2 hinj123_12_2 hcardT123_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK123) (T123_12_2 i) (hfix123_12_2 i) h)

/-! ### Cell (123, 20) twin -/

def T123_20_2 : Fin 5 → Coordinate 2 := fun i => T123_20list.getD i.val (0,0,0,0,0)

theorem hfix123_20_2 : ∀ i, ((T123_20_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK123)
    ∈ fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK123) :=
  repsFix_of_siftB2 rK123 ⟨20, by decide⟩ T123_20_2 (by decide)

theorem hinj123_20_2 : Function.Injective
    (fun i => ((T123_20_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK123)) :=
  repsInj_of_reduceAux2 rK123 T123_20_2 (by decide)

theorem hcardT123_20_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK123)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK123 ⟨20, by decide⟩ R123_2 hpxR123_2 hcardq123_2 (by decide)).symm

/-- **Cell (123, 20) twin (q=2).** -/
theorem cell123_20_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK123) e = true)
    (h : ↥(reps (⟨20, by decide⟩ : Fin 148))) :
    species (reps (⟨20, by decide⟩ : Fin 148)) h (basisElt (reps rK123) (charOfVec2 rK123 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK123 e (h : Coordinate 2) T123_20_2 i :=
  species_entry_eq_sum rK123 ⟨20, by decide⟩ e heK h T123_20_2 hfix123_20_2 hinj123_20_2 hcardT123_20_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨20, by decide⟩) (reps rK123) (T123_20_2 i) (hfix123_20_2 i) h)

/-! ### Cell (123, 29) twin -/

def T123_29_2 : Fin 5 → Coordinate 2 := fun i => T123_29list.getD i.val (0,0,0,0,0)

theorem hfix123_29_2 : ∀ i, ((T123_29_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK123)
    ∈ fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK123) :=
  repsFix_of_siftB2 rK123 ⟨29, by decide⟩ T123_29_2 (by decide)

theorem hinj123_29_2 : Function.Injective
    (fun i => ((T123_29_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK123)) :=
  repsInj_of_reduceAux2 rK123 T123_29_2 (by decide)

theorem hcardT123_29_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK123)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK123 ⟨29, by decide⟩ R123_2 hpxR123_2 hcardq123_2 (by decide)).symm

/-- **Cell (123, 29) twin (q=2).** -/
theorem cell123_29_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK123) e = true)
    (h : ↥(reps (⟨29, by decide⟩ : Fin 148))) :
    species (reps (⟨29, by decide⟩ : Fin 148)) h (basisElt (reps rK123) (charOfVec2 rK123 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK123 e (h : Coordinate 2) T123_29_2 i :=
  species_entry_eq_sum rK123 ⟨29, by decide⟩ e heK h T123_29_2 hfix123_29_2 hinj123_29_2 hcardT123_29_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨29, by decide⟩) (reps rK123) (T123_29_2 i) (hfix123_29_2 i) h)

/-! ### Cell (123, 37) twin -/

def T123_37_2 : Fin 5 → Coordinate 2 := fun i => T123_37list.getD i.val (0,0,0,0,0)

theorem hfix123_37_2 : ∀ i, ((T123_37_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK123)
    ∈ fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK123) :=
  repsFix_of_siftB2 rK123 ⟨37, by decide⟩ T123_37_2 (by decide)

theorem hinj123_37_2 : Function.Injective
    (fun i => ((T123_37_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK123)) :=
  repsInj_of_reduceAux2 rK123 T123_37_2 (by decide)

theorem hcardT123_37_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK123)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK123 ⟨37, by decide⟩ R123_2 hpxR123_2 hcardq123_2 (by decide)).symm

/-- **Cell (123, 37) twin (q=2).** -/
theorem cell123_37_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK123) e = true)
    (h : ↥(reps (⟨37, by decide⟩ : Fin 148))) :
    species (reps (⟨37, by decide⟩ : Fin 148)) h (basisElt (reps rK123) (charOfVec2 rK123 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK123 e (h : Coordinate 2) T123_37_2 i :=
  species_entry_eq_sum rK123 ⟨37, by decide⟩ e heK h T123_37_2 hfix123_37_2 hinj123_37_2 hcardT123_37_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨37, by decide⟩) (reps rK123) (T123_37_2 i) (hfix123_37_2 i) h)

/-! ### Cell (123, 38) twin -/

def T123_38_2 : Fin 5 → Coordinate 2 := fun i => T123_38list.getD i.val (0,0,0,0,0)

theorem hfix123_38_2 : ∀ i, ((T123_38_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK123)
    ∈ fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK123) :=
  repsFix_of_siftB2 rK123 ⟨38, by decide⟩ T123_38_2 (by decide)

theorem hinj123_38_2 : Function.Injective
    (fun i => ((T123_38_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK123)) :=
  repsInj_of_reduceAux2 rK123 T123_38_2 (by decide)

theorem hcardT123_38_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK123)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK123 ⟨38, by decide⟩ R123_2 hpxR123_2 hcardq123_2 (by decide)).symm

/-- **Cell (123, 38) twin (q=2).** -/
theorem cell123_38_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK123) e = true)
    (h : ↥(reps (⟨38, by decide⟩ : Fin 148))) :
    species (reps (⟨38, by decide⟩ : Fin 148)) h (basisElt (reps rK123) (charOfVec2 rK123 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK123 e (h : Coordinate 2) T123_38_2 i :=
  species_entry_eq_sum rK123 ⟨38, by decide⟩ e heK h T123_38_2 hfix123_38_2 hinj123_38_2 hcardT123_38_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨38, by decide⟩) (reps rK123) (T123_38_2 i) (hfix123_38_2 i) h)

/-! ### Cell (123, 46) twin -/

def T123_46_2 : Fin 5 → Coordinate 2 := fun i => T123_46list.getD i.val (0,0,0,0,0)

theorem hfix123_46_2 : ∀ i, ((T123_46_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK123)
    ∈ fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK123) :=
  repsFix_of_siftB2 rK123 ⟨46, by decide⟩ T123_46_2 (by decide)

theorem hinj123_46_2 : Function.Injective
    (fun i => ((T123_46_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK123)) :=
  repsInj_of_reduceAux2 rK123 T123_46_2 (by decide)

theorem hcardT123_46_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK123)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK123 ⟨46, by decide⟩ R123_2 hpxR123_2 hcardq123_2 (by decide)).symm

/-- **Cell (123, 46) twin (q=2).** -/
theorem cell123_46_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK123) e = true)
    (h : ↥(reps (⟨46, by decide⟩ : Fin 148))) :
    species (reps (⟨46, by decide⟩ : Fin 148)) h (basisElt (reps rK123) (charOfVec2 rK123 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK123 e (h : Coordinate 2) T123_46_2 i :=
  species_entry_eq_sum rK123 ⟨46, by decide⟩ e heK h T123_46_2 hfix123_46_2 hinj123_46_2 hcardT123_46_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨46, by decide⟩) (reps rK123) (T123_46_2 i) (hfix123_46_2 i) h)

/-! ### Cell (123, 50) twin -/

def T123_50_2 : Fin 5 → Coordinate 2 := fun i => T123_50list.getD i.val (0,0,0,0,0)

theorem hfix123_50_2 : ∀ i, ((T123_50_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK123)
    ∈ fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK123) :=
  repsFix_of_siftB2 rK123 ⟨50, by decide⟩ T123_50_2 (by decide)

theorem hinj123_50_2 : Function.Injective
    (fun i => ((T123_50_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK123)) :=
  repsInj_of_reduceAux2 rK123 T123_50_2 (by decide)

theorem hcardT123_50_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK123)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK123 ⟨50, by decide⟩ R123_2 hpxR123_2 hcardq123_2 (by decide)).symm

/-- **Cell (123, 50) twin (q=2).** -/
theorem cell123_50_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK123) e = true)
    (h : ↥(reps (⟨50, by decide⟩ : Fin 148))) :
    species (reps (⟨50, by decide⟩ : Fin 148)) h (basisElt (reps rK123) (charOfVec2 rK123 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK123 e (h : Coordinate 2) T123_50_2 i :=
  species_entry_eq_sum rK123 ⟨50, by decide⟩ e heK h T123_50_2 hfix123_50_2 hinj123_50_2 hcardT123_50_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨50, by decide⟩) (reps rK123) (T123_50_2 i) (hfix123_50_2 i) h)

/-! ### Cell (123, 53) twin -/

def T123_53_2 : Fin 5 → Coordinate 2 := fun i => T123_53list.getD i.val (0,0,0,0,0)

theorem hfix123_53_2 : ∀ i, ((T123_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK123)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK123) :=
  repsFix_of_siftB2 rK123 ⟨53, by decide⟩ T123_53_2 (by decide)

theorem hinj123_53_2 : Function.Injective
    (fun i => ((T123_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK123)) :=
  repsInj_of_reduceAux2 rK123 T123_53_2 (by decide)

theorem hcardT123_53_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK123)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK123 ⟨53, by decide⟩ R123_2 hpxR123_2 hcardq123_2 (by decide)).symm

/-- **Cell (123, 53) twin (q=2).** -/
theorem cell123_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK123) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK123) (charOfVec2 rK123 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK123 e (h : Coordinate 2) T123_53_2 i :=
  species_entry_eq_sum rK123 ⟨53, by decide⟩ e heK h T123_53_2 hfix123_53_2 hinj123_53_2 hcardT123_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK123) (T123_53_2 i) (hfix123_53_2 i) h)

/-! ### Cell (123, 81) twin -/

def T123_81_2 : Fin 5 → Coordinate 2 := fun i => T123_81list.getD i.val (0,0,0,0,0)

theorem hfix123_81_2 : ∀ i, ((T123_81_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK123)
    ∈ fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK123) :=
  repsFix_of_siftB2 rK123 ⟨81, by decide⟩ T123_81_2 (by decide)

theorem hinj123_81_2 : Function.Injective
    (fun i => ((T123_81_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK123)) :=
  repsInj_of_reduceAux2 rK123 T123_81_2 (by decide)

theorem hcardT123_81_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK123)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK123 ⟨81, by decide⟩ R123_2 hpxR123_2 hcardq123_2 (by decide)).symm

/-- **Cell (123, 81) twin (q=2).** -/
theorem cell123_81_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK123) e = true)
    (h : ↥(reps (⟨81, by decide⟩ : Fin 148))) :
    species (reps (⟨81, by decide⟩ : Fin 148)) h (basisElt (reps rK123) (charOfVec2 rK123 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK123 e (h : Coordinate 2) T123_81_2 i :=
  species_entry_eq_sum rK123 ⟨81, by decide⟩ e heK h T123_81_2 hfix123_81_2 hinj123_81_2 hcardT123_81_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨81, by decide⟩) (reps rK123) (T123_81_2 i) (hfix123_81_2 i) h)

/-! ### Cell (123, 91) twin -/

def T123_91_2 : Fin 5 → Coordinate 2 := fun i => T123_91list.getD i.val (0,0,0,0,0)

theorem hfix123_91_2 : ∀ i, ((T123_91_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK123)
    ∈ fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK123) :=
  repsFix_of_siftB2 rK123 ⟨91, by decide⟩ T123_91_2 (by decide)

theorem hinj123_91_2 : Function.Injective
    (fun i => ((T123_91_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK123)) :=
  repsInj_of_reduceAux2 rK123 T123_91_2 (by decide)

theorem hcardT123_91_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK123)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK123 ⟨91, by decide⟩ R123_2 hpxR123_2 hcardq123_2 (by decide)).symm

/-- **Cell (123, 91) twin (q=2).** -/
theorem cell123_91_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK123) e = true)
    (h : ↥(reps (⟨91, by decide⟩ : Fin 148))) :
    species (reps (⟨91, by decide⟩ : Fin 148)) h (basisElt (reps rK123) (charOfVec2 rK123 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK123 e (h : Coordinate 2) T123_91_2 i :=
  species_entry_eq_sum rK123 ⟨91, by decide⟩ e heK h T123_91_2 hfix123_91_2 hinj123_91_2 hcardT123_91_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨91, by decide⟩) (reps rK123) (T123_91_2 i) (hfix123_91_2 i) h)

/-! ### Cell (123, 99) twin -/

def T123_99_2 : Fin 5 → Coordinate 2 := fun i => T123_99list.getD i.val (0,0,0,0,0)

theorem hfix123_99_2 : ∀ i, ((T123_99_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK123)
    ∈ fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK123) :=
  repsFix_of_siftB2 rK123 ⟨99, by decide⟩ T123_99_2 (by decide)

theorem hinj123_99_2 : Function.Injective
    (fun i => ((T123_99_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK123)) :=
  repsInj_of_reduceAux2 rK123 T123_99_2 (by decide)

theorem hcardT123_99_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK123)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK123 ⟨99, by decide⟩ R123_2 hpxR123_2 hcardq123_2 (by decide)).symm

/-- **Cell (123, 99) twin (q=2).** -/
theorem cell123_99_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK123) e = true)
    (h : ↥(reps (⟨99, by decide⟩ : Fin 148))) :
    species (reps (⟨99, by decide⟩ : Fin 148)) h (basisElt (reps rK123) (charOfVec2 rK123 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK123 e (h : Coordinate 2) T123_99_2 i :=
  species_entry_eq_sum rK123 ⟨99, by decide⟩ e heK h T123_99_2 hfix123_99_2 hinj123_99_2 hcardT123_99_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨99, by decide⟩) (reps rK123) (T123_99_2 i) (hfix123_99_2 i) h)

/-! ### Cell (123, 100) twin -/

def T123_100_2 : Fin 5 → Coordinate 2 := fun i => T123_100list.getD i.val (0,0,0,0,0)

theorem hfix123_100_2 : ∀ i, ((T123_100_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK123)
    ∈ fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK123) :=
  repsFix_of_siftB2 rK123 ⟨100, by decide⟩ T123_100_2 (by decide)

theorem hinj123_100_2 : Function.Injective
    (fun i => ((T123_100_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK123)) :=
  repsInj_of_reduceAux2 rK123 T123_100_2 (by decide)

theorem hcardT123_100_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK123)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK123 ⟨100, by decide⟩ R123_2 hpxR123_2 hcardq123_2 (by decide)).symm

/-- **Cell (123, 100) twin (q=2).** -/
theorem cell123_100_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK123) e = true)
    (h : ↥(reps (⟨100, by decide⟩ : Fin 148))) :
    species (reps (⟨100, by decide⟩ : Fin 148)) h (basisElt (reps rK123) (charOfVec2 rK123 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK123 e (h : Coordinate 2) T123_100_2 i :=
  species_entry_eq_sum rK123 ⟨100, by decide⟩ e heK h T123_100_2 hfix123_100_2 hinj123_100_2 hcardT123_100_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨100, by decide⟩) (reps rK123) (T123_100_2 i) (hfix123_100_2 i) h)

/-! ### Cell (123, 108) twin -/

def T123_108_2 : Fin 5 → Coordinate 2 := fun i => T123_108list.getD i.val (0,0,0,0,0)

theorem hfix123_108_2 : ∀ i, ((T123_108_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK123)
    ∈ fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK123) :=
  repsFix_of_siftB2 rK123 ⟨108, by decide⟩ T123_108_2 (by decide)

theorem hinj123_108_2 : Function.Injective
    (fun i => ((T123_108_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK123)) :=
  repsInj_of_reduceAux2 rK123 T123_108_2 (by decide)

theorem hcardT123_108_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK123)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK123 ⟨108, by decide⟩ R123_2 hpxR123_2 hcardq123_2 (by decide)).symm

/-- **Cell (123, 108) twin (q=2).** -/
theorem cell123_108_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK123) e = true)
    (h : ↥(reps (⟨108, by decide⟩ : Fin 148))) :
    species (reps (⟨108, by decide⟩ : Fin 148)) h (basisElt (reps rK123) (charOfVec2 rK123 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK123 e (h : Coordinate 2) T123_108_2 i :=
  species_entry_eq_sum rK123 ⟨108, by decide⟩ e heK h T123_108_2 hfix123_108_2 hinj123_108_2 hcardT123_108_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨108, by decide⟩) (reps rK123) (T123_108_2 i) (hfix123_108_2 i) h)

/-! ### Cell (123, 112) twin -/

def T123_112_2 : Fin 5 → Coordinate 2 := fun i => T123_112list.getD i.val (0,0,0,0,0)

theorem hfix123_112_2 : ∀ i, ((T123_112_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK123)
    ∈ fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK123) :=
  repsFix_of_siftB2 rK123 ⟨112, by decide⟩ T123_112_2 (by decide)

theorem hinj123_112_2 : Function.Injective
    (fun i => ((T123_112_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK123)) :=
  repsInj_of_reduceAux2 rK123 T123_112_2 (by decide)

theorem hcardT123_112_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK123)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK123 ⟨112, by decide⟩ R123_2 hpxR123_2 hcardq123_2 (by decide)).symm

/-- **Cell (123, 112) twin (q=2).** -/
theorem cell123_112_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK123) e = true)
    (h : ↥(reps (⟨112, by decide⟩ : Fin 148))) :
    species (reps (⟨112, by decide⟩ : Fin 148)) h (basisElt (reps rK123) (charOfVec2 rK123 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK123 e (h : Coordinate 2) T123_112_2 i :=
  species_entry_eq_sum rK123 ⟨112, by decide⟩ e heK h T123_112_2 hfix123_112_2 hinj123_112_2 hcardT123_112_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨112, by decide⟩) (reps rK123) (T123_112_2 i) (hfix123_112_2 i) h)

/-! ### Cell (123, 123) twin -/

def T123_123_2 : Fin 5 → Coordinate 2 := fun i => T123_123list.getD i.val (0,0,0,0,0)

theorem hfix123_123_2 : ∀ i, ((T123_123_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK123)
    ∈ fixedPoints (reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK123) :=
  repsFix_of_siftB2 rK123 ⟨123, by decide⟩ T123_123_2 (by decide)

theorem hinj123_123_2 : Function.Injective
    (fun i => ((T123_123_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK123)) :=
  repsInj_of_reduceAux2 rK123 T123_123_2 (by decide)

theorem hcardT123_123_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK123)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK123 ⟨123, by decide⟩ R123_2 hpxR123_2 hcardq123_2 (by decide)).symm

/-- **Cell (123, 123) twin (q=2).** -/
theorem cell123_123_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK123) e = true)
    (h : ↥(reps (⟨123, by decide⟩ : Fin 148))) :
    species (reps (⟨123, by decide⟩ : Fin 148)) h (basisElt (reps rK123) (charOfVec2 rK123 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK123 e (h : Coordinate 2) T123_123_2 i :=
  species_entry_eq_sum rK123 ⟨123, by decide⟩ e heK h T123_123_2 hfix123_123_2 hinj123_123_2 hcardT123_123_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨123, by decide⟩) (reps rK123) (T123_123_2 i) (hfix123_123_2 i) h)

end Q2

end LeanDring.P5Presentation
