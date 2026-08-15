/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, K-strata data (5^4 stratum, rK 134-135): certified per-cell species-entry instantiations, both
twins.

Covers K-classes 134, 135 (order-5^4 K, |R|=5).  For each nonzero `H`-column
(`(G/K)^H ≠ ∅`), the full coset transversal `R134..` and each `H`-fixed
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

/-! # K-class rK = 134  (|G/K| = 5) -/

def rK134 : Fin 148 := ⟨134, by decide⟩

def R134list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def R134 : Fin 5 → Coordinate 1 := fun i => R134list.getD i.val (0,0,0,0,0)

theorem hpxR134 : Function.Injective (fun i => reduceAux 1 (basisAt rK134) (R134 i)) := by decide
theorem hcardq134 : Nat.card (Coordinate 1 ⧸ reps rK134) = 5 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (134, 0): |T| = 5 -/

def T134_0list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T134_0 : Fin 5 → Coordinate 1 := fun i => T134_0list.getD i.val (0,0,0,0,0)

theorem hfix134_0 : ∀ i, ((T134_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK134)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134) :=
  repsFix_of_siftB rK134 ⟨0, by decide⟩ T134_0 (by decide)

theorem hinj134_0 : Function.Injective
    (fun i => ((T134_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK134)) :=
  repsInj_of_reduceAux rK134 T134_0 (by decide)

theorem hcardT134_0 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK134 ⟨0, by decide⟩ R134 hpxR134 hcardq134 (by decide)).symm

/-- **Cell (134, 0).** -/
theorem cell134_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK134) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK134) (charOfVec rK134 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK134 e (h : Coordinate 1) T134_0 i :=
  species_entry_eq_sum rK134 ⟨0, by decide⟩ e heK h T134_0 hfix134_0 hinj134_0 hcardT134_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK134) (T134_0 i) (hfix134_0 i) h)

/-! ## Cell (134, 4): |T| = 5 -/

def T134_4list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T134_4 : Fin 5 → Coordinate 1 := fun i => T134_4list.getD i.val (0,0,0,0,0)

theorem hfix134_4 : ∀ i, ((T134_4 i : Coordinate 1) : Coordinate 1 ⧸ reps rK134)
    ∈ fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134) :=
  repsFix_of_siftB rK134 ⟨4, by decide⟩ T134_4 (by decide)

theorem hinj134_4 : Function.Injective
    (fun i => ((T134_4 i : Coordinate 1) : Coordinate 1 ⧸ reps rK134)) :=
  repsInj_of_reduceAux rK134 T134_4 (by decide)

theorem hcardT134_4 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK134 ⟨4, by decide⟩ R134 hpxR134 hcardq134 (by decide)).symm

/-- **Cell (134, 4).** -/
theorem cell134_4 (e : List (ZMod 25)) (heK : charOK (basisAt rK134) e = true)
    (h : ↥(reps (⟨4, by decide⟩ : Fin 148))) :
    species (reps (⟨4, by decide⟩ : Fin 148)) h (basisElt (reps rK134) (charOfVec rK134 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK134 e (h : Coordinate 1) T134_4 i :=
  species_entry_eq_sum rK134 ⟨4, by decide⟩ e heK h T134_4 hfix134_4 hinj134_4 hcardT134_4
    (fun i => conj_mem_of_fixedPoints (reps ⟨4, by decide⟩) (reps rK134) (T134_4 i) (hfix134_4 i) h)

/-! ## Cell (134, 10): |T| = 5 -/

def T134_10list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T134_10 : Fin 5 → Coordinate 1 := fun i => T134_10list.getD i.val (0,0,0,0,0)

theorem hfix134_10 : ∀ i, ((T134_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK134)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134) :=
  repsFix_of_siftB rK134 ⟨10, by decide⟩ T134_10 (by decide)

theorem hinj134_10 : Function.Injective
    (fun i => ((T134_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK134)) :=
  repsInj_of_reduceAux rK134 T134_10 (by decide)

theorem hcardT134_10 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK134 ⟨10, by decide⟩ R134 hpxR134 hcardq134 (by decide)).symm

/-- **Cell (134, 10).** -/
theorem cell134_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK134) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK134) (charOfVec rK134 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK134 e (h : Coordinate 1) T134_10 i :=
  species_entry_eq_sum rK134 ⟨10, by decide⟩ e heK h T134_10 hfix134_10 hinj134_10 hcardT134_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK134) (T134_10 i) (hfix134_10 i) h)

/-! ## Cell (134, 12): |T| = 5 -/

def T134_12list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T134_12 : Fin 5 → Coordinate 1 := fun i => T134_12list.getD i.val (0,0,0,0,0)

theorem hfix134_12 : ∀ i, ((T134_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK134)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134) :=
  repsFix_of_siftB rK134 ⟨12, by decide⟩ T134_12 (by decide)

theorem hinj134_12 : Function.Injective
    (fun i => ((T134_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK134)) :=
  repsInj_of_reduceAux rK134 T134_12 (by decide)

theorem hcardT134_12 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK134 ⟨12, by decide⟩ R134 hpxR134 hcardq134 (by decide)).symm

/-- **Cell (134, 12).** -/
theorem cell134_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK134) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK134) (charOfVec rK134 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK134 e (h : Coordinate 1) T134_12 i :=
  species_entry_eq_sum rK134 ⟨12, by decide⟩ e heK h T134_12 hfix134_12 hinj134_12 hcardT134_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK134) (T134_12 i) (hfix134_12 i) h)

/-! ## Cell (134, 22): |T| = 5 -/

def T134_22list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T134_22 : Fin 5 → Coordinate 1 := fun i => T134_22list.getD i.val (0,0,0,0,0)

theorem hfix134_22 : ∀ i, ((T134_22 i : Coordinate 1) : Coordinate 1 ⧸ reps rK134)
    ∈ fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134) :=
  repsFix_of_siftB rK134 ⟨22, by decide⟩ T134_22 (by decide)

theorem hinj134_22 : Function.Injective
    (fun i => ((T134_22 i : Coordinate 1) : Coordinate 1 ⧸ reps rK134)) :=
  repsInj_of_reduceAux rK134 T134_22 (by decide)

theorem hcardT134_22 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK134 ⟨22, by decide⟩ R134 hpxR134 hcardq134 (by decide)).symm

/-- **Cell (134, 22).** -/
theorem cell134_22 (e : List (ZMod 25)) (heK : charOK (basisAt rK134) e = true)
    (h : ↥(reps (⟨22, by decide⟩ : Fin 148))) :
    species (reps (⟨22, by decide⟩ : Fin 148)) h (basisElt (reps rK134) (charOfVec rK134 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK134 e (h : Coordinate 1) T134_22 i :=
  species_entry_eq_sum rK134 ⟨22, by decide⟩ e heK h T134_22 hfix134_22 hinj134_22 hcardT134_22
    (fun i => conj_mem_of_fixedPoints (reps ⟨22, by decide⟩) (reps rK134) (T134_22 i) (hfix134_22 i) h)

/-! ## Cell (134, 28): |T| = 5 -/

def T134_28list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T134_28 : Fin 5 → Coordinate 1 := fun i => T134_28list.getD i.val (0,0,0,0,0)

theorem hfix134_28 : ∀ i, ((T134_28 i : Coordinate 1) : Coordinate 1 ⧸ reps rK134)
    ∈ fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134) :=
  repsFix_of_siftB rK134 ⟨28, by decide⟩ T134_28 (by decide)

theorem hinj134_28 : Function.Injective
    (fun i => ((T134_28 i : Coordinate 1) : Coordinate 1 ⧸ reps rK134)) :=
  repsInj_of_reduceAux rK134 T134_28 (by decide)

theorem hcardT134_28 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK134 ⟨28, by decide⟩ R134 hpxR134 hcardq134 (by decide)).symm

/-- **Cell (134, 28).** -/
theorem cell134_28 (e : List (ZMod 25)) (heK : charOK (basisAt rK134) e = true)
    (h : ↥(reps (⟨28, by decide⟩ : Fin 148))) :
    species (reps (⟨28, by decide⟩ : Fin 148)) h (basisElt (reps rK134) (charOfVec rK134 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK134 e (h : Coordinate 1) T134_28 i :=
  species_entry_eq_sum rK134 ⟨28, by decide⟩ e heK h T134_28 hfix134_28 hinj134_28 hcardT134_28
    (fun i => conj_mem_of_fixedPoints (reps ⟨28, by decide⟩) (reps rK134) (T134_28 i) (hfix134_28 i) h)

/-! ## Cell (134, 37): |T| = 5 -/

def T134_37list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T134_37 : Fin 5 → Coordinate 1 := fun i => T134_37list.getD i.val (0,0,0,0,0)

theorem hfix134_37 : ∀ i, ((T134_37 i : Coordinate 1) : Coordinate 1 ⧸ reps rK134)
    ∈ fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134) :=
  repsFix_of_siftB rK134 ⟨37, by decide⟩ T134_37 (by decide)

theorem hinj134_37 : Function.Injective
    (fun i => ((T134_37 i : Coordinate 1) : Coordinate 1 ⧸ reps rK134)) :=
  repsInj_of_reduceAux rK134 T134_37 (by decide)

theorem hcardT134_37 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK134 ⟨37, by decide⟩ R134 hpxR134 hcardq134 (by decide)).symm

/-- **Cell (134, 37).** -/
theorem cell134_37 (e : List (ZMod 25)) (heK : charOK (basisAt rK134) e = true)
    (h : ↥(reps (⟨37, by decide⟩ : Fin 148))) :
    species (reps (⟨37, by decide⟩ : Fin 148)) h (basisElt (reps rK134) (charOfVec rK134 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK134 e (h : Coordinate 1) T134_37 i :=
  species_entry_eq_sum rK134 ⟨37, by decide⟩ e heK h T134_37 hfix134_37 hinj134_37 hcardT134_37
    (fun i => conj_mem_of_fixedPoints (reps ⟨37, by decide⟩) (reps rK134) (T134_37 i) (hfix134_37 i) h)

/-! ## Cell (134, 40): |T| = 5 -/

def T134_40list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T134_40 : Fin 5 → Coordinate 1 := fun i => T134_40list.getD i.val (0,0,0,0,0)

theorem hfix134_40 : ∀ i, ((T134_40 i : Coordinate 1) : Coordinate 1 ⧸ reps rK134)
    ∈ fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134) :=
  repsFix_of_siftB rK134 ⟨40, by decide⟩ T134_40 (by decide)

theorem hinj134_40 : Function.Injective
    (fun i => ((T134_40 i : Coordinate 1) : Coordinate 1 ⧸ reps rK134)) :=
  repsInj_of_reduceAux rK134 T134_40 (by decide)

theorem hcardT134_40 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK134 ⟨40, by decide⟩ R134 hpxR134 hcardq134 (by decide)).symm

/-- **Cell (134, 40).** -/
theorem cell134_40 (e : List (ZMod 25)) (heK : charOK (basisAt rK134) e = true)
    (h : ↥(reps (⟨40, by decide⟩ : Fin 148))) :
    species (reps (⟨40, by decide⟩ : Fin 148)) h (basisElt (reps rK134) (charOfVec rK134 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK134 e (h : Coordinate 1) T134_40 i :=
  species_entry_eq_sum rK134 ⟨40, by decide⟩ e heK h T134_40 hfix134_40 hinj134_40 hcardT134_40
    (fun i => conj_mem_of_fixedPoints (reps ⟨40, by decide⟩) (reps rK134) (T134_40 i) (hfix134_40 i) h)

/-! ## Cell (134, 44): |T| = 5 -/

def T134_44list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T134_44 : Fin 5 → Coordinate 1 := fun i => T134_44list.getD i.val (0,0,0,0,0)

theorem hfix134_44 : ∀ i, ((T134_44 i : Coordinate 1) : Coordinate 1 ⧸ reps rK134)
    ∈ fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134) :=
  repsFix_of_siftB rK134 ⟨44, by decide⟩ T134_44 (by decide)

theorem hinj134_44 : Function.Injective
    (fun i => ((T134_44 i : Coordinate 1) : Coordinate 1 ⧸ reps rK134)) :=
  repsInj_of_reduceAux rK134 T134_44 (by decide)

theorem hcardT134_44 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK134 ⟨44, by decide⟩ R134 hpxR134 hcardq134 (by decide)).symm

/-- **Cell (134, 44).** -/
theorem cell134_44 (e : List (ZMod 25)) (heK : charOK (basisAt rK134) e = true)
    (h : ↥(reps (⟨44, by decide⟩ : Fin 148))) :
    species (reps (⟨44, by decide⟩ : Fin 148)) h (basisElt (reps rK134) (charOfVec rK134 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK134 e (h : Coordinate 1) T134_44 i :=
  species_entry_eq_sum rK134 ⟨44, by decide⟩ e heK h T134_44 hfix134_44 hinj134_44 hcardT134_44
    (fun i => conj_mem_of_fixedPoints (reps ⟨44, by decide⟩) (reps rK134) (T134_44 i) (hfix134_44 i) h)

/-! ## Cell (134, 51): |T| = 5 -/

def T134_51list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T134_51 : Fin 5 → Coordinate 1 := fun i => T134_51list.getD i.val (0,0,0,0,0)

theorem hfix134_51 : ∀ i, ((T134_51 i : Coordinate 1) : Coordinate 1 ⧸ reps rK134)
    ∈ fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134) :=
  repsFix_of_siftB rK134 ⟨51, by decide⟩ T134_51 (by decide)

theorem hinj134_51 : Function.Injective
    (fun i => ((T134_51 i : Coordinate 1) : Coordinate 1 ⧸ reps rK134)) :=
  repsInj_of_reduceAux rK134 T134_51 (by decide)

theorem hcardT134_51 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK134 ⟨51, by decide⟩ R134 hpxR134 hcardq134 (by decide)).symm

/-- **Cell (134, 51).** -/
theorem cell134_51 (e : List (ZMod 25)) (heK : charOK (basisAt rK134) e = true)
    (h : ↥(reps (⟨51, by decide⟩ : Fin 148))) :
    species (reps (⟨51, by decide⟩ : Fin 148)) h (basisElt (reps rK134) (charOfVec rK134 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK134 e (h : Coordinate 1) T134_51 i :=
  species_entry_eq_sum rK134 ⟨51, by decide⟩ e heK h T134_51 hfix134_51 hinj134_51 hcardT134_51
    (fun i => conj_mem_of_fixedPoints (reps ⟨51, by decide⟩) (reps rK134) (T134_51 i) (hfix134_51 i) h)

/-! ## Cell (134, 53): |T| = 5 -/

def T134_53list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T134_53 : Fin 5 → Coordinate 1 := fun i => T134_53list.getD i.val (0,0,0,0,0)

theorem hfix134_53 : ∀ i, ((T134_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK134)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134) :=
  repsFix_of_siftB rK134 ⟨53, by decide⟩ T134_53 (by decide)

theorem hinj134_53 : Function.Injective
    (fun i => ((T134_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK134)) :=
  repsInj_of_reduceAux rK134 T134_53 (by decide)

theorem hcardT134_53 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK134 ⟨53, by decide⟩ R134 hpxR134 hcardq134 (by decide)).symm

/-- **Cell (134, 53).** -/
theorem cell134_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK134) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK134) (charOfVec rK134 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK134 e (h : Coordinate 1) T134_53 i :=
  species_entry_eq_sum rK134 ⟨53, by decide⟩ e heK h T134_53 hfix134_53 hinj134_53 hcardT134_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK134) (T134_53 i) (hfix134_53 i) h)

/-! ## Cell (134, 83): |T| = 5 -/

def T134_83list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T134_83 : Fin 5 → Coordinate 1 := fun i => T134_83list.getD i.val (0,0,0,0,0)

theorem hfix134_83 : ∀ i, ((T134_83 i : Coordinate 1) : Coordinate 1 ⧸ reps rK134)
    ∈ fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134) :=
  repsFix_of_siftB rK134 ⟨83, by decide⟩ T134_83 (by decide)

theorem hinj134_83 : Function.Injective
    (fun i => ((T134_83 i : Coordinate 1) : Coordinate 1 ⧸ reps rK134)) :=
  repsInj_of_reduceAux rK134 T134_83 (by decide)

theorem hcardT134_83 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK134 ⟨83, by decide⟩ R134 hpxR134 hcardq134 (by decide)).symm

/-- **Cell (134, 83).** -/
theorem cell134_83 (e : List (ZMod 25)) (heK : charOK (basisAt rK134) e = true)
    (h : ↥(reps (⟨83, by decide⟩ : Fin 148))) :
    species (reps (⟨83, by decide⟩ : Fin 148)) h (basisElt (reps rK134) (charOfVec rK134 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK134 e (h : Coordinate 1) T134_83 i :=
  species_entry_eq_sum rK134 ⟨83, by decide⟩ e heK h T134_83 hfix134_83 hinj134_83 hcardT134_83
    (fun i => conj_mem_of_fixedPoints (reps ⟨83, by decide⟩) (reps rK134) (T134_83 i) (hfix134_83 i) h)

/-! ## Cell (134, 90): |T| = 5 -/

def T134_90list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T134_90 : Fin 5 → Coordinate 1 := fun i => T134_90list.getD i.val (0,0,0,0,0)

theorem hfix134_90 : ∀ i, ((T134_90 i : Coordinate 1) : Coordinate 1 ⧸ reps rK134)
    ∈ fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134) :=
  repsFix_of_siftB rK134 ⟨90, by decide⟩ T134_90 (by decide)

theorem hinj134_90 : Function.Injective
    (fun i => ((T134_90 i : Coordinate 1) : Coordinate 1 ⧸ reps rK134)) :=
  repsInj_of_reduceAux rK134 T134_90 (by decide)

theorem hcardT134_90 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK134 ⟨90, by decide⟩ R134 hpxR134 hcardq134 (by decide)).symm

/-- **Cell (134, 90).** -/
theorem cell134_90 (e : List (ZMod 25)) (heK : charOK (basisAt rK134) e = true)
    (h : ↥(reps (⟨90, by decide⟩ : Fin 148))) :
    species (reps (⟨90, by decide⟩ : Fin 148)) h (basisElt (reps rK134) (charOfVec rK134 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK134 e (h : Coordinate 1) T134_90 i :=
  species_entry_eq_sum rK134 ⟨90, by decide⟩ e heK h T134_90 hfix134_90 hinj134_90 hcardT134_90
    (fun i => conj_mem_of_fixedPoints (reps ⟨90, by decide⟩) (reps rK134) (T134_90 i) (hfix134_90 i) h)

/-! ## Cell (134, 99): |T| = 5 -/

def T134_99list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T134_99 : Fin 5 → Coordinate 1 := fun i => T134_99list.getD i.val (0,0,0,0,0)

theorem hfix134_99 : ∀ i, ((T134_99 i : Coordinate 1) : Coordinate 1 ⧸ reps rK134)
    ∈ fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134) :=
  repsFix_of_siftB rK134 ⟨99, by decide⟩ T134_99 (by decide)

theorem hinj134_99 : Function.Injective
    (fun i => ((T134_99 i : Coordinate 1) : Coordinate 1 ⧸ reps rK134)) :=
  repsInj_of_reduceAux rK134 T134_99 (by decide)

theorem hcardT134_99 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK134 ⟨99, by decide⟩ R134 hpxR134 hcardq134 (by decide)).symm

/-- **Cell (134, 99).** -/
theorem cell134_99 (e : List (ZMod 25)) (heK : charOK (basisAt rK134) e = true)
    (h : ↥(reps (⟨99, by decide⟩ : Fin 148))) :
    species (reps (⟨99, by decide⟩ : Fin 148)) h (basisElt (reps rK134) (charOfVec rK134 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK134 e (h : Coordinate 1) T134_99 i :=
  species_entry_eq_sum rK134 ⟨99, by decide⟩ e heK h T134_99 hfix134_99 hinj134_99 hcardT134_99
    (fun i => conj_mem_of_fixedPoints (reps ⟨99, by decide⟩) (reps rK134) (T134_99 i) (hfix134_99 i) h)

/-! ## Cell (134, 102): |T| = 5 -/

def T134_102list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T134_102 : Fin 5 → Coordinate 1 := fun i => T134_102list.getD i.val (0,0,0,0,0)

theorem hfix134_102 : ∀ i, ((T134_102 i : Coordinate 1) : Coordinate 1 ⧸ reps rK134)
    ∈ fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134) :=
  repsFix_of_siftB rK134 ⟨102, by decide⟩ T134_102 (by decide)

theorem hinj134_102 : Function.Injective
    (fun i => ((T134_102 i : Coordinate 1) : Coordinate 1 ⧸ reps rK134)) :=
  repsInj_of_reduceAux rK134 T134_102 (by decide)

theorem hcardT134_102 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK134 ⟨102, by decide⟩ R134 hpxR134 hcardq134 (by decide)).symm

/-- **Cell (134, 102).** -/
theorem cell134_102 (e : List (ZMod 25)) (heK : charOK (basisAt rK134) e = true)
    (h : ↥(reps (⟨102, by decide⟩ : Fin 148))) :
    species (reps (⟨102, by decide⟩ : Fin 148)) h (basisElt (reps rK134) (charOfVec rK134 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK134 e (h : Coordinate 1) T134_102 i :=
  species_entry_eq_sum rK134 ⟨102, by decide⟩ e heK h T134_102 hfix134_102 hinj134_102 hcardT134_102
    (fun i => conj_mem_of_fixedPoints (reps ⟨102, by decide⟩) (reps rK134) (T134_102 i) (hfix134_102 i) h)

/-! ## Cell (134, 106): |T| = 5 -/

def T134_106list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T134_106 : Fin 5 → Coordinate 1 := fun i => T134_106list.getD i.val (0,0,0,0,0)

theorem hfix134_106 : ∀ i, ((T134_106 i : Coordinate 1) : Coordinate 1 ⧸ reps rK134)
    ∈ fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134) :=
  repsFix_of_siftB rK134 ⟨106, by decide⟩ T134_106 (by decide)

theorem hinj134_106 : Function.Injective
    (fun i => ((T134_106 i : Coordinate 1) : Coordinate 1 ⧸ reps rK134)) :=
  repsInj_of_reduceAux rK134 T134_106 (by decide)

theorem hcardT134_106 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK134 ⟨106, by decide⟩ R134 hpxR134 hcardq134 (by decide)).symm

/-- **Cell (134, 106).** -/
theorem cell134_106 (e : List (ZMod 25)) (heK : charOK (basisAt rK134) e = true)
    (h : ↥(reps (⟨106, by decide⟩ : Fin 148))) :
    species (reps (⟨106, by decide⟩ : Fin 148)) h (basisElt (reps rK134) (charOfVec rK134 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK134 e (h : Coordinate 1) T134_106 i :=
  species_entry_eq_sum rK134 ⟨106, by decide⟩ e heK h T134_106 hfix134_106 hinj134_106 hcardT134_106
    (fun i => conj_mem_of_fixedPoints (reps ⟨106, by decide⟩) (reps rK134) (T134_106 i) (hfix134_106 i) h)

/-! ## Cell (134, 113): |T| = 5 -/

def T134_113list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T134_113 : Fin 5 → Coordinate 1 := fun i => T134_113list.getD i.val (0,0,0,0,0)

theorem hfix134_113 : ∀ i, ((T134_113 i : Coordinate 1) : Coordinate 1 ⧸ reps rK134)
    ∈ fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134) :=
  repsFix_of_siftB rK134 ⟨113, by decide⟩ T134_113 (by decide)

theorem hinj134_113 : Function.Injective
    (fun i => ((T134_113 i : Coordinate 1) : Coordinate 1 ⧸ reps rK134)) :=
  repsInj_of_reduceAux rK134 T134_113 (by decide)

theorem hcardT134_113 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK134 ⟨113, by decide⟩ R134 hpxR134 hcardq134 (by decide)).symm

/-- **Cell (134, 113).** -/
theorem cell134_113 (e : List (ZMod 25)) (heK : charOK (basisAt rK134) e = true)
    (h : ↥(reps (⟨113, by decide⟩ : Fin 148))) :
    species (reps (⟨113, by decide⟩ : Fin 148)) h (basisElt (reps rK134) (charOfVec rK134 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK134 e (h : Coordinate 1) T134_113 i :=
  species_entry_eq_sum rK134 ⟨113, by decide⟩ e heK h T134_113 hfix134_113 hinj134_113 hcardT134_113
    (fun i => conj_mem_of_fixedPoints (reps ⟨113, by decide⟩) (reps rK134) (T134_113 i) (hfix134_113 i) h)

/-! ## Cell (134, 134): |T| = 5 -/

def T134_134list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T134_134 : Fin 5 → Coordinate 1 := fun i => T134_134list.getD i.val (0,0,0,0,0)

theorem hfix134_134 : ∀ i, ((T134_134 i : Coordinate 1) : Coordinate 1 ⧸ reps rK134)
    ∈ fixedPoints (reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134) :=
  repsFix_of_siftB rK134 ⟨134, by decide⟩ T134_134 (by decide)

theorem hinj134_134 : Function.Injective
    (fun i => ((T134_134 i : Coordinate 1) : Coordinate 1 ⧸ reps rK134)) :=
  repsInj_of_reduceAux rK134 T134_134 (by decide)

theorem hcardT134_134 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK134 ⟨134, by decide⟩ R134 hpxR134 hcardq134 (by decide)).symm

/-- **Cell (134, 134).** -/
theorem cell134_134 (e : List (ZMod 25)) (heK : charOK (basisAt rK134) e = true)
    (h : ↥(reps (⟨134, by decide⟩ : Fin 148))) :
    species (reps (⟨134, by decide⟩ : Fin 148)) h (basisElt (reps rK134) (charOfVec rK134 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK134 e (h : Coordinate 1) T134_134 i :=
  species_entry_eq_sum rK134 ⟨134, by decide⟩ e heK h T134_134 hfix134_134 hinj134_134 hcardT134_134
    (fun i => conj_mem_of_fixedPoints (reps ⟨134, by decide⟩) (reps rK134) (T134_134 i) (hfix134_134 i) h)

namespace Q2

def R134_2 : Fin 5 → Coordinate 2 := fun i => R134list.getD i.val (0,0,0,0,0)
theorem hpxR134_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK134) (R134_2 i)) := by decide
theorem hcardq134_2 : Nat.card (Coordinate 2 ⧸ reps rK134) = 5 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (134, 0) twin -/

def T134_0_2 : Fin 5 → Coordinate 2 := fun i => T134_0list.getD i.val (0,0,0,0,0)

theorem hfix134_0_2 : ∀ i, ((T134_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK134)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK134) :=
  repsFix_of_siftB2 rK134 ⟨0, by decide⟩ T134_0_2 (by decide)

theorem hinj134_0_2 : Function.Injective
    (fun i => ((T134_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK134)) :=
  repsInj_of_reduceAux2 rK134 T134_0_2 (by decide)

theorem hcardT134_0_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK134)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK134 ⟨0, by decide⟩ R134_2 hpxR134_2 hcardq134_2 (by decide)).symm

/-- **Cell (134, 0) twin (q=2).** -/
theorem cell134_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK134) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK134) (charOfVec2 rK134 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK134 e (h : Coordinate 2) T134_0_2 i :=
  species_entry_eq_sum rK134 ⟨0, by decide⟩ e heK h T134_0_2 hfix134_0_2 hinj134_0_2 hcardT134_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK134) (T134_0_2 i) (hfix134_0_2 i) h)

/-! ### Cell (134, 4) twin -/

def T134_4_2 : Fin 5 → Coordinate 2 := fun i => T134_4list.getD i.val (0,0,0,0,0)

theorem hfix134_4_2 : ∀ i, ((T134_4_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK134)
    ∈ fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK134) :=
  repsFix_of_siftB2 rK134 ⟨4, by decide⟩ T134_4_2 (by decide)

theorem hinj134_4_2 : Function.Injective
    (fun i => ((T134_4_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK134)) :=
  repsInj_of_reduceAux2 rK134 T134_4_2 (by decide)

theorem hcardT134_4_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK134)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK134 ⟨4, by decide⟩ R134_2 hpxR134_2 hcardq134_2 (by decide)).symm

/-- **Cell (134, 4) twin (q=2).** -/
theorem cell134_4_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK134) e = true)
    (h : ↥(reps (⟨4, by decide⟩ : Fin 148))) :
    species (reps (⟨4, by decide⟩ : Fin 148)) h (basisElt (reps rK134) (charOfVec2 rK134 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK134 e (h : Coordinate 2) T134_4_2 i :=
  species_entry_eq_sum rK134 ⟨4, by decide⟩ e heK h T134_4_2 hfix134_4_2 hinj134_4_2 hcardT134_4_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨4, by decide⟩) (reps rK134) (T134_4_2 i) (hfix134_4_2 i) h)

/-! ### Cell (134, 10) twin -/

def T134_10_2 : Fin 5 → Coordinate 2 := fun i => T134_10list.getD i.val (0,0,0,0,0)

theorem hfix134_10_2 : ∀ i, ((T134_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK134)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK134) :=
  repsFix_of_siftB2 rK134 ⟨10, by decide⟩ T134_10_2 (by decide)

theorem hinj134_10_2 : Function.Injective
    (fun i => ((T134_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK134)) :=
  repsInj_of_reduceAux2 rK134 T134_10_2 (by decide)

theorem hcardT134_10_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK134)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK134 ⟨10, by decide⟩ R134_2 hpxR134_2 hcardq134_2 (by decide)).symm

/-- **Cell (134, 10) twin (q=2).** -/
theorem cell134_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK134) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK134) (charOfVec2 rK134 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK134 e (h : Coordinate 2) T134_10_2 i :=
  species_entry_eq_sum rK134 ⟨10, by decide⟩ e heK h T134_10_2 hfix134_10_2 hinj134_10_2 hcardT134_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK134) (T134_10_2 i) (hfix134_10_2 i) h)

/-! ### Cell (134, 12) twin -/

def T134_12_2 : Fin 5 → Coordinate 2 := fun i => T134_12list.getD i.val (0,0,0,0,0)

theorem hfix134_12_2 : ∀ i, ((T134_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK134)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK134) :=
  repsFix_of_siftB2 rK134 ⟨12, by decide⟩ T134_12_2 (by decide)

theorem hinj134_12_2 : Function.Injective
    (fun i => ((T134_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK134)) :=
  repsInj_of_reduceAux2 rK134 T134_12_2 (by decide)

theorem hcardT134_12_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK134)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK134 ⟨12, by decide⟩ R134_2 hpxR134_2 hcardq134_2 (by decide)).symm

/-- **Cell (134, 12) twin (q=2).** -/
theorem cell134_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK134) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK134) (charOfVec2 rK134 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK134 e (h : Coordinate 2) T134_12_2 i :=
  species_entry_eq_sum rK134 ⟨12, by decide⟩ e heK h T134_12_2 hfix134_12_2 hinj134_12_2 hcardT134_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK134) (T134_12_2 i) (hfix134_12_2 i) h)

/-! ### Cell (134, 22) twin -/

def T134_22_2 : Fin 5 → Coordinate 2 := fun i => T134_22list.getD i.val (0,0,0,0,0)

theorem hfix134_22_2 : ∀ i, ((T134_22_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK134)
    ∈ fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK134) :=
  repsFix_of_siftB2 rK134 ⟨22, by decide⟩ T134_22_2 (by decide)

theorem hinj134_22_2 : Function.Injective
    (fun i => ((T134_22_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK134)) :=
  repsInj_of_reduceAux2 rK134 T134_22_2 (by decide)

theorem hcardT134_22_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK134)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK134 ⟨22, by decide⟩ R134_2 hpxR134_2 hcardq134_2 (by decide)).symm

/-- **Cell (134, 22) twin (q=2).** -/
theorem cell134_22_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK134) e = true)
    (h : ↥(reps (⟨22, by decide⟩ : Fin 148))) :
    species (reps (⟨22, by decide⟩ : Fin 148)) h (basisElt (reps rK134) (charOfVec2 rK134 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK134 e (h : Coordinate 2) T134_22_2 i :=
  species_entry_eq_sum rK134 ⟨22, by decide⟩ e heK h T134_22_2 hfix134_22_2 hinj134_22_2 hcardT134_22_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨22, by decide⟩) (reps rK134) (T134_22_2 i) (hfix134_22_2 i) h)

/-! ### Cell (134, 28) twin -/

def T134_28_2 : Fin 5 → Coordinate 2 := fun i => T134_28list.getD i.val (0,0,0,0,0)

theorem hfix134_28_2 : ∀ i, ((T134_28_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK134)
    ∈ fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK134) :=
  repsFix_of_siftB2 rK134 ⟨28, by decide⟩ T134_28_2 (by decide)

theorem hinj134_28_2 : Function.Injective
    (fun i => ((T134_28_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK134)) :=
  repsInj_of_reduceAux2 rK134 T134_28_2 (by decide)

theorem hcardT134_28_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK134)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK134 ⟨28, by decide⟩ R134_2 hpxR134_2 hcardq134_2 (by decide)).symm

/-- **Cell (134, 28) twin (q=2).** -/
theorem cell134_28_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK134) e = true)
    (h : ↥(reps (⟨28, by decide⟩ : Fin 148))) :
    species (reps (⟨28, by decide⟩ : Fin 148)) h (basisElt (reps rK134) (charOfVec2 rK134 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK134 e (h : Coordinate 2) T134_28_2 i :=
  species_entry_eq_sum rK134 ⟨28, by decide⟩ e heK h T134_28_2 hfix134_28_2 hinj134_28_2 hcardT134_28_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨28, by decide⟩) (reps rK134) (T134_28_2 i) (hfix134_28_2 i) h)

/-! ### Cell (134, 37) twin -/

def T134_37_2 : Fin 5 → Coordinate 2 := fun i => T134_37list.getD i.val (0,0,0,0,0)

theorem hfix134_37_2 : ∀ i, ((T134_37_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK134)
    ∈ fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK134) :=
  repsFix_of_siftB2 rK134 ⟨37, by decide⟩ T134_37_2 (by decide)

theorem hinj134_37_2 : Function.Injective
    (fun i => ((T134_37_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK134)) :=
  repsInj_of_reduceAux2 rK134 T134_37_2 (by decide)

theorem hcardT134_37_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK134)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK134 ⟨37, by decide⟩ R134_2 hpxR134_2 hcardq134_2 (by decide)).symm

/-- **Cell (134, 37) twin (q=2).** -/
theorem cell134_37_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK134) e = true)
    (h : ↥(reps (⟨37, by decide⟩ : Fin 148))) :
    species (reps (⟨37, by decide⟩ : Fin 148)) h (basisElt (reps rK134) (charOfVec2 rK134 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK134 e (h : Coordinate 2) T134_37_2 i :=
  species_entry_eq_sum rK134 ⟨37, by decide⟩ e heK h T134_37_2 hfix134_37_2 hinj134_37_2 hcardT134_37_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨37, by decide⟩) (reps rK134) (T134_37_2 i) (hfix134_37_2 i) h)

/-! ### Cell (134, 40) twin -/

def T134_40_2 : Fin 5 → Coordinate 2 := fun i => T134_40list.getD i.val (0,0,0,0,0)

theorem hfix134_40_2 : ∀ i, ((T134_40_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK134)
    ∈ fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK134) :=
  repsFix_of_siftB2 rK134 ⟨40, by decide⟩ T134_40_2 (by decide)

theorem hinj134_40_2 : Function.Injective
    (fun i => ((T134_40_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK134)) :=
  repsInj_of_reduceAux2 rK134 T134_40_2 (by decide)

theorem hcardT134_40_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK134)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK134 ⟨40, by decide⟩ R134_2 hpxR134_2 hcardq134_2 (by decide)).symm

/-- **Cell (134, 40) twin (q=2).** -/
theorem cell134_40_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK134) e = true)
    (h : ↥(reps (⟨40, by decide⟩ : Fin 148))) :
    species (reps (⟨40, by decide⟩ : Fin 148)) h (basisElt (reps rK134) (charOfVec2 rK134 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK134 e (h : Coordinate 2) T134_40_2 i :=
  species_entry_eq_sum rK134 ⟨40, by decide⟩ e heK h T134_40_2 hfix134_40_2 hinj134_40_2 hcardT134_40_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨40, by decide⟩) (reps rK134) (T134_40_2 i) (hfix134_40_2 i) h)

/-! ### Cell (134, 44) twin -/

def T134_44_2 : Fin 5 → Coordinate 2 := fun i => T134_44list.getD i.val (0,0,0,0,0)

theorem hfix134_44_2 : ∀ i, ((T134_44_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK134)
    ∈ fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK134) :=
  repsFix_of_siftB2 rK134 ⟨44, by decide⟩ T134_44_2 (by decide)

theorem hinj134_44_2 : Function.Injective
    (fun i => ((T134_44_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK134)) :=
  repsInj_of_reduceAux2 rK134 T134_44_2 (by decide)

theorem hcardT134_44_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK134)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK134 ⟨44, by decide⟩ R134_2 hpxR134_2 hcardq134_2 (by decide)).symm

/-- **Cell (134, 44) twin (q=2).** -/
theorem cell134_44_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK134) e = true)
    (h : ↥(reps (⟨44, by decide⟩ : Fin 148))) :
    species (reps (⟨44, by decide⟩ : Fin 148)) h (basisElt (reps rK134) (charOfVec2 rK134 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK134 e (h : Coordinate 2) T134_44_2 i :=
  species_entry_eq_sum rK134 ⟨44, by decide⟩ e heK h T134_44_2 hfix134_44_2 hinj134_44_2 hcardT134_44_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨44, by decide⟩) (reps rK134) (T134_44_2 i) (hfix134_44_2 i) h)

/-! ### Cell (134, 51) twin -/

def T134_51_2 : Fin 5 → Coordinate 2 := fun i => T134_51list.getD i.val (0,0,0,0,0)

theorem hfix134_51_2 : ∀ i, ((T134_51_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK134)
    ∈ fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK134) :=
  repsFix_of_siftB2 rK134 ⟨51, by decide⟩ T134_51_2 (by decide)

theorem hinj134_51_2 : Function.Injective
    (fun i => ((T134_51_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK134)) :=
  repsInj_of_reduceAux2 rK134 T134_51_2 (by decide)

theorem hcardT134_51_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK134)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK134 ⟨51, by decide⟩ R134_2 hpxR134_2 hcardq134_2 (by decide)).symm

/-- **Cell (134, 51) twin (q=2).** -/
theorem cell134_51_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK134) e = true)
    (h : ↥(reps (⟨51, by decide⟩ : Fin 148))) :
    species (reps (⟨51, by decide⟩ : Fin 148)) h (basisElt (reps rK134) (charOfVec2 rK134 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK134 e (h : Coordinate 2) T134_51_2 i :=
  species_entry_eq_sum rK134 ⟨51, by decide⟩ e heK h T134_51_2 hfix134_51_2 hinj134_51_2 hcardT134_51_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨51, by decide⟩) (reps rK134) (T134_51_2 i) (hfix134_51_2 i) h)

/-! ### Cell (134, 53) twin -/

def T134_53_2 : Fin 5 → Coordinate 2 := fun i => T134_53list.getD i.val (0,0,0,0,0)

theorem hfix134_53_2 : ∀ i, ((T134_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK134)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK134) :=
  repsFix_of_siftB2 rK134 ⟨53, by decide⟩ T134_53_2 (by decide)

theorem hinj134_53_2 : Function.Injective
    (fun i => ((T134_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK134)) :=
  repsInj_of_reduceAux2 rK134 T134_53_2 (by decide)

theorem hcardT134_53_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK134)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK134 ⟨53, by decide⟩ R134_2 hpxR134_2 hcardq134_2 (by decide)).symm

/-- **Cell (134, 53) twin (q=2).** -/
theorem cell134_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK134) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK134) (charOfVec2 rK134 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK134 e (h : Coordinate 2) T134_53_2 i :=
  species_entry_eq_sum rK134 ⟨53, by decide⟩ e heK h T134_53_2 hfix134_53_2 hinj134_53_2 hcardT134_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK134) (T134_53_2 i) (hfix134_53_2 i) h)

/-! ### Cell (134, 83) twin -/

def T134_83_2 : Fin 5 → Coordinate 2 := fun i => T134_83list.getD i.val (0,0,0,0,0)

theorem hfix134_83_2 : ∀ i, ((T134_83_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK134)
    ∈ fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK134) :=
  repsFix_of_siftB2 rK134 ⟨83, by decide⟩ T134_83_2 (by decide)

theorem hinj134_83_2 : Function.Injective
    (fun i => ((T134_83_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK134)) :=
  repsInj_of_reduceAux2 rK134 T134_83_2 (by decide)

theorem hcardT134_83_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK134)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK134 ⟨83, by decide⟩ R134_2 hpxR134_2 hcardq134_2 (by decide)).symm

/-- **Cell (134, 83) twin (q=2).** -/
theorem cell134_83_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK134) e = true)
    (h : ↥(reps (⟨83, by decide⟩ : Fin 148))) :
    species (reps (⟨83, by decide⟩ : Fin 148)) h (basisElt (reps rK134) (charOfVec2 rK134 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK134 e (h : Coordinate 2) T134_83_2 i :=
  species_entry_eq_sum rK134 ⟨83, by decide⟩ e heK h T134_83_2 hfix134_83_2 hinj134_83_2 hcardT134_83_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨83, by decide⟩) (reps rK134) (T134_83_2 i) (hfix134_83_2 i) h)

/-! ### Cell (134, 90) twin -/

def T134_90_2 : Fin 5 → Coordinate 2 := fun i => T134_90list.getD i.val (0,0,0,0,0)

theorem hfix134_90_2 : ∀ i, ((T134_90_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK134)
    ∈ fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK134) :=
  repsFix_of_siftB2 rK134 ⟨90, by decide⟩ T134_90_2 (by decide)

theorem hinj134_90_2 : Function.Injective
    (fun i => ((T134_90_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK134)) :=
  repsInj_of_reduceAux2 rK134 T134_90_2 (by decide)

theorem hcardT134_90_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK134)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK134 ⟨90, by decide⟩ R134_2 hpxR134_2 hcardq134_2 (by decide)).symm

/-- **Cell (134, 90) twin (q=2).** -/
theorem cell134_90_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK134) e = true)
    (h : ↥(reps (⟨90, by decide⟩ : Fin 148))) :
    species (reps (⟨90, by decide⟩ : Fin 148)) h (basisElt (reps rK134) (charOfVec2 rK134 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK134 e (h : Coordinate 2) T134_90_2 i :=
  species_entry_eq_sum rK134 ⟨90, by decide⟩ e heK h T134_90_2 hfix134_90_2 hinj134_90_2 hcardT134_90_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨90, by decide⟩) (reps rK134) (T134_90_2 i) (hfix134_90_2 i) h)

/-! ### Cell (134, 99) twin -/

def T134_99_2 : Fin 5 → Coordinate 2 := fun i => T134_99list.getD i.val (0,0,0,0,0)

theorem hfix134_99_2 : ∀ i, ((T134_99_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK134)
    ∈ fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK134) :=
  repsFix_of_siftB2 rK134 ⟨99, by decide⟩ T134_99_2 (by decide)

theorem hinj134_99_2 : Function.Injective
    (fun i => ((T134_99_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK134)) :=
  repsInj_of_reduceAux2 rK134 T134_99_2 (by decide)

theorem hcardT134_99_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK134)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK134 ⟨99, by decide⟩ R134_2 hpxR134_2 hcardq134_2 (by decide)).symm

/-- **Cell (134, 99) twin (q=2).** -/
theorem cell134_99_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK134) e = true)
    (h : ↥(reps (⟨99, by decide⟩ : Fin 148))) :
    species (reps (⟨99, by decide⟩ : Fin 148)) h (basisElt (reps rK134) (charOfVec2 rK134 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK134 e (h : Coordinate 2) T134_99_2 i :=
  species_entry_eq_sum rK134 ⟨99, by decide⟩ e heK h T134_99_2 hfix134_99_2 hinj134_99_2 hcardT134_99_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨99, by decide⟩) (reps rK134) (T134_99_2 i) (hfix134_99_2 i) h)

/-! ### Cell (134, 102) twin -/

def T134_102_2 : Fin 5 → Coordinate 2 := fun i => T134_102list.getD i.val (0,0,0,0,0)

theorem hfix134_102_2 : ∀ i, ((T134_102_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK134)
    ∈ fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK134) :=
  repsFix_of_siftB2 rK134 ⟨102, by decide⟩ T134_102_2 (by decide)

theorem hinj134_102_2 : Function.Injective
    (fun i => ((T134_102_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK134)) :=
  repsInj_of_reduceAux2 rK134 T134_102_2 (by decide)

theorem hcardT134_102_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK134)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK134 ⟨102, by decide⟩ R134_2 hpxR134_2 hcardq134_2 (by decide)).symm

/-- **Cell (134, 102) twin (q=2).** -/
theorem cell134_102_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK134) e = true)
    (h : ↥(reps (⟨102, by decide⟩ : Fin 148))) :
    species (reps (⟨102, by decide⟩ : Fin 148)) h (basisElt (reps rK134) (charOfVec2 rK134 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK134 e (h : Coordinate 2) T134_102_2 i :=
  species_entry_eq_sum rK134 ⟨102, by decide⟩ e heK h T134_102_2 hfix134_102_2 hinj134_102_2 hcardT134_102_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨102, by decide⟩) (reps rK134) (T134_102_2 i) (hfix134_102_2 i) h)

/-! ### Cell (134, 106) twin -/

def T134_106_2 : Fin 5 → Coordinate 2 := fun i => T134_106list.getD i.val (0,0,0,0,0)

theorem hfix134_106_2 : ∀ i, ((T134_106_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK134)
    ∈ fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK134) :=
  repsFix_of_siftB2 rK134 ⟨106, by decide⟩ T134_106_2 (by decide)

theorem hinj134_106_2 : Function.Injective
    (fun i => ((T134_106_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK134)) :=
  repsInj_of_reduceAux2 rK134 T134_106_2 (by decide)

theorem hcardT134_106_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK134)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK134 ⟨106, by decide⟩ R134_2 hpxR134_2 hcardq134_2 (by decide)).symm

/-- **Cell (134, 106) twin (q=2).** -/
theorem cell134_106_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK134) e = true)
    (h : ↥(reps (⟨106, by decide⟩ : Fin 148))) :
    species (reps (⟨106, by decide⟩ : Fin 148)) h (basisElt (reps rK134) (charOfVec2 rK134 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK134 e (h : Coordinate 2) T134_106_2 i :=
  species_entry_eq_sum rK134 ⟨106, by decide⟩ e heK h T134_106_2 hfix134_106_2 hinj134_106_2 hcardT134_106_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨106, by decide⟩) (reps rK134) (T134_106_2 i) (hfix134_106_2 i) h)

/-! ### Cell (134, 113) twin -/

def T134_113_2 : Fin 5 → Coordinate 2 := fun i => T134_113list.getD i.val (0,0,0,0,0)

theorem hfix134_113_2 : ∀ i, ((T134_113_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK134)
    ∈ fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK134) :=
  repsFix_of_siftB2 rK134 ⟨113, by decide⟩ T134_113_2 (by decide)

theorem hinj134_113_2 : Function.Injective
    (fun i => ((T134_113_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK134)) :=
  repsInj_of_reduceAux2 rK134 T134_113_2 (by decide)

theorem hcardT134_113_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK134)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK134 ⟨113, by decide⟩ R134_2 hpxR134_2 hcardq134_2 (by decide)).symm

/-- **Cell (134, 113) twin (q=2).** -/
theorem cell134_113_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK134) e = true)
    (h : ↥(reps (⟨113, by decide⟩ : Fin 148))) :
    species (reps (⟨113, by decide⟩ : Fin 148)) h (basisElt (reps rK134) (charOfVec2 rK134 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK134 e (h : Coordinate 2) T134_113_2 i :=
  species_entry_eq_sum rK134 ⟨113, by decide⟩ e heK h T134_113_2 hfix134_113_2 hinj134_113_2 hcardT134_113_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨113, by decide⟩) (reps rK134) (T134_113_2 i) (hfix134_113_2 i) h)

/-! ### Cell (134, 134) twin -/

def T134_134_2 : Fin 5 → Coordinate 2 := fun i => T134_134list.getD i.val (0,0,0,0,0)

theorem hfix134_134_2 : ∀ i, ((T134_134_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK134)
    ∈ fixedPoints (reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK134) :=
  repsFix_of_siftB2 rK134 ⟨134, by decide⟩ T134_134_2 (by decide)

theorem hinj134_134_2 : Function.Injective
    (fun i => ((T134_134_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK134)) :=
  repsInj_of_reduceAux2 rK134 T134_134_2 (by decide)

theorem hcardT134_134_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK134)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK134 ⟨134, by decide⟩ R134_2 hpxR134_2 hcardq134_2 (by decide)).symm

/-- **Cell (134, 134) twin (q=2).** -/
theorem cell134_134_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK134) e = true)
    (h : ↥(reps (⟨134, by decide⟩ : Fin 148))) :
    species (reps (⟨134, by decide⟩ : Fin 148)) h (basisElt (reps rK134) (charOfVec2 rK134 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK134 e (h : Coordinate 2) T134_134_2 i :=
  species_entry_eq_sum rK134 ⟨134, by decide⟩ e heK h T134_134_2 hfix134_134_2 hinj134_134_2 hcardT134_134_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨134, by decide⟩) (reps rK134) (T134_134_2 i) (hfix134_134_2 i) h)

end Q2

/-! # K-class rK = 135  (|G/K| = 5) -/

def rK135 : Fin 148 := ⟨135, by decide⟩

def R135list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def R135 : Fin 5 → Coordinate 1 := fun i => R135list.getD i.val (0,0,0,0,0)

theorem hpxR135 : Function.Injective (fun i => reduceAux 1 (basisAt rK135) (R135 i)) := by decide
theorem hcardq135 : Nat.card (Coordinate 1 ⧸ reps rK135) = 5 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (135, 0): |T| = 5 -/

def T135_0list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T135_0 : Fin 5 → Coordinate 1 := fun i => T135_0list.getD i.val (0,0,0,0,0)

theorem hfix135_0 : ∀ i, ((T135_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK135)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135) :=
  repsFix_of_siftB rK135 ⟨0, by decide⟩ T135_0 (by decide)

theorem hinj135_0 : Function.Injective
    (fun i => ((T135_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK135)) :=
  repsInj_of_reduceAux rK135 T135_0 (by decide)

theorem hcardT135_0 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK135 ⟨0, by decide⟩ R135 hpxR135 hcardq135 (by decide)).symm

/-- **Cell (135, 0).** -/
theorem cell135_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK135) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK135) (charOfVec rK135 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK135 e (h : Coordinate 1) T135_0 i :=
  species_entry_eq_sum rK135 ⟨0, by decide⟩ e heK h T135_0 hfix135_0 hinj135_0 hcardT135_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK135) (T135_0 i) (hfix135_0 i) h)

/-! ## Cell (135, 4): |T| = 5 -/

def T135_4list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T135_4 : Fin 5 → Coordinate 1 := fun i => T135_4list.getD i.val (0,0,0,0,0)

theorem hfix135_4 : ∀ i, ((T135_4 i : Coordinate 1) : Coordinate 1 ⧸ reps rK135)
    ∈ fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135) :=
  repsFix_of_siftB rK135 ⟨4, by decide⟩ T135_4 (by decide)

theorem hinj135_4 : Function.Injective
    (fun i => ((T135_4 i : Coordinate 1) : Coordinate 1 ⧸ reps rK135)) :=
  repsInj_of_reduceAux rK135 T135_4 (by decide)

theorem hcardT135_4 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK135 ⟨4, by decide⟩ R135 hpxR135 hcardq135 (by decide)).symm

/-- **Cell (135, 4).** -/
theorem cell135_4 (e : List (ZMod 25)) (heK : charOK (basisAt rK135) e = true)
    (h : ↥(reps (⟨4, by decide⟩ : Fin 148))) :
    species (reps (⟨4, by decide⟩ : Fin 148)) h (basisElt (reps rK135) (charOfVec rK135 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK135 e (h : Coordinate 1) T135_4 i :=
  species_entry_eq_sum rK135 ⟨4, by decide⟩ e heK h T135_4 hfix135_4 hinj135_4 hcardT135_4
    (fun i => conj_mem_of_fixedPoints (reps ⟨4, by decide⟩) (reps rK135) (T135_4 i) (hfix135_4 i) h)

/-! ## Cell (135, 10): |T| = 5 -/

def T135_10list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T135_10 : Fin 5 → Coordinate 1 := fun i => T135_10list.getD i.val (0,0,0,0,0)

theorem hfix135_10 : ∀ i, ((T135_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK135)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135) :=
  repsFix_of_siftB rK135 ⟨10, by decide⟩ T135_10 (by decide)

theorem hinj135_10 : Function.Injective
    (fun i => ((T135_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK135)) :=
  repsInj_of_reduceAux rK135 T135_10 (by decide)

theorem hcardT135_10 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK135 ⟨10, by decide⟩ R135 hpxR135 hcardq135 (by decide)).symm

/-- **Cell (135, 10).** -/
theorem cell135_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK135) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK135) (charOfVec rK135 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK135 e (h : Coordinate 1) T135_10 i :=
  species_entry_eq_sum rK135 ⟨10, by decide⟩ e heK h T135_10 hfix135_10 hinj135_10 hcardT135_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK135) (T135_10 i) (hfix135_10 i) h)

/-! ## Cell (135, 12): |T| = 5 -/

def T135_12list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T135_12 : Fin 5 → Coordinate 1 := fun i => T135_12list.getD i.val (0,0,0,0,0)

theorem hfix135_12 : ∀ i, ((T135_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK135)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135) :=
  repsFix_of_siftB rK135 ⟨12, by decide⟩ T135_12 (by decide)

theorem hinj135_12 : Function.Injective
    (fun i => ((T135_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK135)) :=
  repsInj_of_reduceAux rK135 T135_12 (by decide)

theorem hcardT135_12 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK135 ⟨12, by decide⟩ R135 hpxR135 hcardq135 (by decide)).symm

/-- **Cell (135, 12).** -/
theorem cell135_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK135) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK135) (charOfVec rK135 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK135 e (h : Coordinate 1) T135_12 i :=
  species_entry_eq_sum rK135 ⟨12, by decide⟩ e heK h T135_12 hfix135_12 hinj135_12 hcardT135_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK135) (T135_12 i) (hfix135_12 i) h)

/-! ## Cell (135, 22): |T| = 5 -/

def T135_22list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T135_22 : Fin 5 → Coordinate 1 := fun i => T135_22list.getD i.val (0,0,0,0,0)

theorem hfix135_22 : ∀ i, ((T135_22 i : Coordinate 1) : Coordinate 1 ⧸ reps rK135)
    ∈ fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135) :=
  repsFix_of_siftB rK135 ⟨22, by decide⟩ T135_22 (by decide)

theorem hinj135_22 : Function.Injective
    (fun i => ((T135_22 i : Coordinate 1) : Coordinate 1 ⧸ reps rK135)) :=
  repsInj_of_reduceAux rK135 T135_22 (by decide)

theorem hcardT135_22 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK135 ⟨22, by decide⟩ R135 hpxR135 hcardq135 (by decide)).symm

/-- **Cell (135, 22).** -/
theorem cell135_22 (e : List (ZMod 25)) (heK : charOK (basisAt rK135) e = true)
    (h : ↥(reps (⟨22, by decide⟩ : Fin 148))) :
    species (reps (⟨22, by decide⟩ : Fin 148)) h (basisElt (reps rK135) (charOfVec rK135 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK135 e (h : Coordinate 1) T135_22 i :=
  species_entry_eq_sum rK135 ⟨22, by decide⟩ e heK h T135_22 hfix135_22 hinj135_22 hcardT135_22
    (fun i => conj_mem_of_fixedPoints (reps ⟨22, by decide⟩) (reps rK135) (T135_22 i) (hfix135_22 i) h)

/-! ## Cell (135, 29): |T| = 5 -/

def T135_29list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T135_29 : Fin 5 → Coordinate 1 := fun i => T135_29list.getD i.val (0,0,0,0,0)

theorem hfix135_29 : ∀ i, ((T135_29 i : Coordinate 1) : Coordinate 1 ⧸ reps rK135)
    ∈ fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135) :=
  repsFix_of_siftB rK135 ⟨29, by decide⟩ T135_29 (by decide)

theorem hinj135_29 : Function.Injective
    (fun i => ((T135_29 i : Coordinate 1) : Coordinate 1 ⧸ reps rK135)) :=
  repsInj_of_reduceAux rK135 T135_29 (by decide)

theorem hcardT135_29 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK135 ⟨29, by decide⟩ R135 hpxR135 hcardq135 (by decide)).symm

/-- **Cell (135, 29).** -/
theorem cell135_29 (e : List (ZMod 25)) (heK : charOK (basisAt rK135) e = true)
    (h : ↥(reps (⟨29, by decide⟩ : Fin 148))) :
    species (reps (⟨29, by decide⟩ : Fin 148)) h (basisElt (reps rK135) (charOfVec rK135 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK135 e (h : Coordinate 1) T135_29 i :=
  species_entry_eq_sum rK135 ⟨29, by decide⟩ e heK h T135_29 hfix135_29 hinj135_29 hcardT135_29
    (fun i => conj_mem_of_fixedPoints (reps ⟨29, by decide⟩) (reps rK135) (T135_29 i) (hfix135_29 i) h)

/-! ## Cell (135, 33): |T| = 5 -/

def T135_33list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T135_33 : Fin 5 → Coordinate 1 := fun i => T135_33list.getD i.val (0,0,0,0,0)

theorem hfix135_33 : ∀ i, ((T135_33 i : Coordinate 1) : Coordinate 1 ⧸ reps rK135)
    ∈ fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135) :=
  repsFix_of_siftB rK135 ⟨33, by decide⟩ T135_33 (by decide)

theorem hinj135_33 : Function.Injective
    (fun i => ((T135_33 i : Coordinate 1) : Coordinate 1 ⧸ reps rK135)) :=
  repsInj_of_reduceAux rK135 T135_33 (by decide)

theorem hcardT135_33 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK135 ⟨33, by decide⟩ R135 hpxR135 hcardq135 (by decide)).symm

/-- **Cell (135, 33).** -/
theorem cell135_33 (e : List (ZMod 25)) (heK : charOK (basisAt rK135) e = true)
    (h : ↥(reps (⟨33, by decide⟩ : Fin 148))) :
    species (reps (⟨33, by decide⟩ : Fin 148)) h (basisElt (reps rK135) (charOfVec rK135 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK135 e (h : Coordinate 1) T135_33 i :=
  species_entry_eq_sum rK135 ⟨33, by decide⟩ e heK h T135_33 hfix135_33 hinj135_33 hcardT135_33
    (fun i => conj_mem_of_fixedPoints (reps ⟨33, by decide⟩) (reps rK135) (T135_33 i) (hfix135_33 i) h)

/-! ## Cell (135, 41): |T| = 5 -/

def T135_41list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T135_41 : Fin 5 → Coordinate 1 := fun i => T135_41list.getD i.val (0,0,0,0,0)

theorem hfix135_41 : ∀ i, ((T135_41 i : Coordinate 1) : Coordinate 1 ⧸ reps rK135)
    ∈ fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135) :=
  repsFix_of_siftB rK135 ⟨41, by decide⟩ T135_41 (by decide)

theorem hinj135_41 : Function.Injective
    (fun i => ((T135_41 i : Coordinate 1) : Coordinate 1 ⧸ reps rK135)) :=
  repsInj_of_reduceAux rK135 T135_41 (by decide)

theorem hcardT135_41 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK135 ⟨41, by decide⟩ R135 hpxR135 hcardq135 (by decide)).symm

/-- **Cell (135, 41).** -/
theorem cell135_41 (e : List (ZMod 25)) (heK : charOK (basisAt rK135) e = true)
    (h : ↥(reps (⟨41, by decide⟩ : Fin 148))) :
    species (reps (⟨41, by decide⟩ : Fin 148)) h (basisElt (reps rK135) (charOfVec rK135 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK135 e (h : Coordinate 1) T135_41 i :=
  species_entry_eq_sum rK135 ⟨41, by decide⟩ e heK h T135_41 hfix135_41 hinj135_41 hcardT135_41
    (fun i => conj_mem_of_fixedPoints (reps ⟨41, by decide⟩) (reps rK135) (T135_41 i) (hfix135_41 i) h)

/-! ## Cell (135, 45): |T| = 5 -/

def T135_45list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T135_45 : Fin 5 → Coordinate 1 := fun i => T135_45list.getD i.val (0,0,0,0,0)

theorem hfix135_45 : ∀ i, ((T135_45 i : Coordinate 1) : Coordinate 1 ⧸ reps rK135)
    ∈ fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135) :=
  repsFix_of_siftB rK135 ⟨45, by decide⟩ T135_45 (by decide)

theorem hinj135_45 : Function.Injective
    (fun i => ((T135_45 i : Coordinate 1) : Coordinate 1 ⧸ reps rK135)) :=
  repsInj_of_reduceAux rK135 T135_45 (by decide)

theorem hcardT135_45 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK135 ⟨45, by decide⟩ R135 hpxR135 hcardq135 (by decide)).symm

/-- **Cell (135, 45).** -/
theorem cell135_45 (e : List (ZMod 25)) (heK : charOK (basisAt rK135) e = true)
    (h : ↥(reps (⟨45, by decide⟩ : Fin 148))) :
    species (reps (⟨45, by decide⟩ : Fin 148)) h (basisElt (reps rK135) (charOfVec rK135 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK135 e (h : Coordinate 1) T135_45 i :=
  species_entry_eq_sum rK135 ⟨45, by decide⟩ e heK h T135_45 hfix135_45 hinj135_45 hcardT135_45
    (fun i => conj_mem_of_fixedPoints (reps ⟨45, by decide⟩) (reps rK135) (T135_45 i) (hfix135_45 i) h)

/-! ## Cell (135, 52): |T| = 5 -/

def T135_52list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T135_52 : Fin 5 → Coordinate 1 := fun i => T135_52list.getD i.val (0,0,0,0,0)

theorem hfix135_52 : ∀ i, ((T135_52 i : Coordinate 1) : Coordinate 1 ⧸ reps rK135)
    ∈ fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135) :=
  repsFix_of_siftB rK135 ⟨52, by decide⟩ T135_52 (by decide)

theorem hinj135_52 : Function.Injective
    (fun i => ((T135_52 i : Coordinate 1) : Coordinate 1 ⧸ reps rK135)) :=
  repsInj_of_reduceAux rK135 T135_52 (by decide)

theorem hcardT135_52 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK135 ⟨52, by decide⟩ R135 hpxR135 hcardq135 (by decide)).symm

/-- **Cell (135, 52).** -/
theorem cell135_52 (e : List (ZMod 25)) (heK : charOK (basisAt rK135) e = true)
    (h : ↥(reps (⟨52, by decide⟩ : Fin 148))) :
    species (reps (⟨52, by decide⟩ : Fin 148)) h (basisElt (reps rK135) (charOfVec rK135 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK135 e (h : Coordinate 1) T135_52 i :=
  species_entry_eq_sum rK135 ⟨52, by decide⟩ e heK h T135_52 hfix135_52 hinj135_52 hcardT135_52
    (fun i => conj_mem_of_fixedPoints (reps ⟨52, by decide⟩) (reps rK135) (T135_52 i) (hfix135_52 i) h)

/-! ## Cell (135, 53): |T| = 5 -/

def T135_53list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T135_53 : Fin 5 → Coordinate 1 := fun i => T135_53list.getD i.val (0,0,0,0,0)

theorem hfix135_53 : ∀ i, ((T135_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK135)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135) :=
  repsFix_of_siftB rK135 ⟨53, by decide⟩ T135_53 (by decide)

theorem hinj135_53 : Function.Injective
    (fun i => ((T135_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK135)) :=
  repsInj_of_reduceAux rK135 T135_53 (by decide)

theorem hcardT135_53 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK135 ⟨53, by decide⟩ R135 hpxR135 hcardq135 (by decide)).symm

/-- **Cell (135, 53).** -/
theorem cell135_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK135) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK135) (charOfVec rK135 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK135 e (h : Coordinate 1) T135_53 i :=
  species_entry_eq_sum rK135 ⟨53, by decide⟩ e heK h T135_53 hfix135_53 hinj135_53 hcardT135_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK135) (T135_53 i) (hfix135_53 i) h)

/-! ## Cell (135, 83): |T| = 5 -/

def T135_83list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T135_83 : Fin 5 → Coordinate 1 := fun i => T135_83list.getD i.val (0,0,0,0,0)

theorem hfix135_83 : ∀ i, ((T135_83 i : Coordinate 1) : Coordinate 1 ⧸ reps rK135)
    ∈ fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135) :=
  repsFix_of_siftB rK135 ⟨83, by decide⟩ T135_83 (by decide)

theorem hinj135_83 : Function.Injective
    (fun i => ((T135_83 i : Coordinate 1) : Coordinate 1 ⧸ reps rK135)) :=
  repsInj_of_reduceAux rK135 T135_83 (by decide)

theorem hcardT135_83 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK135 ⟨83, by decide⟩ R135 hpxR135 hcardq135 (by decide)).symm

/-- **Cell (135, 83).** -/
theorem cell135_83 (e : List (ZMod 25)) (heK : charOK (basisAt rK135) e = true)
    (h : ↥(reps (⟨83, by decide⟩ : Fin 148))) :
    species (reps (⟨83, by decide⟩ : Fin 148)) h (basisElt (reps rK135) (charOfVec rK135 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK135 e (h : Coordinate 1) T135_83 i :=
  species_entry_eq_sum rK135 ⟨83, by decide⟩ e heK h T135_83 hfix135_83 hinj135_83 hcardT135_83
    (fun i => conj_mem_of_fixedPoints (reps ⟨83, by decide⟩) (reps rK135) (T135_83 i) (hfix135_83 i) h)

/-! ## Cell (135, 91): |T| = 5 -/

def T135_91list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T135_91 : Fin 5 → Coordinate 1 := fun i => T135_91list.getD i.val (0,0,0,0,0)

theorem hfix135_91 : ∀ i, ((T135_91 i : Coordinate 1) : Coordinate 1 ⧸ reps rK135)
    ∈ fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135) :=
  repsFix_of_siftB rK135 ⟨91, by decide⟩ T135_91 (by decide)

theorem hinj135_91 : Function.Injective
    (fun i => ((T135_91 i : Coordinate 1) : Coordinate 1 ⧸ reps rK135)) :=
  repsInj_of_reduceAux rK135 T135_91 (by decide)

theorem hcardT135_91 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK135 ⟨91, by decide⟩ R135 hpxR135 hcardq135 (by decide)).symm

/-- **Cell (135, 91).** -/
theorem cell135_91 (e : List (ZMod 25)) (heK : charOK (basisAt rK135) e = true)
    (h : ↥(reps (⟨91, by decide⟩ : Fin 148))) :
    species (reps (⟨91, by decide⟩ : Fin 148)) h (basisElt (reps rK135) (charOfVec rK135 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK135 e (h : Coordinate 1) T135_91 i :=
  species_entry_eq_sum rK135 ⟨91, by decide⟩ e heK h T135_91 hfix135_91 hinj135_91 hcardT135_91
    (fun i => conj_mem_of_fixedPoints (reps ⟨91, by decide⟩) (reps rK135) (T135_91 i) (hfix135_91 i) h)

/-! ## Cell (135, 95): |T| = 5 -/

def T135_95list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T135_95 : Fin 5 → Coordinate 1 := fun i => T135_95list.getD i.val (0,0,0,0,0)

theorem hfix135_95 : ∀ i, ((T135_95 i : Coordinate 1) : Coordinate 1 ⧸ reps rK135)
    ∈ fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135) :=
  repsFix_of_siftB rK135 ⟨95, by decide⟩ T135_95 (by decide)

theorem hinj135_95 : Function.Injective
    (fun i => ((T135_95 i : Coordinate 1) : Coordinate 1 ⧸ reps rK135)) :=
  repsInj_of_reduceAux rK135 T135_95 (by decide)

theorem hcardT135_95 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK135 ⟨95, by decide⟩ R135 hpxR135 hcardq135 (by decide)).symm

/-- **Cell (135, 95).** -/
theorem cell135_95 (e : List (ZMod 25)) (heK : charOK (basisAt rK135) e = true)
    (h : ↥(reps (⟨95, by decide⟩ : Fin 148))) :
    species (reps (⟨95, by decide⟩ : Fin 148)) h (basisElt (reps rK135) (charOfVec rK135 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK135 e (h : Coordinate 1) T135_95 i :=
  species_entry_eq_sum rK135 ⟨95, by decide⟩ e heK h T135_95 hfix135_95 hinj135_95 hcardT135_95
    (fun i => conj_mem_of_fixedPoints (reps ⟨95, by decide⟩) (reps rK135) (T135_95 i) (hfix135_95 i) h)

/-! ## Cell (135, 103): |T| = 5 -/

def T135_103list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T135_103 : Fin 5 → Coordinate 1 := fun i => T135_103list.getD i.val (0,0,0,0,0)

theorem hfix135_103 : ∀ i, ((T135_103 i : Coordinate 1) : Coordinate 1 ⧸ reps rK135)
    ∈ fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135) :=
  repsFix_of_siftB rK135 ⟨103, by decide⟩ T135_103 (by decide)

theorem hinj135_103 : Function.Injective
    (fun i => ((T135_103 i : Coordinate 1) : Coordinate 1 ⧸ reps rK135)) :=
  repsInj_of_reduceAux rK135 T135_103 (by decide)

theorem hcardT135_103 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK135 ⟨103, by decide⟩ R135 hpxR135 hcardq135 (by decide)).symm

/-- **Cell (135, 103).** -/
theorem cell135_103 (e : List (ZMod 25)) (heK : charOK (basisAt rK135) e = true)
    (h : ↥(reps (⟨103, by decide⟩ : Fin 148))) :
    species (reps (⟨103, by decide⟩ : Fin 148)) h (basisElt (reps rK135) (charOfVec rK135 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK135 e (h : Coordinate 1) T135_103 i :=
  species_entry_eq_sum rK135 ⟨103, by decide⟩ e heK h T135_103 hfix135_103 hinj135_103 hcardT135_103
    (fun i => conj_mem_of_fixedPoints (reps ⟨103, by decide⟩) (reps rK135) (T135_103 i) (hfix135_103 i) h)

/-! ## Cell (135, 107): |T| = 5 -/

def T135_107list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T135_107 : Fin 5 → Coordinate 1 := fun i => T135_107list.getD i.val (0,0,0,0,0)

theorem hfix135_107 : ∀ i, ((T135_107 i : Coordinate 1) : Coordinate 1 ⧸ reps rK135)
    ∈ fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135) :=
  repsFix_of_siftB rK135 ⟨107, by decide⟩ T135_107 (by decide)

theorem hinj135_107 : Function.Injective
    (fun i => ((T135_107 i : Coordinate 1) : Coordinate 1 ⧸ reps rK135)) :=
  repsInj_of_reduceAux rK135 T135_107 (by decide)

theorem hcardT135_107 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK135 ⟨107, by decide⟩ R135 hpxR135 hcardq135 (by decide)).symm

/-- **Cell (135, 107).** -/
theorem cell135_107 (e : List (ZMod 25)) (heK : charOK (basisAt rK135) e = true)
    (h : ↥(reps (⟨107, by decide⟩ : Fin 148))) :
    species (reps (⟨107, by decide⟩ : Fin 148)) h (basisElt (reps rK135) (charOfVec rK135 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK135 e (h : Coordinate 1) T135_107 i :=
  species_entry_eq_sum rK135 ⟨107, by decide⟩ e heK h T135_107 hfix135_107 hinj135_107 hcardT135_107
    (fun i => conj_mem_of_fixedPoints (reps ⟨107, by decide⟩) (reps rK135) (T135_107 i) (hfix135_107 i) h)

/-! ## Cell (135, 114): |T| = 5 -/

def T135_114list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T135_114 : Fin 5 → Coordinate 1 := fun i => T135_114list.getD i.val (0,0,0,0,0)

theorem hfix135_114 : ∀ i, ((T135_114 i : Coordinate 1) : Coordinate 1 ⧸ reps rK135)
    ∈ fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135) :=
  repsFix_of_siftB rK135 ⟨114, by decide⟩ T135_114 (by decide)

theorem hinj135_114 : Function.Injective
    (fun i => ((T135_114 i : Coordinate 1) : Coordinate 1 ⧸ reps rK135)) :=
  repsInj_of_reduceAux rK135 T135_114 (by decide)

theorem hcardT135_114 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK135 ⟨114, by decide⟩ R135 hpxR135 hcardq135 (by decide)).symm

/-- **Cell (135, 114).** -/
theorem cell135_114 (e : List (ZMod 25)) (heK : charOK (basisAt rK135) e = true)
    (h : ↥(reps (⟨114, by decide⟩ : Fin 148))) :
    species (reps (⟨114, by decide⟩ : Fin 148)) h (basisElt (reps rK135) (charOfVec rK135 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK135 e (h : Coordinate 1) T135_114 i :=
  species_entry_eq_sum rK135 ⟨114, by decide⟩ e heK h T135_114 hfix135_114 hinj135_114 hcardT135_114
    (fun i => conj_mem_of_fixedPoints (reps ⟨114, by decide⟩) (reps rK135) (T135_114 i) (hfix135_114 i) h)

/-! ## Cell (135, 135): |T| = 5 -/

def T135_135list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T135_135 : Fin 5 → Coordinate 1 := fun i => T135_135list.getD i.val (0,0,0,0,0)

theorem hfix135_135 : ∀ i, ((T135_135 i : Coordinate 1) : Coordinate 1 ⧸ reps rK135)
    ∈ fixedPoints (reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135) :=
  repsFix_of_siftB rK135 ⟨135, by decide⟩ T135_135 (by decide)

theorem hinj135_135 : Function.Injective
    (fun i => ((T135_135 i : Coordinate 1) : Coordinate 1 ⧸ reps rK135)) :=
  repsInj_of_reduceAux rK135 T135_135 (by decide)

theorem hcardT135_135 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK135 ⟨135, by decide⟩ R135 hpxR135 hcardq135 (by decide)).symm

/-- **Cell (135, 135).** -/
theorem cell135_135 (e : List (ZMod 25)) (heK : charOK (basisAt rK135) e = true)
    (h : ↥(reps (⟨135, by decide⟩ : Fin 148))) :
    species (reps (⟨135, by decide⟩ : Fin 148)) h (basisElt (reps rK135) (charOfVec rK135 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK135 e (h : Coordinate 1) T135_135 i :=
  species_entry_eq_sum rK135 ⟨135, by decide⟩ e heK h T135_135 hfix135_135 hinj135_135 hcardT135_135
    (fun i => conj_mem_of_fixedPoints (reps ⟨135, by decide⟩) (reps rK135) (T135_135 i) (hfix135_135 i) h)

namespace Q2

def R135_2 : Fin 5 → Coordinate 2 := fun i => R135list.getD i.val (0,0,0,0,0)
theorem hpxR135_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK135) (R135_2 i)) := by decide
theorem hcardq135_2 : Nat.card (Coordinate 2 ⧸ reps rK135) = 5 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (135, 0) twin -/

def T135_0_2 : Fin 5 → Coordinate 2 := fun i => T135_0list.getD i.val (0,0,0,0,0)

theorem hfix135_0_2 : ∀ i, ((T135_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK135)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK135) :=
  repsFix_of_siftB2 rK135 ⟨0, by decide⟩ T135_0_2 (by decide)

theorem hinj135_0_2 : Function.Injective
    (fun i => ((T135_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK135)) :=
  repsInj_of_reduceAux2 rK135 T135_0_2 (by decide)

theorem hcardT135_0_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK135)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK135 ⟨0, by decide⟩ R135_2 hpxR135_2 hcardq135_2 (by decide)).symm

/-- **Cell (135, 0) twin (q=2).** -/
theorem cell135_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK135) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK135) (charOfVec2 rK135 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK135 e (h : Coordinate 2) T135_0_2 i :=
  species_entry_eq_sum rK135 ⟨0, by decide⟩ e heK h T135_0_2 hfix135_0_2 hinj135_0_2 hcardT135_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK135) (T135_0_2 i) (hfix135_0_2 i) h)

/-! ### Cell (135, 4) twin -/

def T135_4_2 : Fin 5 → Coordinate 2 := fun i => T135_4list.getD i.val (0,0,0,0,0)

theorem hfix135_4_2 : ∀ i, ((T135_4_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK135)
    ∈ fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK135) :=
  repsFix_of_siftB2 rK135 ⟨4, by decide⟩ T135_4_2 (by decide)

theorem hinj135_4_2 : Function.Injective
    (fun i => ((T135_4_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK135)) :=
  repsInj_of_reduceAux2 rK135 T135_4_2 (by decide)

theorem hcardT135_4_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK135)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK135 ⟨4, by decide⟩ R135_2 hpxR135_2 hcardq135_2 (by decide)).symm

/-- **Cell (135, 4) twin (q=2).** -/
theorem cell135_4_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK135) e = true)
    (h : ↥(reps (⟨4, by decide⟩ : Fin 148))) :
    species (reps (⟨4, by decide⟩ : Fin 148)) h (basisElt (reps rK135) (charOfVec2 rK135 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK135 e (h : Coordinate 2) T135_4_2 i :=
  species_entry_eq_sum rK135 ⟨4, by decide⟩ e heK h T135_4_2 hfix135_4_2 hinj135_4_2 hcardT135_4_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨4, by decide⟩) (reps rK135) (T135_4_2 i) (hfix135_4_2 i) h)

/-! ### Cell (135, 10) twin -/

def T135_10_2 : Fin 5 → Coordinate 2 := fun i => T135_10list.getD i.val (0,0,0,0,0)

theorem hfix135_10_2 : ∀ i, ((T135_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK135)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK135) :=
  repsFix_of_siftB2 rK135 ⟨10, by decide⟩ T135_10_2 (by decide)

theorem hinj135_10_2 : Function.Injective
    (fun i => ((T135_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK135)) :=
  repsInj_of_reduceAux2 rK135 T135_10_2 (by decide)

theorem hcardT135_10_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK135)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK135 ⟨10, by decide⟩ R135_2 hpxR135_2 hcardq135_2 (by decide)).symm

/-- **Cell (135, 10) twin (q=2).** -/
theorem cell135_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK135) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK135) (charOfVec2 rK135 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK135 e (h : Coordinate 2) T135_10_2 i :=
  species_entry_eq_sum rK135 ⟨10, by decide⟩ e heK h T135_10_2 hfix135_10_2 hinj135_10_2 hcardT135_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK135) (T135_10_2 i) (hfix135_10_2 i) h)

/-! ### Cell (135, 12) twin -/

def T135_12_2 : Fin 5 → Coordinate 2 := fun i => T135_12list.getD i.val (0,0,0,0,0)

theorem hfix135_12_2 : ∀ i, ((T135_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK135)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK135) :=
  repsFix_of_siftB2 rK135 ⟨12, by decide⟩ T135_12_2 (by decide)

theorem hinj135_12_2 : Function.Injective
    (fun i => ((T135_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK135)) :=
  repsInj_of_reduceAux2 rK135 T135_12_2 (by decide)

theorem hcardT135_12_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK135)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK135 ⟨12, by decide⟩ R135_2 hpxR135_2 hcardq135_2 (by decide)).symm

/-- **Cell (135, 12) twin (q=2).** -/
theorem cell135_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK135) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK135) (charOfVec2 rK135 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK135 e (h : Coordinate 2) T135_12_2 i :=
  species_entry_eq_sum rK135 ⟨12, by decide⟩ e heK h T135_12_2 hfix135_12_2 hinj135_12_2 hcardT135_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK135) (T135_12_2 i) (hfix135_12_2 i) h)

/-! ### Cell (135, 22) twin -/

def T135_22_2 : Fin 5 → Coordinate 2 := fun i => T135_22list.getD i.val (0,0,0,0,0)

theorem hfix135_22_2 : ∀ i, ((T135_22_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK135)
    ∈ fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK135) :=
  repsFix_of_siftB2 rK135 ⟨22, by decide⟩ T135_22_2 (by decide)

theorem hinj135_22_2 : Function.Injective
    (fun i => ((T135_22_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK135)) :=
  repsInj_of_reduceAux2 rK135 T135_22_2 (by decide)

theorem hcardT135_22_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK135)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK135 ⟨22, by decide⟩ R135_2 hpxR135_2 hcardq135_2 (by decide)).symm

/-- **Cell (135, 22) twin (q=2).** -/
theorem cell135_22_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK135) e = true)
    (h : ↥(reps (⟨22, by decide⟩ : Fin 148))) :
    species (reps (⟨22, by decide⟩ : Fin 148)) h (basisElt (reps rK135) (charOfVec2 rK135 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK135 e (h : Coordinate 2) T135_22_2 i :=
  species_entry_eq_sum rK135 ⟨22, by decide⟩ e heK h T135_22_2 hfix135_22_2 hinj135_22_2 hcardT135_22_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨22, by decide⟩) (reps rK135) (T135_22_2 i) (hfix135_22_2 i) h)

/-! ### Cell (135, 29) twin -/

def T135_29_2 : Fin 5 → Coordinate 2 := fun i => T135_29list.getD i.val (0,0,0,0,0)

theorem hfix135_29_2 : ∀ i, ((T135_29_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK135)
    ∈ fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK135) :=
  repsFix_of_siftB2 rK135 ⟨29, by decide⟩ T135_29_2 (by decide)

theorem hinj135_29_2 : Function.Injective
    (fun i => ((T135_29_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK135)) :=
  repsInj_of_reduceAux2 rK135 T135_29_2 (by decide)

theorem hcardT135_29_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK135)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK135 ⟨29, by decide⟩ R135_2 hpxR135_2 hcardq135_2 (by decide)).symm

/-- **Cell (135, 29) twin (q=2).** -/
theorem cell135_29_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK135) e = true)
    (h : ↥(reps (⟨29, by decide⟩ : Fin 148))) :
    species (reps (⟨29, by decide⟩ : Fin 148)) h (basisElt (reps rK135) (charOfVec2 rK135 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK135 e (h : Coordinate 2) T135_29_2 i :=
  species_entry_eq_sum rK135 ⟨29, by decide⟩ e heK h T135_29_2 hfix135_29_2 hinj135_29_2 hcardT135_29_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨29, by decide⟩) (reps rK135) (T135_29_2 i) (hfix135_29_2 i) h)

/-! ### Cell (135, 33) twin -/

def T135_33_2 : Fin 5 → Coordinate 2 := fun i => T135_33list.getD i.val (0,0,0,0,0)

theorem hfix135_33_2 : ∀ i, ((T135_33_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK135)
    ∈ fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK135) :=
  repsFix_of_siftB2 rK135 ⟨33, by decide⟩ T135_33_2 (by decide)

theorem hinj135_33_2 : Function.Injective
    (fun i => ((T135_33_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK135)) :=
  repsInj_of_reduceAux2 rK135 T135_33_2 (by decide)

theorem hcardT135_33_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK135)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK135 ⟨33, by decide⟩ R135_2 hpxR135_2 hcardq135_2 (by decide)).symm

/-- **Cell (135, 33) twin (q=2).** -/
theorem cell135_33_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK135) e = true)
    (h : ↥(reps (⟨33, by decide⟩ : Fin 148))) :
    species (reps (⟨33, by decide⟩ : Fin 148)) h (basisElt (reps rK135) (charOfVec2 rK135 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK135 e (h : Coordinate 2) T135_33_2 i :=
  species_entry_eq_sum rK135 ⟨33, by decide⟩ e heK h T135_33_2 hfix135_33_2 hinj135_33_2 hcardT135_33_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨33, by decide⟩) (reps rK135) (T135_33_2 i) (hfix135_33_2 i) h)

/-! ### Cell (135, 41) twin -/

def T135_41_2 : Fin 5 → Coordinate 2 := fun i => T135_41list.getD i.val (0,0,0,0,0)

theorem hfix135_41_2 : ∀ i, ((T135_41_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK135)
    ∈ fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK135) :=
  repsFix_of_siftB2 rK135 ⟨41, by decide⟩ T135_41_2 (by decide)

theorem hinj135_41_2 : Function.Injective
    (fun i => ((T135_41_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK135)) :=
  repsInj_of_reduceAux2 rK135 T135_41_2 (by decide)

theorem hcardT135_41_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK135)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK135 ⟨41, by decide⟩ R135_2 hpxR135_2 hcardq135_2 (by decide)).symm

/-- **Cell (135, 41) twin (q=2).** -/
theorem cell135_41_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK135) e = true)
    (h : ↥(reps (⟨41, by decide⟩ : Fin 148))) :
    species (reps (⟨41, by decide⟩ : Fin 148)) h (basisElt (reps rK135) (charOfVec2 rK135 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK135 e (h : Coordinate 2) T135_41_2 i :=
  species_entry_eq_sum rK135 ⟨41, by decide⟩ e heK h T135_41_2 hfix135_41_2 hinj135_41_2 hcardT135_41_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨41, by decide⟩) (reps rK135) (T135_41_2 i) (hfix135_41_2 i) h)

/-! ### Cell (135, 45) twin -/

def T135_45_2 : Fin 5 → Coordinate 2 := fun i => T135_45list.getD i.val (0,0,0,0,0)

theorem hfix135_45_2 : ∀ i, ((T135_45_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK135)
    ∈ fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK135) :=
  repsFix_of_siftB2 rK135 ⟨45, by decide⟩ T135_45_2 (by decide)

theorem hinj135_45_2 : Function.Injective
    (fun i => ((T135_45_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK135)) :=
  repsInj_of_reduceAux2 rK135 T135_45_2 (by decide)

theorem hcardT135_45_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK135)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK135 ⟨45, by decide⟩ R135_2 hpxR135_2 hcardq135_2 (by decide)).symm

/-- **Cell (135, 45) twin (q=2).** -/
theorem cell135_45_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK135) e = true)
    (h : ↥(reps (⟨45, by decide⟩ : Fin 148))) :
    species (reps (⟨45, by decide⟩ : Fin 148)) h (basisElt (reps rK135) (charOfVec2 rK135 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK135 e (h : Coordinate 2) T135_45_2 i :=
  species_entry_eq_sum rK135 ⟨45, by decide⟩ e heK h T135_45_2 hfix135_45_2 hinj135_45_2 hcardT135_45_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨45, by decide⟩) (reps rK135) (T135_45_2 i) (hfix135_45_2 i) h)

/-! ### Cell (135, 52) twin -/

def T135_52_2 : Fin 5 → Coordinate 2 := fun i => T135_52list.getD i.val (0,0,0,0,0)

theorem hfix135_52_2 : ∀ i, ((T135_52_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK135)
    ∈ fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK135) :=
  repsFix_of_siftB2 rK135 ⟨52, by decide⟩ T135_52_2 (by decide)

theorem hinj135_52_2 : Function.Injective
    (fun i => ((T135_52_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK135)) :=
  repsInj_of_reduceAux2 rK135 T135_52_2 (by decide)

theorem hcardT135_52_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK135)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK135 ⟨52, by decide⟩ R135_2 hpxR135_2 hcardq135_2 (by decide)).symm

/-- **Cell (135, 52) twin (q=2).** -/
theorem cell135_52_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK135) e = true)
    (h : ↥(reps (⟨52, by decide⟩ : Fin 148))) :
    species (reps (⟨52, by decide⟩ : Fin 148)) h (basisElt (reps rK135) (charOfVec2 rK135 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK135 e (h : Coordinate 2) T135_52_2 i :=
  species_entry_eq_sum rK135 ⟨52, by decide⟩ e heK h T135_52_2 hfix135_52_2 hinj135_52_2 hcardT135_52_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨52, by decide⟩) (reps rK135) (T135_52_2 i) (hfix135_52_2 i) h)

/-! ### Cell (135, 53) twin -/

def T135_53_2 : Fin 5 → Coordinate 2 := fun i => T135_53list.getD i.val (0,0,0,0,0)

theorem hfix135_53_2 : ∀ i, ((T135_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK135)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK135) :=
  repsFix_of_siftB2 rK135 ⟨53, by decide⟩ T135_53_2 (by decide)

theorem hinj135_53_2 : Function.Injective
    (fun i => ((T135_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK135)) :=
  repsInj_of_reduceAux2 rK135 T135_53_2 (by decide)

theorem hcardT135_53_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK135)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK135 ⟨53, by decide⟩ R135_2 hpxR135_2 hcardq135_2 (by decide)).symm

/-- **Cell (135, 53) twin (q=2).** -/
theorem cell135_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK135) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK135) (charOfVec2 rK135 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK135 e (h : Coordinate 2) T135_53_2 i :=
  species_entry_eq_sum rK135 ⟨53, by decide⟩ e heK h T135_53_2 hfix135_53_2 hinj135_53_2 hcardT135_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK135) (T135_53_2 i) (hfix135_53_2 i) h)

/-! ### Cell (135, 83) twin -/

def T135_83_2 : Fin 5 → Coordinate 2 := fun i => T135_83list.getD i.val (0,0,0,0,0)

theorem hfix135_83_2 : ∀ i, ((T135_83_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK135)
    ∈ fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK135) :=
  repsFix_of_siftB2 rK135 ⟨83, by decide⟩ T135_83_2 (by decide)

theorem hinj135_83_2 : Function.Injective
    (fun i => ((T135_83_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK135)) :=
  repsInj_of_reduceAux2 rK135 T135_83_2 (by decide)

theorem hcardT135_83_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK135)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK135 ⟨83, by decide⟩ R135_2 hpxR135_2 hcardq135_2 (by decide)).symm

/-- **Cell (135, 83) twin (q=2).** -/
theorem cell135_83_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK135) e = true)
    (h : ↥(reps (⟨83, by decide⟩ : Fin 148))) :
    species (reps (⟨83, by decide⟩ : Fin 148)) h (basisElt (reps rK135) (charOfVec2 rK135 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK135 e (h : Coordinate 2) T135_83_2 i :=
  species_entry_eq_sum rK135 ⟨83, by decide⟩ e heK h T135_83_2 hfix135_83_2 hinj135_83_2 hcardT135_83_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨83, by decide⟩) (reps rK135) (T135_83_2 i) (hfix135_83_2 i) h)

/-! ### Cell (135, 91) twin -/

def T135_91_2 : Fin 5 → Coordinate 2 := fun i => T135_91list.getD i.val (0,0,0,0,0)

theorem hfix135_91_2 : ∀ i, ((T135_91_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK135)
    ∈ fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK135) :=
  repsFix_of_siftB2 rK135 ⟨91, by decide⟩ T135_91_2 (by decide)

theorem hinj135_91_2 : Function.Injective
    (fun i => ((T135_91_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK135)) :=
  repsInj_of_reduceAux2 rK135 T135_91_2 (by decide)

theorem hcardT135_91_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK135)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK135 ⟨91, by decide⟩ R135_2 hpxR135_2 hcardq135_2 (by decide)).symm

/-- **Cell (135, 91) twin (q=2).** -/
theorem cell135_91_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK135) e = true)
    (h : ↥(reps (⟨91, by decide⟩ : Fin 148))) :
    species (reps (⟨91, by decide⟩ : Fin 148)) h (basisElt (reps rK135) (charOfVec2 rK135 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK135 e (h : Coordinate 2) T135_91_2 i :=
  species_entry_eq_sum rK135 ⟨91, by decide⟩ e heK h T135_91_2 hfix135_91_2 hinj135_91_2 hcardT135_91_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨91, by decide⟩) (reps rK135) (T135_91_2 i) (hfix135_91_2 i) h)

/-! ### Cell (135, 95) twin -/

def T135_95_2 : Fin 5 → Coordinate 2 := fun i => T135_95list.getD i.val (0,0,0,0,0)

theorem hfix135_95_2 : ∀ i, ((T135_95_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK135)
    ∈ fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK135) :=
  repsFix_of_siftB2 rK135 ⟨95, by decide⟩ T135_95_2 (by decide)

theorem hinj135_95_2 : Function.Injective
    (fun i => ((T135_95_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK135)) :=
  repsInj_of_reduceAux2 rK135 T135_95_2 (by decide)

theorem hcardT135_95_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK135)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK135 ⟨95, by decide⟩ R135_2 hpxR135_2 hcardq135_2 (by decide)).symm

/-- **Cell (135, 95) twin (q=2).** -/
theorem cell135_95_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK135) e = true)
    (h : ↥(reps (⟨95, by decide⟩ : Fin 148))) :
    species (reps (⟨95, by decide⟩ : Fin 148)) h (basisElt (reps rK135) (charOfVec2 rK135 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK135 e (h : Coordinate 2) T135_95_2 i :=
  species_entry_eq_sum rK135 ⟨95, by decide⟩ e heK h T135_95_2 hfix135_95_2 hinj135_95_2 hcardT135_95_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨95, by decide⟩) (reps rK135) (T135_95_2 i) (hfix135_95_2 i) h)

/-! ### Cell (135, 103) twin -/

def T135_103_2 : Fin 5 → Coordinate 2 := fun i => T135_103list.getD i.val (0,0,0,0,0)

theorem hfix135_103_2 : ∀ i, ((T135_103_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK135)
    ∈ fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK135) :=
  repsFix_of_siftB2 rK135 ⟨103, by decide⟩ T135_103_2 (by decide)

theorem hinj135_103_2 : Function.Injective
    (fun i => ((T135_103_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK135)) :=
  repsInj_of_reduceAux2 rK135 T135_103_2 (by decide)

theorem hcardT135_103_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK135)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK135 ⟨103, by decide⟩ R135_2 hpxR135_2 hcardq135_2 (by decide)).symm

/-- **Cell (135, 103) twin (q=2).** -/
theorem cell135_103_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK135) e = true)
    (h : ↥(reps (⟨103, by decide⟩ : Fin 148))) :
    species (reps (⟨103, by decide⟩ : Fin 148)) h (basisElt (reps rK135) (charOfVec2 rK135 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK135 e (h : Coordinate 2) T135_103_2 i :=
  species_entry_eq_sum rK135 ⟨103, by decide⟩ e heK h T135_103_2 hfix135_103_2 hinj135_103_2 hcardT135_103_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨103, by decide⟩) (reps rK135) (T135_103_2 i) (hfix135_103_2 i) h)

/-! ### Cell (135, 107) twin -/

def T135_107_2 : Fin 5 → Coordinate 2 := fun i => T135_107list.getD i.val (0,0,0,0,0)

theorem hfix135_107_2 : ∀ i, ((T135_107_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK135)
    ∈ fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK135) :=
  repsFix_of_siftB2 rK135 ⟨107, by decide⟩ T135_107_2 (by decide)

theorem hinj135_107_2 : Function.Injective
    (fun i => ((T135_107_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK135)) :=
  repsInj_of_reduceAux2 rK135 T135_107_2 (by decide)

theorem hcardT135_107_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK135)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK135 ⟨107, by decide⟩ R135_2 hpxR135_2 hcardq135_2 (by decide)).symm

/-- **Cell (135, 107) twin (q=2).** -/
theorem cell135_107_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK135) e = true)
    (h : ↥(reps (⟨107, by decide⟩ : Fin 148))) :
    species (reps (⟨107, by decide⟩ : Fin 148)) h (basisElt (reps rK135) (charOfVec2 rK135 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK135 e (h : Coordinate 2) T135_107_2 i :=
  species_entry_eq_sum rK135 ⟨107, by decide⟩ e heK h T135_107_2 hfix135_107_2 hinj135_107_2 hcardT135_107_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨107, by decide⟩) (reps rK135) (T135_107_2 i) (hfix135_107_2 i) h)

/-! ### Cell (135, 114) twin -/

def T135_114_2 : Fin 5 → Coordinate 2 := fun i => T135_114list.getD i.val (0,0,0,0,0)

theorem hfix135_114_2 : ∀ i, ((T135_114_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK135)
    ∈ fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK135) :=
  repsFix_of_siftB2 rK135 ⟨114, by decide⟩ T135_114_2 (by decide)

theorem hinj135_114_2 : Function.Injective
    (fun i => ((T135_114_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK135)) :=
  repsInj_of_reduceAux2 rK135 T135_114_2 (by decide)

theorem hcardT135_114_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK135)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK135 ⟨114, by decide⟩ R135_2 hpxR135_2 hcardq135_2 (by decide)).symm

/-- **Cell (135, 114) twin (q=2).** -/
theorem cell135_114_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK135) e = true)
    (h : ↥(reps (⟨114, by decide⟩ : Fin 148))) :
    species (reps (⟨114, by decide⟩ : Fin 148)) h (basisElt (reps rK135) (charOfVec2 rK135 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK135 e (h : Coordinate 2) T135_114_2 i :=
  species_entry_eq_sum rK135 ⟨114, by decide⟩ e heK h T135_114_2 hfix135_114_2 hinj135_114_2 hcardT135_114_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨114, by decide⟩) (reps rK135) (T135_114_2 i) (hfix135_114_2 i) h)

/-! ### Cell (135, 135) twin -/

def T135_135_2 : Fin 5 → Coordinate 2 := fun i => T135_135list.getD i.val (0,0,0,0,0)

theorem hfix135_135_2 : ∀ i, ((T135_135_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK135)
    ∈ fixedPoints (reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK135) :=
  repsFix_of_siftB2 rK135 ⟨135, by decide⟩ T135_135_2 (by decide)

theorem hinj135_135_2 : Function.Injective
    (fun i => ((T135_135_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK135)) :=
  repsInj_of_reduceAux2 rK135 T135_135_2 (by decide)

theorem hcardT135_135_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK135)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK135 ⟨135, by decide⟩ R135_2 hpxR135_2 hcardq135_2 (by decide)).symm

/-- **Cell (135, 135) twin (q=2).** -/
theorem cell135_135_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK135) e = true)
    (h : ↥(reps (⟨135, by decide⟩ : Fin 148))) :
    species (reps (⟨135, by decide⟩ : Fin 148)) h (basisElt (reps rK135) (charOfVec2 rK135 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK135 e (h : Coordinate 2) T135_135_2 i :=
  species_entry_eq_sum rK135 ⟨135, by decide⟩ e heK h T135_135_2 hfix135_135_2 hinj135_135_2 hcardT135_135_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨135, by decide⟩) (reps rK135) (T135_135_2 i) (hfix135_135_2 i) h)

end Q2

end LeanDring.P5Presentation
