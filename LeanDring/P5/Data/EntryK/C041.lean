/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, K-strata data (5^4 stratum, rK 142-143): certified per-cell species-entry instantiations, both
twins.

Covers K-classes 142, 143 (order-5^4 K, |R|=5).  For each nonzero `H`-column
(`(G/K)^H ≠ ∅`), the full coset transversal `R142..` and each `H`-fixed
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

/-! # K-class rK = 142  (|G/K| = 5) -/

def rK142 : Fin 148 := ⟨142, by decide⟩

def R142list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def R142 : Fin 5 → Coordinate 1 := fun i => R142list.getD i.val (0,0,0,0,0)

theorem hpxR142 : Function.Injective (fun i => reduceAux 1 (basisAt rK142) (R142 i)) := by decide
theorem hcardq142 : Nat.card (Coordinate 1 ⧸ reps rK142) = 5 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (142, 0): |T| = 5 -/

def T142_0list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T142_0 : Fin 5 → Coordinate 1 := fun i => T142_0list.getD i.val (0,0,0,0,0)

theorem hfix142_0 : ∀ i, ((T142_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK142)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142) :=
  repsFix_of_siftB rK142 ⟨0, by decide⟩ T142_0 (by decide)

theorem hinj142_0 : Function.Injective
    (fun i => ((T142_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK142)) :=
  repsInj_of_reduceAux rK142 T142_0 (by decide)

theorem hcardT142_0 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK142 ⟨0, by decide⟩ R142 hpxR142 hcardq142 (by decide)).symm

/-- **Cell (142, 0).** -/
theorem cell142_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK142) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK142) (charOfVec rK142 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK142 e (h : Coordinate 1) T142_0 i :=
  species_entry_eq_sum rK142 ⟨0, by decide⟩ e heK h T142_0 hfix142_0 hinj142_0 hcardT142_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK142) (T142_0 i) (hfix142_0 i) h)

/-! ## Cell (142, 10): |T| = 5 -/

def T142_10list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T142_10 : Fin 5 → Coordinate 1 := fun i => T142_10list.getD i.val (0,0,0,0,0)

theorem hfix142_10 : ∀ i, ((T142_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK142)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142) :=
  repsFix_of_siftB rK142 ⟨10, by decide⟩ T142_10 (by decide)

theorem hinj142_10 : Function.Injective
    (fun i => ((T142_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK142)) :=
  repsInj_of_reduceAux rK142 T142_10 (by decide)

theorem hcardT142_10 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK142 ⟨10, by decide⟩ R142 hpxR142 hcardq142 (by decide)).symm

/-- **Cell (142, 10).** -/
theorem cell142_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK142) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK142) (charOfVec rK142 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK142 e (h : Coordinate 1) T142_10 i :=
  species_entry_eq_sum rK142 ⟨10, by decide⟩ e heK h T142_10 hfix142_10 hinj142_10 hcardT142_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK142) (T142_10 i) (hfix142_10 i) h)

/-! ## Cell (142, 11): |T| = 5 -/

def T142_11list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T142_11 : Fin 5 → Coordinate 1 := fun i => T142_11list.getD i.val (0,0,0,0,0)

theorem hfix142_11 : ∀ i, ((T142_11 i : Coordinate 1) : Coordinate 1 ⧸ reps rK142)
    ∈ fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142) :=
  repsFix_of_siftB rK142 ⟨11, by decide⟩ T142_11 (by decide)

theorem hinj142_11 : Function.Injective
    (fun i => ((T142_11 i : Coordinate 1) : Coordinate 1 ⧸ reps rK142)) :=
  repsInj_of_reduceAux rK142 T142_11 (by decide)

theorem hcardT142_11 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK142 ⟨11, by decide⟩ R142 hpxR142 hcardq142 (by decide)).symm

/-- **Cell (142, 11).** -/
theorem cell142_11 (e : List (ZMod 25)) (heK : charOK (basisAt rK142) e = true)
    (h : ↥(reps (⟨11, by decide⟩ : Fin 148))) :
    species (reps (⟨11, by decide⟩ : Fin 148)) h (basisElt (reps rK142) (charOfVec rK142 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK142 e (h : Coordinate 1) T142_11 i :=
  species_entry_eq_sum rK142 ⟨11, by decide⟩ e heK h T142_11 hfix142_11 hinj142_11 hcardT142_11
    (fun i => conj_mem_of_fixedPoints (reps ⟨11, by decide⟩) (reps rK142) (T142_11 i) (hfix142_11 i) h)

/-! ## Cell (142, 12): |T| = 5 -/

def T142_12list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T142_12 : Fin 5 → Coordinate 1 := fun i => T142_12list.getD i.val (0,0,0,0,0)

theorem hfix142_12 : ∀ i, ((T142_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK142)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142) :=
  repsFix_of_siftB rK142 ⟨12, by decide⟩ T142_12 (by decide)

theorem hinj142_12 : Function.Injective
    (fun i => ((T142_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK142)) :=
  repsInj_of_reduceAux rK142 T142_12 (by decide)

theorem hcardT142_12 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK142 ⟨12, by decide⟩ R142 hpxR142 hcardq142 (by decide)).symm

/-- **Cell (142, 12).** -/
theorem cell142_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK142) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK142) (charOfVec rK142 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK142 e (h : Coordinate 1) T142_12 i :=
  species_entry_eq_sum rK142 ⟨12, by decide⟩ e heK h T142_12 hfix142_12 hinj142_12 hcardT142_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK142) (T142_12 i) (hfix142_12 i) h)

/-! ## Cell (142, 28): |T| = 5 -/

def T142_28list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T142_28 : Fin 5 → Coordinate 1 := fun i => T142_28list.getD i.val (0,0,0,0,0)

theorem hfix142_28 : ∀ i, ((T142_28 i : Coordinate 1) : Coordinate 1 ⧸ reps rK142)
    ∈ fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142) :=
  repsFix_of_siftB rK142 ⟨28, by decide⟩ T142_28 (by decide)

theorem hinj142_28 : Function.Injective
    (fun i => ((T142_28 i : Coordinate 1) : Coordinate 1 ⧸ reps rK142)) :=
  repsInj_of_reduceAux rK142 T142_28 (by decide)

theorem hcardT142_28 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK142 ⟨28, by decide⟩ R142 hpxR142 hcardq142 (by decide)).symm

/-- **Cell (142, 28).** -/
theorem cell142_28 (e : List (ZMod 25)) (heK : charOK (basisAt rK142) e = true)
    (h : ↥(reps (⟨28, by decide⟩ : Fin 148))) :
    species (reps (⟨28, by decide⟩ : Fin 148)) h (basisElt (reps rK142) (charOfVec rK142 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK142 e (h : Coordinate 1) T142_28 i :=
  species_entry_eq_sum rK142 ⟨28, by decide⟩ e heK h T142_28 hfix142_28 hinj142_28 hcardT142_28
    (fun i => conj_mem_of_fixedPoints (reps ⟨28, by decide⟩) (reps rK142) (T142_28 i) (hfix142_28 i) h)

/-! ## Cell (142, 29): |T| = 5 -/

def T142_29list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T142_29 : Fin 5 → Coordinate 1 := fun i => T142_29list.getD i.val (0,0,0,0,0)

theorem hfix142_29 : ∀ i, ((T142_29 i : Coordinate 1) : Coordinate 1 ⧸ reps rK142)
    ∈ fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142) :=
  repsFix_of_siftB rK142 ⟨29, by decide⟩ T142_29 (by decide)

theorem hinj142_29 : Function.Injective
    (fun i => ((T142_29 i : Coordinate 1) : Coordinate 1 ⧸ reps rK142)) :=
  repsInj_of_reduceAux rK142 T142_29 (by decide)

theorem hcardT142_29 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK142 ⟨29, by decide⟩ R142 hpxR142 hcardq142 (by decide)).symm

/-- **Cell (142, 29).** -/
theorem cell142_29 (e : List (ZMod 25)) (heK : charOK (basisAt rK142) e = true)
    (h : ↥(reps (⟨29, by decide⟩ : Fin 148))) :
    species (reps (⟨29, by decide⟩ : Fin 148)) h (basisElt (reps rK142) (charOfVec rK142 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK142 e (h : Coordinate 1) T142_29 i :=
  species_entry_eq_sum rK142 ⟨29, by decide⟩ e heK h T142_29 hfix142_29 hinj142_29 hcardT142_29
    (fun i => conj_mem_of_fixedPoints (reps ⟨29, by decide⟩) (reps rK142) (T142_29 i) (hfix142_29 i) h)

/-! ## Cell (142, 30): |T| = 5 -/

def T142_30list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T142_30 : Fin 5 → Coordinate 1 := fun i => T142_30list.getD i.val (0,0,0,0,0)

theorem hfix142_30 : ∀ i, ((T142_30 i : Coordinate 1) : Coordinate 1 ⧸ reps rK142)
    ∈ fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142) :=
  repsFix_of_siftB rK142 ⟨30, by decide⟩ T142_30 (by decide)

theorem hinj142_30 : Function.Injective
    (fun i => ((T142_30 i : Coordinate 1) : Coordinate 1 ⧸ reps rK142)) :=
  repsInj_of_reduceAux rK142 T142_30 (by decide)

theorem hcardT142_30 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK142 ⟨30, by decide⟩ R142 hpxR142 hcardq142 (by decide)).symm

/-- **Cell (142, 30).** -/
theorem cell142_30 (e : List (ZMod 25)) (heK : charOK (basisAt rK142) e = true)
    (h : ↥(reps (⟨30, by decide⟩ : Fin 148))) :
    species (reps (⟨30, by decide⟩ : Fin 148)) h (basisElt (reps rK142) (charOfVec rK142 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK142 e (h : Coordinate 1) T142_30 i :=
  species_entry_eq_sum rK142 ⟨30, by decide⟩ e heK h T142_30 hfix142_30 hinj142_30 hcardT142_30
    (fun i => conj_mem_of_fixedPoints (reps ⟨30, by decide⟩) (reps rK142) (T142_30 i) (hfix142_30 i) h)

/-! ## Cell (142, 31): |T| = 5 -/

def T142_31list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T142_31 : Fin 5 → Coordinate 1 := fun i => T142_31list.getD i.val (0,0,0,0,0)

theorem hfix142_31 : ∀ i, ((T142_31 i : Coordinate 1) : Coordinate 1 ⧸ reps rK142)
    ∈ fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142) :=
  repsFix_of_siftB rK142 ⟨31, by decide⟩ T142_31 (by decide)

theorem hinj142_31 : Function.Injective
    (fun i => ((T142_31 i : Coordinate 1) : Coordinate 1 ⧸ reps rK142)) :=
  repsInj_of_reduceAux rK142 T142_31 (by decide)

theorem hcardT142_31 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK142 ⟨31, by decide⟩ R142 hpxR142 hcardq142 (by decide)).symm

/-- **Cell (142, 31).** -/
theorem cell142_31 (e : List (ZMod 25)) (heK : charOK (basisAt rK142) e = true)
    (h : ↥(reps (⟨31, by decide⟩ : Fin 148))) :
    species (reps (⟨31, by decide⟩ : Fin 148)) h (basisElt (reps rK142) (charOfVec rK142 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK142 e (h : Coordinate 1) T142_31 i :=
  species_entry_eq_sum rK142 ⟨31, by decide⟩ e heK h T142_31 hfix142_31 hinj142_31 hcardT142_31
    (fun i => conj_mem_of_fixedPoints (reps ⟨31, by decide⟩) (reps rK142) (T142_31 i) (hfix142_31 i) h)

/-! ## Cell (142, 32): |T| = 5 -/

def T142_32list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T142_32 : Fin 5 → Coordinate 1 := fun i => T142_32list.getD i.val (0,0,0,0,0)

theorem hfix142_32 : ∀ i, ((T142_32 i : Coordinate 1) : Coordinate 1 ⧸ reps rK142)
    ∈ fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142) :=
  repsFix_of_siftB rK142 ⟨32, by decide⟩ T142_32 (by decide)

theorem hinj142_32 : Function.Injective
    (fun i => ((T142_32 i : Coordinate 1) : Coordinate 1 ⧸ reps rK142)) :=
  repsInj_of_reduceAux rK142 T142_32 (by decide)

theorem hcardT142_32 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK142 ⟨32, by decide⟩ R142 hpxR142 hcardq142 (by decide)).symm

/-- **Cell (142, 32).** -/
theorem cell142_32 (e : List (ZMod 25)) (heK : charOK (basisAt rK142) e = true)
    (h : ↥(reps (⟨32, by decide⟩ : Fin 148))) :
    species (reps (⟨32, by decide⟩ : Fin 148)) h (basisElt (reps rK142) (charOfVec rK142 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK142 e (h : Coordinate 1) T142_32 i :=
  species_entry_eq_sum rK142 ⟨32, by decide⟩ e heK h T142_32 hfix142_32 hinj142_32 hcardT142_32
    (fun i => conj_mem_of_fixedPoints (reps ⟨32, by decide⟩) (reps rK142) (T142_32 i) (hfix142_32 i) h)

/-! ## Cell (142, 53): |T| = 5 -/

def T142_53list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T142_53 : Fin 5 → Coordinate 1 := fun i => T142_53list.getD i.val (0,0,0,0,0)

theorem hfix142_53 : ∀ i, ((T142_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK142)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142) :=
  repsFix_of_siftB rK142 ⟨53, by decide⟩ T142_53 (by decide)

theorem hinj142_53 : Function.Injective
    (fun i => ((T142_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK142)) :=
  repsInj_of_reduceAux rK142 T142_53 (by decide)

theorem hcardT142_53 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK142 ⟨53, by decide⟩ R142 hpxR142 hcardq142 (by decide)).symm

/-- **Cell (142, 53).** -/
theorem cell142_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK142) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK142) (charOfVec rK142 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK142 e (h : Coordinate 1) T142_53 i :=
  species_entry_eq_sum rK142 ⟨53, by decide⟩ e heK h T142_53 hfix142_53 hinj142_53 hcardT142_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK142) (T142_53 i) (hfix142_53 i) h)

/-! ## Cell (142, 54): |T| = 5 -/

def T142_54list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T142_54 : Fin 5 → Coordinate 1 := fun i => T142_54list.getD i.val (0,0,0,0,0)

theorem hfix142_54 : ∀ i, ((T142_54 i : Coordinate 1) : Coordinate 1 ⧸ reps rK142)
    ∈ fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142) :=
  repsFix_of_siftB rK142 ⟨54, by decide⟩ T142_54 (by decide)

theorem hinj142_54 : Function.Injective
    (fun i => ((T142_54 i : Coordinate 1) : Coordinate 1 ⧸ reps rK142)) :=
  repsInj_of_reduceAux rK142 T142_54 (by decide)

theorem hcardT142_54 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK142 ⟨54, by decide⟩ R142 hpxR142 hcardq142 (by decide)).symm

/-- **Cell (142, 54).** -/
theorem cell142_54 (e : List (ZMod 25)) (heK : charOK (basisAt rK142) e = true)
    (h : ↥(reps (⟨54, by decide⟩ : Fin 148))) :
    species (reps (⟨54, by decide⟩ : Fin 148)) h (basisElt (reps rK142) (charOfVec rK142 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK142 e (h : Coordinate 1) T142_54 i :=
  species_entry_eq_sum rK142 ⟨54, by decide⟩ e heK h T142_54 hfix142_54 hinj142_54 hcardT142_54
    (fun i => conj_mem_of_fixedPoints (reps ⟨54, by decide⟩) (reps rK142) (T142_54 i) (hfix142_54 i) h)

/-! ## Cell (142, 90): |T| = 5 -/

def T142_90list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T142_90 : Fin 5 → Coordinate 1 := fun i => T142_90list.getD i.val (0,0,0,0,0)

theorem hfix142_90 : ∀ i, ((T142_90 i : Coordinate 1) : Coordinate 1 ⧸ reps rK142)
    ∈ fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142) :=
  repsFix_of_siftB rK142 ⟨90, by decide⟩ T142_90 (by decide)

theorem hinj142_90 : Function.Injective
    (fun i => ((T142_90 i : Coordinate 1) : Coordinate 1 ⧸ reps rK142)) :=
  repsInj_of_reduceAux rK142 T142_90 (by decide)

theorem hcardT142_90 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK142 ⟨90, by decide⟩ R142 hpxR142 hcardq142 (by decide)).symm

/-- **Cell (142, 90).** -/
theorem cell142_90 (e : List (ZMod 25)) (heK : charOK (basisAt rK142) e = true)
    (h : ↥(reps (⟨90, by decide⟩ : Fin 148))) :
    species (reps (⟨90, by decide⟩ : Fin 148)) h (basisElt (reps rK142) (charOfVec rK142 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK142 e (h : Coordinate 1) T142_90 i :=
  species_entry_eq_sum rK142 ⟨90, by decide⟩ e heK h T142_90 hfix142_90 hinj142_90 hcardT142_90
    (fun i => conj_mem_of_fixedPoints (reps ⟨90, by decide⟩) (reps rK142) (T142_90 i) (hfix142_90 i) h)

/-! ## Cell (142, 91): |T| = 5 -/

def T142_91list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T142_91 : Fin 5 → Coordinate 1 := fun i => T142_91list.getD i.val (0,0,0,0,0)

theorem hfix142_91 : ∀ i, ((T142_91 i : Coordinate 1) : Coordinate 1 ⧸ reps rK142)
    ∈ fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142) :=
  repsFix_of_siftB rK142 ⟨91, by decide⟩ T142_91 (by decide)

theorem hinj142_91 : Function.Injective
    (fun i => ((T142_91 i : Coordinate 1) : Coordinate 1 ⧸ reps rK142)) :=
  repsInj_of_reduceAux rK142 T142_91 (by decide)

theorem hcardT142_91 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK142 ⟨91, by decide⟩ R142 hpxR142 hcardq142 (by decide)).symm

/-- **Cell (142, 91).** -/
theorem cell142_91 (e : List (ZMod 25)) (heK : charOK (basisAt rK142) e = true)
    (h : ↥(reps (⟨91, by decide⟩ : Fin 148))) :
    species (reps (⟨91, by decide⟩ : Fin 148)) h (basisElt (reps rK142) (charOfVec rK142 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK142 e (h : Coordinate 1) T142_91 i :=
  species_entry_eq_sum rK142 ⟨91, by decide⟩ e heK h T142_91 hfix142_91 hinj142_91 hcardT142_91
    (fun i => conj_mem_of_fixedPoints (reps ⟨91, by decide⟩) (reps rK142) (T142_91 i) (hfix142_91 i) h)

/-! ## Cell (142, 92): |T| = 5 -/

def T142_92list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T142_92 : Fin 5 → Coordinate 1 := fun i => T142_92list.getD i.val (0,0,0,0,0)

theorem hfix142_92 : ∀ i, ((T142_92 i : Coordinate 1) : Coordinate 1 ⧸ reps rK142)
    ∈ fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142) :=
  repsFix_of_siftB rK142 ⟨92, by decide⟩ T142_92 (by decide)

theorem hinj142_92 : Function.Injective
    (fun i => ((T142_92 i : Coordinate 1) : Coordinate 1 ⧸ reps rK142)) :=
  repsInj_of_reduceAux rK142 T142_92 (by decide)

theorem hcardT142_92 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK142 ⟨92, by decide⟩ R142 hpxR142 hcardq142 (by decide)).symm

/-- **Cell (142, 92).** -/
theorem cell142_92 (e : List (ZMod 25)) (heK : charOK (basisAt rK142) e = true)
    (h : ↥(reps (⟨92, by decide⟩ : Fin 148))) :
    species (reps (⟨92, by decide⟩ : Fin 148)) h (basisElt (reps rK142) (charOfVec rK142 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK142 e (h : Coordinate 1) T142_92 i :=
  species_entry_eq_sum rK142 ⟨92, by decide⟩ e heK h T142_92 hfix142_92 hinj142_92 hcardT142_92
    (fun i => conj_mem_of_fixedPoints (reps ⟨92, by decide⟩) (reps rK142) (T142_92 i) (hfix142_92 i) h)

/-! ## Cell (142, 93): |T| = 5 -/

def T142_93list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T142_93 : Fin 5 → Coordinate 1 := fun i => T142_93list.getD i.val (0,0,0,0,0)

theorem hfix142_93 : ∀ i, ((T142_93 i : Coordinate 1) : Coordinate 1 ⧸ reps rK142)
    ∈ fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142) :=
  repsFix_of_siftB rK142 ⟨93, by decide⟩ T142_93 (by decide)

theorem hinj142_93 : Function.Injective
    (fun i => ((T142_93 i : Coordinate 1) : Coordinate 1 ⧸ reps rK142)) :=
  repsInj_of_reduceAux rK142 T142_93 (by decide)

theorem hcardT142_93 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK142 ⟨93, by decide⟩ R142 hpxR142 hcardq142 (by decide)).symm

/-- **Cell (142, 93).** -/
theorem cell142_93 (e : List (ZMod 25)) (heK : charOK (basisAt rK142) e = true)
    (h : ↥(reps (⟨93, by decide⟩ : Fin 148))) :
    species (reps (⟨93, by decide⟩ : Fin 148)) h (basisElt (reps rK142) (charOfVec rK142 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK142 e (h : Coordinate 1) T142_93 i :=
  species_entry_eq_sum rK142 ⟨93, by decide⟩ e heK h T142_93 hfix142_93 hinj142_93 hcardT142_93
    (fun i => conj_mem_of_fixedPoints (reps ⟨93, by decide⟩) (reps rK142) (T142_93 i) (hfix142_93 i) h)

/-! ## Cell (142, 94): |T| = 5 -/

def T142_94list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T142_94 : Fin 5 → Coordinate 1 := fun i => T142_94list.getD i.val (0,0,0,0,0)

theorem hfix142_94 : ∀ i, ((T142_94 i : Coordinate 1) : Coordinate 1 ⧸ reps rK142)
    ∈ fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142) :=
  repsFix_of_siftB rK142 ⟨94, by decide⟩ T142_94 (by decide)

theorem hinj142_94 : Function.Injective
    (fun i => ((T142_94 i : Coordinate 1) : Coordinate 1 ⧸ reps rK142)) :=
  repsInj_of_reduceAux rK142 T142_94 (by decide)

theorem hcardT142_94 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK142 ⟨94, by decide⟩ R142 hpxR142 hcardq142 (by decide)).symm

/-- **Cell (142, 94).** -/
theorem cell142_94 (e : List (ZMod 25)) (heK : charOK (basisAt rK142) e = true)
    (h : ↥(reps (⟨94, by decide⟩ : Fin 148))) :
    species (reps (⟨94, by decide⟩ : Fin 148)) h (basisElt (reps rK142) (charOfVec rK142 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK142 e (h : Coordinate 1) T142_94 i :=
  species_entry_eq_sum rK142 ⟨94, by decide⟩ e heK h T142_94 hfix142_94 hinj142_94 hcardT142_94
    (fun i => conj_mem_of_fixedPoints (reps ⟨94, by decide⟩) (reps rK142) (T142_94 i) (hfix142_94 i) h)

/-! ## Cell (142, 115): |T| = 5 -/

def T142_115list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T142_115 : Fin 5 → Coordinate 1 := fun i => T142_115list.getD i.val (0,0,0,0,0)

theorem hfix142_115 : ∀ i, ((T142_115 i : Coordinate 1) : Coordinate 1 ⧸ reps rK142)
    ∈ fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142) :=
  repsFix_of_siftB rK142 ⟨115, by decide⟩ T142_115 (by decide)

theorem hinj142_115 : Function.Injective
    (fun i => ((T142_115 i : Coordinate 1) : Coordinate 1 ⧸ reps rK142)) :=
  repsInj_of_reduceAux rK142 T142_115 (by decide)

theorem hcardT142_115 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK142 ⟨115, by decide⟩ R142 hpxR142 hcardq142 (by decide)).symm

/-- **Cell (142, 115).** -/
theorem cell142_115 (e : List (ZMod 25)) (heK : charOK (basisAt rK142) e = true)
    (h : ↥(reps (⟨115, by decide⟩ : Fin 148))) :
    species (reps (⟨115, by decide⟩ : Fin 148)) h (basisElt (reps rK142) (charOfVec rK142 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK142 e (h : Coordinate 1) T142_115 i :=
  species_entry_eq_sum rK142 ⟨115, by decide⟩ e heK h T142_115 hfix142_115 hinj142_115 hcardT142_115
    (fun i => conj_mem_of_fixedPoints (reps ⟨115, by decide⟩) (reps rK142) (T142_115 i) (hfix142_115 i) h)

/-! ## Cell (142, 142): |T| = 5 -/

def T142_142list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T142_142 : Fin 5 → Coordinate 1 := fun i => T142_142list.getD i.val (0,0,0,0,0)

theorem hfix142_142 : ∀ i, ((T142_142 i : Coordinate 1) : Coordinate 1 ⧸ reps rK142)
    ∈ fixedPoints (reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142) :=
  repsFix_of_siftB rK142 ⟨142, by decide⟩ T142_142 (by decide)

theorem hinj142_142 : Function.Injective
    (fun i => ((T142_142 i : Coordinate 1) : Coordinate 1 ⧸ reps rK142)) :=
  repsInj_of_reduceAux rK142 T142_142 (by decide)

theorem hcardT142_142 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK142 ⟨142, by decide⟩ R142 hpxR142 hcardq142 (by decide)).symm

/-- **Cell (142, 142).** -/
theorem cell142_142 (e : List (ZMod 25)) (heK : charOK (basisAt rK142) e = true)
    (h : ↥(reps (⟨142, by decide⟩ : Fin 148))) :
    species (reps (⟨142, by decide⟩ : Fin 148)) h (basisElt (reps rK142) (charOfVec rK142 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK142 e (h : Coordinate 1) T142_142 i :=
  species_entry_eq_sum rK142 ⟨142, by decide⟩ e heK h T142_142 hfix142_142 hinj142_142 hcardT142_142
    (fun i => conj_mem_of_fixedPoints (reps ⟨142, by decide⟩) (reps rK142) (T142_142 i) (hfix142_142 i) h)

namespace Q2

def R142_2 : Fin 5 → Coordinate 2 := fun i => R142list.getD i.val (0,0,0,0,0)
theorem hpxR142_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK142) (R142_2 i)) := by decide
theorem hcardq142_2 : Nat.card (Coordinate 2 ⧸ reps rK142) = 5 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (142, 0) twin -/

def T142_0_2 : Fin 5 → Coordinate 2 := fun i => T142_0list.getD i.val (0,0,0,0,0)

theorem hfix142_0_2 : ∀ i, ((T142_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK142)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK142) :=
  repsFix_of_siftB2 rK142 ⟨0, by decide⟩ T142_0_2 (by decide)

theorem hinj142_0_2 : Function.Injective
    (fun i => ((T142_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK142)) :=
  repsInj_of_reduceAux2 rK142 T142_0_2 (by decide)

theorem hcardT142_0_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK142)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK142 ⟨0, by decide⟩ R142_2 hpxR142_2 hcardq142_2 (by decide)).symm

/-- **Cell (142, 0) twin (q=2).** -/
theorem cell142_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK142) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK142) (charOfVec2 rK142 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK142 e (h : Coordinate 2) T142_0_2 i :=
  species_entry_eq_sum rK142 ⟨0, by decide⟩ e heK h T142_0_2 hfix142_0_2 hinj142_0_2 hcardT142_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK142) (T142_0_2 i) (hfix142_0_2 i) h)

/-! ### Cell (142, 10) twin -/

def T142_10_2 : Fin 5 → Coordinate 2 := fun i => T142_10list.getD i.val (0,0,0,0,0)

theorem hfix142_10_2 : ∀ i, ((T142_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK142)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK142) :=
  repsFix_of_siftB2 rK142 ⟨10, by decide⟩ T142_10_2 (by decide)

theorem hinj142_10_2 : Function.Injective
    (fun i => ((T142_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK142)) :=
  repsInj_of_reduceAux2 rK142 T142_10_2 (by decide)

theorem hcardT142_10_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK142)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK142 ⟨10, by decide⟩ R142_2 hpxR142_2 hcardq142_2 (by decide)).symm

/-- **Cell (142, 10) twin (q=2).** -/
theorem cell142_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK142) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK142) (charOfVec2 rK142 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK142 e (h : Coordinate 2) T142_10_2 i :=
  species_entry_eq_sum rK142 ⟨10, by decide⟩ e heK h T142_10_2 hfix142_10_2 hinj142_10_2 hcardT142_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK142) (T142_10_2 i) (hfix142_10_2 i) h)

/-! ### Cell (142, 11) twin -/

def T142_11_2 : Fin 5 → Coordinate 2 := fun i => T142_11list.getD i.val (0,0,0,0,0)

theorem hfix142_11_2 : ∀ i, ((T142_11_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK142)
    ∈ fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK142) :=
  repsFix_of_siftB2 rK142 ⟨11, by decide⟩ T142_11_2 (by decide)

theorem hinj142_11_2 : Function.Injective
    (fun i => ((T142_11_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK142)) :=
  repsInj_of_reduceAux2 rK142 T142_11_2 (by decide)

theorem hcardT142_11_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK142)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK142 ⟨11, by decide⟩ R142_2 hpxR142_2 hcardq142_2 (by decide)).symm

/-- **Cell (142, 11) twin (q=2).** -/
theorem cell142_11_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK142) e = true)
    (h : ↥(reps (⟨11, by decide⟩ : Fin 148))) :
    species (reps (⟨11, by decide⟩ : Fin 148)) h (basisElt (reps rK142) (charOfVec2 rK142 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK142 e (h : Coordinate 2) T142_11_2 i :=
  species_entry_eq_sum rK142 ⟨11, by decide⟩ e heK h T142_11_2 hfix142_11_2 hinj142_11_2 hcardT142_11_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨11, by decide⟩) (reps rK142) (T142_11_2 i) (hfix142_11_2 i) h)

/-! ### Cell (142, 12) twin -/

def T142_12_2 : Fin 5 → Coordinate 2 := fun i => T142_12list.getD i.val (0,0,0,0,0)

theorem hfix142_12_2 : ∀ i, ((T142_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK142)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK142) :=
  repsFix_of_siftB2 rK142 ⟨12, by decide⟩ T142_12_2 (by decide)

theorem hinj142_12_2 : Function.Injective
    (fun i => ((T142_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK142)) :=
  repsInj_of_reduceAux2 rK142 T142_12_2 (by decide)

theorem hcardT142_12_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK142)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK142 ⟨12, by decide⟩ R142_2 hpxR142_2 hcardq142_2 (by decide)).symm

/-- **Cell (142, 12) twin (q=2).** -/
theorem cell142_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK142) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK142) (charOfVec2 rK142 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK142 e (h : Coordinate 2) T142_12_2 i :=
  species_entry_eq_sum rK142 ⟨12, by decide⟩ e heK h T142_12_2 hfix142_12_2 hinj142_12_2 hcardT142_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK142) (T142_12_2 i) (hfix142_12_2 i) h)

/-! ### Cell (142, 28) twin -/

def T142_28_2 : Fin 5 → Coordinate 2 := fun i => T142_28list.getD i.val (0,0,0,0,0)

theorem hfix142_28_2 : ∀ i, ((T142_28_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK142)
    ∈ fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK142) :=
  repsFix_of_siftB2 rK142 ⟨28, by decide⟩ T142_28_2 (by decide)

theorem hinj142_28_2 : Function.Injective
    (fun i => ((T142_28_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK142)) :=
  repsInj_of_reduceAux2 rK142 T142_28_2 (by decide)

theorem hcardT142_28_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK142)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK142 ⟨28, by decide⟩ R142_2 hpxR142_2 hcardq142_2 (by decide)).symm

/-- **Cell (142, 28) twin (q=2).** -/
theorem cell142_28_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK142) e = true)
    (h : ↥(reps (⟨28, by decide⟩ : Fin 148))) :
    species (reps (⟨28, by decide⟩ : Fin 148)) h (basisElt (reps rK142) (charOfVec2 rK142 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK142 e (h : Coordinate 2) T142_28_2 i :=
  species_entry_eq_sum rK142 ⟨28, by decide⟩ e heK h T142_28_2 hfix142_28_2 hinj142_28_2 hcardT142_28_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨28, by decide⟩) (reps rK142) (T142_28_2 i) (hfix142_28_2 i) h)

/-! ### Cell (142, 29) twin -/

def T142_29_2 : Fin 5 → Coordinate 2 := fun i => T142_29list.getD i.val (0,0,0,0,0)

theorem hfix142_29_2 : ∀ i, ((T142_29_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK142)
    ∈ fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK142) :=
  repsFix_of_siftB2 rK142 ⟨29, by decide⟩ T142_29_2 (by decide)

theorem hinj142_29_2 : Function.Injective
    (fun i => ((T142_29_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK142)) :=
  repsInj_of_reduceAux2 rK142 T142_29_2 (by decide)

theorem hcardT142_29_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK142)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK142 ⟨29, by decide⟩ R142_2 hpxR142_2 hcardq142_2 (by decide)).symm

/-- **Cell (142, 29) twin (q=2).** -/
theorem cell142_29_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK142) e = true)
    (h : ↥(reps (⟨29, by decide⟩ : Fin 148))) :
    species (reps (⟨29, by decide⟩ : Fin 148)) h (basisElt (reps rK142) (charOfVec2 rK142 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK142 e (h : Coordinate 2) T142_29_2 i :=
  species_entry_eq_sum rK142 ⟨29, by decide⟩ e heK h T142_29_2 hfix142_29_2 hinj142_29_2 hcardT142_29_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨29, by decide⟩) (reps rK142) (T142_29_2 i) (hfix142_29_2 i) h)

/-! ### Cell (142, 30) twin -/

def T142_30_2 : Fin 5 → Coordinate 2 := fun i => T142_30list.getD i.val (0,0,0,0,0)

theorem hfix142_30_2 : ∀ i, ((T142_30_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK142)
    ∈ fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK142) :=
  repsFix_of_siftB2 rK142 ⟨30, by decide⟩ T142_30_2 (by decide)

theorem hinj142_30_2 : Function.Injective
    (fun i => ((T142_30_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK142)) :=
  repsInj_of_reduceAux2 rK142 T142_30_2 (by decide)

theorem hcardT142_30_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK142)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK142 ⟨30, by decide⟩ R142_2 hpxR142_2 hcardq142_2 (by decide)).symm

/-- **Cell (142, 30) twin (q=2).** -/
theorem cell142_30_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK142) e = true)
    (h : ↥(reps (⟨30, by decide⟩ : Fin 148))) :
    species (reps (⟨30, by decide⟩ : Fin 148)) h (basisElt (reps rK142) (charOfVec2 rK142 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK142 e (h : Coordinate 2) T142_30_2 i :=
  species_entry_eq_sum rK142 ⟨30, by decide⟩ e heK h T142_30_2 hfix142_30_2 hinj142_30_2 hcardT142_30_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨30, by decide⟩) (reps rK142) (T142_30_2 i) (hfix142_30_2 i) h)

/-! ### Cell (142, 31) twin -/

def T142_31_2 : Fin 5 → Coordinate 2 := fun i => T142_31list.getD i.val (0,0,0,0,0)

theorem hfix142_31_2 : ∀ i, ((T142_31_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK142)
    ∈ fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK142) :=
  repsFix_of_siftB2 rK142 ⟨31, by decide⟩ T142_31_2 (by decide)

theorem hinj142_31_2 : Function.Injective
    (fun i => ((T142_31_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK142)) :=
  repsInj_of_reduceAux2 rK142 T142_31_2 (by decide)

theorem hcardT142_31_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK142)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK142 ⟨31, by decide⟩ R142_2 hpxR142_2 hcardq142_2 (by decide)).symm

/-- **Cell (142, 31) twin (q=2).** -/
theorem cell142_31_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK142) e = true)
    (h : ↥(reps (⟨31, by decide⟩ : Fin 148))) :
    species (reps (⟨31, by decide⟩ : Fin 148)) h (basisElt (reps rK142) (charOfVec2 rK142 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK142 e (h : Coordinate 2) T142_31_2 i :=
  species_entry_eq_sum rK142 ⟨31, by decide⟩ e heK h T142_31_2 hfix142_31_2 hinj142_31_2 hcardT142_31_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨31, by decide⟩) (reps rK142) (T142_31_2 i) (hfix142_31_2 i) h)

/-! ### Cell (142, 32) twin -/

def T142_32_2 : Fin 5 → Coordinate 2 := fun i => T142_32list.getD i.val (0,0,0,0,0)

theorem hfix142_32_2 : ∀ i, ((T142_32_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK142)
    ∈ fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK142) :=
  repsFix_of_siftB2 rK142 ⟨32, by decide⟩ T142_32_2 (by decide)

theorem hinj142_32_2 : Function.Injective
    (fun i => ((T142_32_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK142)) :=
  repsInj_of_reduceAux2 rK142 T142_32_2 (by decide)

theorem hcardT142_32_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK142)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK142 ⟨32, by decide⟩ R142_2 hpxR142_2 hcardq142_2 (by decide)).symm

/-- **Cell (142, 32) twin (q=2).** -/
theorem cell142_32_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK142) e = true)
    (h : ↥(reps (⟨32, by decide⟩ : Fin 148))) :
    species (reps (⟨32, by decide⟩ : Fin 148)) h (basisElt (reps rK142) (charOfVec2 rK142 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK142 e (h : Coordinate 2) T142_32_2 i :=
  species_entry_eq_sum rK142 ⟨32, by decide⟩ e heK h T142_32_2 hfix142_32_2 hinj142_32_2 hcardT142_32_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨32, by decide⟩) (reps rK142) (T142_32_2 i) (hfix142_32_2 i) h)

/-! ### Cell (142, 53) twin -/

def T142_53_2 : Fin 5 → Coordinate 2 := fun i => T142_53list.getD i.val (0,0,0,0,0)

theorem hfix142_53_2 : ∀ i, ((T142_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK142)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK142) :=
  repsFix_of_siftB2 rK142 ⟨53, by decide⟩ T142_53_2 (by decide)

theorem hinj142_53_2 : Function.Injective
    (fun i => ((T142_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK142)) :=
  repsInj_of_reduceAux2 rK142 T142_53_2 (by decide)

theorem hcardT142_53_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK142)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK142 ⟨53, by decide⟩ R142_2 hpxR142_2 hcardq142_2 (by decide)).symm

/-- **Cell (142, 53) twin (q=2).** -/
theorem cell142_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK142) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK142) (charOfVec2 rK142 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK142 e (h : Coordinate 2) T142_53_2 i :=
  species_entry_eq_sum rK142 ⟨53, by decide⟩ e heK h T142_53_2 hfix142_53_2 hinj142_53_2 hcardT142_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK142) (T142_53_2 i) (hfix142_53_2 i) h)

/-! ### Cell (142, 54) twin -/

def T142_54_2 : Fin 5 → Coordinate 2 := fun i => T142_54list.getD i.val (0,0,0,0,0)

theorem hfix142_54_2 : ∀ i, ((T142_54_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK142)
    ∈ fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK142) :=
  repsFix_of_siftB2 rK142 ⟨54, by decide⟩ T142_54_2 (by decide)

theorem hinj142_54_2 : Function.Injective
    (fun i => ((T142_54_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK142)) :=
  repsInj_of_reduceAux2 rK142 T142_54_2 (by decide)

theorem hcardT142_54_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK142)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK142 ⟨54, by decide⟩ R142_2 hpxR142_2 hcardq142_2 (by decide)).symm

/-- **Cell (142, 54) twin (q=2).** -/
theorem cell142_54_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK142) e = true)
    (h : ↥(reps (⟨54, by decide⟩ : Fin 148))) :
    species (reps (⟨54, by decide⟩ : Fin 148)) h (basisElt (reps rK142) (charOfVec2 rK142 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK142 e (h : Coordinate 2) T142_54_2 i :=
  species_entry_eq_sum rK142 ⟨54, by decide⟩ e heK h T142_54_2 hfix142_54_2 hinj142_54_2 hcardT142_54_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨54, by decide⟩) (reps rK142) (T142_54_2 i) (hfix142_54_2 i) h)

/-! ### Cell (142, 90) twin -/

def T142_90_2 : Fin 5 → Coordinate 2 := fun i => T142_90list.getD i.val (0,0,0,0,0)

theorem hfix142_90_2 : ∀ i, ((T142_90_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK142)
    ∈ fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK142) :=
  repsFix_of_siftB2 rK142 ⟨90, by decide⟩ T142_90_2 (by decide)

theorem hinj142_90_2 : Function.Injective
    (fun i => ((T142_90_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK142)) :=
  repsInj_of_reduceAux2 rK142 T142_90_2 (by decide)

theorem hcardT142_90_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK142)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK142 ⟨90, by decide⟩ R142_2 hpxR142_2 hcardq142_2 (by decide)).symm

/-- **Cell (142, 90) twin (q=2).** -/
theorem cell142_90_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK142) e = true)
    (h : ↥(reps (⟨90, by decide⟩ : Fin 148))) :
    species (reps (⟨90, by decide⟩ : Fin 148)) h (basisElt (reps rK142) (charOfVec2 rK142 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK142 e (h : Coordinate 2) T142_90_2 i :=
  species_entry_eq_sum rK142 ⟨90, by decide⟩ e heK h T142_90_2 hfix142_90_2 hinj142_90_2 hcardT142_90_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨90, by decide⟩) (reps rK142) (T142_90_2 i) (hfix142_90_2 i) h)

/-! ### Cell (142, 91) twin -/

def T142_91_2 : Fin 5 → Coordinate 2 := fun i => T142_91list.getD i.val (0,0,0,0,0)

theorem hfix142_91_2 : ∀ i, ((T142_91_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK142)
    ∈ fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK142) :=
  repsFix_of_siftB2 rK142 ⟨91, by decide⟩ T142_91_2 (by decide)

theorem hinj142_91_2 : Function.Injective
    (fun i => ((T142_91_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK142)) :=
  repsInj_of_reduceAux2 rK142 T142_91_2 (by decide)

theorem hcardT142_91_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK142)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK142 ⟨91, by decide⟩ R142_2 hpxR142_2 hcardq142_2 (by decide)).symm

/-- **Cell (142, 91) twin (q=2).** -/
theorem cell142_91_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK142) e = true)
    (h : ↥(reps (⟨91, by decide⟩ : Fin 148))) :
    species (reps (⟨91, by decide⟩ : Fin 148)) h (basisElt (reps rK142) (charOfVec2 rK142 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK142 e (h : Coordinate 2) T142_91_2 i :=
  species_entry_eq_sum rK142 ⟨91, by decide⟩ e heK h T142_91_2 hfix142_91_2 hinj142_91_2 hcardT142_91_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨91, by decide⟩) (reps rK142) (T142_91_2 i) (hfix142_91_2 i) h)

/-! ### Cell (142, 92) twin -/

def T142_92_2 : Fin 5 → Coordinate 2 := fun i => T142_92list.getD i.val (0,0,0,0,0)

theorem hfix142_92_2 : ∀ i, ((T142_92_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK142)
    ∈ fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK142) :=
  repsFix_of_siftB2 rK142 ⟨92, by decide⟩ T142_92_2 (by decide)

theorem hinj142_92_2 : Function.Injective
    (fun i => ((T142_92_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK142)) :=
  repsInj_of_reduceAux2 rK142 T142_92_2 (by decide)

theorem hcardT142_92_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK142)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK142 ⟨92, by decide⟩ R142_2 hpxR142_2 hcardq142_2 (by decide)).symm

/-- **Cell (142, 92) twin (q=2).** -/
theorem cell142_92_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK142) e = true)
    (h : ↥(reps (⟨92, by decide⟩ : Fin 148))) :
    species (reps (⟨92, by decide⟩ : Fin 148)) h (basisElt (reps rK142) (charOfVec2 rK142 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK142 e (h : Coordinate 2) T142_92_2 i :=
  species_entry_eq_sum rK142 ⟨92, by decide⟩ e heK h T142_92_2 hfix142_92_2 hinj142_92_2 hcardT142_92_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨92, by decide⟩) (reps rK142) (T142_92_2 i) (hfix142_92_2 i) h)

/-! ### Cell (142, 93) twin -/

def T142_93_2 : Fin 5 → Coordinate 2 := fun i => T142_93list.getD i.val (0,0,0,0,0)

theorem hfix142_93_2 : ∀ i, ((T142_93_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK142)
    ∈ fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK142) :=
  repsFix_of_siftB2 rK142 ⟨93, by decide⟩ T142_93_2 (by decide)

theorem hinj142_93_2 : Function.Injective
    (fun i => ((T142_93_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK142)) :=
  repsInj_of_reduceAux2 rK142 T142_93_2 (by decide)

theorem hcardT142_93_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK142)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK142 ⟨93, by decide⟩ R142_2 hpxR142_2 hcardq142_2 (by decide)).symm

/-- **Cell (142, 93) twin (q=2).** -/
theorem cell142_93_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK142) e = true)
    (h : ↥(reps (⟨93, by decide⟩ : Fin 148))) :
    species (reps (⟨93, by decide⟩ : Fin 148)) h (basisElt (reps rK142) (charOfVec2 rK142 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK142 e (h : Coordinate 2) T142_93_2 i :=
  species_entry_eq_sum rK142 ⟨93, by decide⟩ e heK h T142_93_2 hfix142_93_2 hinj142_93_2 hcardT142_93_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨93, by decide⟩) (reps rK142) (T142_93_2 i) (hfix142_93_2 i) h)

/-! ### Cell (142, 94) twin -/

def T142_94_2 : Fin 5 → Coordinate 2 := fun i => T142_94list.getD i.val (0,0,0,0,0)

theorem hfix142_94_2 : ∀ i, ((T142_94_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK142)
    ∈ fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK142) :=
  repsFix_of_siftB2 rK142 ⟨94, by decide⟩ T142_94_2 (by decide)

theorem hinj142_94_2 : Function.Injective
    (fun i => ((T142_94_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK142)) :=
  repsInj_of_reduceAux2 rK142 T142_94_2 (by decide)

theorem hcardT142_94_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK142)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK142 ⟨94, by decide⟩ R142_2 hpxR142_2 hcardq142_2 (by decide)).symm

/-- **Cell (142, 94) twin (q=2).** -/
theorem cell142_94_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK142) e = true)
    (h : ↥(reps (⟨94, by decide⟩ : Fin 148))) :
    species (reps (⟨94, by decide⟩ : Fin 148)) h (basisElt (reps rK142) (charOfVec2 rK142 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK142 e (h : Coordinate 2) T142_94_2 i :=
  species_entry_eq_sum rK142 ⟨94, by decide⟩ e heK h T142_94_2 hfix142_94_2 hinj142_94_2 hcardT142_94_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨94, by decide⟩) (reps rK142) (T142_94_2 i) (hfix142_94_2 i) h)

/-! ### Cell (142, 115) twin -/

def T142_115_2 : Fin 5 → Coordinate 2 := fun i => T142_115list.getD i.val (0,0,0,0,0)

theorem hfix142_115_2 : ∀ i, ((T142_115_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK142)
    ∈ fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK142) :=
  repsFix_of_siftB2 rK142 ⟨115, by decide⟩ T142_115_2 (by decide)

theorem hinj142_115_2 : Function.Injective
    (fun i => ((T142_115_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK142)) :=
  repsInj_of_reduceAux2 rK142 T142_115_2 (by decide)

theorem hcardT142_115_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK142)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK142 ⟨115, by decide⟩ R142_2 hpxR142_2 hcardq142_2 (by decide)).symm

/-- **Cell (142, 115) twin (q=2).** -/
theorem cell142_115_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK142) e = true)
    (h : ↥(reps (⟨115, by decide⟩ : Fin 148))) :
    species (reps (⟨115, by decide⟩ : Fin 148)) h (basisElt (reps rK142) (charOfVec2 rK142 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK142 e (h : Coordinate 2) T142_115_2 i :=
  species_entry_eq_sum rK142 ⟨115, by decide⟩ e heK h T142_115_2 hfix142_115_2 hinj142_115_2 hcardT142_115_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨115, by decide⟩) (reps rK142) (T142_115_2 i) (hfix142_115_2 i) h)

/-! ### Cell (142, 142) twin -/

def T142_142_2 : Fin 5 → Coordinate 2 := fun i => T142_142list.getD i.val (0,0,0,0,0)

theorem hfix142_142_2 : ∀ i, ((T142_142_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK142)
    ∈ fixedPoints (reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK142) :=
  repsFix_of_siftB2 rK142 ⟨142, by decide⟩ T142_142_2 (by decide)

theorem hinj142_142_2 : Function.Injective
    (fun i => ((T142_142_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK142)) :=
  repsInj_of_reduceAux2 rK142 T142_142_2 (by decide)

theorem hcardT142_142_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK142)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK142 ⟨142, by decide⟩ R142_2 hpxR142_2 hcardq142_2 (by decide)).symm

/-- **Cell (142, 142) twin (q=2).** -/
theorem cell142_142_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK142) e = true)
    (h : ↥(reps (⟨142, by decide⟩ : Fin 148))) :
    species (reps (⟨142, by decide⟩ : Fin 148)) h (basisElt (reps rK142) (charOfVec2 rK142 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK142 e (h : Coordinate 2) T142_142_2 i :=
  species_entry_eq_sum rK142 ⟨142, by decide⟩ e heK h T142_142_2 hfix142_142_2 hinj142_142_2 hcardT142_142_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨142, by decide⟩) (reps rK142) (T142_142_2 i) (hfix142_142_2 i) h)

end Q2

/-! # K-class rK = 143  (|G/K| = 5) -/

def rK143 : Fin 148 := ⟨143, by decide⟩

def R143list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def R143 : Fin 5 → Coordinate 1 := fun i => R143list.getD i.val (0,0,0,0,0)

theorem hpxR143 : Function.Injective (fun i => reduceAux 1 (basisAt rK143) (R143 i)) := by decide
theorem hcardq143 : Nat.card (Coordinate 1 ⧸ reps rK143) = 5 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (143, 0): |T| = 5 -/

def T143_0list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T143_0 : Fin 5 → Coordinate 1 := fun i => T143_0list.getD i.val (0,0,0,0,0)

theorem hfix143_0 : ∀ i, ((T143_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK143)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143) :=
  repsFix_of_siftB rK143 ⟨0, by decide⟩ T143_0 (by decide)

theorem hinj143_0 : Function.Injective
    (fun i => ((T143_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK143)) :=
  repsInj_of_reduceAux rK143 T143_0 (by decide)

theorem hcardT143_0 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK143 ⟨0, by decide⟩ R143 hpxR143 hcardq143 (by decide)).symm

/-- **Cell (143, 0).** -/
theorem cell143_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK143) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK143) (charOfVec rK143 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK143 e (h : Coordinate 1) T143_0 i :=
  species_entry_eq_sum rK143 ⟨0, by decide⟩ e heK h T143_0 hfix143_0 hinj143_0 hcardT143_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK143) (T143_0 i) (hfix143_0 i) h)

/-! ## Cell (143, 10): |T| = 5 -/

def T143_10list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T143_10 : Fin 5 → Coordinate 1 := fun i => T143_10list.getD i.val (0,0,0,0,0)

theorem hfix143_10 : ∀ i, ((T143_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK143)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143) :=
  repsFix_of_siftB rK143 ⟨10, by decide⟩ T143_10 (by decide)

theorem hinj143_10 : Function.Injective
    (fun i => ((T143_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK143)) :=
  repsInj_of_reduceAux rK143 T143_10 (by decide)

theorem hcardT143_10 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK143 ⟨10, by decide⟩ R143 hpxR143 hcardq143 (by decide)).symm

/-- **Cell (143, 10).** -/
theorem cell143_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK143) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK143) (charOfVec rK143 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK143 e (h : Coordinate 1) T143_10 i :=
  species_entry_eq_sum rK143 ⟨10, by decide⟩ e heK h T143_10 hfix143_10 hinj143_10 hcardT143_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK143) (T143_10 i) (hfix143_10 i) h)

/-! ## Cell (143, 11): |T| = 5 -/

def T143_11list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T143_11 : Fin 5 → Coordinate 1 := fun i => T143_11list.getD i.val (0,0,0,0,0)

theorem hfix143_11 : ∀ i, ((T143_11 i : Coordinate 1) : Coordinate 1 ⧸ reps rK143)
    ∈ fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143) :=
  repsFix_of_siftB rK143 ⟨11, by decide⟩ T143_11 (by decide)

theorem hinj143_11 : Function.Injective
    (fun i => ((T143_11 i : Coordinate 1) : Coordinate 1 ⧸ reps rK143)) :=
  repsInj_of_reduceAux rK143 T143_11 (by decide)

theorem hcardT143_11 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK143 ⟨11, by decide⟩ R143 hpxR143 hcardq143 (by decide)).symm

/-- **Cell (143, 11).** -/
theorem cell143_11 (e : List (ZMod 25)) (heK : charOK (basisAt rK143) e = true)
    (h : ↥(reps (⟨11, by decide⟩ : Fin 148))) :
    species (reps (⟨11, by decide⟩ : Fin 148)) h (basisElt (reps rK143) (charOfVec rK143 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK143 e (h : Coordinate 1) T143_11 i :=
  species_entry_eq_sum rK143 ⟨11, by decide⟩ e heK h T143_11 hfix143_11 hinj143_11 hcardT143_11
    (fun i => conj_mem_of_fixedPoints (reps ⟨11, by decide⟩) (reps rK143) (T143_11 i) (hfix143_11 i) h)

/-! ## Cell (143, 12): |T| = 5 -/

def T143_12list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T143_12 : Fin 5 → Coordinate 1 := fun i => T143_12list.getD i.val (0,0,0,0,0)

theorem hfix143_12 : ∀ i, ((T143_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK143)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143) :=
  repsFix_of_siftB rK143 ⟨12, by decide⟩ T143_12 (by decide)

theorem hinj143_12 : Function.Injective
    (fun i => ((T143_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK143)) :=
  repsInj_of_reduceAux rK143 T143_12 (by decide)

theorem hcardT143_12 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK143 ⟨12, by decide⟩ R143 hpxR143 hcardq143 (by decide)).symm

/-- **Cell (143, 12).** -/
theorem cell143_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK143) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK143) (charOfVec rK143 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK143 e (h : Coordinate 1) T143_12 i :=
  species_entry_eq_sum rK143 ⟨12, by decide⟩ e heK h T143_12 hfix143_12 hinj143_12 hcardT143_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK143) (T143_12 i) (hfix143_12 i) h)

/-! ## Cell (143, 33): |T| = 5 -/

def T143_33list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T143_33 : Fin 5 → Coordinate 1 := fun i => T143_33list.getD i.val (0,0,0,0,0)

theorem hfix143_33 : ∀ i, ((T143_33 i : Coordinate 1) : Coordinate 1 ⧸ reps rK143)
    ∈ fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143) :=
  repsFix_of_siftB rK143 ⟨33, by decide⟩ T143_33 (by decide)

theorem hinj143_33 : Function.Injective
    (fun i => ((T143_33 i : Coordinate 1) : Coordinate 1 ⧸ reps rK143)) :=
  repsInj_of_reduceAux rK143 T143_33 (by decide)

theorem hcardT143_33 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK143 ⟨33, by decide⟩ R143 hpxR143 hcardq143 (by decide)).symm

/-- **Cell (143, 33).** -/
theorem cell143_33 (e : List (ZMod 25)) (heK : charOK (basisAt rK143) e = true)
    (h : ↥(reps (⟨33, by decide⟩ : Fin 148))) :
    species (reps (⟨33, by decide⟩ : Fin 148)) h (basisElt (reps rK143) (charOfVec rK143 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK143 e (h : Coordinate 1) T143_33 i :=
  species_entry_eq_sum rK143 ⟨33, by decide⟩ e heK h T143_33 hfix143_33 hinj143_33 hcardT143_33
    (fun i => conj_mem_of_fixedPoints (reps ⟨33, by decide⟩) (reps rK143) (T143_33 i) (hfix143_33 i) h)

/-! ## Cell (143, 34): |T| = 5 -/

def T143_34list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T143_34 : Fin 5 → Coordinate 1 := fun i => T143_34list.getD i.val (0,0,0,0,0)

theorem hfix143_34 : ∀ i, ((T143_34 i : Coordinate 1) : Coordinate 1 ⧸ reps rK143)
    ∈ fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143) :=
  repsFix_of_siftB rK143 ⟨34, by decide⟩ T143_34 (by decide)

theorem hinj143_34 : Function.Injective
    (fun i => ((T143_34 i : Coordinate 1) : Coordinate 1 ⧸ reps rK143)) :=
  repsInj_of_reduceAux rK143 T143_34 (by decide)

theorem hcardT143_34 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK143 ⟨34, by decide⟩ R143 hpxR143 hcardq143 (by decide)).symm

/-- **Cell (143, 34).** -/
theorem cell143_34 (e : List (ZMod 25)) (heK : charOK (basisAt rK143) e = true)
    (h : ↥(reps (⟨34, by decide⟩ : Fin 148))) :
    species (reps (⟨34, by decide⟩ : Fin 148)) h (basisElt (reps rK143) (charOfVec rK143 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK143 e (h : Coordinate 1) T143_34 i :=
  species_entry_eq_sum rK143 ⟨34, by decide⟩ e heK h T143_34 hfix143_34 hinj143_34 hcardT143_34
    (fun i => conj_mem_of_fixedPoints (reps ⟨34, by decide⟩) (reps rK143) (T143_34 i) (hfix143_34 i) h)

/-! ## Cell (143, 35): |T| = 5 -/

def T143_35list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T143_35 : Fin 5 → Coordinate 1 := fun i => T143_35list.getD i.val (0,0,0,0,0)

theorem hfix143_35 : ∀ i, ((T143_35 i : Coordinate 1) : Coordinate 1 ⧸ reps rK143)
    ∈ fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143) :=
  repsFix_of_siftB rK143 ⟨35, by decide⟩ T143_35 (by decide)

theorem hinj143_35 : Function.Injective
    (fun i => ((T143_35 i : Coordinate 1) : Coordinate 1 ⧸ reps rK143)) :=
  repsInj_of_reduceAux rK143 T143_35 (by decide)

theorem hcardT143_35 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK143 ⟨35, by decide⟩ R143 hpxR143 hcardq143 (by decide)).symm

/-- **Cell (143, 35).** -/
theorem cell143_35 (e : List (ZMod 25)) (heK : charOK (basisAt rK143) e = true)
    (h : ↥(reps (⟨35, by decide⟩ : Fin 148))) :
    species (reps (⟨35, by decide⟩ : Fin 148)) h (basisElt (reps rK143) (charOfVec rK143 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK143 e (h : Coordinate 1) T143_35 i :=
  species_entry_eq_sum rK143 ⟨35, by decide⟩ e heK h T143_35 hfix143_35 hinj143_35 hcardT143_35
    (fun i => conj_mem_of_fixedPoints (reps ⟨35, by decide⟩) (reps rK143) (T143_35 i) (hfix143_35 i) h)

/-! ## Cell (143, 36): |T| = 5 -/

def T143_36list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T143_36 : Fin 5 → Coordinate 1 := fun i => T143_36list.getD i.val (0,0,0,0,0)

theorem hfix143_36 : ∀ i, ((T143_36 i : Coordinate 1) : Coordinate 1 ⧸ reps rK143)
    ∈ fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143) :=
  repsFix_of_siftB rK143 ⟨36, by decide⟩ T143_36 (by decide)

theorem hinj143_36 : Function.Injective
    (fun i => ((T143_36 i : Coordinate 1) : Coordinate 1 ⧸ reps rK143)) :=
  repsInj_of_reduceAux rK143 T143_36 (by decide)

theorem hcardT143_36 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK143 ⟨36, by decide⟩ R143 hpxR143 hcardq143 (by decide)).symm

/-- **Cell (143, 36).** -/
theorem cell143_36 (e : List (ZMod 25)) (heK : charOK (basisAt rK143) e = true)
    (h : ↥(reps (⟨36, by decide⟩ : Fin 148))) :
    species (reps (⟨36, by decide⟩ : Fin 148)) h (basisElt (reps rK143) (charOfVec rK143 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK143 e (h : Coordinate 1) T143_36 i :=
  species_entry_eq_sum rK143 ⟨36, by decide⟩ e heK h T143_36 hfix143_36 hinj143_36 hcardT143_36
    (fun i => conj_mem_of_fixedPoints (reps ⟨36, by decide⟩) (reps rK143) (T143_36 i) (hfix143_36 i) h)

/-! ## Cell (143, 37): |T| = 5 -/

def T143_37list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T143_37 : Fin 5 → Coordinate 1 := fun i => T143_37list.getD i.val (0,0,0,0,0)

theorem hfix143_37 : ∀ i, ((T143_37 i : Coordinate 1) : Coordinate 1 ⧸ reps rK143)
    ∈ fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143) :=
  repsFix_of_siftB rK143 ⟨37, by decide⟩ T143_37 (by decide)

theorem hinj143_37 : Function.Injective
    (fun i => ((T143_37 i : Coordinate 1) : Coordinate 1 ⧸ reps rK143)) :=
  repsInj_of_reduceAux rK143 T143_37 (by decide)

theorem hcardT143_37 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK143 ⟨37, by decide⟩ R143 hpxR143 hcardq143 (by decide)).symm

/-- **Cell (143, 37).** -/
theorem cell143_37 (e : List (ZMod 25)) (heK : charOK (basisAt rK143) e = true)
    (h : ↥(reps (⟨37, by decide⟩ : Fin 148))) :
    species (reps (⟨37, by decide⟩ : Fin 148)) h (basisElt (reps rK143) (charOfVec rK143 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK143 e (h : Coordinate 1) T143_37 i :=
  species_entry_eq_sum rK143 ⟨37, by decide⟩ e heK h T143_37 hfix143_37 hinj143_37 hcardT143_37
    (fun i => conj_mem_of_fixedPoints (reps ⟨37, by decide⟩) (reps rK143) (T143_37 i) (hfix143_37 i) h)

/-! ## Cell (143, 53): |T| = 5 -/

def T143_53list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T143_53 : Fin 5 → Coordinate 1 := fun i => T143_53list.getD i.val (0,0,0,0,0)

theorem hfix143_53 : ∀ i, ((T143_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK143)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143) :=
  repsFix_of_siftB rK143 ⟨53, by decide⟩ T143_53 (by decide)

theorem hinj143_53 : Function.Injective
    (fun i => ((T143_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK143)) :=
  repsInj_of_reduceAux rK143 T143_53 (by decide)

theorem hcardT143_53 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK143 ⟨53, by decide⟩ R143 hpxR143 hcardq143 (by decide)).symm

/-- **Cell (143, 53).** -/
theorem cell143_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK143) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK143) (charOfVec rK143 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK143 e (h : Coordinate 1) T143_53 i :=
  species_entry_eq_sum rK143 ⟨53, by decide⟩ e heK h T143_53 hfix143_53 hinj143_53 hcardT143_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK143) (T143_53 i) (hfix143_53 i) h)

/-! ## Cell (143, 54): |T| = 5 -/

def T143_54list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T143_54 : Fin 5 → Coordinate 1 := fun i => T143_54list.getD i.val (0,0,0,0,0)

theorem hfix143_54 : ∀ i, ((T143_54 i : Coordinate 1) : Coordinate 1 ⧸ reps rK143)
    ∈ fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143) :=
  repsFix_of_siftB rK143 ⟨54, by decide⟩ T143_54 (by decide)

theorem hinj143_54 : Function.Injective
    (fun i => ((T143_54 i : Coordinate 1) : Coordinate 1 ⧸ reps rK143)) :=
  repsInj_of_reduceAux rK143 T143_54 (by decide)

theorem hcardT143_54 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK143 ⟨54, by decide⟩ R143 hpxR143 hcardq143 (by decide)).symm

/-- **Cell (143, 54).** -/
theorem cell143_54 (e : List (ZMod 25)) (heK : charOK (basisAt rK143) e = true)
    (h : ↥(reps (⟨54, by decide⟩ : Fin 148))) :
    species (reps (⟨54, by decide⟩ : Fin 148)) h (basisElt (reps rK143) (charOfVec rK143 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK143 e (h : Coordinate 1) T143_54 i :=
  species_entry_eq_sum rK143 ⟨54, by decide⟩ e heK h T143_54 hfix143_54 hinj143_54 hcardT143_54
    (fun i => conj_mem_of_fixedPoints (reps ⟨54, by decide⟩) (reps rK143) (T143_54 i) (hfix143_54 i) h)

/-! ## Cell (143, 95): |T| = 5 -/

def T143_95list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T143_95 : Fin 5 → Coordinate 1 := fun i => T143_95list.getD i.val (0,0,0,0,0)

theorem hfix143_95 : ∀ i, ((T143_95 i : Coordinate 1) : Coordinate 1 ⧸ reps rK143)
    ∈ fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143) :=
  repsFix_of_siftB rK143 ⟨95, by decide⟩ T143_95 (by decide)

theorem hinj143_95 : Function.Injective
    (fun i => ((T143_95 i : Coordinate 1) : Coordinate 1 ⧸ reps rK143)) :=
  repsInj_of_reduceAux rK143 T143_95 (by decide)

theorem hcardT143_95 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK143 ⟨95, by decide⟩ R143 hpxR143 hcardq143 (by decide)).symm

/-- **Cell (143, 95).** -/
theorem cell143_95 (e : List (ZMod 25)) (heK : charOK (basisAt rK143) e = true)
    (h : ↥(reps (⟨95, by decide⟩ : Fin 148))) :
    species (reps (⟨95, by decide⟩ : Fin 148)) h (basisElt (reps rK143) (charOfVec rK143 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK143 e (h : Coordinate 1) T143_95 i :=
  species_entry_eq_sum rK143 ⟨95, by decide⟩ e heK h T143_95 hfix143_95 hinj143_95 hcardT143_95
    (fun i => conj_mem_of_fixedPoints (reps ⟨95, by decide⟩) (reps rK143) (T143_95 i) (hfix143_95 i) h)

/-! ## Cell (143, 96): |T| = 5 -/

def T143_96list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T143_96 : Fin 5 → Coordinate 1 := fun i => T143_96list.getD i.val (0,0,0,0,0)

theorem hfix143_96 : ∀ i, ((T143_96 i : Coordinate 1) : Coordinate 1 ⧸ reps rK143)
    ∈ fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143) :=
  repsFix_of_siftB rK143 ⟨96, by decide⟩ T143_96 (by decide)

theorem hinj143_96 : Function.Injective
    (fun i => ((T143_96 i : Coordinate 1) : Coordinate 1 ⧸ reps rK143)) :=
  repsInj_of_reduceAux rK143 T143_96 (by decide)

theorem hcardT143_96 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK143 ⟨96, by decide⟩ R143 hpxR143 hcardq143 (by decide)).symm

/-- **Cell (143, 96).** -/
theorem cell143_96 (e : List (ZMod 25)) (heK : charOK (basisAt rK143) e = true)
    (h : ↥(reps (⟨96, by decide⟩ : Fin 148))) :
    species (reps (⟨96, by decide⟩ : Fin 148)) h (basisElt (reps rK143) (charOfVec rK143 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK143 e (h : Coordinate 1) T143_96 i :=
  species_entry_eq_sum rK143 ⟨96, by decide⟩ e heK h T143_96 hfix143_96 hinj143_96 hcardT143_96
    (fun i => conj_mem_of_fixedPoints (reps ⟨96, by decide⟩) (reps rK143) (T143_96 i) (hfix143_96 i) h)

/-! ## Cell (143, 97): |T| = 5 -/

def T143_97list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T143_97 : Fin 5 → Coordinate 1 := fun i => T143_97list.getD i.val (0,0,0,0,0)

theorem hfix143_97 : ∀ i, ((T143_97 i : Coordinate 1) : Coordinate 1 ⧸ reps rK143)
    ∈ fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143) :=
  repsFix_of_siftB rK143 ⟨97, by decide⟩ T143_97 (by decide)

theorem hinj143_97 : Function.Injective
    (fun i => ((T143_97 i : Coordinate 1) : Coordinate 1 ⧸ reps rK143)) :=
  repsInj_of_reduceAux rK143 T143_97 (by decide)

theorem hcardT143_97 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK143 ⟨97, by decide⟩ R143 hpxR143 hcardq143 (by decide)).symm

/-- **Cell (143, 97).** -/
theorem cell143_97 (e : List (ZMod 25)) (heK : charOK (basisAt rK143) e = true)
    (h : ↥(reps (⟨97, by decide⟩ : Fin 148))) :
    species (reps (⟨97, by decide⟩ : Fin 148)) h (basisElt (reps rK143) (charOfVec rK143 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK143 e (h : Coordinate 1) T143_97 i :=
  species_entry_eq_sum rK143 ⟨97, by decide⟩ e heK h T143_97 hfix143_97 hinj143_97 hcardT143_97
    (fun i => conj_mem_of_fixedPoints (reps ⟨97, by decide⟩) (reps rK143) (T143_97 i) (hfix143_97 i) h)

/-! ## Cell (143, 98): |T| = 5 -/

def T143_98list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T143_98 : Fin 5 → Coordinate 1 := fun i => T143_98list.getD i.val (0,0,0,0,0)

theorem hfix143_98 : ∀ i, ((T143_98 i : Coordinate 1) : Coordinate 1 ⧸ reps rK143)
    ∈ fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143) :=
  repsFix_of_siftB rK143 ⟨98, by decide⟩ T143_98 (by decide)

theorem hinj143_98 : Function.Injective
    (fun i => ((T143_98 i : Coordinate 1) : Coordinate 1 ⧸ reps rK143)) :=
  repsInj_of_reduceAux rK143 T143_98 (by decide)

theorem hcardT143_98 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK143 ⟨98, by decide⟩ R143 hpxR143 hcardq143 (by decide)).symm

/-- **Cell (143, 98).** -/
theorem cell143_98 (e : List (ZMod 25)) (heK : charOK (basisAt rK143) e = true)
    (h : ↥(reps (⟨98, by decide⟩ : Fin 148))) :
    species (reps (⟨98, by decide⟩ : Fin 148)) h (basisElt (reps rK143) (charOfVec rK143 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK143 e (h : Coordinate 1) T143_98 i :=
  species_entry_eq_sum rK143 ⟨98, by decide⟩ e heK h T143_98 hfix143_98 hinj143_98 hcardT143_98
    (fun i => conj_mem_of_fixedPoints (reps ⟨98, by decide⟩) (reps rK143) (T143_98 i) (hfix143_98 i) h)

/-! ## Cell (143, 99): |T| = 5 -/

def T143_99list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T143_99 : Fin 5 → Coordinate 1 := fun i => T143_99list.getD i.val (0,0,0,0,0)

theorem hfix143_99 : ∀ i, ((T143_99 i : Coordinate 1) : Coordinate 1 ⧸ reps rK143)
    ∈ fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143) :=
  repsFix_of_siftB rK143 ⟨99, by decide⟩ T143_99 (by decide)

theorem hinj143_99 : Function.Injective
    (fun i => ((T143_99 i : Coordinate 1) : Coordinate 1 ⧸ reps rK143)) :=
  repsInj_of_reduceAux rK143 T143_99 (by decide)

theorem hcardT143_99 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK143 ⟨99, by decide⟩ R143 hpxR143 hcardq143 (by decide)).symm

/-- **Cell (143, 99).** -/
theorem cell143_99 (e : List (ZMod 25)) (heK : charOK (basisAt rK143) e = true)
    (h : ↥(reps (⟨99, by decide⟩ : Fin 148))) :
    species (reps (⟨99, by decide⟩ : Fin 148)) h (basisElt (reps rK143) (charOfVec rK143 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK143 e (h : Coordinate 1) T143_99 i :=
  species_entry_eq_sum rK143 ⟨99, by decide⟩ e heK h T143_99 hfix143_99 hinj143_99 hcardT143_99
    (fun i => conj_mem_of_fixedPoints (reps ⟨99, by decide⟩) (reps rK143) (T143_99 i) (hfix143_99 i) h)

/-! ## Cell (143, 115): |T| = 5 -/

def T143_115list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T143_115 : Fin 5 → Coordinate 1 := fun i => T143_115list.getD i.val (0,0,0,0,0)

theorem hfix143_115 : ∀ i, ((T143_115 i : Coordinate 1) : Coordinate 1 ⧸ reps rK143)
    ∈ fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143) :=
  repsFix_of_siftB rK143 ⟨115, by decide⟩ T143_115 (by decide)

theorem hinj143_115 : Function.Injective
    (fun i => ((T143_115 i : Coordinate 1) : Coordinate 1 ⧸ reps rK143)) :=
  repsInj_of_reduceAux rK143 T143_115 (by decide)

theorem hcardT143_115 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK143 ⟨115, by decide⟩ R143 hpxR143 hcardq143 (by decide)).symm

/-- **Cell (143, 115).** -/
theorem cell143_115 (e : List (ZMod 25)) (heK : charOK (basisAt rK143) e = true)
    (h : ↥(reps (⟨115, by decide⟩ : Fin 148))) :
    species (reps (⟨115, by decide⟩ : Fin 148)) h (basisElt (reps rK143) (charOfVec rK143 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK143 e (h : Coordinate 1) T143_115 i :=
  species_entry_eq_sum rK143 ⟨115, by decide⟩ e heK h T143_115 hfix143_115 hinj143_115 hcardT143_115
    (fun i => conj_mem_of_fixedPoints (reps ⟨115, by decide⟩) (reps rK143) (T143_115 i) (hfix143_115 i) h)

/-! ## Cell (143, 143): |T| = 5 -/

def T143_143list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T143_143 : Fin 5 → Coordinate 1 := fun i => T143_143list.getD i.val (0,0,0,0,0)

theorem hfix143_143 : ∀ i, ((T143_143 i : Coordinate 1) : Coordinate 1 ⧸ reps rK143)
    ∈ fixedPoints (reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143) :=
  repsFix_of_siftB rK143 ⟨143, by decide⟩ T143_143 (by decide)

theorem hinj143_143 : Function.Injective
    (fun i => ((T143_143 i : Coordinate 1) : Coordinate 1 ⧸ reps rK143)) :=
  repsInj_of_reduceAux rK143 T143_143 (by decide)

theorem hcardT143_143 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK143 ⟨143, by decide⟩ R143 hpxR143 hcardq143 (by decide)).symm

/-- **Cell (143, 143).** -/
theorem cell143_143 (e : List (ZMod 25)) (heK : charOK (basisAt rK143) e = true)
    (h : ↥(reps (⟨143, by decide⟩ : Fin 148))) :
    species (reps (⟨143, by decide⟩ : Fin 148)) h (basisElt (reps rK143) (charOfVec rK143 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK143 e (h : Coordinate 1) T143_143 i :=
  species_entry_eq_sum rK143 ⟨143, by decide⟩ e heK h T143_143 hfix143_143 hinj143_143 hcardT143_143
    (fun i => conj_mem_of_fixedPoints (reps ⟨143, by decide⟩) (reps rK143) (T143_143 i) (hfix143_143 i) h)

namespace Q2

def R143_2 : Fin 5 → Coordinate 2 := fun i => R143list.getD i.val (0,0,0,0,0)
theorem hpxR143_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK143) (R143_2 i)) := by decide
theorem hcardq143_2 : Nat.card (Coordinate 2 ⧸ reps rK143) = 5 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (143, 0) twin -/

def T143_0_2 : Fin 5 → Coordinate 2 := fun i => T143_0list.getD i.val (0,0,0,0,0)

theorem hfix143_0_2 : ∀ i, ((T143_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK143)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK143) :=
  repsFix_of_siftB2 rK143 ⟨0, by decide⟩ T143_0_2 (by decide)

theorem hinj143_0_2 : Function.Injective
    (fun i => ((T143_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK143)) :=
  repsInj_of_reduceAux2 rK143 T143_0_2 (by decide)

theorem hcardT143_0_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK143)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK143 ⟨0, by decide⟩ R143_2 hpxR143_2 hcardq143_2 (by decide)).symm

/-- **Cell (143, 0) twin (q=2).** -/
theorem cell143_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK143) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK143) (charOfVec2 rK143 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK143 e (h : Coordinate 2) T143_0_2 i :=
  species_entry_eq_sum rK143 ⟨0, by decide⟩ e heK h T143_0_2 hfix143_0_2 hinj143_0_2 hcardT143_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK143) (T143_0_2 i) (hfix143_0_2 i) h)

/-! ### Cell (143, 10) twin -/

def T143_10_2 : Fin 5 → Coordinate 2 := fun i => T143_10list.getD i.val (0,0,0,0,0)

theorem hfix143_10_2 : ∀ i, ((T143_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK143)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK143) :=
  repsFix_of_siftB2 rK143 ⟨10, by decide⟩ T143_10_2 (by decide)

theorem hinj143_10_2 : Function.Injective
    (fun i => ((T143_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK143)) :=
  repsInj_of_reduceAux2 rK143 T143_10_2 (by decide)

theorem hcardT143_10_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK143)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK143 ⟨10, by decide⟩ R143_2 hpxR143_2 hcardq143_2 (by decide)).symm

/-- **Cell (143, 10) twin (q=2).** -/
theorem cell143_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK143) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK143) (charOfVec2 rK143 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK143 e (h : Coordinate 2) T143_10_2 i :=
  species_entry_eq_sum rK143 ⟨10, by decide⟩ e heK h T143_10_2 hfix143_10_2 hinj143_10_2 hcardT143_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK143) (T143_10_2 i) (hfix143_10_2 i) h)

/-! ### Cell (143, 11) twin -/

def T143_11_2 : Fin 5 → Coordinate 2 := fun i => T143_11list.getD i.val (0,0,0,0,0)

theorem hfix143_11_2 : ∀ i, ((T143_11_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK143)
    ∈ fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK143) :=
  repsFix_of_siftB2 rK143 ⟨11, by decide⟩ T143_11_2 (by decide)

theorem hinj143_11_2 : Function.Injective
    (fun i => ((T143_11_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK143)) :=
  repsInj_of_reduceAux2 rK143 T143_11_2 (by decide)

theorem hcardT143_11_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK143)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK143 ⟨11, by decide⟩ R143_2 hpxR143_2 hcardq143_2 (by decide)).symm

/-- **Cell (143, 11) twin (q=2).** -/
theorem cell143_11_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK143) e = true)
    (h : ↥(reps (⟨11, by decide⟩ : Fin 148))) :
    species (reps (⟨11, by decide⟩ : Fin 148)) h (basisElt (reps rK143) (charOfVec2 rK143 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK143 e (h : Coordinate 2) T143_11_2 i :=
  species_entry_eq_sum rK143 ⟨11, by decide⟩ e heK h T143_11_2 hfix143_11_2 hinj143_11_2 hcardT143_11_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨11, by decide⟩) (reps rK143) (T143_11_2 i) (hfix143_11_2 i) h)

/-! ### Cell (143, 12) twin -/

def T143_12_2 : Fin 5 → Coordinate 2 := fun i => T143_12list.getD i.val (0,0,0,0,0)

theorem hfix143_12_2 : ∀ i, ((T143_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK143)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK143) :=
  repsFix_of_siftB2 rK143 ⟨12, by decide⟩ T143_12_2 (by decide)

theorem hinj143_12_2 : Function.Injective
    (fun i => ((T143_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK143)) :=
  repsInj_of_reduceAux2 rK143 T143_12_2 (by decide)

theorem hcardT143_12_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK143)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK143 ⟨12, by decide⟩ R143_2 hpxR143_2 hcardq143_2 (by decide)).symm

/-- **Cell (143, 12) twin (q=2).** -/
theorem cell143_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK143) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK143) (charOfVec2 rK143 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK143 e (h : Coordinate 2) T143_12_2 i :=
  species_entry_eq_sum rK143 ⟨12, by decide⟩ e heK h T143_12_2 hfix143_12_2 hinj143_12_2 hcardT143_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK143) (T143_12_2 i) (hfix143_12_2 i) h)

/-! ### Cell (143, 33) twin -/

def T143_33_2 : Fin 5 → Coordinate 2 := fun i => T143_33list.getD i.val (0,0,0,0,0)

theorem hfix143_33_2 : ∀ i, ((T143_33_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK143)
    ∈ fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK143) :=
  repsFix_of_siftB2 rK143 ⟨33, by decide⟩ T143_33_2 (by decide)

theorem hinj143_33_2 : Function.Injective
    (fun i => ((T143_33_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK143)) :=
  repsInj_of_reduceAux2 rK143 T143_33_2 (by decide)

theorem hcardT143_33_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK143)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK143 ⟨33, by decide⟩ R143_2 hpxR143_2 hcardq143_2 (by decide)).symm

/-- **Cell (143, 33) twin (q=2).** -/
theorem cell143_33_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK143) e = true)
    (h : ↥(reps (⟨33, by decide⟩ : Fin 148))) :
    species (reps (⟨33, by decide⟩ : Fin 148)) h (basisElt (reps rK143) (charOfVec2 rK143 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK143 e (h : Coordinate 2) T143_33_2 i :=
  species_entry_eq_sum rK143 ⟨33, by decide⟩ e heK h T143_33_2 hfix143_33_2 hinj143_33_2 hcardT143_33_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨33, by decide⟩) (reps rK143) (T143_33_2 i) (hfix143_33_2 i) h)

/-! ### Cell (143, 34) twin -/

def T143_34_2 : Fin 5 → Coordinate 2 := fun i => T143_34list.getD i.val (0,0,0,0,0)

theorem hfix143_34_2 : ∀ i, ((T143_34_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK143)
    ∈ fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK143) :=
  repsFix_of_siftB2 rK143 ⟨34, by decide⟩ T143_34_2 (by decide)

theorem hinj143_34_2 : Function.Injective
    (fun i => ((T143_34_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK143)) :=
  repsInj_of_reduceAux2 rK143 T143_34_2 (by decide)

theorem hcardT143_34_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK143)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK143 ⟨34, by decide⟩ R143_2 hpxR143_2 hcardq143_2 (by decide)).symm

/-- **Cell (143, 34) twin (q=2).** -/
theorem cell143_34_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK143) e = true)
    (h : ↥(reps (⟨34, by decide⟩ : Fin 148))) :
    species (reps (⟨34, by decide⟩ : Fin 148)) h (basisElt (reps rK143) (charOfVec2 rK143 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK143 e (h : Coordinate 2) T143_34_2 i :=
  species_entry_eq_sum rK143 ⟨34, by decide⟩ e heK h T143_34_2 hfix143_34_2 hinj143_34_2 hcardT143_34_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨34, by decide⟩) (reps rK143) (T143_34_2 i) (hfix143_34_2 i) h)

/-! ### Cell (143, 35) twin -/

def T143_35_2 : Fin 5 → Coordinate 2 := fun i => T143_35list.getD i.val (0,0,0,0,0)

theorem hfix143_35_2 : ∀ i, ((T143_35_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK143)
    ∈ fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK143) :=
  repsFix_of_siftB2 rK143 ⟨35, by decide⟩ T143_35_2 (by decide)

theorem hinj143_35_2 : Function.Injective
    (fun i => ((T143_35_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK143)) :=
  repsInj_of_reduceAux2 rK143 T143_35_2 (by decide)

theorem hcardT143_35_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK143)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK143 ⟨35, by decide⟩ R143_2 hpxR143_2 hcardq143_2 (by decide)).symm

/-- **Cell (143, 35) twin (q=2).** -/
theorem cell143_35_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK143) e = true)
    (h : ↥(reps (⟨35, by decide⟩ : Fin 148))) :
    species (reps (⟨35, by decide⟩ : Fin 148)) h (basisElt (reps rK143) (charOfVec2 rK143 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK143 e (h : Coordinate 2) T143_35_2 i :=
  species_entry_eq_sum rK143 ⟨35, by decide⟩ e heK h T143_35_2 hfix143_35_2 hinj143_35_2 hcardT143_35_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨35, by decide⟩) (reps rK143) (T143_35_2 i) (hfix143_35_2 i) h)

/-! ### Cell (143, 36) twin -/

def T143_36_2 : Fin 5 → Coordinate 2 := fun i => T143_36list.getD i.val (0,0,0,0,0)

theorem hfix143_36_2 : ∀ i, ((T143_36_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK143)
    ∈ fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK143) :=
  repsFix_of_siftB2 rK143 ⟨36, by decide⟩ T143_36_2 (by decide)

theorem hinj143_36_2 : Function.Injective
    (fun i => ((T143_36_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK143)) :=
  repsInj_of_reduceAux2 rK143 T143_36_2 (by decide)

theorem hcardT143_36_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK143)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK143 ⟨36, by decide⟩ R143_2 hpxR143_2 hcardq143_2 (by decide)).symm

/-- **Cell (143, 36) twin (q=2).** -/
theorem cell143_36_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK143) e = true)
    (h : ↥(reps (⟨36, by decide⟩ : Fin 148))) :
    species (reps (⟨36, by decide⟩ : Fin 148)) h (basisElt (reps rK143) (charOfVec2 rK143 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK143 e (h : Coordinate 2) T143_36_2 i :=
  species_entry_eq_sum rK143 ⟨36, by decide⟩ e heK h T143_36_2 hfix143_36_2 hinj143_36_2 hcardT143_36_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨36, by decide⟩) (reps rK143) (T143_36_2 i) (hfix143_36_2 i) h)

/-! ### Cell (143, 37) twin -/

def T143_37_2 : Fin 5 → Coordinate 2 := fun i => T143_37list.getD i.val (0,0,0,0,0)

theorem hfix143_37_2 : ∀ i, ((T143_37_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK143)
    ∈ fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK143) :=
  repsFix_of_siftB2 rK143 ⟨37, by decide⟩ T143_37_2 (by decide)

theorem hinj143_37_2 : Function.Injective
    (fun i => ((T143_37_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK143)) :=
  repsInj_of_reduceAux2 rK143 T143_37_2 (by decide)

theorem hcardT143_37_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK143)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK143 ⟨37, by decide⟩ R143_2 hpxR143_2 hcardq143_2 (by decide)).symm

/-- **Cell (143, 37) twin (q=2).** -/
theorem cell143_37_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK143) e = true)
    (h : ↥(reps (⟨37, by decide⟩ : Fin 148))) :
    species (reps (⟨37, by decide⟩ : Fin 148)) h (basisElt (reps rK143) (charOfVec2 rK143 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK143 e (h : Coordinate 2) T143_37_2 i :=
  species_entry_eq_sum rK143 ⟨37, by decide⟩ e heK h T143_37_2 hfix143_37_2 hinj143_37_2 hcardT143_37_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨37, by decide⟩) (reps rK143) (T143_37_2 i) (hfix143_37_2 i) h)

/-! ### Cell (143, 53) twin -/

def T143_53_2 : Fin 5 → Coordinate 2 := fun i => T143_53list.getD i.val (0,0,0,0,0)

theorem hfix143_53_2 : ∀ i, ((T143_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK143)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK143) :=
  repsFix_of_siftB2 rK143 ⟨53, by decide⟩ T143_53_2 (by decide)

theorem hinj143_53_2 : Function.Injective
    (fun i => ((T143_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK143)) :=
  repsInj_of_reduceAux2 rK143 T143_53_2 (by decide)

theorem hcardT143_53_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK143)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK143 ⟨53, by decide⟩ R143_2 hpxR143_2 hcardq143_2 (by decide)).symm

/-- **Cell (143, 53) twin (q=2).** -/
theorem cell143_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK143) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK143) (charOfVec2 rK143 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK143 e (h : Coordinate 2) T143_53_2 i :=
  species_entry_eq_sum rK143 ⟨53, by decide⟩ e heK h T143_53_2 hfix143_53_2 hinj143_53_2 hcardT143_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK143) (T143_53_2 i) (hfix143_53_2 i) h)

/-! ### Cell (143, 54) twin -/

def T143_54_2 : Fin 5 → Coordinate 2 := fun i => T143_54list.getD i.val (0,0,0,0,0)

theorem hfix143_54_2 : ∀ i, ((T143_54_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK143)
    ∈ fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK143) :=
  repsFix_of_siftB2 rK143 ⟨54, by decide⟩ T143_54_2 (by decide)

theorem hinj143_54_2 : Function.Injective
    (fun i => ((T143_54_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK143)) :=
  repsInj_of_reduceAux2 rK143 T143_54_2 (by decide)

theorem hcardT143_54_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK143)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK143 ⟨54, by decide⟩ R143_2 hpxR143_2 hcardq143_2 (by decide)).symm

/-- **Cell (143, 54) twin (q=2).** -/
theorem cell143_54_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK143) e = true)
    (h : ↥(reps (⟨54, by decide⟩ : Fin 148))) :
    species (reps (⟨54, by decide⟩ : Fin 148)) h (basisElt (reps rK143) (charOfVec2 rK143 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK143 e (h : Coordinate 2) T143_54_2 i :=
  species_entry_eq_sum rK143 ⟨54, by decide⟩ e heK h T143_54_2 hfix143_54_2 hinj143_54_2 hcardT143_54_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨54, by decide⟩) (reps rK143) (T143_54_2 i) (hfix143_54_2 i) h)

/-! ### Cell (143, 95) twin -/

def T143_95_2 : Fin 5 → Coordinate 2 := fun i => T143_95list.getD i.val (0,0,0,0,0)

theorem hfix143_95_2 : ∀ i, ((T143_95_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK143)
    ∈ fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK143) :=
  repsFix_of_siftB2 rK143 ⟨95, by decide⟩ T143_95_2 (by decide)

theorem hinj143_95_2 : Function.Injective
    (fun i => ((T143_95_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK143)) :=
  repsInj_of_reduceAux2 rK143 T143_95_2 (by decide)

theorem hcardT143_95_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK143)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK143 ⟨95, by decide⟩ R143_2 hpxR143_2 hcardq143_2 (by decide)).symm

/-- **Cell (143, 95) twin (q=2).** -/
theorem cell143_95_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK143) e = true)
    (h : ↥(reps (⟨95, by decide⟩ : Fin 148))) :
    species (reps (⟨95, by decide⟩ : Fin 148)) h (basisElt (reps rK143) (charOfVec2 rK143 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK143 e (h : Coordinate 2) T143_95_2 i :=
  species_entry_eq_sum rK143 ⟨95, by decide⟩ e heK h T143_95_2 hfix143_95_2 hinj143_95_2 hcardT143_95_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨95, by decide⟩) (reps rK143) (T143_95_2 i) (hfix143_95_2 i) h)

/-! ### Cell (143, 96) twin -/

def T143_96_2 : Fin 5 → Coordinate 2 := fun i => T143_96list.getD i.val (0,0,0,0,0)

theorem hfix143_96_2 : ∀ i, ((T143_96_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK143)
    ∈ fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK143) :=
  repsFix_of_siftB2 rK143 ⟨96, by decide⟩ T143_96_2 (by decide)

theorem hinj143_96_2 : Function.Injective
    (fun i => ((T143_96_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK143)) :=
  repsInj_of_reduceAux2 rK143 T143_96_2 (by decide)

theorem hcardT143_96_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK143)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK143 ⟨96, by decide⟩ R143_2 hpxR143_2 hcardq143_2 (by decide)).symm

/-- **Cell (143, 96) twin (q=2).** -/
theorem cell143_96_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK143) e = true)
    (h : ↥(reps (⟨96, by decide⟩ : Fin 148))) :
    species (reps (⟨96, by decide⟩ : Fin 148)) h (basisElt (reps rK143) (charOfVec2 rK143 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK143 e (h : Coordinate 2) T143_96_2 i :=
  species_entry_eq_sum rK143 ⟨96, by decide⟩ e heK h T143_96_2 hfix143_96_2 hinj143_96_2 hcardT143_96_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨96, by decide⟩) (reps rK143) (T143_96_2 i) (hfix143_96_2 i) h)

/-! ### Cell (143, 97) twin -/

def T143_97_2 : Fin 5 → Coordinate 2 := fun i => T143_97list.getD i.val (0,0,0,0,0)

theorem hfix143_97_2 : ∀ i, ((T143_97_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK143)
    ∈ fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK143) :=
  repsFix_of_siftB2 rK143 ⟨97, by decide⟩ T143_97_2 (by decide)

theorem hinj143_97_2 : Function.Injective
    (fun i => ((T143_97_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK143)) :=
  repsInj_of_reduceAux2 rK143 T143_97_2 (by decide)

theorem hcardT143_97_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK143)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK143 ⟨97, by decide⟩ R143_2 hpxR143_2 hcardq143_2 (by decide)).symm

/-- **Cell (143, 97) twin (q=2).** -/
theorem cell143_97_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK143) e = true)
    (h : ↥(reps (⟨97, by decide⟩ : Fin 148))) :
    species (reps (⟨97, by decide⟩ : Fin 148)) h (basisElt (reps rK143) (charOfVec2 rK143 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK143 e (h : Coordinate 2) T143_97_2 i :=
  species_entry_eq_sum rK143 ⟨97, by decide⟩ e heK h T143_97_2 hfix143_97_2 hinj143_97_2 hcardT143_97_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨97, by decide⟩) (reps rK143) (T143_97_2 i) (hfix143_97_2 i) h)

/-! ### Cell (143, 98) twin -/

def T143_98_2 : Fin 5 → Coordinate 2 := fun i => T143_98list.getD i.val (0,0,0,0,0)

theorem hfix143_98_2 : ∀ i, ((T143_98_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK143)
    ∈ fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK143) :=
  repsFix_of_siftB2 rK143 ⟨98, by decide⟩ T143_98_2 (by decide)

theorem hinj143_98_2 : Function.Injective
    (fun i => ((T143_98_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK143)) :=
  repsInj_of_reduceAux2 rK143 T143_98_2 (by decide)

theorem hcardT143_98_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK143)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK143 ⟨98, by decide⟩ R143_2 hpxR143_2 hcardq143_2 (by decide)).symm

/-- **Cell (143, 98) twin (q=2).** -/
theorem cell143_98_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK143) e = true)
    (h : ↥(reps (⟨98, by decide⟩ : Fin 148))) :
    species (reps (⟨98, by decide⟩ : Fin 148)) h (basisElt (reps rK143) (charOfVec2 rK143 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK143 e (h : Coordinate 2) T143_98_2 i :=
  species_entry_eq_sum rK143 ⟨98, by decide⟩ e heK h T143_98_2 hfix143_98_2 hinj143_98_2 hcardT143_98_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨98, by decide⟩) (reps rK143) (T143_98_2 i) (hfix143_98_2 i) h)

/-! ### Cell (143, 99) twin -/

def T143_99_2 : Fin 5 → Coordinate 2 := fun i => T143_99list.getD i.val (0,0,0,0,0)

theorem hfix143_99_2 : ∀ i, ((T143_99_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK143)
    ∈ fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK143) :=
  repsFix_of_siftB2 rK143 ⟨99, by decide⟩ T143_99_2 (by decide)

theorem hinj143_99_2 : Function.Injective
    (fun i => ((T143_99_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK143)) :=
  repsInj_of_reduceAux2 rK143 T143_99_2 (by decide)

theorem hcardT143_99_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK143)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK143 ⟨99, by decide⟩ R143_2 hpxR143_2 hcardq143_2 (by decide)).symm

/-- **Cell (143, 99) twin (q=2).** -/
theorem cell143_99_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK143) e = true)
    (h : ↥(reps (⟨99, by decide⟩ : Fin 148))) :
    species (reps (⟨99, by decide⟩ : Fin 148)) h (basisElt (reps rK143) (charOfVec2 rK143 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK143 e (h : Coordinate 2) T143_99_2 i :=
  species_entry_eq_sum rK143 ⟨99, by decide⟩ e heK h T143_99_2 hfix143_99_2 hinj143_99_2 hcardT143_99_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨99, by decide⟩) (reps rK143) (T143_99_2 i) (hfix143_99_2 i) h)

/-! ### Cell (143, 115) twin -/

def T143_115_2 : Fin 5 → Coordinate 2 := fun i => T143_115list.getD i.val (0,0,0,0,0)

theorem hfix143_115_2 : ∀ i, ((T143_115_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK143)
    ∈ fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK143) :=
  repsFix_of_siftB2 rK143 ⟨115, by decide⟩ T143_115_2 (by decide)

theorem hinj143_115_2 : Function.Injective
    (fun i => ((T143_115_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK143)) :=
  repsInj_of_reduceAux2 rK143 T143_115_2 (by decide)

theorem hcardT143_115_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK143)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK143 ⟨115, by decide⟩ R143_2 hpxR143_2 hcardq143_2 (by decide)).symm

/-- **Cell (143, 115) twin (q=2).** -/
theorem cell143_115_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK143) e = true)
    (h : ↥(reps (⟨115, by decide⟩ : Fin 148))) :
    species (reps (⟨115, by decide⟩ : Fin 148)) h (basisElt (reps rK143) (charOfVec2 rK143 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK143 e (h : Coordinate 2) T143_115_2 i :=
  species_entry_eq_sum rK143 ⟨115, by decide⟩ e heK h T143_115_2 hfix143_115_2 hinj143_115_2 hcardT143_115_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨115, by decide⟩) (reps rK143) (T143_115_2 i) (hfix143_115_2 i) h)

/-! ### Cell (143, 143) twin -/

def T143_143_2 : Fin 5 → Coordinate 2 := fun i => T143_143list.getD i.val (0,0,0,0,0)

theorem hfix143_143_2 : ∀ i, ((T143_143_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK143)
    ∈ fixedPoints (reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK143) :=
  repsFix_of_siftB2 rK143 ⟨143, by decide⟩ T143_143_2 (by decide)

theorem hinj143_143_2 : Function.Injective
    (fun i => ((T143_143_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK143)) :=
  repsInj_of_reduceAux2 rK143 T143_143_2 (by decide)

theorem hcardT143_143_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK143)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK143 ⟨143, by decide⟩ R143_2 hpxR143_2 hcardq143_2 (by decide)).symm

/-- **Cell (143, 143) twin (q=2).** -/
theorem cell143_143_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK143) e = true)
    (h : ↥(reps (⟨143, by decide⟩ : Fin 148))) :
    species (reps (⟨143, by decide⟩ : Fin 148)) h (basisElt (reps rK143) (charOfVec2 rK143 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK143 e (h : Coordinate 2) T143_143_2 i :=
  species_entry_eq_sum rK143 ⟨143, by decide⟩ e heK h T143_143_2 hfix143_143_2 hinj143_143_2 hcardT143_143_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨143, by decide⟩) (reps rK143) (T143_143_2 i) (hfix143_143_2 i) h)

end Q2

end LeanDring.P5Presentation
