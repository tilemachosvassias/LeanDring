/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, K-strata data (5^4 stratum, rK 144-145): certified per-cell species-entry instantiations, both
twins.

Covers K-classes 144, 145 (order-5^4 K, |R|=5).  For each nonzero `H`-column
(`(G/K)^H ≠ ∅`), the full coset transversal `R144..` and each `H`-fixed
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

/-! # K-class rK = 144  (|G/K| = 5) -/

def rK144 : Fin 148 := ⟨144, by decide⟩

def R144list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def R144 : Fin 5 → Coordinate 1 := fun i => R144list.getD i.val (0,0,0,0,0)

theorem hpxR144 : Function.Injective (fun i => reduceAux 1 (basisAt rK144) (R144 i)) := by decide
theorem hcardq144 : Nat.card (Coordinate 1 ⧸ reps rK144) = 5 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (144, 0): |T| = 5 -/

def T144_0list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T144_0 : Fin 5 → Coordinate 1 := fun i => T144_0list.getD i.val (0,0,0,0,0)

theorem hfix144_0 : ∀ i, ((T144_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK144)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144) :=
  repsFix_of_siftB rK144 ⟨0, by decide⟩ T144_0 (by decide)

theorem hinj144_0 : Function.Injective
    (fun i => ((T144_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK144)) :=
  repsInj_of_reduceAux rK144 T144_0 (by decide)

theorem hcardT144_0 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK144 ⟨0, by decide⟩ R144 hpxR144 hcardq144 (by decide)).symm

/-- **Cell (144, 0).** -/
theorem cell144_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK144) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK144) (charOfVec rK144 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK144 e (h : Coordinate 1) T144_0 i :=
  species_entry_eq_sum rK144 ⟨0, by decide⟩ e heK h T144_0 hfix144_0 hinj144_0 hcardT144_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK144) (T144_0 i) (hfix144_0 i) h)

/-! ## Cell (144, 10): |T| = 5 -/

def T144_10list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T144_10 : Fin 5 → Coordinate 1 := fun i => T144_10list.getD i.val (0,0,0,0,0)

theorem hfix144_10 : ∀ i, ((T144_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK144)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144) :=
  repsFix_of_siftB rK144 ⟨10, by decide⟩ T144_10 (by decide)

theorem hinj144_10 : Function.Injective
    (fun i => ((T144_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK144)) :=
  repsInj_of_reduceAux rK144 T144_10 (by decide)

theorem hcardT144_10 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK144 ⟨10, by decide⟩ R144 hpxR144 hcardq144 (by decide)).symm

/-- **Cell (144, 10).** -/
theorem cell144_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK144) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK144) (charOfVec rK144 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK144 e (h : Coordinate 1) T144_10 i :=
  species_entry_eq_sum rK144 ⟨10, by decide⟩ e heK h T144_10 hfix144_10 hinj144_10 hcardT144_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK144) (T144_10 i) (hfix144_10 i) h)

/-! ## Cell (144, 11): |T| = 5 -/

def T144_11list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T144_11 : Fin 5 → Coordinate 1 := fun i => T144_11list.getD i.val (0,0,0,0,0)

theorem hfix144_11 : ∀ i, ((T144_11 i : Coordinate 1) : Coordinate 1 ⧸ reps rK144)
    ∈ fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144) :=
  repsFix_of_siftB rK144 ⟨11, by decide⟩ T144_11 (by decide)

theorem hinj144_11 : Function.Injective
    (fun i => ((T144_11 i : Coordinate 1) : Coordinate 1 ⧸ reps rK144)) :=
  repsInj_of_reduceAux rK144 T144_11 (by decide)

theorem hcardT144_11 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK144 ⟨11, by decide⟩ R144 hpxR144 hcardq144 (by decide)).symm

/-- **Cell (144, 11).** -/
theorem cell144_11 (e : List (ZMod 25)) (heK : charOK (basisAt rK144) e = true)
    (h : ↥(reps (⟨11, by decide⟩ : Fin 148))) :
    species (reps (⟨11, by decide⟩ : Fin 148)) h (basisElt (reps rK144) (charOfVec rK144 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK144 e (h : Coordinate 1) T144_11 i :=
  species_entry_eq_sum rK144 ⟨11, by decide⟩ e heK h T144_11 hfix144_11 hinj144_11 hcardT144_11
    (fun i => conj_mem_of_fixedPoints (reps ⟨11, by decide⟩) (reps rK144) (T144_11 i) (hfix144_11 i) h)

/-! ## Cell (144, 12): |T| = 5 -/

def T144_12list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T144_12 : Fin 5 → Coordinate 1 := fun i => T144_12list.getD i.val (0,0,0,0,0)

theorem hfix144_12 : ∀ i, ((T144_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK144)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144) :=
  repsFix_of_siftB rK144 ⟨12, by decide⟩ T144_12 (by decide)

theorem hinj144_12 : Function.Injective
    (fun i => ((T144_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK144)) :=
  repsInj_of_reduceAux rK144 T144_12 (by decide)

theorem hcardT144_12 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK144 ⟨12, by decide⟩ R144 hpxR144 hcardq144 (by decide)).symm

/-- **Cell (144, 12).** -/
theorem cell144_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK144) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK144) (charOfVec rK144 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK144 e (h : Coordinate 1) T144_12 i :=
  species_entry_eq_sum rK144 ⟨12, by decide⟩ e heK h T144_12 hfix144_12 hinj144_12 hcardT144_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK144) (T144_12 i) (hfix144_12 i) h)

/-! ## Cell (144, 38): |T| = 5 -/

def T144_38list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T144_38 : Fin 5 → Coordinate 1 := fun i => T144_38list.getD i.val (0,0,0,0,0)

theorem hfix144_38 : ∀ i, ((T144_38 i : Coordinate 1) : Coordinate 1 ⧸ reps rK144)
    ∈ fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144) :=
  repsFix_of_siftB rK144 ⟨38, by decide⟩ T144_38 (by decide)

theorem hinj144_38 : Function.Injective
    (fun i => ((T144_38 i : Coordinate 1) : Coordinate 1 ⧸ reps rK144)) :=
  repsInj_of_reduceAux rK144 T144_38 (by decide)

theorem hcardT144_38 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK144 ⟨38, by decide⟩ R144 hpxR144 hcardq144 (by decide)).symm

/-- **Cell (144, 38).** -/
theorem cell144_38 (e : List (ZMod 25)) (heK : charOK (basisAt rK144) e = true)
    (h : ↥(reps (⟨38, by decide⟩ : Fin 148))) :
    species (reps (⟨38, by decide⟩ : Fin 148)) h (basisElt (reps rK144) (charOfVec rK144 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK144 e (h : Coordinate 1) T144_38 i :=
  species_entry_eq_sum rK144 ⟨38, by decide⟩ e heK h T144_38 hfix144_38 hinj144_38 hcardT144_38
    (fun i => conj_mem_of_fixedPoints (reps ⟨38, by decide⟩) (reps rK144) (T144_38 i) (hfix144_38 i) h)

/-! ## Cell (144, 39): |T| = 5 -/

def T144_39list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T144_39 : Fin 5 → Coordinate 1 := fun i => T144_39list.getD i.val (0,0,0,0,0)

theorem hfix144_39 : ∀ i, ((T144_39 i : Coordinate 1) : Coordinate 1 ⧸ reps rK144)
    ∈ fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144) :=
  repsFix_of_siftB rK144 ⟨39, by decide⟩ T144_39 (by decide)

theorem hinj144_39 : Function.Injective
    (fun i => ((T144_39 i : Coordinate 1) : Coordinate 1 ⧸ reps rK144)) :=
  repsInj_of_reduceAux rK144 T144_39 (by decide)

theorem hcardT144_39 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK144 ⟨39, by decide⟩ R144 hpxR144 hcardq144 (by decide)).symm

/-- **Cell (144, 39).** -/
theorem cell144_39 (e : List (ZMod 25)) (heK : charOK (basisAt rK144) e = true)
    (h : ↥(reps (⟨39, by decide⟩ : Fin 148))) :
    species (reps (⟨39, by decide⟩ : Fin 148)) h (basisElt (reps rK144) (charOfVec rK144 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK144 e (h : Coordinate 1) T144_39 i :=
  species_entry_eq_sum rK144 ⟨39, by decide⟩ e heK h T144_39 hfix144_39 hinj144_39 hcardT144_39
    (fun i => conj_mem_of_fixedPoints (reps ⟨39, by decide⟩) (reps rK144) (T144_39 i) (hfix144_39 i) h)

/-! ## Cell (144, 40): |T| = 5 -/

def T144_40list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T144_40 : Fin 5 → Coordinate 1 := fun i => T144_40list.getD i.val (0,0,0,0,0)

theorem hfix144_40 : ∀ i, ((T144_40 i : Coordinate 1) : Coordinate 1 ⧸ reps rK144)
    ∈ fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144) :=
  repsFix_of_siftB rK144 ⟨40, by decide⟩ T144_40 (by decide)

theorem hinj144_40 : Function.Injective
    (fun i => ((T144_40 i : Coordinate 1) : Coordinate 1 ⧸ reps rK144)) :=
  repsInj_of_reduceAux rK144 T144_40 (by decide)

theorem hcardT144_40 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK144 ⟨40, by decide⟩ R144 hpxR144 hcardq144 (by decide)).symm

/-- **Cell (144, 40).** -/
theorem cell144_40 (e : List (ZMod 25)) (heK : charOK (basisAt rK144) e = true)
    (h : ↥(reps (⟨40, by decide⟩ : Fin 148))) :
    species (reps (⟨40, by decide⟩ : Fin 148)) h (basisElt (reps rK144) (charOfVec rK144 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK144 e (h : Coordinate 1) T144_40 i :=
  species_entry_eq_sum rK144 ⟨40, by decide⟩ e heK h T144_40 hfix144_40 hinj144_40 hcardT144_40
    (fun i => conj_mem_of_fixedPoints (reps ⟨40, by decide⟩) (reps rK144) (T144_40 i) (hfix144_40 i) h)

/-! ## Cell (144, 41): |T| = 5 -/

def T144_41list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T144_41 : Fin 5 → Coordinate 1 := fun i => T144_41list.getD i.val (0,0,0,0,0)

theorem hfix144_41 : ∀ i, ((T144_41 i : Coordinate 1) : Coordinate 1 ⧸ reps rK144)
    ∈ fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144) :=
  repsFix_of_siftB rK144 ⟨41, by decide⟩ T144_41 (by decide)

theorem hinj144_41 : Function.Injective
    (fun i => ((T144_41 i : Coordinate 1) : Coordinate 1 ⧸ reps rK144)) :=
  repsInj_of_reduceAux rK144 T144_41 (by decide)

theorem hcardT144_41 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK144 ⟨41, by decide⟩ R144 hpxR144 hcardq144 (by decide)).symm

/-- **Cell (144, 41).** -/
theorem cell144_41 (e : List (ZMod 25)) (heK : charOK (basisAt rK144) e = true)
    (h : ↥(reps (⟨41, by decide⟩ : Fin 148))) :
    species (reps (⟨41, by decide⟩ : Fin 148)) h (basisElt (reps rK144) (charOfVec rK144 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK144 e (h : Coordinate 1) T144_41 i :=
  species_entry_eq_sum rK144 ⟨41, by decide⟩ e heK h T144_41 hfix144_41 hinj144_41 hcardT144_41
    (fun i => conj_mem_of_fixedPoints (reps ⟨41, by decide⟩) (reps rK144) (T144_41 i) (hfix144_41 i) h)

/-! ## Cell (144, 42): |T| = 5 -/

def T144_42list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T144_42 : Fin 5 → Coordinate 1 := fun i => T144_42list.getD i.val (0,0,0,0,0)

theorem hfix144_42 : ∀ i, ((T144_42 i : Coordinate 1) : Coordinate 1 ⧸ reps rK144)
    ∈ fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144) :=
  repsFix_of_siftB rK144 ⟨42, by decide⟩ T144_42 (by decide)

theorem hinj144_42 : Function.Injective
    (fun i => ((T144_42 i : Coordinate 1) : Coordinate 1 ⧸ reps rK144)) :=
  repsInj_of_reduceAux rK144 T144_42 (by decide)

theorem hcardT144_42 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK144 ⟨42, by decide⟩ R144 hpxR144 hcardq144 (by decide)).symm

/-- **Cell (144, 42).** -/
theorem cell144_42 (e : List (ZMod 25)) (heK : charOK (basisAt rK144) e = true)
    (h : ↥(reps (⟨42, by decide⟩ : Fin 148))) :
    species (reps (⟨42, by decide⟩ : Fin 148)) h (basisElt (reps rK144) (charOfVec rK144 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK144 e (h : Coordinate 1) T144_42 i :=
  species_entry_eq_sum rK144 ⟨42, by decide⟩ e heK h T144_42 hfix144_42 hinj144_42 hcardT144_42
    (fun i => conj_mem_of_fixedPoints (reps ⟨42, by decide⟩) (reps rK144) (T144_42 i) (hfix144_42 i) h)

/-! ## Cell (144, 53): |T| = 5 -/

def T144_53list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T144_53 : Fin 5 → Coordinate 1 := fun i => T144_53list.getD i.val (0,0,0,0,0)

theorem hfix144_53 : ∀ i, ((T144_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK144)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144) :=
  repsFix_of_siftB rK144 ⟨53, by decide⟩ T144_53 (by decide)

theorem hinj144_53 : Function.Injective
    (fun i => ((T144_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK144)) :=
  repsInj_of_reduceAux rK144 T144_53 (by decide)

theorem hcardT144_53 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK144 ⟨53, by decide⟩ R144 hpxR144 hcardq144 (by decide)).symm

/-- **Cell (144, 53).** -/
theorem cell144_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK144) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK144) (charOfVec rK144 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK144 e (h : Coordinate 1) T144_53 i :=
  species_entry_eq_sum rK144 ⟨53, by decide⟩ e heK h T144_53 hfix144_53 hinj144_53 hcardT144_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK144) (T144_53 i) (hfix144_53 i) h)

/-! ## Cell (144, 54): |T| = 5 -/

def T144_54list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T144_54 : Fin 5 → Coordinate 1 := fun i => T144_54list.getD i.val (0,0,0,0,0)

theorem hfix144_54 : ∀ i, ((T144_54 i : Coordinate 1) : Coordinate 1 ⧸ reps rK144)
    ∈ fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144) :=
  repsFix_of_siftB rK144 ⟨54, by decide⟩ T144_54 (by decide)

theorem hinj144_54 : Function.Injective
    (fun i => ((T144_54 i : Coordinate 1) : Coordinate 1 ⧸ reps rK144)) :=
  repsInj_of_reduceAux rK144 T144_54 (by decide)

theorem hcardT144_54 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK144 ⟨54, by decide⟩ R144 hpxR144 hcardq144 (by decide)).symm

/-- **Cell (144, 54).** -/
theorem cell144_54 (e : List (ZMod 25)) (heK : charOK (basisAt rK144) e = true)
    (h : ↥(reps (⟨54, by decide⟩ : Fin 148))) :
    species (reps (⟨54, by decide⟩ : Fin 148)) h (basisElt (reps rK144) (charOfVec rK144 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK144 e (h : Coordinate 1) T144_54 i :=
  species_entry_eq_sum rK144 ⟨54, by decide⟩ e heK h T144_54 hfix144_54 hinj144_54 hcardT144_54
    (fun i => conj_mem_of_fixedPoints (reps ⟨54, by decide⟩) (reps rK144) (T144_54 i) (hfix144_54 i) h)

/-! ## Cell (144, 100): |T| = 5 -/

def T144_100list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T144_100 : Fin 5 → Coordinate 1 := fun i => T144_100list.getD i.val (0,0,0,0,0)

theorem hfix144_100 : ∀ i, ((T144_100 i : Coordinate 1) : Coordinate 1 ⧸ reps rK144)
    ∈ fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144) :=
  repsFix_of_siftB rK144 ⟨100, by decide⟩ T144_100 (by decide)

theorem hinj144_100 : Function.Injective
    (fun i => ((T144_100 i : Coordinate 1) : Coordinate 1 ⧸ reps rK144)) :=
  repsInj_of_reduceAux rK144 T144_100 (by decide)

theorem hcardT144_100 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK144 ⟨100, by decide⟩ R144 hpxR144 hcardq144 (by decide)).symm

/-- **Cell (144, 100).** -/
theorem cell144_100 (e : List (ZMod 25)) (heK : charOK (basisAt rK144) e = true)
    (h : ↥(reps (⟨100, by decide⟩ : Fin 148))) :
    species (reps (⟨100, by decide⟩ : Fin 148)) h (basisElt (reps rK144) (charOfVec rK144 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK144 e (h : Coordinate 1) T144_100 i :=
  species_entry_eq_sum rK144 ⟨100, by decide⟩ e heK h T144_100 hfix144_100 hinj144_100 hcardT144_100
    (fun i => conj_mem_of_fixedPoints (reps ⟨100, by decide⟩) (reps rK144) (T144_100 i) (hfix144_100 i) h)

/-! ## Cell (144, 101): |T| = 5 -/

def T144_101list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T144_101 : Fin 5 → Coordinate 1 := fun i => T144_101list.getD i.val (0,0,0,0,0)

theorem hfix144_101 : ∀ i, ((T144_101 i : Coordinate 1) : Coordinate 1 ⧸ reps rK144)
    ∈ fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144) :=
  repsFix_of_siftB rK144 ⟨101, by decide⟩ T144_101 (by decide)

theorem hinj144_101 : Function.Injective
    (fun i => ((T144_101 i : Coordinate 1) : Coordinate 1 ⧸ reps rK144)) :=
  repsInj_of_reduceAux rK144 T144_101 (by decide)

theorem hcardT144_101 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK144 ⟨101, by decide⟩ R144 hpxR144 hcardq144 (by decide)).symm

/-- **Cell (144, 101).** -/
theorem cell144_101 (e : List (ZMod 25)) (heK : charOK (basisAt rK144) e = true)
    (h : ↥(reps (⟨101, by decide⟩ : Fin 148))) :
    species (reps (⟨101, by decide⟩ : Fin 148)) h (basisElt (reps rK144) (charOfVec rK144 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK144 e (h : Coordinate 1) T144_101 i :=
  species_entry_eq_sum rK144 ⟨101, by decide⟩ e heK h T144_101 hfix144_101 hinj144_101 hcardT144_101
    (fun i => conj_mem_of_fixedPoints (reps ⟨101, by decide⟩) (reps rK144) (T144_101 i) (hfix144_101 i) h)

/-! ## Cell (144, 102): |T| = 5 -/

def T144_102list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T144_102 : Fin 5 → Coordinate 1 := fun i => T144_102list.getD i.val (0,0,0,0,0)

theorem hfix144_102 : ∀ i, ((T144_102 i : Coordinate 1) : Coordinate 1 ⧸ reps rK144)
    ∈ fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144) :=
  repsFix_of_siftB rK144 ⟨102, by decide⟩ T144_102 (by decide)

theorem hinj144_102 : Function.Injective
    (fun i => ((T144_102 i : Coordinate 1) : Coordinate 1 ⧸ reps rK144)) :=
  repsInj_of_reduceAux rK144 T144_102 (by decide)

theorem hcardT144_102 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK144 ⟨102, by decide⟩ R144 hpxR144 hcardq144 (by decide)).symm

/-- **Cell (144, 102).** -/
theorem cell144_102 (e : List (ZMod 25)) (heK : charOK (basisAt rK144) e = true)
    (h : ↥(reps (⟨102, by decide⟩ : Fin 148))) :
    species (reps (⟨102, by decide⟩ : Fin 148)) h (basisElt (reps rK144) (charOfVec rK144 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK144 e (h : Coordinate 1) T144_102 i :=
  species_entry_eq_sum rK144 ⟨102, by decide⟩ e heK h T144_102 hfix144_102 hinj144_102 hcardT144_102
    (fun i => conj_mem_of_fixedPoints (reps ⟨102, by decide⟩) (reps rK144) (T144_102 i) (hfix144_102 i) h)

/-! ## Cell (144, 103): |T| = 5 -/

def T144_103list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T144_103 : Fin 5 → Coordinate 1 := fun i => T144_103list.getD i.val (0,0,0,0,0)

theorem hfix144_103 : ∀ i, ((T144_103 i : Coordinate 1) : Coordinate 1 ⧸ reps rK144)
    ∈ fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144) :=
  repsFix_of_siftB rK144 ⟨103, by decide⟩ T144_103 (by decide)

theorem hinj144_103 : Function.Injective
    (fun i => ((T144_103 i : Coordinate 1) : Coordinate 1 ⧸ reps rK144)) :=
  repsInj_of_reduceAux rK144 T144_103 (by decide)

theorem hcardT144_103 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK144 ⟨103, by decide⟩ R144 hpxR144 hcardq144 (by decide)).symm

/-- **Cell (144, 103).** -/
theorem cell144_103 (e : List (ZMod 25)) (heK : charOK (basisAt rK144) e = true)
    (h : ↥(reps (⟨103, by decide⟩ : Fin 148))) :
    species (reps (⟨103, by decide⟩ : Fin 148)) h (basisElt (reps rK144) (charOfVec rK144 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK144 e (h : Coordinate 1) T144_103 i :=
  species_entry_eq_sum rK144 ⟨103, by decide⟩ e heK h T144_103 hfix144_103 hinj144_103 hcardT144_103
    (fun i => conj_mem_of_fixedPoints (reps ⟨103, by decide⟩) (reps rK144) (T144_103 i) (hfix144_103 i) h)

/-! ## Cell (144, 104): |T| = 5 -/

def T144_104list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T144_104 : Fin 5 → Coordinate 1 := fun i => T144_104list.getD i.val (0,0,0,0,0)

theorem hfix144_104 : ∀ i, ((T144_104 i : Coordinate 1) : Coordinate 1 ⧸ reps rK144)
    ∈ fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144) :=
  repsFix_of_siftB rK144 ⟨104, by decide⟩ T144_104 (by decide)

theorem hinj144_104 : Function.Injective
    (fun i => ((T144_104 i : Coordinate 1) : Coordinate 1 ⧸ reps rK144)) :=
  repsInj_of_reduceAux rK144 T144_104 (by decide)

theorem hcardT144_104 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK144 ⟨104, by decide⟩ R144 hpxR144 hcardq144 (by decide)).symm

/-- **Cell (144, 104).** -/
theorem cell144_104 (e : List (ZMod 25)) (heK : charOK (basisAt rK144) e = true)
    (h : ↥(reps (⟨104, by decide⟩ : Fin 148))) :
    species (reps (⟨104, by decide⟩ : Fin 148)) h (basisElt (reps rK144) (charOfVec rK144 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK144 e (h : Coordinate 1) T144_104 i :=
  species_entry_eq_sum rK144 ⟨104, by decide⟩ e heK h T144_104 hfix144_104 hinj144_104 hcardT144_104
    (fun i => conj_mem_of_fixedPoints (reps ⟨104, by decide⟩) (reps rK144) (T144_104 i) (hfix144_104 i) h)

/-! ## Cell (144, 115): |T| = 5 -/

def T144_115list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T144_115 : Fin 5 → Coordinate 1 := fun i => T144_115list.getD i.val (0,0,0,0,0)

theorem hfix144_115 : ∀ i, ((T144_115 i : Coordinate 1) : Coordinate 1 ⧸ reps rK144)
    ∈ fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144) :=
  repsFix_of_siftB rK144 ⟨115, by decide⟩ T144_115 (by decide)

theorem hinj144_115 : Function.Injective
    (fun i => ((T144_115 i : Coordinate 1) : Coordinate 1 ⧸ reps rK144)) :=
  repsInj_of_reduceAux rK144 T144_115 (by decide)

theorem hcardT144_115 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK144 ⟨115, by decide⟩ R144 hpxR144 hcardq144 (by decide)).symm

/-- **Cell (144, 115).** -/
theorem cell144_115 (e : List (ZMod 25)) (heK : charOK (basisAt rK144) e = true)
    (h : ↥(reps (⟨115, by decide⟩ : Fin 148))) :
    species (reps (⟨115, by decide⟩ : Fin 148)) h (basisElt (reps rK144) (charOfVec rK144 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK144 e (h : Coordinate 1) T144_115 i :=
  species_entry_eq_sum rK144 ⟨115, by decide⟩ e heK h T144_115 hfix144_115 hinj144_115 hcardT144_115
    (fun i => conj_mem_of_fixedPoints (reps ⟨115, by decide⟩) (reps rK144) (T144_115 i) (hfix144_115 i) h)

/-! ## Cell (144, 144): |T| = 5 -/

def T144_144list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T144_144 : Fin 5 → Coordinate 1 := fun i => T144_144list.getD i.val (0,0,0,0,0)

theorem hfix144_144 : ∀ i, ((T144_144 i : Coordinate 1) : Coordinate 1 ⧸ reps rK144)
    ∈ fixedPoints (reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144) :=
  repsFix_of_siftB rK144 ⟨144, by decide⟩ T144_144 (by decide)

theorem hinj144_144 : Function.Injective
    (fun i => ((T144_144 i : Coordinate 1) : Coordinate 1 ⧸ reps rK144)) :=
  repsInj_of_reduceAux rK144 T144_144 (by decide)

theorem hcardT144_144 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK144 ⟨144, by decide⟩ R144 hpxR144 hcardq144 (by decide)).symm

/-- **Cell (144, 144).** -/
theorem cell144_144 (e : List (ZMod 25)) (heK : charOK (basisAt rK144) e = true)
    (h : ↥(reps (⟨144, by decide⟩ : Fin 148))) :
    species (reps (⟨144, by decide⟩ : Fin 148)) h (basisElt (reps rK144) (charOfVec rK144 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK144 e (h : Coordinate 1) T144_144 i :=
  species_entry_eq_sum rK144 ⟨144, by decide⟩ e heK h T144_144 hfix144_144 hinj144_144 hcardT144_144
    (fun i => conj_mem_of_fixedPoints (reps ⟨144, by decide⟩) (reps rK144) (T144_144 i) (hfix144_144 i) h)

namespace Q2

def R144_2 : Fin 5 → Coordinate 2 := fun i => R144list.getD i.val (0,0,0,0,0)
theorem hpxR144_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK144) (R144_2 i)) := by decide
theorem hcardq144_2 : Nat.card (Coordinate 2 ⧸ reps rK144) = 5 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (144, 0) twin -/

def T144_0_2 : Fin 5 → Coordinate 2 := fun i => T144_0list.getD i.val (0,0,0,0,0)

theorem hfix144_0_2 : ∀ i, ((T144_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK144)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK144) :=
  repsFix_of_siftB2 rK144 ⟨0, by decide⟩ T144_0_2 (by decide)

theorem hinj144_0_2 : Function.Injective
    (fun i => ((T144_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK144)) :=
  repsInj_of_reduceAux2 rK144 T144_0_2 (by decide)

theorem hcardT144_0_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK144)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK144 ⟨0, by decide⟩ R144_2 hpxR144_2 hcardq144_2 (by decide)).symm

/-- **Cell (144, 0) twin (q=2).** -/
theorem cell144_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK144) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK144) (charOfVec2 rK144 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK144 e (h : Coordinate 2) T144_0_2 i :=
  species_entry_eq_sum rK144 ⟨0, by decide⟩ e heK h T144_0_2 hfix144_0_2 hinj144_0_2 hcardT144_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK144) (T144_0_2 i) (hfix144_0_2 i) h)

/-! ### Cell (144, 10) twin -/

def T144_10_2 : Fin 5 → Coordinate 2 := fun i => T144_10list.getD i.val (0,0,0,0,0)

theorem hfix144_10_2 : ∀ i, ((T144_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK144)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK144) :=
  repsFix_of_siftB2 rK144 ⟨10, by decide⟩ T144_10_2 (by decide)

theorem hinj144_10_2 : Function.Injective
    (fun i => ((T144_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK144)) :=
  repsInj_of_reduceAux2 rK144 T144_10_2 (by decide)

theorem hcardT144_10_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK144)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK144 ⟨10, by decide⟩ R144_2 hpxR144_2 hcardq144_2 (by decide)).symm

/-- **Cell (144, 10) twin (q=2).** -/
theorem cell144_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK144) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK144) (charOfVec2 rK144 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK144 e (h : Coordinate 2) T144_10_2 i :=
  species_entry_eq_sum rK144 ⟨10, by decide⟩ e heK h T144_10_2 hfix144_10_2 hinj144_10_2 hcardT144_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK144) (T144_10_2 i) (hfix144_10_2 i) h)

/-! ### Cell (144, 11) twin -/

def T144_11_2 : Fin 5 → Coordinate 2 := fun i => T144_11list.getD i.val (0,0,0,0,0)

theorem hfix144_11_2 : ∀ i, ((T144_11_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK144)
    ∈ fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK144) :=
  repsFix_of_siftB2 rK144 ⟨11, by decide⟩ T144_11_2 (by decide)

theorem hinj144_11_2 : Function.Injective
    (fun i => ((T144_11_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK144)) :=
  repsInj_of_reduceAux2 rK144 T144_11_2 (by decide)

theorem hcardT144_11_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK144)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK144 ⟨11, by decide⟩ R144_2 hpxR144_2 hcardq144_2 (by decide)).symm

/-- **Cell (144, 11) twin (q=2).** -/
theorem cell144_11_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK144) e = true)
    (h : ↥(reps (⟨11, by decide⟩ : Fin 148))) :
    species (reps (⟨11, by decide⟩ : Fin 148)) h (basisElt (reps rK144) (charOfVec2 rK144 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK144 e (h : Coordinate 2) T144_11_2 i :=
  species_entry_eq_sum rK144 ⟨11, by decide⟩ e heK h T144_11_2 hfix144_11_2 hinj144_11_2 hcardT144_11_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨11, by decide⟩) (reps rK144) (T144_11_2 i) (hfix144_11_2 i) h)

/-! ### Cell (144, 12) twin -/

def T144_12_2 : Fin 5 → Coordinate 2 := fun i => T144_12list.getD i.val (0,0,0,0,0)

theorem hfix144_12_2 : ∀ i, ((T144_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK144)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK144) :=
  repsFix_of_siftB2 rK144 ⟨12, by decide⟩ T144_12_2 (by decide)

theorem hinj144_12_2 : Function.Injective
    (fun i => ((T144_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK144)) :=
  repsInj_of_reduceAux2 rK144 T144_12_2 (by decide)

theorem hcardT144_12_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK144)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK144 ⟨12, by decide⟩ R144_2 hpxR144_2 hcardq144_2 (by decide)).symm

/-- **Cell (144, 12) twin (q=2).** -/
theorem cell144_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK144) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK144) (charOfVec2 rK144 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK144 e (h : Coordinate 2) T144_12_2 i :=
  species_entry_eq_sum rK144 ⟨12, by decide⟩ e heK h T144_12_2 hfix144_12_2 hinj144_12_2 hcardT144_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK144) (T144_12_2 i) (hfix144_12_2 i) h)

/-! ### Cell (144, 38) twin -/

def T144_38_2 : Fin 5 → Coordinate 2 := fun i => T144_38list.getD i.val (0,0,0,0,0)

theorem hfix144_38_2 : ∀ i, ((T144_38_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK144)
    ∈ fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK144) :=
  repsFix_of_siftB2 rK144 ⟨38, by decide⟩ T144_38_2 (by decide)

theorem hinj144_38_2 : Function.Injective
    (fun i => ((T144_38_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK144)) :=
  repsInj_of_reduceAux2 rK144 T144_38_2 (by decide)

theorem hcardT144_38_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK144)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK144 ⟨38, by decide⟩ R144_2 hpxR144_2 hcardq144_2 (by decide)).symm

/-- **Cell (144, 38) twin (q=2).** -/
theorem cell144_38_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK144) e = true)
    (h : ↥(reps (⟨38, by decide⟩ : Fin 148))) :
    species (reps (⟨38, by decide⟩ : Fin 148)) h (basisElt (reps rK144) (charOfVec2 rK144 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK144 e (h : Coordinate 2) T144_38_2 i :=
  species_entry_eq_sum rK144 ⟨38, by decide⟩ e heK h T144_38_2 hfix144_38_2 hinj144_38_2 hcardT144_38_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨38, by decide⟩) (reps rK144) (T144_38_2 i) (hfix144_38_2 i) h)

/-! ### Cell (144, 39) twin -/

def T144_39_2 : Fin 5 → Coordinate 2 := fun i => T144_39list.getD i.val (0,0,0,0,0)

theorem hfix144_39_2 : ∀ i, ((T144_39_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK144)
    ∈ fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK144) :=
  repsFix_of_siftB2 rK144 ⟨39, by decide⟩ T144_39_2 (by decide)

theorem hinj144_39_2 : Function.Injective
    (fun i => ((T144_39_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK144)) :=
  repsInj_of_reduceAux2 rK144 T144_39_2 (by decide)

theorem hcardT144_39_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK144)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK144 ⟨39, by decide⟩ R144_2 hpxR144_2 hcardq144_2 (by decide)).symm

/-- **Cell (144, 39) twin (q=2).** -/
theorem cell144_39_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK144) e = true)
    (h : ↥(reps (⟨39, by decide⟩ : Fin 148))) :
    species (reps (⟨39, by decide⟩ : Fin 148)) h (basisElt (reps rK144) (charOfVec2 rK144 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK144 e (h : Coordinate 2) T144_39_2 i :=
  species_entry_eq_sum rK144 ⟨39, by decide⟩ e heK h T144_39_2 hfix144_39_2 hinj144_39_2 hcardT144_39_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨39, by decide⟩) (reps rK144) (T144_39_2 i) (hfix144_39_2 i) h)

/-! ### Cell (144, 40) twin -/

def T144_40_2 : Fin 5 → Coordinate 2 := fun i => T144_40list.getD i.val (0,0,0,0,0)

theorem hfix144_40_2 : ∀ i, ((T144_40_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK144)
    ∈ fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK144) :=
  repsFix_of_siftB2 rK144 ⟨40, by decide⟩ T144_40_2 (by decide)

theorem hinj144_40_2 : Function.Injective
    (fun i => ((T144_40_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK144)) :=
  repsInj_of_reduceAux2 rK144 T144_40_2 (by decide)

theorem hcardT144_40_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK144)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK144 ⟨40, by decide⟩ R144_2 hpxR144_2 hcardq144_2 (by decide)).symm

/-- **Cell (144, 40) twin (q=2).** -/
theorem cell144_40_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK144) e = true)
    (h : ↥(reps (⟨40, by decide⟩ : Fin 148))) :
    species (reps (⟨40, by decide⟩ : Fin 148)) h (basisElt (reps rK144) (charOfVec2 rK144 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK144 e (h : Coordinate 2) T144_40_2 i :=
  species_entry_eq_sum rK144 ⟨40, by decide⟩ e heK h T144_40_2 hfix144_40_2 hinj144_40_2 hcardT144_40_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨40, by decide⟩) (reps rK144) (T144_40_2 i) (hfix144_40_2 i) h)

/-! ### Cell (144, 41) twin -/

def T144_41_2 : Fin 5 → Coordinate 2 := fun i => T144_41list.getD i.val (0,0,0,0,0)

theorem hfix144_41_2 : ∀ i, ((T144_41_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK144)
    ∈ fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK144) :=
  repsFix_of_siftB2 rK144 ⟨41, by decide⟩ T144_41_2 (by decide)

theorem hinj144_41_2 : Function.Injective
    (fun i => ((T144_41_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK144)) :=
  repsInj_of_reduceAux2 rK144 T144_41_2 (by decide)

theorem hcardT144_41_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK144)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK144 ⟨41, by decide⟩ R144_2 hpxR144_2 hcardq144_2 (by decide)).symm

/-- **Cell (144, 41) twin (q=2).** -/
theorem cell144_41_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK144) e = true)
    (h : ↥(reps (⟨41, by decide⟩ : Fin 148))) :
    species (reps (⟨41, by decide⟩ : Fin 148)) h (basisElt (reps rK144) (charOfVec2 rK144 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK144 e (h : Coordinate 2) T144_41_2 i :=
  species_entry_eq_sum rK144 ⟨41, by decide⟩ e heK h T144_41_2 hfix144_41_2 hinj144_41_2 hcardT144_41_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨41, by decide⟩) (reps rK144) (T144_41_2 i) (hfix144_41_2 i) h)

/-! ### Cell (144, 42) twin -/

def T144_42_2 : Fin 5 → Coordinate 2 := fun i => T144_42list.getD i.val (0,0,0,0,0)

theorem hfix144_42_2 : ∀ i, ((T144_42_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK144)
    ∈ fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK144) :=
  repsFix_of_siftB2 rK144 ⟨42, by decide⟩ T144_42_2 (by decide)

theorem hinj144_42_2 : Function.Injective
    (fun i => ((T144_42_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK144)) :=
  repsInj_of_reduceAux2 rK144 T144_42_2 (by decide)

theorem hcardT144_42_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK144)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK144 ⟨42, by decide⟩ R144_2 hpxR144_2 hcardq144_2 (by decide)).symm

/-- **Cell (144, 42) twin (q=2).** -/
theorem cell144_42_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK144) e = true)
    (h : ↥(reps (⟨42, by decide⟩ : Fin 148))) :
    species (reps (⟨42, by decide⟩ : Fin 148)) h (basisElt (reps rK144) (charOfVec2 rK144 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK144 e (h : Coordinate 2) T144_42_2 i :=
  species_entry_eq_sum rK144 ⟨42, by decide⟩ e heK h T144_42_2 hfix144_42_2 hinj144_42_2 hcardT144_42_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨42, by decide⟩) (reps rK144) (T144_42_2 i) (hfix144_42_2 i) h)

/-! ### Cell (144, 53) twin -/

def T144_53_2 : Fin 5 → Coordinate 2 := fun i => T144_53list.getD i.val (0,0,0,0,0)

theorem hfix144_53_2 : ∀ i, ((T144_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK144)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK144) :=
  repsFix_of_siftB2 rK144 ⟨53, by decide⟩ T144_53_2 (by decide)

theorem hinj144_53_2 : Function.Injective
    (fun i => ((T144_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK144)) :=
  repsInj_of_reduceAux2 rK144 T144_53_2 (by decide)

theorem hcardT144_53_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK144)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK144 ⟨53, by decide⟩ R144_2 hpxR144_2 hcardq144_2 (by decide)).symm

/-- **Cell (144, 53) twin (q=2).** -/
theorem cell144_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK144) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK144) (charOfVec2 rK144 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK144 e (h : Coordinate 2) T144_53_2 i :=
  species_entry_eq_sum rK144 ⟨53, by decide⟩ e heK h T144_53_2 hfix144_53_2 hinj144_53_2 hcardT144_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK144) (T144_53_2 i) (hfix144_53_2 i) h)

/-! ### Cell (144, 54) twin -/

def T144_54_2 : Fin 5 → Coordinate 2 := fun i => T144_54list.getD i.val (0,0,0,0,0)

theorem hfix144_54_2 : ∀ i, ((T144_54_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK144)
    ∈ fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK144) :=
  repsFix_of_siftB2 rK144 ⟨54, by decide⟩ T144_54_2 (by decide)

theorem hinj144_54_2 : Function.Injective
    (fun i => ((T144_54_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK144)) :=
  repsInj_of_reduceAux2 rK144 T144_54_2 (by decide)

theorem hcardT144_54_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK144)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK144 ⟨54, by decide⟩ R144_2 hpxR144_2 hcardq144_2 (by decide)).symm

/-- **Cell (144, 54) twin (q=2).** -/
theorem cell144_54_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK144) e = true)
    (h : ↥(reps (⟨54, by decide⟩ : Fin 148))) :
    species (reps (⟨54, by decide⟩ : Fin 148)) h (basisElt (reps rK144) (charOfVec2 rK144 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK144 e (h : Coordinate 2) T144_54_2 i :=
  species_entry_eq_sum rK144 ⟨54, by decide⟩ e heK h T144_54_2 hfix144_54_2 hinj144_54_2 hcardT144_54_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨54, by decide⟩) (reps rK144) (T144_54_2 i) (hfix144_54_2 i) h)

/-! ### Cell (144, 100) twin -/

def T144_100_2 : Fin 5 → Coordinate 2 := fun i => T144_100list.getD i.val (0,0,0,0,0)

theorem hfix144_100_2 : ∀ i, ((T144_100_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK144)
    ∈ fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK144) :=
  repsFix_of_siftB2 rK144 ⟨100, by decide⟩ T144_100_2 (by decide)

theorem hinj144_100_2 : Function.Injective
    (fun i => ((T144_100_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK144)) :=
  repsInj_of_reduceAux2 rK144 T144_100_2 (by decide)

theorem hcardT144_100_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK144)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK144 ⟨100, by decide⟩ R144_2 hpxR144_2 hcardq144_2 (by decide)).symm

/-- **Cell (144, 100) twin (q=2).** -/
theorem cell144_100_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK144) e = true)
    (h : ↥(reps (⟨100, by decide⟩ : Fin 148))) :
    species (reps (⟨100, by decide⟩ : Fin 148)) h (basisElt (reps rK144) (charOfVec2 rK144 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK144 e (h : Coordinate 2) T144_100_2 i :=
  species_entry_eq_sum rK144 ⟨100, by decide⟩ e heK h T144_100_2 hfix144_100_2 hinj144_100_2 hcardT144_100_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨100, by decide⟩) (reps rK144) (T144_100_2 i) (hfix144_100_2 i) h)

/-! ### Cell (144, 101) twin -/

def T144_101_2 : Fin 5 → Coordinate 2 := fun i => T144_101list.getD i.val (0,0,0,0,0)

theorem hfix144_101_2 : ∀ i, ((T144_101_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK144)
    ∈ fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK144) :=
  repsFix_of_siftB2 rK144 ⟨101, by decide⟩ T144_101_2 (by decide)

theorem hinj144_101_2 : Function.Injective
    (fun i => ((T144_101_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK144)) :=
  repsInj_of_reduceAux2 rK144 T144_101_2 (by decide)

theorem hcardT144_101_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK144)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK144 ⟨101, by decide⟩ R144_2 hpxR144_2 hcardq144_2 (by decide)).symm

/-- **Cell (144, 101) twin (q=2).** -/
theorem cell144_101_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK144) e = true)
    (h : ↥(reps (⟨101, by decide⟩ : Fin 148))) :
    species (reps (⟨101, by decide⟩ : Fin 148)) h (basisElt (reps rK144) (charOfVec2 rK144 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK144 e (h : Coordinate 2) T144_101_2 i :=
  species_entry_eq_sum rK144 ⟨101, by decide⟩ e heK h T144_101_2 hfix144_101_2 hinj144_101_2 hcardT144_101_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨101, by decide⟩) (reps rK144) (T144_101_2 i) (hfix144_101_2 i) h)

/-! ### Cell (144, 102) twin -/

def T144_102_2 : Fin 5 → Coordinate 2 := fun i => T144_102list.getD i.val (0,0,0,0,0)

theorem hfix144_102_2 : ∀ i, ((T144_102_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK144)
    ∈ fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK144) :=
  repsFix_of_siftB2 rK144 ⟨102, by decide⟩ T144_102_2 (by decide)

theorem hinj144_102_2 : Function.Injective
    (fun i => ((T144_102_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK144)) :=
  repsInj_of_reduceAux2 rK144 T144_102_2 (by decide)

theorem hcardT144_102_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK144)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK144 ⟨102, by decide⟩ R144_2 hpxR144_2 hcardq144_2 (by decide)).symm

/-- **Cell (144, 102) twin (q=2).** -/
theorem cell144_102_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK144) e = true)
    (h : ↥(reps (⟨102, by decide⟩ : Fin 148))) :
    species (reps (⟨102, by decide⟩ : Fin 148)) h (basisElt (reps rK144) (charOfVec2 rK144 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK144 e (h : Coordinate 2) T144_102_2 i :=
  species_entry_eq_sum rK144 ⟨102, by decide⟩ e heK h T144_102_2 hfix144_102_2 hinj144_102_2 hcardT144_102_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨102, by decide⟩) (reps rK144) (T144_102_2 i) (hfix144_102_2 i) h)

/-! ### Cell (144, 103) twin -/

def T144_103_2 : Fin 5 → Coordinate 2 := fun i => T144_103list.getD i.val (0,0,0,0,0)

theorem hfix144_103_2 : ∀ i, ((T144_103_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK144)
    ∈ fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK144) :=
  repsFix_of_siftB2 rK144 ⟨103, by decide⟩ T144_103_2 (by decide)

theorem hinj144_103_2 : Function.Injective
    (fun i => ((T144_103_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK144)) :=
  repsInj_of_reduceAux2 rK144 T144_103_2 (by decide)

theorem hcardT144_103_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK144)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK144 ⟨103, by decide⟩ R144_2 hpxR144_2 hcardq144_2 (by decide)).symm

/-- **Cell (144, 103) twin (q=2).** -/
theorem cell144_103_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK144) e = true)
    (h : ↥(reps (⟨103, by decide⟩ : Fin 148))) :
    species (reps (⟨103, by decide⟩ : Fin 148)) h (basisElt (reps rK144) (charOfVec2 rK144 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK144 e (h : Coordinate 2) T144_103_2 i :=
  species_entry_eq_sum rK144 ⟨103, by decide⟩ e heK h T144_103_2 hfix144_103_2 hinj144_103_2 hcardT144_103_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨103, by decide⟩) (reps rK144) (T144_103_2 i) (hfix144_103_2 i) h)

/-! ### Cell (144, 104) twin -/

def T144_104_2 : Fin 5 → Coordinate 2 := fun i => T144_104list.getD i.val (0,0,0,0,0)

theorem hfix144_104_2 : ∀ i, ((T144_104_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK144)
    ∈ fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK144) :=
  repsFix_of_siftB2 rK144 ⟨104, by decide⟩ T144_104_2 (by decide)

theorem hinj144_104_2 : Function.Injective
    (fun i => ((T144_104_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK144)) :=
  repsInj_of_reduceAux2 rK144 T144_104_2 (by decide)

theorem hcardT144_104_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK144)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK144 ⟨104, by decide⟩ R144_2 hpxR144_2 hcardq144_2 (by decide)).symm

/-- **Cell (144, 104) twin (q=2).** -/
theorem cell144_104_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK144) e = true)
    (h : ↥(reps (⟨104, by decide⟩ : Fin 148))) :
    species (reps (⟨104, by decide⟩ : Fin 148)) h (basisElt (reps rK144) (charOfVec2 rK144 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK144 e (h : Coordinate 2) T144_104_2 i :=
  species_entry_eq_sum rK144 ⟨104, by decide⟩ e heK h T144_104_2 hfix144_104_2 hinj144_104_2 hcardT144_104_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨104, by decide⟩) (reps rK144) (T144_104_2 i) (hfix144_104_2 i) h)

/-! ### Cell (144, 115) twin -/

def T144_115_2 : Fin 5 → Coordinate 2 := fun i => T144_115list.getD i.val (0,0,0,0,0)

theorem hfix144_115_2 : ∀ i, ((T144_115_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK144)
    ∈ fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK144) :=
  repsFix_of_siftB2 rK144 ⟨115, by decide⟩ T144_115_2 (by decide)

theorem hinj144_115_2 : Function.Injective
    (fun i => ((T144_115_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK144)) :=
  repsInj_of_reduceAux2 rK144 T144_115_2 (by decide)

theorem hcardT144_115_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK144)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK144 ⟨115, by decide⟩ R144_2 hpxR144_2 hcardq144_2 (by decide)).symm

/-- **Cell (144, 115) twin (q=2).** -/
theorem cell144_115_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK144) e = true)
    (h : ↥(reps (⟨115, by decide⟩ : Fin 148))) :
    species (reps (⟨115, by decide⟩ : Fin 148)) h (basisElt (reps rK144) (charOfVec2 rK144 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK144 e (h : Coordinate 2) T144_115_2 i :=
  species_entry_eq_sum rK144 ⟨115, by decide⟩ e heK h T144_115_2 hfix144_115_2 hinj144_115_2 hcardT144_115_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨115, by decide⟩) (reps rK144) (T144_115_2 i) (hfix144_115_2 i) h)

/-! ### Cell (144, 144) twin -/

def T144_144_2 : Fin 5 → Coordinate 2 := fun i => T144_144list.getD i.val (0,0,0,0,0)

theorem hfix144_144_2 : ∀ i, ((T144_144_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK144)
    ∈ fixedPoints (reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK144) :=
  repsFix_of_siftB2 rK144 ⟨144, by decide⟩ T144_144_2 (by decide)

theorem hinj144_144_2 : Function.Injective
    (fun i => ((T144_144_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK144)) :=
  repsInj_of_reduceAux2 rK144 T144_144_2 (by decide)

theorem hcardT144_144_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK144)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK144 ⟨144, by decide⟩ R144_2 hpxR144_2 hcardq144_2 (by decide)).symm

/-- **Cell (144, 144) twin (q=2).** -/
theorem cell144_144_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK144) e = true)
    (h : ↥(reps (⟨144, by decide⟩ : Fin 148))) :
    species (reps (⟨144, by decide⟩ : Fin 148)) h (basisElt (reps rK144) (charOfVec2 rK144 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK144 e (h : Coordinate 2) T144_144_2 i :=
  species_entry_eq_sum rK144 ⟨144, by decide⟩ e heK h T144_144_2 hfix144_144_2 hinj144_144_2 hcardT144_144_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨144, by decide⟩) (reps rK144) (T144_144_2 i) (hfix144_144_2 i) h)

end Q2

/-! # K-class rK = 145  (|G/K| = 5) -/

def rK145 : Fin 148 := ⟨145, by decide⟩

def R145list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def R145 : Fin 5 → Coordinate 1 := fun i => R145list.getD i.val (0,0,0,0,0)

theorem hpxR145 : Function.Injective (fun i => reduceAux 1 (basisAt rK145) (R145 i)) := by decide
theorem hcardq145 : Nat.card (Coordinate 1 ⧸ reps rK145) = 5 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (145, 0): |T| = 5 -/

def T145_0list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T145_0 : Fin 5 → Coordinate 1 := fun i => T145_0list.getD i.val (0,0,0,0,0)

theorem hfix145_0 : ∀ i, ((T145_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK145)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145) :=
  repsFix_of_siftB rK145 ⟨0, by decide⟩ T145_0 (by decide)

theorem hinj145_0 : Function.Injective
    (fun i => ((T145_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK145)) :=
  repsInj_of_reduceAux rK145 T145_0 (by decide)

theorem hcardT145_0 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK145 ⟨0, by decide⟩ R145 hpxR145 hcardq145 (by decide)).symm

/-- **Cell (145, 0).** -/
theorem cell145_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK145) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK145) (charOfVec rK145 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK145 e (h : Coordinate 1) T145_0 i :=
  species_entry_eq_sum rK145 ⟨0, by decide⟩ e heK h T145_0 hfix145_0 hinj145_0 hcardT145_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK145) (T145_0 i) (hfix145_0 i) h)

/-! ## Cell (145, 10): |T| = 5 -/

def T145_10list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T145_10 : Fin 5 → Coordinate 1 := fun i => T145_10list.getD i.val (0,0,0,0,0)

theorem hfix145_10 : ∀ i, ((T145_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK145)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145) :=
  repsFix_of_siftB rK145 ⟨10, by decide⟩ T145_10 (by decide)

theorem hinj145_10 : Function.Injective
    (fun i => ((T145_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK145)) :=
  repsInj_of_reduceAux rK145 T145_10 (by decide)

theorem hcardT145_10 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK145 ⟨10, by decide⟩ R145 hpxR145 hcardq145 (by decide)).symm

/-- **Cell (145, 10).** -/
theorem cell145_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK145) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK145) (charOfVec rK145 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK145 e (h : Coordinate 1) T145_10 i :=
  species_entry_eq_sum rK145 ⟨10, by decide⟩ e heK h T145_10 hfix145_10 hinj145_10 hcardT145_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK145) (T145_10 i) (hfix145_10 i) h)

/-! ## Cell (145, 11): |T| = 5 -/

def T145_11list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T145_11 : Fin 5 → Coordinate 1 := fun i => T145_11list.getD i.val (0,0,0,0,0)

theorem hfix145_11 : ∀ i, ((T145_11 i : Coordinate 1) : Coordinate 1 ⧸ reps rK145)
    ∈ fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145) :=
  repsFix_of_siftB rK145 ⟨11, by decide⟩ T145_11 (by decide)

theorem hinj145_11 : Function.Injective
    (fun i => ((T145_11 i : Coordinate 1) : Coordinate 1 ⧸ reps rK145)) :=
  repsInj_of_reduceAux rK145 T145_11 (by decide)

theorem hcardT145_11 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK145 ⟨11, by decide⟩ R145 hpxR145 hcardq145 (by decide)).symm

/-- **Cell (145, 11).** -/
theorem cell145_11 (e : List (ZMod 25)) (heK : charOK (basisAt rK145) e = true)
    (h : ↥(reps (⟨11, by decide⟩ : Fin 148))) :
    species (reps (⟨11, by decide⟩ : Fin 148)) h (basisElt (reps rK145) (charOfVec rK145 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK145 e (h : Coordinate 1) T145_11 i :=
  species_entry_eq_sum rK145 ⟨11, by decide⟩ e heK h T145_11 hfix145_11 hinj145_11 hcardT145_11
    (fun i => conj_mem_of_fixedPoints (reps ⟨11, by decide⟩) (reps rK145) (T145_11 i) (hfix145_11 i) h)

/-! ## Cell (145, 12): |T| = 5 -/

def T145_12list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T145_12 : Fin 5 → Coordinate 1 := fun i => T145_12list.getD i.val (0,0,0,0,0)

theorem hfix145_12 : ∀ i, ((T145_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK145)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145) :=
  repsFix_of_siftB rK145 ⟨12, by decide⟩ T145_12 (by decide)

theorem hinj145_12 : Function.Injective
    (fun i => ((T145_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK145)) :=
  repsInj_of_reduceAux rK145 T145_12 (by decide)

theorem hcardT145_12 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK145 ⟨12, by decide⟩ R145 hpxR145 hcardq145 (by decide)).symm

/-- **Cell (145, 12).** -/
theorem cell145_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK145) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK145) (charOfVec rK145 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK145 e (h : Coordinate 1) T145_12 i :=
  species_entry_eq_sum rK145 ⟨12, by decide⟩ e heK h T145_12 hfix145_12 hinj145_12 hcardT145_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK145) (T145_12 i) (hfix145_12 i) h)

/-! ## Cell (145, 43): |T| = 5 -/

def T145_43list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T145_43 : Fin 5 → Coordinate 1 := fun i => T145_43list.getD i.val (0,0,0,0,0)

theorem hfix145_43 : ∀ i, ((T145_43 i : Coordinate 1) : Coordinate 1 ⧸ reps rK145)
    ∈ fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145) :=
  repsFix_of_siftB rK145 ⟨43, by decide⟩ T145_43 (by decide)

theorem hinj145_43 : Function.Injective
    (fun i => ((T145_43 i : Coordinate 1) : Coordinate 1 ⧸ reps rK145)) :=
  repsInj_of_reduceAux rK145 T145_43 (by decide)

theorem hcardT145_43 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK145 ⟨43, by decide⟩ R145 hpxR145 hcardq145 (by decide)).symm

/-- **Cell (145, 43).** -/
theorem cell145_43 (e : List (ZMod 25)) (heK : charOK (basisAt rK145) e = true)
    (h : ↥(reps (⟨43, by decide⟩ : Fin 148))) :
    species (reps (⟨43, by decide⟩ : Fin 148)) h (basisElt (reps rK145) (charOfVec rK145 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK145 e (h : Coordinate 1) T145_43 i :=
  species_entry_eq_sum rK145 ⟨43, by decide⟩ e heK h T145_43 hfix145_43 hinj145_43 hcardT145_43
    (fun i => conj_mem_of_fixedPoints (reps ⟨43, by decide⟩) (reps rK145) (T145_43 i) (hfix145_43 i) h)

/-! ## Cell (145, 44): |T| = 5 -/

def T145_44list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T145_44 : Fin 5 → Coordinate 1 := fun i => T145_44list.getD i.val (0,0,0,0,0)

theorem hfix145_44 : ∀ i, ((T145_44 i : Coordinate 1) : Coordinate 1 ⧸ reps rK145)
    ∈ fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145) :=
  repsFix_of_siftB rK145 ⟨44, by decide⟩ T145_44 (by decide)

theorem hinj145_44 : Function.Injective
    (fun i => ((T145_44 i : Coordinate 1) : Coordinate 1 ⧸ reps rK145)) :=
  repsInj_of_reduceAux rK145 T145_44 (by decide)

theorem hcardT145_44 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK145 ⟨44, by decide⟩ R145 hpxR145 hcardq145 (by decide)).symm

/-- **Cell (145, 44).** -/
theorem cell145_44 (e : List (ZMod 25)) (heK : charOK (basisAt rK145) e = true)
    (h : ↥(reps (⟨44, by decide⟩ : Fin 148))) :
    species (reps (⟨44, by decide⟩ : Fin 148)) h (basisElt (reps rK145) (charOfVec rK145 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK145 e (h : Coordinate 1) T145_44 i :=
  species_entry_eq_sum rK145 ⟨44, by decide⟩ e heK h T145_44 hfix145_44 hinj145_44 hcardT145_44
    (fun i => conj_mem_of_fixedPoints (reps ⟨44, by decide⟩) (reps rK145) (T145_44 i) (hfix145_44 i) h)

/-! ## Cell (145, 45): |T| = 5 -/

def T145_45list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T145_45 : Fin 5 → Coordinate 1 := fun i => T145_45list.getD i.val (0,0,0,0,0)

theorem hfix145_45 : ∀ i, ((T145_45 i : Coordinate 1) : Coordinate 1 ⧸ reps rK145)
    ∈ fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145) :=
  repsFix_of_siftB rK145 ⟨45, by decide⟩ T145_45 (by decide)

theorem hinj145_45 : Function.Injective
    (fun i => ((T145_45 i : Coordinate 1) : Coordinate 1 ⧸ reps rK145)) :=
  repsInj_of_reduceAux rK145 T145_45 (by decide)

theorem hcardT145_45 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK145 ⟨45, by decide⟩ R145 hpxR145 hcardq145 (by decide)).symm

/-- **Cell (145, 45).** -/
theorem cell145_45 (e : List (ZMod 25)) (heK : charOK (basisAt rK145) e = true)
    (h : ↥(reps (⟨45, by decide⟩ : Fin 148))) :
    species (reps (⟨45, by decide⟩ : Fin 148)) h (basisElt (reps rK145) (charOfVec rK145 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK145 e (h : Coordinate 1) T145_45 i :=
  species_entry_eq_sum rK145 ⟨45, by decide⟩ e heK h T145_45 hfix145_45 hinj145_45 hcardT145_45
    (fun i => conj_mem_of_fixedPoints (reps ⟨45, by decide⟩) (reps rK145) (T145_45 i) (hfix145_45 i) h)

/-! ## Cell (145, 46): |T| = 5 -/

def T145_46list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T145_46 : Fin 5 → Coordinate 1 := fun i => T145_46list.getD i.val (0,0,0,0,0)

theorem hfix145_46 : ∀ i, ((T145_46 i : Coordinate 1) : Coordinate 1 ⧸ reps rK145)
    ∈ fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145) :=
  repsFix_of_siftB rK145 ⟨46, by decide⟩ T145_46 (by decide)

theorem hinj145_46 : Function.Injective
    (fun i => ((T145_46 i : Coordinate 1) : Coordinate 1 ⧸ reps rK145)) :=
  repsInj_of_reduceAux rK145 T145_46 (by decide)

theorem hcardT145_46 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK145 ⟨46, by decide⟩ R145 hpxR145 hcardq145 (by decide)).symm

/-- **Cell (145, 46).** -/
theorem cell145_46 (e : List (ZMod 25)) (heK : charOK (basisAt rK145) e = true)
    (h : ↥(reps (⟨46, by decide⟩ : Fin 148))) :
    species (reps (⟨46, by decide⟩ : Fin 148)) h (basisElt (reps rK145) (charOfVec rK145 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK145 e (h : Coordinate 1) T145_46 i :=
  species_entry_eq_sum rK145 ⟨46, by decide⟩ e heK h T145_46 hfix145_46 hinj145_46 hcardT145_46
    (fun i => conj_mem_of_fixedPoints (reps ⟨46, by decide⟩) (reps rK145) (T145_46 i) (hfix145_46 i) h)

/-! ## Cell (145, 47): |T| = 5 -/

def T145_47list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T145_47 : Fin 5 → Coordinate 1 := fun i => T145_47list.getD i.val (0,0,0,0,0)

theorem hfix145_47 : ∀ i, ((T145_47 i : Coordinate 1) : Coordinate 1 ⧸ reps rK145)
    ∈ fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145) :=
  repsFix_of_siftB rK145 ⟨47, by decide⟩ T145_47 (by decide)

theorem hinj145_47 : Function.Injective
    (fun i => ((T145_47 i : Coordinate 1) : Coordinate 1 ⧸ reps rK145)) :=
  repsInj_of_reduceAux rK145 T145_47 (by decide)

theorem hcardT145_47 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK145 ⟨47, by decide⟩ R145 hpxR145 hcardq145 (by decide)).symm

/-- **Cell (145, 47).** -/
theorem cell145_47 (e : List (ZMod 25)) (heK : charOK (basisAt rK145) e = true)
    (h : ↥(reps (⟨47, by decide⟩ : Fin 148))) :
    species (reps (⟨47, by decide⟩ : Fin 148)) h (basisElt (reps rK145) (charOfVec rK145 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK145 e (h : Coordinate 1) T145_47 i :=
  species_entry_eq_sum rK145 ⟨47, by decide⟩ e heK h T145_47 hfix145_47 hinj145_47 hcardT145_47
    (fun i => conj_mem_of_fixedPoints (reps ⟨47, by decide⟩) (reps rK145) (T145_47 i) (hfix145_47 i) h)

/-! ## Cell (145, 53): |T| = 5 -/

def T145_53list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T145_53 : Fin 5 → Coordinate 1 := fun i => T145_53list.getD i.val (0,0,0,0,0)

theorem hfix145_53 : ∀ i, ((T145_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK145)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145) :=
  repsFix_of_siftB rK145 ⟨53, by decide⟩ T145_53 (by decide)

theorem hinj145_53 : Function.Injective
    (fun i => ((T145_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK145)) :=
  repsInj_of_reduceAux rK145 T145_53 (by decide)

theorem hcardT145_53 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK145 ⟨53, by decide⟩ R145 hpxR145 hcardq145 (by decide)).symm

/-- **Cell (145, 53).** -/
theorem cell145_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK145) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK145) (charOfVec rK145 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK145 e (h : Coordinate 1) T145_53 i :=
  species_entry_eq_sum rK145 ⟨53, by decide⟩ e heK h T145_53 hfix145_53 hinj145_53 hcardT145_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK145) (T145_53 i) (hfix145_53 i) h)

/-! ## Cell (145, 54): |T| = 5 -/

def T145_54list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T145_54 : Fin 5 → Coordinate 1 := fun i => T145_54list.getD i.val (0,0,0,0,0)

theorem hfix145_54 : ∀ i, ((T145_54 i : Coordinate 1) : Coordinate 1 ⧸ reps rK145)
    ∈ fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145) :=
  repsFix_of_siftB rK145 ⟨54, by decide⟩ T145_54 (by decide)

theorem hinj145_54 : Function.Injective
    (fun i => ((T145_54 i : Coordinate 1) : Coordinate 1 ⧸ reps rK145)) :=
  repsInj_of_reduceAux rK145 T145_54 (by decide)

theorem hcardT145_54 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK145 ⟨54, by decide⟩ R145 hpxR145 hcardq145 (by decide)).symm

/-- **Cell (145, 54).** -/
theorem cell145_54 (e : List (ZMod 25)) (heK : charOK (basisAt rK145) e = true)
    (h : ↥(reps (⟨54, by decide⟩ : Fin 148))) :
    species (reps (⟨54, by decide⟩ : Fin 148)) h (basisElt (reps rK145) (charOfVec rK145 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK145 e (h : Coordinate 1) T145_54 i :=
  species_entry_eq_sum rK145 ⟨54, by decide⟩ e heK h T145_54 hfix145_54 hinj145_54 hcardT145_54
    (fun i => conj_mem_of_fixedPoints (reps ⟨54, by decide⟩) (reps rK145) (T145_54 i) (hfix145_54 i) h)

/-! ## Cell (145, 105): |T| = 5 -/

def T145_105list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T145_105 : Fin 5 → Coordinate 1 := fun i => T145_105list.getD i.val (0,0,0,0,0)

theorem hfix145_105 : ∀ i, ((T145_105 i : Coordinate 1) : Coordinate 1 ⧸ reps rK145)
    ∈ fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145) :=
  repsFix_of_siftB rK145 ⟨105, by decide⟩ T145_105 (by decide)

theorem hinj145_105 : Function.Injective
    (fun i => ((T145_105 i : Coordinate 1) : Coordinate 1 ⧸ reps rK145)) :=
  repsInj_of_reduceAux rK145 T145_105 (by decide)

theorem hcardT145_105 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK145 ⟨105, by decide⟩ R145 hpxR145 hcardq145 (by decide)).symm

/-- **Cell (145, 105).** -/
theorem cell145_105 (e : List (ZMod 25)) (heK : charOK (basisAt rK145) e = true)
    (h : ↥(reps (⟨105, by decide⟩ : Fin 148))) :
    species (reps (⟨105, by decide⟩ : Fin 148)) h (basisElt (reps rK145) (charOfVec rK145 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK145 e (h : Coordinate 1) T145_105 i :=
  species_entry_eq_sum rK145 ⟨105, by decide⟩ e heK h T145_105 hfix145_105 hinj145_105 hcardT145_105
    (fun i => conj_mem_of_fixedPoints (reps ⟨105, by decide⟩) (reps rK145) (T145_105 i) (hfix145_105 i) h)

/-! ## Cell (145, 106): |T| = 5 -/

def T145_106list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T145_106 : Fin 5 → Coordinate 1 := fun i => T145_106list.getD i.val (0,0,0,0,0)

theorem hfix145_106 : ∀ i, ((T145_106 i : Coordinate 1) : Coordinate 1 ⧸ reps rK145)
    ∈ fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145) :=
  repsFix_of_siftB rK145 ⟨106, by decide⟩ T145_106 (by decide)

theorem hinj145_106 : Function.Injective
    (fun i => ((T145_106 i : Coordinate 1) : Coordinate 1 ⧸ reps rK145)) :=
  repsInj_of_reduceAux rK145 T145_106 (by decide)

theorem hcardT145_106 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK145 ⟨106, by decide⟩ R145 hpxR145 hcardq145 (by decide)).symm

/-- **Cell (145, 106).** -/
theorem cell145_106 (e : List (ZMod 25)) (heK : charOK (basisAt rK145) e = true)
    (h : ↥(reps (⟨106, by decide⟩ : Fin 148))) :
    species (reps (⟨106, by decide⟩ : Fin 148)) h (basisElt (reps rK145) (charOfVec rK145 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK145 e (h : Coordinate 1) T145_106 i :=
  species_entry_eq_sum rK145 ⟨106, by decide⟩ e heK h T145_106 hfix145_106 hinj145_106 hcardT145_106
    (fun i => conj_mem_of_fixedPoints (reps ⟨106, by decide⟩) (reps rK145) (T145_106 i) (hfix145_106 i) h)

/-! ## Cell (145, 107): |T| = 5 -/

def T145_107list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T145_107 : Fin 5 → Coordinate 1 := fun i => T145_107list.getD i.val (0,0,0,0,0)

theorem hfix145_107 : ∀ i, ((T145_107 i : Coordinate 1) : Coordinate 1 ⧸ reps rK145)
    ∈ fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145) :=
  repsFix_of_siftB rK145 ⟨107, by decide⟩ T145_107 (by decide)

theorem hinj145_107 : Function.Injective
    (fun i => ((T145_107 i : Coordinate 1) : Coordinate 1 ⧸ reps rK145)) :=
  repsInj_of_reduceAux rK145 T145_107 (by decide)

theorem hcardT145_107 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK145 ⟨107, by decide⟩ R145 hpxR145 hcardq145 (by decide)).symm

/-- **Cell (145, 107).** -/
theorem cell145_107 (e : List (ZMod 25)) (heK : charOK (basisAt rK145) e = true)
    (h : ↥(reps (⟨107, by decide⟩ : Fin 148))) :
    species (reps (⟨107, by decide⟩ : Fin 148)) h (basisElt (reps rK145) (charOfVec rK145 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK145 e (h : Coordinate 1) T145_107 i :=
  species_entry_eq_sum rK145 ⟨107, by decide⟩ e heK h T145_107 hfix145_107 hinj145_107 hcardT145_107
    (fun i => conj_mem_of_fixedPoints (reps ⟨107, by decide⟩) (reps rK145) (T145_107 i) (hfix145_107 i) h)

/-! ## Cell (145, 108): |T| = 5 -/

def T145_108list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T145_108 : Fin 5 → Coordinate 1 := fun i => T145_108list.getD i.val (0,0,0,0,0)

theorem hfix145_108 : ∀ i, ((T145_108 i : Coordinate 1) : Coordinate 1 ⧸ reps rK145)
    ∈ fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145) :=
  repsFix_of_siftB rK145 ⟨108, by decide⟩ T145_108 (by decide)

theorem hinj145_108 : Function.Injective
    (fun i => ((T145_108 i : Coordinate 1) : Coordinate 1 ⧸ reps rK145)) :=
  repsInj_of_reduceAux rK145 T145_108 (by decide)

theorem hcardT145_108 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK145 ⟨108, by decide⟩ R145 hpxR145 hcardq145 (by decide)).symm

/-- **Cell (145, 108).** -/
theorem cell145_108 (e : List (ZMod 25)) (heK : charOK (basisAt rK145) e = true)
    (h : ↥(reps (⟨108, by decide⟩ : Fin 148))) :
    species (reps (⟨108, by decide⟩ : Fin 148)) h (basisElt (reps rK145) (charOfVec rK145 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK145 e (h : Coordinate 1) T145_108 i :=
  species_entry_eq_sum rK145 ⟨108, by decide⟩ e heK h T145_108 hfix145_108 hinj145_108 hcardT145_108
    (fun i => conj_mem_of_fixedPoints (reps ⟨108, by decide⟩) (reps rK145) (T145_108 i) (hfix145_108 i) h)

/-! ## Cell (145, 109): |T| = 5 -/

def T145_109list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T145_109 : Fin 5 → Coordinate 1 := fun i => T145_109list.getD i.val (0,0,0,0,0)

theorem hfix145_109 : ∀ i, ((T145_109 i : Coordinate 1) : Coordinate 1 ⧸ reps rK145)
    ∈ fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145) :=
  repsFix_of_siftB rK145 ⟨109, by decide⟩ T145_109 (by decide)

theorem hinj145_109 : Function.Injective
    (fun i => ((T145_109 i : Coordinate 1) : Coordinate 1 ⧸ reps rK145)) :=
  repsInj_of_reduceAux rK145 T145_109 (by decide)

theorem hcardT145_109 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK145 ⟨109, by decide⟩ R145 hpxR145 hcardq145 (by decide)).symm

/-- **Cell (145, 109).** -/
theorem cell145_109 (e : List (ZMod 25)) (heK : charOK (basisAt rK145) e = true)
    (h : ↥(reps (⟨109, by decide⟩ : Fin 148))) :
    species (reps (⟨109, by decide⟩ : Fin 148)) h (basisElt (reps rK145) (charOfVec rK145 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK145 e (h : Coordinate 1) T145_109 i :=
  species_entry_eq_sum rK145 ⟨109, by decide⟩ e heK h T145_109 hfix145_109 hinj145_109 hcardT145_109
    (fun i => conj_mem_of_fixedPoints (reps ⟨109, by decide⟩) (reps rK145) (T145_109 i) (hfix145_109 i) h)

/-! ## Cell (145, 115): |T| = 5 -/

def T145_115list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T145_115 : Fin 5 → Coordinate 1 := fun i => T145_115list.getD i.val (0,0,0,0,0)

theorem hfix145_115 : ∀ i, ((T145_115 i : Coordinate 1) : Coordinate 1 ⧸ reps rK145)
    ∈ fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145) :=
  repsFix_of_siftB rK145 ⟨115, by decide⟩ T145_115 (by decide)

theorem hinj145_115 : Function.Injective
    (fun i => ((T145_115 i : Coordinate 1) : Coordinate 1 ⧸ reps rK145)) :=
  repsInj_of_reduceAux rK145 T145_115 (by decide)

theorem hcardT145_115 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK145 ⟨115, by decide⟩ R145 hpxR145 hcardq145 (by decide)).symm

/-- **Cell (145, 115).** -/
theorem cell145_115 (e : List (ZMod 25)) (heK : charOK (basisAt rK145) e = true)
    (h : ↥(reps (⟨115, by decide⟩ : Fin 148))) :
    species (reps (⟨115, by decide⟩ : Fin 148)) h (basisElt (reps rK145) (charOfVec rK145 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK145 e (h : Coordinate 1) T145_115 i :=
  species_entry_eq_sum rK145 ⟨115, by decide⟩ e heK h T145_115 hfix145_115 hinj145_115 hcardT145_115
    (fun i => conj_mem_of_fixedPoints (reps ⟨115, by decide⟩) (reps rK145) (T145_115 i) (hfix145_115 i) h)

/-! ## Cell (145, 145): |T| = 5 -/

def T145_145list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T145_145 : Fin 5 → Coordinate 1 := fun i => T145_145list.getD i.val (0,0,0,0,0)

theorem hfix145_145 : ∀ i, ((T145_145 i : Coordinate 1) : Coordinate 1 ⧸ reps rK145)
    ∈ fixedPoints (reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145) :=
  repsFix_of_siftB rK145 ⟨145, by decide⟩ T145_145 (by decide)

theorem hinj145_145 : Function.Injective
    (fun i => ((T145_145 i : Coordinate 1) : Coordinate 1 ⧸ reps rK145)) :=
  repsInj_of_reduceAux rK145 T145_145 (by decide)

theorem hcardT145_145 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK145 ⟨145, by decide⟩ R145 hpxR145 hcardq145 (by decide)).symm

/-- **Cell (145, 145).** -/
theorem cell145_145 (e : List (ZMod 25)) (heK : charOK (basisAt rK145) e = true)
    (h : ↥(reps (⟨145, by decide⟩ : Fin 148))) :
    species (reps (⟨145, by decide⟩ : Fin 148)) h (basisElt (reps rK145) (charOfVec rK145 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK145 e (h : Coordinate 1) T145_145 i :=
  species_entry_eq_sum rK145 ⟨145, by decide⟩ e heK h T145_145 hfix145_145 hinj145_145 hcardT145_145
    (fun i => conj_mem_of_fixedPoints (reps ⟨145, by decide⟩) (reps rK145) (T145_145 i) (hfix145_145 i) h)

namespace Q2

def R145_2 : Fin 5 → Coordinate 2 := fun i => R145list.getD i.val (0,0,0,0,0)
theorem hpxR145_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK145) (R145_2 i)) := by decide
theorem hcardq145_2 : Nat.card (Coordinate 2 ⧸ reps rK145) = 5 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (145, 0) twin -/

def T145_0_2 : Fin 5 → Coordinate 2 := fun i => T145_0list.getD i.val (0,0,0,0,0)

theorem hfix145_0_2 : ∀ i, ((T145_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK145)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK145) :=
  repsFix_of_siftB2 rK145 ⟨0, by decide⟩ T145_0_2 (by decide)

theorem hinj145_0_2 : Function.Injective
    (fun i => ((T145_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK145)) :=
  repsInj_of_reduceAux2 rK145 T145_0_2 (by decide)

theorem hcardT145_0_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK145)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK145 ⟨0, by decide⟩ R145_2 hpxR145_2 hcardq145_2 (by decide)).symm

/-- **Cell (145, 0) twin (q=2).** -/
theorem cell145_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK145) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK145) (charOfVec2 rK145 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK145 e (h : Coordinate 2) T145_0_2 i :=
  species_entry_eq_sum rK145 ⟨0, by decide⟩ e heK h T145_0_2 hfix145_0_2 hinj145_0_2 hcardT145_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK145) (T145_0_2 i) (hfix145_0_2 i) h)

/-! ### Cell (145, 10) twin -/

def T145_10_2 : Fin 5 → Coordinate 2 := fun i => T145_10list.getD i.val (0,0,0,0,0)

theorem hfix145_10_2 : ∀ i, ((T145_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK145)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK145) :=
  repsFix_of_siftB2 rK145 ⟨10, by decide⟩ T145_10_2 (by decide)

theorem hinj145_10_2 : Function.Injective
    (fun i => ((T145_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK145)) :=
  repsInj_of_reduceAux2 rK145 T145_10_2 (by decide)

theorem hcardT145_10_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK145)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK145 ⟨10, by decide⟩ R145_2 hpxR145_2 hcardq145_2 (by decide)).symm

/-- **Cell (145, 10) twin (q=2).** -/
theorem cell145_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK145) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK145) (charOfVec2 rK145 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK145 e (h : Coordinate 2) T145_10_2 i :=
  species_entry_eq_sum rK145 ⟨10, by decide⟩ e heK h T145_10_2 hfix145_10_2 hinj145_10_2 hcardT145_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK145) (T145_10_2 i) (hfix145_10_2 i) h)

/-! ### Cell (145, 11) twin -/

def T145_11_2 : Fin 5 → Coordinate 2 := fun i => T145_11list.getD i.val (0,0,0,0,0)

theorem hfix145_11_2 : ∀ i, ((T145_11_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK145)
    ∈ fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK145) :=
  repsFix_of_siftB2 rK145 ⟨11, by decide⟩ T145_11_2 (by decide)

theorem hinj145_11_2 : Function.Injective
    (fun i => ((T145_11_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK145)) :=
  repsInj_of_reduceAux2 rK145 T145_11_2 (by decide)

theorem hcardT145_11_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK145)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK145 ⟨11, by decide⟩ R145_2 hpxR145_2 hcardq145_2 (by decide)).symm

/-- **Cell (145, 11) twin (q=2).** -/
theorem cell145_11_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK145) e = true)
    (h : ↥(reps (⟨11, by decide⟩ : Fin 148))) :
    species (reps (⟨11, by decide⟩ : Fin 148)) h (basisElt (reps rK145) (charOfVec2 rK145 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK145 e (h : Coordinate 2) T145_11_2 i :=
  species_entry_eq_sum rK145 ⟨11, by decide⟩ e heK h T145_11_2 hfix145_11_2 hinj145_11_2 hcardT145_11_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨11, by decide⟩) (reps rK145) (T145_11_2 i) (hfix145_11_2 i) h)

/-! ### Cell (145, 12) twin -/

def T145_12_2 : Fin 5 → Coordinate 2 := fun i => T145_12list.getD i.val (0,0,0,0,0)

theorem hfix145_12_2 : ∀ i, ((T145_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK145)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK145) :=
  repsFix_of_siftB2 rK145 ⟨12, by decide⟩ T145_12_2 (by decide)

theorem hinj145_12_2 : Function.Injective
    (fun i => ((T145_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK145)) :=
  repsInj_of_reduceAux2 rK145 T145_12_2 (by decide)

theorem hcardT145_12_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK145)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK145 ⟨12, by decide⟩ R145_2 hpxR145_2 hcardq145_2 (by decide)).symm

/-- **Cell (145, 12) twin (q=2).** -/
theorem cell145_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK145) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK145) (charOfVec2 rK145 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK145 e (h : Coordinate 2) T145_12_2 i :=
  species_entry_eq_sum rK145 ⟨12, by decide⟩ e heK h T145_12_2 hfix145_12_2 hinj145_12_2 hcardT145_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK145) (T145_12_2 i) (hfix145_12_2 i) h)

/-! ### Cell (145, 43) twin -/

def T145_43_2 : Fin 5 → Coordinate 2 := fun i => T145_43list.getD i.val (0,0,0,0,0)

theorem hfix145_43_2 : ∀ i, ((T145_43_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK145)
    ∈ fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK145) :=
  repsFix_of_siftB2 rK145 ⟨43, by decide⟩ T145_43_2 (by decide)

theorem hinj145_43_2 : Function.Injective
    (fun i => ((T145_43_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK145)) :=
  repsInj_of_reduceAux2 rK145 T145_43_2 (by decide)

theorem hcardT145_43_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK145)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK145 ⟨43, by decide⟩ R145_2 hpxR145_2 hcardq145_2 (by decide)).symm

/-- **Cell (145, 43) twin (q=2).** -/
theorem cell145_43_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK145) e = true)
    (h : ↥(reps (⟨43, by decide⟩ : Fin 148))) :
    species (reps (⟨43, by decide⟩ : Fin 148)) h (basisElt (reps rK145) (charOfVec2 rK145 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK145 e (h : Coordinate 2) T145_43_2 i :=
  species_entry_eq_sum rK145 ⟨43, by decide⟩ e heK h T145_43_2 hfix145_43_2 hinj145_43_2 hcardT145_43_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨43, by decide⟩) (reps rK145) (T145_43_2 i) (hfix145_43_2 i) h)

/-! ### Cell (145, 44) twin -/

def T145_44_2 : Fin 5 → Coordinate 2 := fun i => T145_44list.getD i.val (0,0,0,0,0)

theorem hfix145_44_2 : ∀ i, ((T145_44_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK145)
    ∈ fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK145) :=
  repsFix_of_siftB2 rK145 ⟨44, by decide⟩ T145_44_2 (by decide)

theorem hinj145_44_2 : Function.Injective
    (fun i => ((T145_44_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK145)) :=
  repsInj_of_reduceAux2 rK145 T145_44_2 (by decide)

theorem hcardT145_44_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK145)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK145 ⟨44, by decide⟩ R145_2 hpxR145_2 hcardq145_2 (by decide)).symm

/-- **Cell (145, 44) twin (q=2).** -/
theorem cell145_44_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK145) e = true)
    (h : ↥(reps (⟨44, by decide⟩ : Fin 148))) :
    species (reps (⟨44, by decide⟩ : Fin 148)) h (basisElt (reps rK145) (charOfVec2 rK145 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK145 e (h : Coordinate 2) T145_44_2 i :=
  species_entry_eq_sum rK145 ⟨44, by decide⟩ e heK h T145_44_2 hfix145_44_2 hinj145_44_2 hcardT145_44_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨44, by decide⟩) (reps rK145) (T145_44_2 i) (hfix145_44_2 i) h)

/-! ### Cell (145, 45) twin -/

def T145_45_2 : Fin 5 → Coordinate 2 := fun i => T145_45list.getD i.val (0,0,0,0,0)

theorem hfix145_45_2 : ∀ i, ((T145_45_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK145)
    ∈ fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK145) :=
  repsFix_of_siftB2 rK145 ⟨45, by decide⟩ T145_45_2 (by decide)

theorem hinj145_45_2 : Function.Injective
    (fun i => ((T145_45_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK145)) :=
  repsInj_of_reduceAux2 rK145 T145_45_2 (by decide)

theorem hcardT145_45_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK145)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK145 ⟨45, by decide⟩ R145_2 hpxR145_2 hcardq145_2 (by decide)).symm

/-- **Cell (145, 45) twin (q=2).** -/
theorem cell145_45_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK145) e = true)
    (h : ↥(reps (⟨45, by decide⟩ : Fin 148))) :
    species (reps (⟨45, by decide⟩ : Fin 148)) h (basisElt (reps rK145) (charOfVec2 rK145 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK145 e (h : Coordinate 2) T145_45_2 i :=
  species_entry_eq_sum rK145 ⟨45, by decide⟩ e heK h T145_45_2 hfix145_45_2 hinj145_45_2 hcardT145_45_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨45, by decide⟩) (reps rK145) (T145_45_2 i) (hfix145_45_2 i) h)

/-! ### Cell (145, 46) twin -/

def T145_46_2 : Fin 5 → Coordinate 2 := fun i => T145_46list.getD i.val (0,0,0,0,0)

theorem hfix145_46_2 : ∀ i, ((T145_46_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK145)
    ∈ fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK145) :=
  repsFix_of_siftB2 rK145 ⟨46, by decide⟩ T145_46_2 (by decide)

theorem hinj145_46_2 : Function.Injective
    (fun i => ((T145_46_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK145)) :=
  repsInj_of_reduceAux2 rK145 T145_46_2 (by decide)

theorem hcardT145_46_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK145)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK145 ⟨46, by decide⟩ R145_2 hpxR145_2 hcardq145_2 (by decide)).symm

/-- **Cell (145, 46) twin (q=2).** -/
theorem cell145_46_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK145) e = true)
    (h : ↥(reps (⟨46, by decide⟩ : Fin 148))) :
    species (reps (⟨46, by decide⟩ : Fin 148)) h (basisElt (reps rK145) (charOfVec2 rK145 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK145 e (h : Coordinate 2) T145_46_2 i :=
  species_entry_eq_sum rK145 ⟨46, by decide⟩ e heK h T145_46_2 hfix145_46_2 hinj145_46_2 hcardT145_46_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨46, by decide⟩) (reps rK145) (T145_46_2 i) (hfix145_46_2 i) h)

/-! ### Cell (145, 47) twin -/

def T145_47_2 : Fin 5 → Coordinate 2 := fun i => T145_47list.getD i.val (0,0,0,0,0)

theorem hfix145_47_2 : ∀ i, ((T145_47_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK145)
    ∈ fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK145) :=
  repsFix_of_siftB2 rK145 ⟨47, by decide⟩ T145_47_2 (by decide)

theorem hinj145_47_2 : Function.Injective
    (fun i => ((T145_47_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK145)) :=
  repsInj_of_reduceAux2 rK145 T145_47_2 (by decide)

theorem hcardT145_47_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK145)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK145 ⟨47, by decide⟩ R145_2 hpxR145_2 hcardq145_2 (by decide)).symm

/-- **Cell (145, 47) twin (q=2).** -/
theorem cell145_47_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK145) e = true)
    (h : ↥(reps (⟨47, by decide⟩ : Fin 148))) :
    species (reps (⟨47, by decide⟩ : Fin 148)) h (basisElt (reps rK145) (charOfVec2 rK145 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK145 e (h : Coordinate 2) T145_47_2 i :=
  species_entry_eq_sum rK145 ⟨47, by decide⟩ e heK h T145_47_2 hfix145_47_2 hinj145_47_2 hcardT145_47_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨47, by decide⟩) (reps rK145) (T145_47_2 i) (hfix145_47_2 i) h)

/-! ### Cell (145, 53) twin -/

def T145_53_2 : Fin 5 → Coordinate 2 := fun i => T145_53list.getD i.val (0,0,0,0,0)

theorem hfix145_53_2 : ∀ i, ((T145_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK145)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK145) :=
  repsFix_of_siftB2 rK145 ⟨53, by decide⟩ T145_53_2 (by decide)

theorem hinj145_53_2 : Function.Injective
    (fun i => ((T145_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK145)) :=
  repsInj_of_reduceAux2 rK145 T145_53_2 (by decide)

theorem hcardT145_53_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK145)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK145 ⟨53, by decide⟩ R145_2 hpxR145_2 hcardq145_2 (by decide)).symm

/-- **Cell (145, 53) twin (q=2).** -/
theorem cell145_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK145) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK145) (charOfVec2 rK145 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK145 e (h : Coordinate 2) T145_53_2 i :=
  species_entry_eq_sum rK145 ⟨53, by decide⟩ e heK h T145_53_2 hfix145_53_2 hinj145_53_2 hcardT145_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK145) (T145_53_2 i) (hfix145_53_2 i) h)

/-! ### Cell (145, 54) twin -/

def T145_54_2 : Fin 5 → Coordinate 2 := fun i => T145_54list.getD i.val (0,0,0,0,0)

theorem hfix145_54_2 : ∀ i, ((T145_54_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK145)
    ∈ fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK145) :=
  repsFix_of_siftB2 rK145 ⟨54, by decide⟩ T145_54_2 (by decide)

theorem hinj145_54_2 : Function.Injective
    (fun i => ((T145_54_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK145)) :=
  repsInj_of_reduceAux2 rK145 T145_54_2 (by decide)

theorem hcardT145_54_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK145)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK145 ⟨54, by decide⟩ R145_2 hpxR145_2 hcardq145_2 (by decide)).symm

/-- **Cell (145, 54) twin (q=2).** -/
theorem cell145_54_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK145) e = true)
    (h : ↥(reps (⟨54, by decide⟩ : Fin 148))) :
    species (reps (⟨54, by decide⟩ : Fin 148)) h (basisElt (reps rK145) (charOfVec2 rK145 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK145 e (h : Coordinate 2) T145_54_2 i :=
  species_entry_eq_sum rK145 ⟨54, by decide⟩ e heK h T145_54_2 hfix145_54_2 hinj145_54_2 hcardT145_54_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨54, by decide⟩) (reps rK145) (T145_54_2 i) (hfix145_54_2 i) h)

/-! ### Cell (145, 105) twin -/

def T145_105_2 : Fin 5 → Coordinate 2 := fun i => T145_105list.getD i.val (0,0,0,0,0)

theorem hfix145_105_2 : ∀ i, ((T145_105_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK145)
    ∈ fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK145) :=
  repsFix_of_siftB2 rK145 ⟨105, by decide⟩ T145_105_2 (by decide)

theorem hinj145_105_2 : Function.Injective
    (fun i => ((T145_105_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK145)) :=
  repsInj_of_reduceAux2 rK145 T145_105_2 (by decide)

theorem hcardT145_105_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK145)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK145 ⟨105, by decide⟩ R145_2 hpxR145_2 hcardq145_2 (by decide)).symm

/-- **Cell (145, 105) twin (q=2).** -/
theorem cell145_105_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK145) e = true)
    (h : ↥(reps (⟨105, by decide⟩ : Fin 148))) :
    species (reps (⟨105, by decide⟩ : Fin 148)) h (basisElt (reps rK145) (charOfVec2 rK145 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK145 e (h : Coordinate 2) T145_105_2 i :=
  species_entry_eq_sum rK145 ⟨105, by decide⟩ e heK h T145_105_2 hfix145_105_2 hinj145_105_2 hcardT145_105_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨105, by decide⟩) (reps rK145) (T145_105_2 i) (hfix145_105_2 i) h)

/-! ### Cell (145, 106) twin -/

def T145_106_2 : Fin 5 → Coordinate 2 := fun i => T145_106list.getD i.val (0,0,0,0,0)

theorem hfix145_106_2 : ∀ i, ((T145_106_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK145)
    ∈ fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK145) :=
  repsFix_of_siftB2 rK145 ⟨106, by decide⟩ T145_106_2 (by decide)

theorem hinj145_106_2 : Function.Injective
    (fun i => ((T145_106_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK145)) :=
  repsInj_of_reduceAux2 rK145 T145_106_2 (by decide)

theorem hcardT145_106_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK145)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK145 ⟨106, by decide⟩ R145_2 hpxR145_2 hcardq145_2 (by decide)).symm

/-- **Cell (145, 106) twin (q=2).** -/
theorem cell145_106_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK145) e = true)
    (h : ↥(reps (⟨106, by decide⟩ : Fin 148))) :
    species (reps (⟨106, by decide⟩ : Fin 148)) h (basisElt (reps rK145) (charOfVec2 rK145 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK145 e (h : Coordinate 2) T145_106_2 i :=
  species_entry_eq_sum rK145 ⟨106, by decide⟩ e heK h T145_106_2 hfix145_106_2 hinj145_106_2 hcardT145_106_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨106, by decide⟩) (reps rK145) (T145_106_2 i) (hfix145_106_2 i) h)

/-! ### Cell (145, 107) twin -/

def T145_107_2 : Fin 5 → Coordinate 2 := fun i => T145_107list.getD i.val (0,0,0,0,0)

theorem hfix145_107_2 : ∀ i, ((T145_107_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK145)
    ∈ fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK145) :=
  repsFix_of_siftB2 rK145 ⟨107, by decide⟩ T145_107_2 (by decide)

theorem hinj145_107_2 : Function.Injective
    (fun i => ((T145_107_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK145)) :=
  repsInj_of_reduceAux2 rK145 T145_107_2 (by decide)

theorem hcardT145_107_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK145)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK145 ⟨107, by decide⟩ R145_2 hpxR145_2 hcardq145_2 (by decide)).symm

/-- **Cell (145, 107) twin (q=2).** -/
theorem cell145_107_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK145) e = true)
    (h : ↥(reps (⟨107, by decide⟩ : Fin 148))) :
    species (reps (⟨107, by decide⟩ : Fin 148)) h (basisElt (reps rK145) (charOfVec2 rK145 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK145 e (h : Coordinate 2) T145_107_2 i :=
  species_entry_eq_sum rK145 ⟨107, by decide⟩ e heK h T145_107_2 hfix145_107_2 hinj145_107_2 hcardT145_107_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨107, by decide⟩) (reps rK145) (T145_107_2 i) (hfix145_107_2 i) h)

/-! ### Cell (145, 108) twin -/

def T145_108_2 : Fin 5 → Coordinate 2 := fun i => T145_108list.getD i.val (0,0,0,0,0)

theorem hfix145_108_2 : ∀ i, ((T145_108_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK145)
    ∈ fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK145) :=
  repsFix_of_siftB2 rK145 ⟨108, by decide⟩ T145_108_2 (by decide)

theorem hinj145_108_2 : Function.Injective
    (fun i => ((T145_108_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK145)) :=
  repsInj_of_reduceAux2 rK145 T145_108_2 (by decide)

theorem hcardT145_108_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK145)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK145 ⟨108, by decide⟩ R145_2 hpxR145_2 hcardq145_2 (by decide)).symm

/-- **Cell (145, 108) twin (q=2).** -/
theorem cell145_108_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK145) e = true)
    (h : ↥(reps (⟨108, by decide⟩ : Fin 148))) :
    species (reps (⟨108, by decide⟩ : Fin 148)) h (basisElt (reps rK145) (charOfVec2 rK145 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK145 e (h : Coordinate 2) T145_108_2 i :=
  species_entry_eq_sum rK145 ⟨108, by decide⟩ e heK h T145_108_2 hfix145_108_2 hinj145_108_2 hcardT145_108_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨108, by decide⟩) (reps rK145) (T145_108_2 i) (hfix145_108_2 i) h)

/-! ### Cell (145, 109) twin -/

def T145_109_2 : Fin 5 → Coordinate 2 := fun i => T145_109list.getD i.val (0,0,0,0,0)

theorem hfix145_109_2 : ∀ i, ((T145_109_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK145)
    ∈ fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK145) :=
  repsFix_of_siftB2 rK145 ⟨109, by decide⟩ T145_109_2 (by decide)

theorem hinj145_109_2 : Function.Injective
    (fun i => ((T145_109_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK145)) :=
  repsInj_of_reduceAux2 rK145 T145_109_2 (by decide)

theorem hcardT145_109_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK145)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK145 ⟨109, by decide⟩ R145_2 hpxR145_2 hcardq145_2 (by decide)).symm

/-- **Cell (145, 109) twin (q=2).** -/
theorem cell145_109_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK145) e = true)
    (h : ↥(reps (⟨109, by decide⟩ : Fin 148))) :
    species (reps (⟨109, by decide⟩ : Fin 148)) h (basisElt (reps rK145) (charOfVec2 rK145 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK145 e (h : Coordinate 2) T145_109_2 i :=
  species_entry_eq_sum rK145 ⟨109, by decide⟩ e heK h T145_109_2 hfix145_109_2 hinj145_109_2 hcardT145_109_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨109, by decide⟩) (reps rK145) (T145_109_2 i) (hfix145_109_2 i) h)

/-! ### Cell (145, 115) twin -/

def T145_115_2 : Fin 5 → Coordinate 2 := fun i => T145_115list.getD i.val (0,0,0,0,0)

theorem hfix145_115_2 : ∀ i, ((T145_115_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK145)
    ∈ fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK145) :=
  repsFix_of_siftB2 rK145 ⟨115, by decide⟩ T145_115_2 (by decide)

theorem hinj145_115_2 : Function.Injective
    (fun i => ((T145_115_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK145)) :=
  repsInj_of_reduceAux2 rK145 T145_115_2 (by decide)

theorem hcardT145_115_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK145)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK145 ⟨115, by decide⟩ R145_2 hpxR145_2 hcardq145_2 (by decide)).symm

/-- **Cell (145, 115) twin (q=2).** -/
theorem cell145_115_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK145) e = true)
    (h : ↥(reps (⟨115, by decide⟩ : Fin 148))) :
    species (reps (⟨115, by decide⟩ : Fin 148)) h (basisElt (reps rK145) (charOfVec2 rK145 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK145 e (h : Coordinate 2) T145_115_2 i :=
  species_entry_eq_sum rK145 ⟨115, by decide⟩ e heK h T145_115_2 hfix145_115_2 hinj145_115_2 hcardT145_115_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨115, by decide⟩) (reps rK145) (T145_115_2 i) (hfix145_115_2 i) h)

/-! ### Cell (145, 145) twin -/

def T145_145_2 : Fin 5 → Coordinate 2 := fun i => T145_145list.getD i.val (0,0,0,0,0)

theorem hfix145_145_2 : ∀ i, ((T145_145_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK145)
    ∈ fixedPoints (reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK145) :=
  repsFix_of_siftB2 rK145 ⟨145, by decide⟩ T145_145_2 (by decide)

theorem hinj145_145_2 : Function.Injective
    (fun i => ((T145_145_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK145)) :=
  repsInj_of_reduceAux2 rK145 T145_145_2 (by decide)

theorem hcardT145_145_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK145)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK145 ⟨145, by decide⟩ R145_2 hpxR145_2 hcardq145_2 (by decide)).symm

/-- **Cell (145, 145) twin (q=2).** -/
theorem cell145_145_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK145) e = true)
    (h : ↥(reps (⟨145, by decide⟩ : Fin 148))) :
    species (reps (⟨145, by decide⟩ : Fin 148)) h (basisElt (reps rK145) (charOfVec2 rK145 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK145 e (h : Coordinate 2) T145_145_2 i :=
  species_entry_eq_sum rK145 ⟨145, by decide⟩ e heK h T145_145_2 hfix145_145_2 hinj145_145_2 hcardT145_145_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨145, by decide⟩) (reps rK145) (T145_145_2 i) (hfix145_145_2 i) h)

end Q2

end LeanDring.P5Presentation
