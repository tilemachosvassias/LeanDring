/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, K-strata data (5^3 stratum, rK 93-100): certified per-cell species-entry instantiations, both
twins.

Covers K-classes 93, 94, 95, 96, 97, 98, 99, 100 (order-5^3 K, |R|=25).  For each nonzero `H`-column
(`(G/K)^H ≠ ∅`), the full coset transversal `R93..` and each `H`-fixed
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

/-! # K-class rK = 93  (|G/K| = 25) -/

def rK93 : Fin 148 := ⟨93, by decide⟩

def R93list : List Coordinates := [(0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0)]
def R93 : Fin 25 → Coordinate 1 := fun i => R93list.getD i.val (0,0,0,0,0)

theorem hpxR93 : Function.Injective (fun i => reduceAux 1 (basisAt rK93) (R93 i)) := by decide
theorem hcardq93 : Nat.card (Coordinate 1 ⧸ reps rK93) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (93, 0): |T| = 25 -/

def T93_0list : List Coordinates := [(0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0)]
def T93_0 : Fin 25 → Coordinate 1 := fun i => T93_0list.getD i.val (0,0,0,0,0)

theorem hfix93_0 : ∀ i, ((T93_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK93)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93) :=
  repsFix_of_siftB rK93 ⟨0, by decide⟩ T93_0 (by decide)

theorem hinj93_0 : Function.Injective
    (fun i => ((T93_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK93)) :=
  repsInj_of_reduceAux rK93 T93_0 (by decide)

theorem hcardT93_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK93 ⟨0, by decide⟩ R93 hpxR93 hcardq93 (by decide)).symm

/-- **Cell (93, 0).** -/
theorem cell93_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK93) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK93) (charOfVec rK93 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK93 e (h : Coordinate 1) T93_0 i :=
  species_entry_eq_sum rK93 ⟨0, by decide⟩ e heK h T93_0 hfix93_0 hinj93_0 hcardT93_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK93) (T93_0 i) (hfix93_0 i) h)

/-! ## Cell (93, 10): |T| = 25 -/

def T93_10list : List Coordinates := [(0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0)]
def T93_10 : Fin 25 → Coordinate 1 := fun i => T93_10list.getD i.val (0,0,0,0,0)

theorem hfix93_10 : ∀ i, ((T93_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK93)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93) :=
  repsFix_of_siftB rK93 ⟨10, by decide⟩ T93_10 (by decide)

theorem hinj93_10 : Function.Injective
    (fun i => ((T93_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK93)) :=
  repsInj_of_reduceAux rK93 T93_10 (by decide)

theorem hcardT93_10 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK93 ⟨10, by decide⟩ R93 hpxR93 hcardq93 (by decide)).symm

/-- **Cell (93, 10).** -/
theorem cell93_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK93) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK93) (charOfVec rK93 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK93 e (h : Coordinate 1) T93_10 i :=
  species_entry_eq_sum rK93 ⟨10, by decide⟩ e heK h T93_10 hfix93_10 hinj93_10 hcardT93_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK93) (T93_10 i) (hfix93_10 i) h)

/-! ## Cell (93, 12): |T| = 25 -/

def T93_12list : List Coordinates := [(0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0)]
def T93_12 : Fin 25 → Coordinate 1 := fun i => T93_12list.getD i.val (0,0,0,0,0)

theorem hfix93_12 : ∀ i, ((T93_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK93)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93) :=
  repsFix_of_siftB rK93 ⟨12, by decide⟩ T93_12 (by decide)

theorem hinj93_12 : Function.Injective
    (fun i => ((T93_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK93)) :=
  repsInj_of_reduceAux rK93 T93_12 (by decide)

theorem hcardT93_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK93 ⟨12, by decide⟩ R93 hpxR93 hcardq93 (by decide)).symm

/-- **Cell (93, 12).** -/
theorem cell93_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK93) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK93) (charOfVec rK93 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK93 e (h : Coordinate 1) T93_12 i :=
  species_entry_eq_sum rK93 ⟨12, by decide⟩ e heK h T93_12 hfix93_12 hinj93_12 hcardT93_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK93) (T93_12 i) (hfix93_12 i) h)

/-! ## Cell (93, 31): |T| = 25 -/

def T93_31list : List Coordinates := [(0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0)]
def T93_31 : Fin 25 → Coordinate 1 := fun i => T93_31list.getD i.val (0,0,0,0,0)

theorem hfix93_31 : ∀ i, ((T93_31 i : Coordinate 1) : Coordinate 1 ⧸ reps rK93)
    ∈ fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93) :=
  repsFix_of_siftB rK93 ⟨31, by decide⟩ T93_31 (by decide)

theorem hinj93_31 : Function.Injective
    (fun i => ((T93_31 i : Coordinate 1) : Coordinate 1 ⧸ reps rK93)) :=
  repsInj_of_reduceAux rK93 T93_31 (by decide)

theorem hcardT93_31 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK93 ⟨31, by decide⟩ R93 hpxR93 hcardq93 (by decide)).symm

/-- **Cell (93, 31).** -/
theorem cell93_31 (e : List (ZMod 25)) (heK : charOK (basisAt rK93) e = true)
    (h : ↥(reps (⟨31, by decide⟩ : Fin 148))) :
    species (reps (⟨31, by decide⟩ : Fin 148)) h (basisElt (reps rK93) (charOfVec rK93 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK93 e (h : Coordinate 1) T93_31 i :=
  species_entry_eq_sum rK93 ⟨31, by decide⟩ e heK h T93_31 hfix93_31 hinj93_31 hcardT93_31
    (fun i => conj_mem_of_fixedPoints (reps ⟨31, by decide⟩) (reps rK93) (T93_31 i) (hfix93_31 i) h)

/-! ## Cell (93, 53): |T| = 25 -/

def T93_53list : List Coordinates := [(0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0)]
def T93_53 : Fin 25 → Coordinate 1 := fun i => T93_53list.getD i.val (0,0,0,0,0)

theorem hfix93_53 : ∀ i, ((T93_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK93)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93) :=
  repsFix_of_siftB rK93 ⟨53, by decide⟩ T93_53 (by decide)

theorem hinj93_53 : Function.Injective
    (fun i => ((T93_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK93)) :=
  repsInj_of_reduceAux rK93 T93_53 (by decide)

theorem hcardT93_53 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK93 ⟨53, by decide⟩ R93 hpxR93 hcardq93 (by decide)).symm

/-- **Cell (93, 53).** -/
theorem cell93_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK93) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK93) (charOfVec rK93 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK93 e (h : Coordinate 1) T93_53 i :=
  species_entry_eq_sum rK93 ⟨53, by decide⟩ e heK h T93_53 hfix93_53 hinj93_53 hcardT93_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK93) (T93_53 i) (hfix93_53 i) h)

/-! ## Cell (93, 93): |T| = 25 -/

def T93_93list : List Coordinates := [(0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0)]
def T93_93 : Fin 25 → Coordinate 1 := fun i => T93_93list.getD i.val (0,0,0,0,0)

theorem hfix93_93 : ∀ i, ((T93_93 i : Coordinate 1) : Coordinate 1 ⧸ reps rK93)
    ∈ fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93) :=
  repsFix_of_siftB rK93 ⟨93, by decide⟩ T93_93 (by decide)

theorem hinj93_93 : Function.Injective
    (fun i => ((T93_93 i : Coordinate 1) : Coordinate 1 ⧸ reps rK93)) :=
  repsInj_of_reduceAux rK93 T93_93 (by decide)

theorem hcardT93_93 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK93 ⟨93, by decide⟩ R93 hpxR93 hcardq93 (by decide)).symm

/-- **Cell (93, 93).** -/
theorem cell93_93 (e : List (ZMod 25)) (heK : charOK (basisAt rK93) e = true)
    (h : ↥(reps (⟨93, by decide⟩ : Fin 148))) :
    species (reps (⟨93, by decide⟩ : Fin 148)) h (basisElt (reps rK93) (charOfVec rK93 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK93 e (h : Coordinate 1) T93_93 i :=
  species_entry_eq_sum rK93 ⟨93, by decide⟩ e heK h T93_93 hfix93_93 hinj93_93 hcardT93_93
    (fun i => conj_mem_of_fixedPoints (reps ⟨93, by decide⟩) (reps rK93) (T93_93 i) (hfix93_93 i) h)

namespace Q2

def R93_2 : Fin 25 → Coordinate 2 := fun i => R93list.getD i.val (0,0,0,0,0)
theorem hpxR93_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK93) (R93_2 i)) := by decide
theorem hcardq93_2 : Nat.card (Coordinate 2 ⧸ reps rK93) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (93, 0) twin -/

def T93_0_2 : Fin 25 → Coordinate 2 := fun i => T93_0list.getD i.val (0,0,0,0,0)

theorem hfix93_0_2 : ∀ i, ((T93_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK93)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK93) :=
  repsFix_of_siftB2 rK93 ⟨0, by decide⟩ T93_0_2 (by decide)

theorem hinj93_0_2 : Function.Injective
    (fun i => ((T93_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK93)) :=
  repsInj_of_reduceAux2 rK93 T93_0_2 (by decide)

theorem hcardT93_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK93)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK93 ⟨0, by decide⟩ R93_2 hpxR93_2 hcardq93_2 (by decide)).symm

/-- **Cell (93, 0) twin (q=2).** -/
theorem cell93_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK93) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK93) (charOfVec2 rK93 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK93 e (h : Coordinate 2) T93_0_2 i :=
  species_entry_eq_sum rK93 ⟨0, by decide⟩ e heK h T93_0_2 hfix93_0_2 hinj93_0_2 hcardT93_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK93) (T93_0_2 i) (hfix93_0_2 i) h)

/-! ### Cell (93, 10) twin -/

def T93_10_2 : Fin 25 → Coordinate 2 := fun i => T93_10list.getD i.val (0,0,0,0,0)

theorem hfix93_10_2 : ∀ i, ((T93_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK93)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK93) :=
  repsFix_of_siftB2 rK93 ⟨10, by decide⟩ T93_10_2 (by decide)

theorem hinj93_10_2 : Function.Injective
    (fun i => ((T93_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK93)) :=
  repsInj_of_reduceAux2 rK93 T93_10_2 (by decide)

theorem hcardT93_10_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK93)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK93 ⟨10, by decide⟩ R93_2 hpxR93_2 hcardq93_2 (by decide)).symm

/-- **Cell (93, 10) twin (q=2).** -/
theorem cell93_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK93) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK93) (charOfVec2 rK93 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK93 e (h : Coordinate 2) T93_10_2 i :=
  species_entry_eq_sum rK93 ⟨10, by decide⟩ e heK h T93_10_2 hfix93_10_2 hinj93_10_2 hcardT93_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK93) (T93_10_2 i) (hfix93_10_2 i) h)

/-! ### Cell (93, 12) twin -/

def T93_12_2 : Fin 25 → Coordinate 2 := fun i => T93_12list.getD i.val (0,0,0,0,0)

theorem hfix93_12_2 : ∀ i, ((T93_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK93)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK93) :=
  repsFix_of_siftB2 rK93 ⟨12, by decide⟩ T93_12_2 (by decide)

theorem hinj93_12_2 : Function.Injective
    (fun i => ((T93_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK93)) :=
  repsInj_of_reduceAux2 rK93 T93_12_2 (by decide)

theorem hcardT93_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK93)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK93 ⟨12, by decide⟩ R93_2 hpxR93_2 hcardq93_2 (by decide)).symm

/-- **Cell (93, 12) twin (q=2).** -/
theorem cell93_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK93) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK93) (charOfVec2 rK93 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK93 e (h : Coordinate 2) T93_12_2 i :=
  species_entry_eq_sum rK93 ⟨12, by decide⟩ e heK h T93_12_2 hfix93_12_2 hinj93_12_2 hcardT93_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK93) (T93_12_2 i) (hfix93_12_2 i) h)

/-! ### Cell (93, 31) twin -/

def T93_31_2 : Fin 25 → Coordinate 2 := fun i => T93_31list.getD i.val (0,0,0,0,0)

theorem hfix93_31_2 : ∀ i, ((T93_31_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK93)
    ∈ fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK93) :=
  repsFix_of_siftB2 rK93 ⟨31, by decide⟩ T93_31_2 (by decide)

theorem hinj93_31_2 : Function.Injective
    (fun i => ((T93_31_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK93)) :=
  repsInj_of_reduceAux2 rK93 T93_31_2 (by decide)

theorem hcardT93_31_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK93)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK93 ⟨31, by decide⟩ R93_2 hpxR93_2 hcardq93_2 (by decide)).symm

/-- **Cell (93, 31) twin (q=2).** -/
theorem cell93_31_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK93) e = true)
    (h : ↥(reps (⟨31, by decide⟩ : Fin 148))) :
    species (reps (⟨31, by decide⟩ : Fin 148)) h (basisElt (reps rK93) (charOfVec2 rK93 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK93 e (h : Coordinate 2) T93_31_2 i :=
  species_entry_eq_sum rK93 ⟨31, by decide⟩ e heK h T93_31_2 hfix93_31_2 hinj93_31_2 hcardT93_31_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨31, by decide⟩) (reps rK93) (T93_31_2 i) (hfix93_31_2 i) h)

/-! ### Cell (93, 53) twin -/

def T93_53_2 : Fin 25 → Coordinate 2 := fun i => T93_53list.getD i.val (0,0,0,0,0)

theorem hfix93_53_2 : ∀ i, ((T93_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK93)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK93) :=
  repsFix_of_siftB2 rK93 ⟨53, by decide⟩ T93_53_2 (by decide)

theorem hinj93_53_2 : Function.Injective
    (fun i => ((T93_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK93)) :=
  repsInj_of_reduceAux2 rK93 T93_53_2 (by decide)

theorem hcardT93_53_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK93)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK93 ⟨53, by decide⟩ R93_2 hpxR93_2 hcardq93_2 (by decide)).symm

/-- **Cell (93, 53) twin (q=2).** -/
theorem cell93_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK93) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK93) (charOfVec2 rK93 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK93 e (h : Coordinate 2) T93_53_2 i :=
  species_entry_eq_sum rK93 ⟨53, by decide⟩ e heK h T93_53_2 hfix93_53_2 hinj93_53_2 hcardT93_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK93) (T93_53_2 i) (hfix93_53_2 i) h)

/-! ### Cell (93, 93) twin -/

def T93_93_2 : Fin 25 → Coordinate 2 := fun i => T93_93list.getD i.val (0,0,0,0,0)

theorem hfix93_93_2 : ∀ i, ((T93_93_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK93)
    ∈ fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK93) :=
  repsFix_of_siftB2 rK93 ⟨93, by decide⟩ T93_93_2 (by decide)

theorem hinj93_93_2 : Function.Injective
    (fun i => ((T93_93_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK93)) :=
  repsInj_of_reduceAux2 rK93 T93_93_2 (by decide)

theorem hcardT93_93_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK93)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK93 ⟨93, by decide⟩ R93_2 hpxR93_2 hcardq93_2 (by decide)).symm

/-- **Cell (93, 93) twin (q=2).** -/
theorem cell93_93_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK93) e = true)
    (h : ↥(reps (⟨93, by decide⟩ : Fin 148))) :
    species (reps (⟨93, by decide⟩ : Fin 148)) h (basisElt (reps rK93) (charOfVec2 rK93 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK93 e (h : Coordinate 2) T93_93_2 i :=
  species_entry_eq_sum rK93 ⟨93, by decide⟩ e heK h T93_93_2 hfix93_93_2 hinj93_93_2 hcardT93_93_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨93, by decide⟩) (reps rK93) (T93_93_2 i) (hfix93_93_2 i) h)

end Q2

/-! # K-class rK = 94  (|G/K| = 25) -/

def rK94 : Fin 148 := ⟨94, by decide⟩

def R94list : List Coordinates := [(0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def R94 : Fin 25 → Coordinate 1 := fun i => R94list.getD i.val (0,0,0,0,0)

theorem hpxR94 : Function.Injective (fun i => reduceAux 1 (basisAt rK94) (R94 i)) := by decide
theorem hcardq94 : Nat.card (Coordinate 1 ⧸ reps rK94) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (94, 0): |T| = 25 -/

def T94_0list : List Coordinates := [(0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T94_0 : Fin 25 → Coordinate 1 := fun i => T94_0list.getD i.val (0,0,0,0,0)

theorem hfix94_0 : ∀ i, ((T94_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK94)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94) :=
  repsFix_of_siftB rK94 ⟨0, by decide⟩ T94_0 (by decide)

theorem hinj94_0 : Function.Injective
    (fun i => ((T94_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK94)) :=
  repsInj_of_reduceAux rK94 T94_0 (by decide)

theorem hcardT94_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK94 ⟨0, by decide⟩ R94 hpxR94 hcardq94 (by decide)).symm

/-- **Cell (94, 0).** -/
theorem cell94_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK94) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK94) (charOfVec rK94 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK94 e (h : Coordinate 1) T94_0 i :=
  species_entry_eq_sum rK94 ⟨0, by decide⟩ e heK h T94_0 hfix94_0 hinj94_0 hcardT94_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK94) (T94_0 i) (hfix94_0 i) h)

/-! ## Cell (94, 10): |T| = 25 -/

def T94_10list : List Coordinates := [(0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T94_10 : Fin 25 → Coordinate 1 := fun i => T94_10list.getD i.val (0,0,0,0,0)

theorem hfix94_10 : ∀ i, ((T94_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK94)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94) :=
  repsFix_of_siftB rK94 ⟨10, by decide⟩ T94_10 (by decide)

theorem hinj94_10 : Function.Injective
    (fun i => ((T94_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK94)) :=
  repsInj_of_reduceAux rK94 T94_10 (by decide)

theorem hcardT94_10 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK94 ⟨10, by decide⟩ R94 hpxR94 hcardq94 (by decide)).symm

/-- **Cell (94, 10).** -/
theorem cell94_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK94) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK94) (charOfVec rK94 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK94 e (h : Coordinate 1) T94_10 i :=
  species_entry_eq_sum rK94 ⟨10, by decide⟩ e heK h T94_10 hfix94_10 hinj94_10 hcardT94_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK94) (T94_10 i) (hfix94_10 i) h)

/-! ## Cell (94, 12): |T| = 25 -/

def T94_12list : List Coordinates := [(0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T94_12 : Fin 25 → Coordinate 1 := fun i => T94_12list.getD i.val (0,0,0,0,0)

theorem hfix94_12 : ∀ i, ((T94_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK94)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94) :=
  repsFix_of_siftB rK94 ⟨12, by decide⟩ T94_12 (by decide)

theorem hinj94_12 : Function.Injective
    (fun i => ((T94_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK94)) :=
  repsInj_of_reduceAux rK94 T94_12 (by decide)

theorem hcardT94_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK94 ⟨12, by decide⟩ R94 hpxR94 hcardq94 (by decide)).symm

/-- **Cell (94, 12).** -/
theorem cell94_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK94) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK94) (charOfVec rK94 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK94 e (h : Coordinate 1) T94_12 i :=
  species_entry_eq_sum rK94 ⟨12, by decide⟩ e heK h T94_12 hfix94_12 hinj94_12 hcardT94_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK94) (T94_12 i) (hfix94_12 i) h)

/-! ## Cell (94, 32): |T| = 25 -/

def T94_32list : List Coordinates := [(0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T94_32 : Fin 25 → Coordinate 1 := fun i => T94_32list.getD i.val (0,0,0,0,0)

theorem hfix94_32 : ∀ i, ((T94_32 i : Coordinate 1) : Coordinate 1 ⧸ reps rK94)
    ∈ fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94) :=
  repsFix_of_siftB rK94 ⟨32, by decide⟩ T94_32 (by decide)

theorem hinj94_32 : Function.Injective
    (fun i => ((T94_32 i : Coordinate 1) : Coordinate 1 ⧸ reps rK94)) :=
  repsInj_of_reduceAux rK94 T94_32 (by decide)

theorem hcardT94_32 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK94 ⟨32, by decide⟩ R94 hpxR94 hcardq94 (by decide)).symm

/-- **Cell (94, 32).** -/
theorem cell94_32 (e : List (ZMod 25)) (heK : charOK (basisAt rK94) e = true)
    (h : ↥(reps (⟨32, by decide⟩ : Fin 148))) :
    species (reps (⟨32, by decide⟩ : Fin 148)) h (basisElt (reps rK94) (charOfVec rK94 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK94 e (h : Coordinate 1) T94_32 i :=
  species_entry_eq_sum rK94 ⟨32, by decide⟩ e heK h T94_32 hfix94_32 hinj94_32 hcardT94_32
    (fun i => conj_mem_of_fixedPoints (reps ⟨32, by decide⟩) (reps rK94) (T94_32 i) (hfix94_32 i) h)

/-! ## Cell (94, 53): |T| = 25 -/

def T94_53list : List Coordinates := [(0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T94_53 : Fin 25 → Coordinate 1 := fun i => T94_53list.getD i.val (0,0,0,0,0)

theorem hfix94_53 : ∀ i, ((T94_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK94)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94) :=
  repsFix_of_siftB rK94 ⟨53, by decide⟩ T94_53 (by decide)

theorem hinj94_53 : Function.Injective
    (fun i => ((T94_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK94)) :=
  repsInj_of_reduceAux rK94 T94_53 (by decide)

theorem hcardT94_53 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK94 ⟨53, by decide⟩ R94 hpxR94 hcardq94 (by decide)).symm

/-- **Cell (94, 53).** -/
theorem cell94_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK94) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK94) (charOfVec rK94 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK94 e (h : Coordinate 1) T94_53 i :=
  species_entry_eq_sum rK94 ⟨53, by decide⟩ e heK h T94_53 hfix94_53 hinj94_53 hcardT94_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK94) (T94_53 i) (hfix94_53 i) h)

/-! ## Cell (94, 94): |T| = 25 -/

def T94_94list : List Coordinates := [(0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T94_94 : Fin 25 → Coordinate 1 := fun i => T94_94list.getD i.val (0,0,0,0,0)

theorem hfix94_94 : ∀ i, ((T94_94 i : Coordinate 1) : Coordinate 1 ⧸ reps rK94)
    ∈ fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94) :=
  repsFix_of_siftB rK94 ⟨94, by decide⟩ T94_94 (by decide)

theorem hinj94_94 : Function.Injective
    (fun i => ((T94_94 i : Coordinate 1) : Coordinate 1 ⧸ reps rK94)) :=
  repsInj_of_reduceAux rK94 T94_94 (by decide)

theorem hcardT94_94 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK94 ⟨94, by decide⟩ R94 hpxR94 hcardq94 (by decide)).symm

/-- **Cell (94, 94).** -/
theorem cell94_94 (e : List (ZMod 25)) (heK : charOK (basisAt rK94) e = true)
    (h : ↥(reps (⟨94, by decide⟩ : Fin 148))) :
    species (reps (⟨94, by decide⟩ : Fin 148)) h (basisElt (reps rK94) (charOfVec rK94 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK94 e (h : Coordinate 1) T94_94 i :=
  species_entry_eq_sum rK94 ⟨94, by decide⟩ e heK h T94_94 hfix94_94 hinj94_94 hcardT94_94
    (fun i => conj_mem_of_fixedPoints (reps ⟨94, by decide⟩) (reps rK94) (T94_94 i) (hfix94_94 i) h)

namespace Q2

def R94_2 : Fin 25 → Coordinate 2 := fun i => R94list.getD i.val (0,0,0,0,0)
theorem hpxR94_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK94) (R94_2 i)) := by decide
theorem hcardq94_2 : Nat.card (Coordinate 2 ⧸ reps rK94) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (94, 0) twin -/

def T94_0_2 : Fin 25 → Coordinate 2 := fun i => T94_0list.getD i.val (0,0,0,0,0)

theorem hfix94_0_2 : ∀ i, ((T94_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK94)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK94) :=
  repsFix_of_siftB2 rK94 ⟨0, by decide⟩ T94_0_2 (by decide)

theorem hinj94_0_2 : Function.Injective
    (fun i => ((T94_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK94)) :=
  repsInj_of_reduceAux2 rK94 T94_0_2 (by decide)

theorem hcardT94_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK94)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK94 ⟨0, by decide⟩ R94_2 hpxR94_2 hcardq94_2 (by decide)).symm

/-- **Cell (94, 0) twin (q=2).** -/
theorem cell94_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK94) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK94) (charOfVec2 rK94 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK94 e (h : Coordinate 2) T94_0_2 i :=
  species_entry_eq_sum rK94 ⟨0, by decide⟩ e heK h T94_0_2 hfix94_0_2 hinj94_0_2 hcardT94_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK94) (T94_0_2 i) (hfix94_0_2 i) h)

/-! ### Cell (94, 10) twin -/

def T94_10_2 : Fin 25 → Coordinate 2 := fun i => T94_10list.getD i.val (0,0,0,0,0)

theorem hfix94_10_2 : ∀ i, ((T94_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK94)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK94) :=
  repsFix_of_siftB2 rK94 ⟨10, by decide⟩ T94_10_2 (by decide)

theorem hinj94_10_2 : Function.Injective
    (fun i => ((T94_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK94)) :=
  repsInj_of_reduceAux2 rK94 T94_10_2 (by decide)

theorem hcardT94_10_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK94)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK94 ⟨10, by decide⟩ R94_2 hpxR94_2 hcardq94_2 (by decide)).symm

/-- **Cell (94, 10) twin (q=2).** -/
theorem cell94_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK94) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK94) (charOfVec2 rK94 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK94 e (h : Coordinate 2) T94_10_2 i :=
  species_entry_eq_sum rK94 ⟨10, by decide⟩ e heK h T94_10_2 hfix94_10_2 hinj94_10_2 hcardT94_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK94) (T94_10_2 i) (hfix94_10_2 i) h)

/-! ### Cell (94, 12) twin -/

def T94_12_2 : Fin 25 → Coordinate 2 := fun i => T94_12list.getD i.val (0,0,0,0,0)

theorem hfix94_12_2 : ∀ i, ((T94_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK94)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK94) :=
  repsFix_of_siftB2 rK94 ⟨12, by decide⟩ T94_12_2 (by decide)

theorem hinj94_12_2 : Function.Injective
    (fun i => ((T94_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK94)) :=
  repsInj_of_reduceAux2 rK94 T94_12_2 (by decide)

theorem hcardT94_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK94)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK94 ⟨12, by decide⟩ R94_2 hpxR94_2 hcardq94_2 (by decide)).symm

/-- **Cell (94, 12) twin (q=2).** -/
theorem cell94_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK94) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK94) (charOfVec2 rK94 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK94 e (h : Coordinate 2) T94_12_2 i :=
  species_entry_eq_sum rK94 ⟨12, by decide⟩ e heK h T94_12_2 hfix94_12_2 hinj94_12_2 hcardT94_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK94) (T94_12_2 i) (hfix94_12_2 i) h)

/-! ### Cell (94, 32) twin -/

def T94_32_2 : Fin 25 → Coordinate 2 := fun i => T94_32list.getD i.val (0,0,0,0,0)

theorem hfix94_32_2 : ∀ i, ((T94_32_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK94)
    ∈ fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK94) :=
  repsFix_of_siftB2 rK94 ⟨32, by decide⟩ T94_32_2 (by decide)

theorem hinj94_32_2 : Function.Injective
    (fun i => ((T94_32_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK94)) :=
  repsInj_of_reduceAux2 rK94 T94_32_2 (by decide)

theorem hcardT94_32_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK94)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK94 ⟨32, by decide⟩ R94_2 hpxR94_2 hcardq94_2 (by decide)).symm

/-- **Cell (94, 32) twin (q=2).** -/
theorem cell94_32_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK94) e = true)
    (h : ↥(reps (⟨32, by decide⟩ : Fin 148))) :
    species (reps (⟨32, by decide⟩ : Fin 148)) h (basisElt (reps rK94) (charOfVec2 rK94 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK94 e (h : Coordinate 2) T94_32_2 i :=
  species_entry_eq_sum rK94 ⟨32, by decide⟩ e heK h T94_32_2 hfix94_32_2 hinj94_32_2 hcardT94_32_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨32, by decide⟩) (reps rK94) (T94_32_2 i) (hfix94_32_2 i) h)

/-! ### Cell (94, 53) twin -/

def T94_53_2 : Fin 25 → Coordinate 2 := fun i => T94_53list.getD i.val (0,0,0,0,0)

theorem hfix94_53_2 : ∀ i, ((T94_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK94)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK94) :=
  repsFix_of_siftB2 rK94 ⟨53, by decide⟩ T94_53_2 (by decide)

theorem hinj94_53_2 : Function.Injective
    (fun i => ((T94_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK94)) :=
  repsInj_of_reduceAux2 rK94 T94_53_2 (by decide)

theorem hcardT94_53_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK94)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK94 ⟨53, by decide⟩ R94_2 hpxR94_2 hcardq94_2 (by decide)).symm

/-- **Cell (94, 53) twin (q=2).** -/
theorem cell94_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK94) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK94) (charOfVec2 rK94 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK94 e (h : Coordinate 2) T94_53_2 i :=
  species_entry_eq_sum rK94 ⟨53, by decide⟩ e heK h T94_53_2 hfix94_53_2 hinj94_53_2 hcardT94_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK94) (T94_53_2 i) (hfix94_53_2 i) h)

/-! ### Cell (94, 94) twin -/

def T94_94_2 : Fin 25 → Coordinate 2 := fun i => T94_94list.getD i.val (0,0,0,0,0)

theorem hfix94_94_2 : ∀ i, ((T94_94_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK94)
    ∈ fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK94) :=
  repsFix_of_siftB2 rK94 ⟨94, by decide⟩ T94_94_2 (by decide)

theorem hinj94_94_2 : Function.Injective
    (fun i => ((T94_94_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK94)) :=
  repsInj_of_reduceAux2 rK94 T94_94_2 (by decide)

theorem hcardT94_94_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK94)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK94 ⟨94, by decide⟩ R94_2 hpxR94_2 hcardq94_2 (by decide)).symm

/-- **Cell (94, 94) twin (q=2).** -/
theorem cell94_94_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK94) e = true)
    (h : ↥(reps (⟨94, by decide⟩ : Fin 148))) :
    species (reps (⟨94, by decide⟩ : Fin 148)) h (basisElt (reps rK94) (charOfVec2 rK94 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK94 e (h : Coordinate 2) T94_94_2 i :=
  species_entry_eq_sum rK94 ⟨94, by decide⟩ e heK h T94_94_2 hfix94_94_2 hinj94_94_2 hcardT94_94_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨94, by decide⟩) (reps rK94) (T94_94_2 i) (hfix94_94_2 i) h)

end Q2

/-! # K-class rK = 95  (|G/K| = 25) -/

def rK95 : Fin 148 := ⟨95, by decide⟩

def R95list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (1,0,2,0,0), (1,0,3,0,0), (1,0,4,0,0), (1,0,0,0,0), (1,0,1,0,0), (2,0,2,0,0), (2,0,3,0,0), (2,0,4,0,0), (2,0,0,0,0), (2,0,1,0,0), (3,0,2,0,0), (3,0,3,0,0), (3,0,4,0,0), (3,0,0,0,0), (3,0,1,0,0), (4,0,2,0,0), (4,0,3,0,0), (4,0,4,0,0), (4,0,0,0,0), (4,0,1,0,0)]
def R95 : Fin 25 → Coordinate 1 := fun i => R95list.getD i.val (0,0,0,0,0)

theorem hpxR95 : Function.Injective (fun i => reduceAux 1 (basisAt rK95) (R95 i)) := by decide
theorem hcardq95 : Nat.card (Coordinate 1 ⧸ reps rK95) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (95, 0): |T| = 25 -/

def T95_0list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (1,0,2,0,0), (1,0,3,0,0), (1,0,4,0,0), (1,0,0,0,0), (1,0,1,0,0), (2,0,2,0,0), (2,0,3,0,0), (2,0,4,0,0), (2,0,0,0,0), (2,0,1,0,0), (3,0,2,0,0), (3,0,3,0,0), (3,0,4,0,0), (3,0,0,0,0), (3,0,1,0,0), (4,0,2,0,0), (4,0,3,0,0), (4,0,4,0,0), (4,0,0,0,0), (4,0,1,0,0)]
def T95_0 : Fin 25 → Coordinate 1 := fun i => T95_0list.getD i.val (0,0,0,0,0)

theorem hfix95_0 : ∀ i, ((T95_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK95)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95) :=
  repsFix_of_siftB rK95 ⟨0, by decide⟩ T95_0 (by decide)

theorem hinj95_0 : Function.Injective
    (fun i => ((T95_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK95)) :=
  repsInj_of_reduceAux rK95 T95_0 (by decide)

theorem hcardT95_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK95 ⟨0, by decide⟩ R95 hpxR95 hcardq95 (by decide)).symm

/-- **Cell (95, 0).** -/
theorem cell95_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK95) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK95) (charOfVec rK95 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK95 e (h : Coordinate 1) T95_0 i :=
  species_entry_eq_sum rK95 ⟨0, by decide⟩ e heK h T95_0 hfix95_0 hinj95_0 hcardT95_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK95) (T95_0 i) (hfix95_0 i) h)

/-! ## Cell (95, 10): |T| = 25 -/

def T95_10list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (1,0,2,0,0), (1,0,3,0,0), (1,0,4,0,0), (1,0,0,0,0), (1,0,1,0,0), (2,0,2,0,0), (2,0,3,0,0), (2,0,4,0,0), (2,0,0,0,0), (2,0,1,0,0), (3,0,2,0,0), (3,0,3,0,0), (3,0,4,0,0), (3,0,0,0,0), (3,0,1,0,0), (4,0,2,0,0), (4,0,3,0,0), (4,0,4,0,0), (4,0,0,0,0), (4,0,1,0,0)]
def T95_10 : Fin 25 → Coordinate 1 := fun i => T95_10list.getD i.val (0,0,0,0,0)

theorem hfix95_10 : ∀ i, ((T95_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK95)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95) :=
  repsFix_of_siftB rK95 ⟨10, by decide⟩ T95_10 (by decide)

theorem hinj95_10 : Function.Injective
    (fun i => ((T95_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK95)) :=
  repsInj_of_reduceAux rK95 T95_10 (by decide)

theorem hcardT95_10 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK95 ⟨10, by decide⟩ R95 hpxR95 hcardq95 (by decide)).symm

/-- **Cell (95, 10).** -/
theorem cell95_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK95) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK95) (charOfVec rK95 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK95 e (h : Coordinate 1) T95_10 i :=
  species_entry_eq_sum rK95 ⟨10, by decide⟩ e heK h T95_10 hfix95_10 hinj95_10 hcardT95_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK95) (T95_10 i) (hfix95_10 i) h)

/-! ## Cell (95, 12): |T| = 25 -/

def T95_12list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (1,0,2,0,0), (1,0,3,0,0), (1,0,4,0,0), (1,0,0,0,0), (1,0,1,0,0), (2,0,2,0,0), (2,0,3,0,0), (2,0,4,0,0), (2,0,0,0,0), (2,0,1,0,0), (3,0,2,0,0), (3,0,3,0,0), (3,0,4,0,0), (3,0,0,0,0), (3,0,1,0,0), (4,0,2,0,0), (4,0,3,0,0), (4,0,4,0,0), (4,0,0,0,0), (4,0,1,0,0)]
def T95_12 : Fin 25 → Coordinate 1 := fun i => T95_12list.getD i.val (0,0,0,0,0)

theorem hfix95_12 : ∀ i, ((T95_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK95)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95) :=
  repsFix_of_siftB rK95 ⟨12, by decide⟩ T95_12 (by decide)

theorem hinj95_12 : Function.Injective
    (fun i => ((T95_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK95)) :=
  repsInj_of_reduceAux rK95 T95_12 (by decide)

theorem hcardT95_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK95 ⟨12, by decide⟩ R95 hpxR95 hcardq95 (by decide)).symm

/-- **Cell (95, 12).** -/
theorem cell95_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK95) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK95) (charOfVec rK95 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK95 e (h : Coordinate 1) T95_12 i :=
  species_entry_eq_sum rK95 ⟨12, by decide⟩ e heK h T95_12 hfix95_12 hinj95_12 hcardT95_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK95) (T95_12 i) (hfix95_12 i) h)

/-! ## Cell (95, 33): |T| = 25 -/

def T95_33list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (1,0,2,0,0), (1,0,3,0,0), (1,0,4,0,0), (1,0,0,0,0), (1,0,1,0,0), (2,0,2,0,0), (2,0,3,0,0), (2,0,4,0,0), (2,0,0,0,0), (2,0,1,0,0), (3,0,2,0,0), (3,0,3,0,0), (3,0,4,0,0), (3,0,0,0,0), (3,0,1,0,0), (4,0,2,0,0), (4,0,3,0,0), (4,0,4,0,0), (4,0,0,0,0), (4,0,1,0,0)]
def T95_33 : Fin 25 → Coordinate 1 := fun i => T95_33list.getD i.val (0,0,0,0,0)

theorem hfix95_33 : ∀ i, ((T95_33 i : Coordinate 1) : Coordinate 1 ⧸ reps rK95)
    ∈ fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95) :=
  repsFix_of_siftB rK95 ⟨33, by decide⟩ T95_33 (by decide)

theorem hinj95_33 : Function.Injective
    (fun i => ((T95_33 i : Coordinate 1) : Coordinate 1 ⧸ reps rK95)) :=
  repsInj_of_reduceAux rK95 T95_33 (by decide)

theorem hcardT95_33 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK95 ⟨33, by decide⟩ R95 hpxR95 hcardq95 (by decide)).symm

/-- **Cell (95, 33).** -/
theorem cell95_33 (e : List (ZMod 25)) (heK : charOK (basisAt rK95) e = true)
    (h : ↥(reps (⟨33, by decide⟩ : Fin 148))) :
    species (reps (⟨33, by decide⟩ : Fin 148)) h (basisElt (reps rK95) (charOfVec rK95 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK95 e (h : Coordinate 1) T95_33 i :=
  species_entry_eq_sum rK95 ⟨33, by decide⟩ e heK h T95_33 hfix95_33 hinj95_33 hcardT95_33
    (fun i => conj_mem_of_fixedPoints (reps ⟨33, by decide⟩) (reps rK95) (T95_33 i) (hfix95_33 i) h)

/-! ## Cell (95, 53): |T| = 25 -/

def T95_53list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (1,0,2,0,0), (1,0,3,0,0), (1,0,4,0,0), (1,0,0,0,0), (1,0,1,0,0), (2,0,2,0,0), (2,0,3,0,0), (2,0,4,0,0), (2,0,0,0,0), (2,0,1,0,0), (3,0,2,0,0), (3,0,3,0,0), (3,0,4,0,0), (3,0,0,0,0), (3,0,1,0,0), (4,0,2,0,0), (4,0,3,0,0), (4,0,4,0,0), (4,0,0,0,0), (4,0,1,0,0)]
def T95_53 : Fin 25 → Coordinate 1 := fun i => T95_53list.getD i.val (0,0,0,0,0)

theorem hfix95_53 : ∀ i, ((T95_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK95)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95) :=
  repsFix_of_siftB rK95 ⟨53, by decide⟩ T95_53 (by decide)

theorem hinj95_53 : Function.Injective
    (fun i => ((T95_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK95)) :=
  repsInj_of_reduceAux rK95 T95_53 (by decide)

theorem hcardT95_53 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK95 ⟨53, by decide⟩ R95 hpxR95 hcardq95 (by decide)).symm

/-- **Cell (95, 53).** -/
theorem cell95_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK95) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK95) (charOfVec rK95 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK95 e (h : Coordinate 1) T95_53 i :=
  species_entry_eq_sum rK95 ⟨53, by decide⟩ e heK h T95_53 hfix95_53 hinj95_53 hcardT95_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK95) (T95_53 i) (hfix95_53 i) h)

/-! ## Cell (95, 95): |T| = 25 -/

def T95_95list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (1,0,2,0,0), (1,0,3,0,0), (1,0,4,0,0), (1,0,0,0,0), (1,0,1,0,0), (2,0,2,0,0), (2,0,3,0,0), (2,0,4,0,0), (2,0,0,0,0), (2,0,1,0,0), (3,0,2,0,0), (3,0,3,0,0), (3,0,4,0,0), (3,0,0,0,0), (3,0,1,0,0), (4,0,2,0,0), (4,0,3,0,0), (4,0,4,0,0), (4,0,0,0,0), (4,0,1,0,0)]
def T95_95 : Fin 25 → Coordinate 1 := fun i => T95_95list.getD i.val (0,0,0,0,0)

theorem hfix95_95 : ∀ i, ((T95_95 i : Coordinate 1) : Coordinate 1 ⧸ reps rK95)
    ∈ fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95) :=
  repsFix_of_siftB rK95 ⟨95, by decide⟩ T95_95 (by decide)

theorem hinj95_95 : Function.Injective
    (fun i => ((T95_95 i : Coordinate 1) : Coordinate 1 ⧸ reps rK95)) :=
  repsInj_of_reduceAux rK95 T95_95 (by decide)

theorem hcardT95_95 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK95 ⟨95, by decide⟩ R95 hpxR95 hcardq95 (by decide)).symm

/-- **Cell (95, 95).** -/
theorem cell95_95 (e : List (ZMod 25)) (heK : charOK (basisAt rK95) e = true)
    (h : ↥(reps (⟨95, by decide⟩ : Fin 148))) :
    species (reps (⟨95, by decide⟩ : Fin 148)) h (basisElt (reps rK95) (charOfVec rK95 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK95 e (h : Coordinate 1) T95_95 i :=
  species_entry_eq_sum rK95 ⟨95, by decide⟩ e heK h T95_95 hfix95_95 hinj95_95 hcardT95_95
    (fun i => conj_mem_of_fixedPoints (reps ⟨95, by decide⟩) (reps rK95) (T95_95 i) (hfix95_95 i) h)

namespace Q2

def R95_2 : Fin 25 → Coordinate 2 := fun i => R95list.getD i.val (0,0,0,0,0)
theorem hpxR95_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK95) (R95_2 i)) := by decide
theorem hcardq95_2 : Nat.card (Coordinate 2 ⧸ reps rK95) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (95, 0) twin -/

def T95_0_2 : Fin 25 → Coordinate 2 := fun i => T95_0list.getD i.val (0,0,0,0,0)

theorem hfix95_0_2 : ∀ i, ((T95_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK95)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK95) :=
  repsFix_of_siftB2 rK95 ⟨0, by decide⟩ T95_0_2 (by decide)

theorem hinj95_0_2 : Function.Injective
    (fun i => ((T95_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK95)) :=
  repsInj_of_reduceAux2 rK95 T95_0_2 (by decide)

theorem hcardT95_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK95)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK95 ⟨0, by decide⟩ R95_2 hpxR95_2 hcardq95_2 (by decide)).symm

/-- **Cell (95, 0) twin (q=2).** -/
theorem cell95_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK95) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK95) (charOfVec2 rK95 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK95 e (h : Coordinate 2) T95_0_2 i :=
  species_entry_eq_sum rK95 ⟨0, by decide⟩ e heK h T95_0_2 hfix95_0_2 hinj95_0_2 hcardT95_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK95) (T95_0_2 i) (hfix95_0_2 i) h)

/-! ### Cell (95, 10) twin -/

def T95_10_2 : Fin 25 → Coordinate 2 := fun i => T95_10list.getD i.val (0,0,0,0,0)

theorem hfix95_10_2 : ∀ i, ((T95_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK95)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK95) :=
  repsFix_of_siftB2 rK95 ⟨10, by decide⟩ T95_10_2 (by decide)

theorem hinj95_10_2 : Function.Injective
    (fun i => ((T95_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK95)) :=
  repsInj_of_reduceAux2 rK95 T95_10_2 (by decide)

theorem hcardT95_10_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK95)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK95 ⟨10, by decide⟩ R95_2 hpxR95_2 hcardq95_2 (by decide)).symm

/-- **Cell (95, 10) twin (q=2).** -/
theorem cell95_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK95) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK95) (charOfVec2 rK95 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK95 e (h : Coordinate 2) T95_10_2 i :=
  species_entry_eq_sum rK95 ⟨10, by decide⟩ e heK h T95_10_2 hfix95_10_2 hinj95_10_2 hcardT95_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK95) (T95_10_2 i) (hfix95_10_2 i) h)

/-! ### Cell (95, 12) twin -/

def T95_12_2 : Fin 25 → Coordinate 2 := fun i => T95_12list.getD i.val (0,0,0,0,0)

theorem hfix95_12_2 : ∀ i, ((T95_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK95)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK95) :=
  repsFix_of_siftB2 rK95 ⟨12, by decide⟩ T95_12_2 (by decide)

theorem hinj95_12_2 : Function.Injective
    (fun i => ((T95_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK95)) :=
  repsInj_of_reduceAux2 rK95 T95_12_2 (by decide)

theorem hcardT95_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK95)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK95 ⟨12, by decide⟩ R95_2 hpxR95_2 hcardq95_2 (by decide)).symm

/-- **Cell (95, 12) twin (q=2).** -/
theorem cell95_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK95) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK95) (charOfVec2 rK95 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK95 e (h : Coordinate 2) T95_12_2 i :=
  species_entry_eq_sum rK95 ⟨12, by decide⟩ e heK h T95_12_2 hfix95_12_2 hinj95_12_2 hcardT95_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK95) (T95_12_2 i) (hfix95_12_2 i) h)

/-! ### Cell (95, 33) twin -/

def T95_33_2 : Fin 25 → Coordinate 2 := fun i => T95_33list.getD i.val (0,0,0,0,0)

theorem hfix95_33_2 : ∀ i, ((T95_33_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK95)
    ∈ fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK95) :=
  repsFix_of_siftB2 rK95 ⟨33, by decide⟩ T95_33_2 (by decide)

theorem hinj95_33_2 : Function.Injective
    (fun i => ((T95_33_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK95)) :=
  repsInj_of_reduceAux2 rK95 T95_33_2 (by decide)

theorem hcardT95_33_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK95)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK95 ⟨33, by decide⟩ R95_2 hpxR95_2 hcardq95_2 (by decide)).symm

/-- **Cell (95, 33) twin (q=2).** -/
theorem cell95_33_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK95) e = true)
    (h : ↥(reps (⟨33, by decide⟩ : Fin 148))) :
    species (reps (⟨33, by decide⟩ : Fin 148)) h (basisElt (reps rK95) (charOfVec2 rK95 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK95 e (h : Coordinate 2) T95_33_2 i :=
  species_entry_eq_sum rK95 ⟨33, by decide⟩ e heK h T95_33_2 hfix95_33_2 hinj95_33_2 hcardT95_33_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨33, by decide⟩) (reps rK95) (T95_33_2 i) (hfix95_33_2 i) h)

/-! ### Cell (95, 53) twin -/

def T95_53_2 : Fin 25 → Coordinate 2 := fun i => T95_53list.getD i.val (0,0,0,0,0)

theorem hfix95_53_2 : ∀ i, ((T95_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK95)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK95) :=
  repsFix_of_siftB2 rK95 ⟨53, by decide⟩ T95_53_2 (by decide)

theorem hinj95_53_2 : Function.Injective
    (fun i => ((T95_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK95)) :=
  repsInj_of_reduceAux2 rK95 T95_53_2 (by decide)

theorem hcardT95_53_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK95)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK95 ⟨53, by decide⟩ R95_2 hpxR95_2 hcardq95_2 (by decide)).symm

/-- **Cell (95, 53) twin (q=2).** -/
theorem cell95_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK95) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK95) (charOfVec2 rK95 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK95 e (h : Coordinate 2) T95_53_2 i :=
  species_entry_eq_sum rK95 ⟨53, by decide⟩ e heK h T95_53_2 hfix95_53_2 hinj95_53_2 hcardT95_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK95) (T95_53_2 i) (hfix95_53_2 i) h)

/-! ### Cell (95, 95) twin -/

def T95_95_2 : Fin 25 → Coordinate 2 := fun i => T95_95list.getD i.val (0,0,0,0,0)

theorem hfix95_95_2 : ∀ i, ((T95_95_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK95)
    ∈ fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK95) :=
  repsFix_of_siftB2 rK95 ⟨95, by decide⟩ T95_95_2 (by decide)

theorem hinj95_95_2 : Function.Injective
    (fun i => ((T95_95_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK95)) :=
  repsInj_of_reduceAux2 rK95 T95_95_2 (by decide)

theorem hcardT95_95_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK95)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK95 ⟨95, by decide⟩ R95_2 hpxR95_2 hcardq95_2 (by decide)).symm

/-- **Cell (95, 95) twin (q=2).** -/
theorem cell95_95_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK95) e = true)
    (h : ↥(reps (⟨95, by decide⟩ : Fin 148))) :
    species (reps (⟨95, by decide⟩ : Fin 148)) h (basisElt (reps rK95) (charOfVec2 rK95 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK95 e (h : Coordinate 2) T95_95_2 i :=
  species_entry_eq_sum rK95 ⟨95, by decide⟩ e heK h T95_95_2 hfix95_95_2 hinj95_95_2 hcardT95_95_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨95, by decide⟩) (reps rK95) (T95_95_2 i) (hfix95_95_2 i) h)

end Q2

/-! # K-class rK = 96  (|G/K| = 25) -/

def rK96 : Fin 148 := ⟨96, by decide⟩

def R96list : List Coordinates := [(0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0)]
def R96 : Fin 25 → Coordinate 1 := fun i => R96list.getD i.val (0,0,0,0,0)

theorem hpxR96 : Function.Injective (fun i => reduceAux 1 (basisAt rK96) (R96 i)) := by decide
theorem hcardq96 : Nat.card (Coordinate 1 ⧸ reps rK96) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (96, 0): |T| = 25 -/

def T96_0list : List Coordinates := [(0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0)]
def T96_0 : Fin 25 → Coordinate 1 := fun i => T96_0list.getD i.val (0,0,0,0,0)

theorem hfix96_0 : ∀ i, ((T96_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK96)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96) :=
  repsFix_of_siftB rK96 ⟨0, by decide⟩ T96_0 (by decide)

theorem hinj96_0 : Function.Injective
    (fun i => ((T96_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK96)) :=
  repsInj_of_reduceAux rK96 T96_0 (by decide)

theorem hcardT96_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK96 ⟨0, by decide⟩ R96 hpxR96 hcardq96 (by decide)).symm

/-- **Cell (96, 0).** -/
theorem cell96_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK96) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK96) (charOfVec rK96 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK96 e (h : Coordinate 1) T96_0 i :=
  species_entry_eq_sum rK96 ⟨0, by decide⟩ e heK h T96_0 hfix96_0 hinj96_0 hcardT96_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK96) (T96_0 i) (hfix96_0 i) h)

/-! ## Cell (96, 10): |T| = 25 -/

def T96_10list : List Coordinates := [(0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0)]
def T96_10 : Fin 25 → Coordinate 1 := fun i => T96_10list.getD i.val (0,0,0,0,0)

theorem hfix96_10 : ∀ i, ((T96_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK96)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96) :=
  repsFix_of_siftB rK96 ⟨10, by decide⟩ T96_10 (by decide)

theorem hinj96_10 : Function.Injective
    (fun i => ((T96_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK96)) :=
  repsInj_of_reduceAux rK96 T96_10 (by decide)

theorem hcardT96_10 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK96 ⟨10, by decide⟩ R96 hpxR96 hcardq96 (by decide)).symm

/-- **Cell (96, 10).** -/
theorem cell96_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK96) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK96) (charOfVec rK96 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK96 e (h : Coordinate 1) T96_10 i :=
  species_entry_eq_sum rK96 ⟨10, by decide⟩ e heK h T96_10 hfix96_10 hinj96_10 hcardT96_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK96) (T96_10 i) (hfix96_10 i) h)

/-! ## Cell (96, 12): |T| = 25 -/

def T96_12list : List Coordinates := [(0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0)]
def T96_12 : Fin 25 → Coordinate 1 := fun i => T96_12list.getD i.val (0,0,0,0,0)

theorem hfix96_12 : ∀ i, ((T96_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK96)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96) :=
  repsFix_of_siftB rK96 ⟨12, by decide⟩ T96_12 (by decide)

theorem hinj96_12 : Function.Injective
    (fun i => ((T96_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK96)) :=
  repsInj_of_reduceAux rK96 T96_12 (by decide)

theorem hcardT96_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK96 ⟨12, by decide⟩ R96 hpxR96 hcardq96 (by decide)).symm

/-- **Cell (96, 12).** -/
theorem cell96_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK96) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK96) (charOfVec rK96 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK96 e (h : Coordinate 1) T96_12 i :=
  species_entry_eq_sum rK96 ⟨12, by decide⟩ e heK h T96_12 hfix96_12 hinj96_12 hcardT96_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK96) (T96_12 i) (hfix96_12 i) h)

/-! ## Cell (96, 34): |T| = 25 -/

def T96_34list : List Coordinates := [(0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0)]
def T96_34 : Fin 25 → Coordinate 1 := fun i => T96_34list.getD i.val (0,0,0,0,0)

theorem hfix96_34 : ∀ i, ((T96_34 i : Coordinate 1) : Coordinate 1 ⧸ reps rK96)
    ∈ fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96) :=
  repsFix_of_siftB rK96 ⟨34, by decide⟩ T96_34 (by decide)

theorem hinj96_34 : Function.Injective
    (fun i => ((T96_34 i : Coordinate 1) : Coordinate 1 ⧸ reps rK96)) :=
  repsInj_of_reduceAux rK96 T96_34 (by decide)

theorem hcardT96_34 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK96 ⟨34, by decide⟩ R96 hpxR96 hcardq96 (by decide)).symm

/-- **Cell (96, 34).** -/
theorem cell96_34 (e : List (ZMod 25)) (heK : charOK (basisAt rK96) e = true)
    (h : ↥(reps (⟨34, by decide⟩ : Fin 148))) :
    species (reps (⟨34, by decide⟩ : Fin 148)) h (basisElt (reps rK96) (charOfVec rK96 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK96 e (h : Coordinate 1) T96_34 i :=
  species_entry_eq_sum rK96 ⟨34, by decide⟩ e heK h T96_34 hfix96_34 hinj96_34 hcardT96_34
    (fun i => conj_mem_of_fixedPoints (reps ⟨34, by decide⟩) (reps rK96) (T96_34 i) (hfix96_34 i) h)

/-! ## Cell (96, 53): |T| = 25 -/

def T96_53list : List Coordinates := [(0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0)]
def T96_53 : Fin 25 → Coordinate 1 := fun i => T96_53list.getD i.val (0,0,0,0,0)

theorem hfix96_53 : ∀ i, ((T96_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK96)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96) :=
  repsFix_of_siftB rK96 ⟨53, by decide⟩ T96_53 (by decide)

theorem hinj96_53 : Function.Injective
    (fun i => ((T96_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK96)) :=
  repsInj_of_reduceAux rK96 T96_53 (by decide)

theorem hcardT96_53 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK96 ⟨53, by decide⟩ R96 hpxR96 hcardq96 (by decide)).symm

/-- **Cell (96, 53).** -/
theorem cell96_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK96) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK96) (charOfVec rK96 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK96 e (h : Coordinate 1) T96_53 i :=
  species_entry_eq_sum rK96 ⟨53, by decide⟩ e heK h T96_53 hfix96_53 hinj96_53 hcardT96_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK96) (T96_53 i) (hfix96_53 i) h)

/-! ## Cell (96, 96): |T| = 25 -/

def T96_96list : List Coordinates := [(0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0)]
def T96_96 : Fin 25 → Coordinate 1 := fun i => T96_96list.getD i.val (0,0,0,0,0)

theorem hfix96_96 : ∀ i, ((T96_96 i : Coordinate 1) : Coordinate 1 ⧸ reps rK96)
    ∈ fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96) :=
  repsFix_of_siftB rK96 ⟨96, by decide⟩ T96_96 (by decide)

theorem hinj96_96 : Function.Injective
    (fun i => ((T96_96 i : Coordinate 1) : Coordinate 1 ⧸ reps rK96)) :=
  repsInj_of_reduceAux rK96 T96_96 (by decide)

theorem hcardT96_96 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK96 ⟨96, by decide⟩ R96 hpxR96 hcardq96 (by decide)).symm

/-- **Cell (96, 96).** -/
theorem cell96_96 (e : List (ZMod 25)) (heK : charOK (basisAt rK96) e = true)
    (h : ↥(reps (⟨96, by decide⟩ : Fin 148))) :
    species (reps (⟨96, by decide⟩ : Fin 148)) h (basisElt (reps rK96) (charOfVec rK96 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK96 e (h : Coordinate 1) T96_96 i :=
  species_entry_eq_sum rK96 ⟨96, by decide⟩ e heK h T96_96 hfix96_96 hinj96_96 hcardT96_96
    (fun i => conj_mem_of_fixedPoints (reps ⟨96, by decide⟩) (reps rK96) (T96_96 i) (hfix96_96 i) h)

namespace Q2

def R96_2 : Fin 25 → Coordinate 2 := fun i => R96list.getD i.val (0,0,0,0,0)
theorem hpxR96_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK96) (R96_2 i)) := by decide
theorem hcardq96_2 : Nat.card (Coordinate 2 ⧸ reps rK96) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (96, 0) twin -/

def T96_0_2 : Fin 25 → Coordinate 2 := fun i => T96_0list.getD i.val (0,0,0,0,0)

theorem hfix96_0_2 : ∀ i, ((T96_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK96)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK96) :=
  repsFix_of_siftB2 rK96 ⟨0, by decide⟩ T96_0_2 (by decide)

theorem hinj96_0_2 : Function.Injective
    (fun i => ((T96_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK96)) :=
  repsInj_of_reduceAux2 rK96 T96_0_2 (by decide)

theorem hcardT96_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK96)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK96 ⟨0, by decide⟩ R96_2 hpxR96_2 hcardq96_2 (by decide)).symm

/-- **Cell (96, 0) twin (q=2).** -/
theorem cell96_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK96) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK96) (charOfVec2 rK96 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK96 e (h : Coordinate 2) T96_0_2 i :=
  species_entry_eq_sum rK96 ⟨0, by decide⟩ e heK h T96_0_2 hfix96_0_2 hinj96_0_2 hcardT96_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK96) (T96_0_2 i) (hfix96_0_2 i) h)

/-! ### Cell (96, 10) twin -/

def T96_10_2 : Fin 25 → Coordinate 2 := fun i => T96_10list.getD i.val (0,0,0,0,0)

theorem hfix96_10_2 : ∀ i, ((T96_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK96)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK96) :=
  repsFix_of_siftB2 rK96 ⟨10, by decide⟩ T96_10_2 (by decide)

theorem hinj96_10_2 : Function.Injective
    (fun i => ((T96_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK96)) :=
  repsInj_of_reduceAux2 rK96 T96_10_2 (by decide)

theorem hcardT96_10_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK96)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK96 ⟨10, by decide⟩ R96_2 hpxR96_2 hcardq96_2 (by decide)).symm

/-- **Cell (96, 10) twin (q=2).** -/
theorem cell96_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK96) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK96) (charOfVec2 rK96 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK96 e (h : Coordinate 2) T96_10_2 i :=
  species_entry_eq_sum rK96 ⟨10, by decide⟩ e heK h T96_10_2 hfix96_10_2 hinj96_10_2 hcardT96_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK96) (T96_10_2 i) (hfix96_10_2 i) h)

/-! ### Cell (96, 12) twin -/

def T96_12_2 : Fin 25 → Coordinate 2 := fun i => T96_12list.getD i.val (0,0,0,0,0)

theorem hfix96_12_2 : ∀ i, ((T96_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK96)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK96) :=
  repsFix_of_siftB2 rK96 ⟨12, by decide⟩ T96_12_2 (by decide)

theorem hinj96_12_2 : Function.Injective
    (fun i => ((T96_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK96)) :=
  repsInj_of_reduceAux2 rK96 T96_12_2 (by decide)

theorem hcardT96_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK96)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK96 ⟨12, by decide⟩ R96_2 hpxR96_2 hcardq96_2 (by decide)).symm

/-- **Cell (96, 12) twin (q=2).** -/
theorem cell96_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK96) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK96) (charOfVec2 rK96 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK96 e (h : Coordinate 2) T96_12_2 i :=
  species_entry_eq_sum rK96 ⟨12, by decide⟩ e heK h T96_12_2 hfix96_12_2 hinj96_12_2 hcardT96_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK96) (T96_12_2 i) (hfix96_12_2 i) h)

/-! ### Cell (96, 34) twin -/

def T96_34_2 : Fin 25 → Coordinate 2 := fun i => T96_34list.getD i.val (0,0,0,0,0)

theorem hfix96_34_2 : ∀ i, ((T96_34_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK96)
    ∈ fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK96) :=
  repsFix_of_siftB2 rK96 ⟨34, by decide⟩ T96_34_2 (by decide)

theorem hinj96_34_2 : Function.Injective
    (fun i => ((T96_34_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK96)) :=
  repsInj_of_reduceAux2 rK96 T96_34_2 (by decide)

theorem hcardT96_34_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK96)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK96 ⟨34, by decide⟩ R96_2 hpxR96_2 hcardq96_2 (by decide)).symm

/-- **Cell (96, 34) twin (q=2).** -/
theorem cell96_34_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK96) e = true)
    (h : ↥(reps (⟨34, by decide⟩ : Fin 148))) :
    species (reps (⟨34, by decide⟩ : Fin 148)) h (basisElt (reps rK96) (charOfVec2 rK96 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK96 e (h : Coordinate 2) T96_34_2 i :=
  species_entry_eq_sum rK96 ⟨34, by decide⟩ e heK h T96_34_2 hfix96_34_2 hinj96_34_2 hcardT96_34_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨34, by decide⟩) (reps rK96) (T96_34_2 i) (hfix96_34_2 i) h)

/-! ### Cell (96, 53) twin -/

def T96_53_2 : Fin 25 → Coordinate 2 := fun i => T96_53list.getD i.val (0,0,0,0,0)

theorem hfix96_53_2 : ∀ i, ((T96_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK96)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK96) :=
  repsFix_of_siftB2 rK96 ⟨53, by decide⟩ T96_53_2 (by decide)

theorem hinj96_53_2 : Function.Injective
    (fun i => ((T96_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK96)) :=
  repsInj_of_reduceAux2 rK96 T96_53_2 (by decide)

theorem hcardT96_53_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK96)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK96 ⟨53, by decide⟩ R96_2 hpxR96_2 hcardq96_2 (by decide)).symm

/-- **Cell (96, 53) twin (q=2).** -/
theorem cell96_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK96) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK96) (charOfVec2 rK96 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK96 e (h : Coordinate 2) T96_53_2 i :=
  species_entry_eq_sum rK96 ⟨53, by decide⟩ e heK h T96_53_2 hfix96_53_2 hinj96_53_2 hcardT96_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK96) (T96_53_2 i) (hfix96_53_2 i) h)

/-! ### Cell (96, 96) twin -/

def T96_96_2 : Fin 25 → Coordinate 2 := fun i => T96_96list.getD i.val (0,0,0,0,0)

theorem hfix96_96_2 : ∀ i, ((T96_96_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK96)
    ∈ fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK96) :=
  repsFix_of_siftB2 rK96 ⟨96, by decide⟩ T96_96_2 (by decide)

theorem hinj96_96_2 : Function.Injective
    (fun i => ((T96_96_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK96)) :=
  repsInj_of_reduceAux2 rK96 T96_96_2 (by decide)

theorem hcardT96_96_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK96)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK96 ⟨96, by decide⟩ R96_2 hpxR96_2 hcardq96_2 (by decide)).symm

/-- **Cell (96, 96) twin (q=2).** -/
theorem cell96_96_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK96) e = true)
    (h : ↥(reps (⟨96, by decide⟩ : Fin 148))) :
    species (reps (⟨96, by decide⟩ : Fin 148)) h (basisElt (reps rK96) (charOfVec2 rK96 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK96 e (h : Coordinate 2) T96_96_2 i :=
  species_entry_eq_sum rK96 ⟨96, by decide⟩ e heK h T96_96_2 hfix96_96_2 hinj96_96_2 hcardT96_96_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨96, by decide⟩) (reps rK96) (T96_96_2 i) (hfix96_96_2 i) h)

end Q2

/-! # K-class rK = 97  (|G/K| = 25) -/

def rK97 : Fin 148 := ⟨97, by decide⟩

def R97list : List Coordinates := [(0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0)]
def R97 : Fin 25 → Coordinate 1 := fun i => R97list.getD i.val (0,0,0,0,0)

theorem hpxR97 : Function.Injective (fun i => reduceAux 1 (basisAt rK97) (R97 i)) := by decide
theorem hcardq97 : Nat.card (Coordinate 1 ⧸ reps rK97) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (97, 0): |T| = 25 -/

def T97_0list : List Coordinates := [(0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0)]
def T97_0 : Fin 25 → Coordinate 1 := fun i => T97_0list.getD i.val (0,0,0,0,0)

theorem hfix97_0 : ∀ i, ((T97_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK97)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97) :=
  repsFix_of_siftB rK97 ⟨0, by decide⟩ T97_0 (by decide)

theorem hinj97_0 : Function.Injective
    (fun i => ((T97_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK97)) :=
  repsInj_of_reduceAux rK97 T97_0 (by decide)

theorem hcardT97_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK97 ⟨0, by decide⟩ R97 hpxR97 hcardq97 (by decide)).symm

/-- **Cell (97, 0).** -/
theorem cell97_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK97) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK97) (charOfVec rK97 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK97 e (h : Coordinate 1) T97_0 i :=
  species_entry_eq_sum rK97 ⟨0, by decide⟩ e heK h T97_0 hfix97_0 hinj97_0 hcardT97_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK97) (T97_0 i) (hfix97_0 i) h)

/-! ## Cell (97, 10): |T| = 25 -/

def T97_10list : List Coordinates := [(0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0)]
def T97_10 : Fin 25 → Coordinate 1 := fun i => T97_10list.getD i.val (0,0,0,0,0)

theorem hfix97_10 : ∀ i, ((T97_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK97)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97) :=
  repsFix_of_siftB rK97 ⟨10, by decide⟩ T97_10 (by decide)

theorem hinj97_10 : Function.Injective
    (fun i => ((T97_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK97)) :=
  repsInj_of_reduceAux rK97 T97_10 (by decide)

theorem hcardT97_10 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK97 ⟨10, by decide⟩ R97 hpxR97 hcardq97 (by decide)).symm

/-- **Cell (97, 10).** -/
theorem cell97_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK97) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK97) (charOfVec rK97 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK97 e (h : Coordinate 1) T97_10 i :=
  species_entry_eq_sum rK97 ⟨10, by decide⟩ e heK h T97_10 hfix97_10 hinj97_10 hcardT97_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK97) (T97_10 i) (hfix97_10 i) h)

/-! ## Cell (97, 12): |T| = 25 -/

def T97_12list : List Coordinates := [(0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0)]
def T97_12 : Fin 25 → Coordinate 1 := fun i => T97_12list.getD i.val (0,0,0,0,0)

theorem hfix97_12 : ∀ i, ((T97_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK97)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97) :=
  repsFix_of_siftB rK97 ⟨12, by decide⟩ T97_12 (by decide)

theorem hinj97_12 : Function.Injective
    (fun i => ((T97_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK97)) :=
  repsInj_of_reduceAux rK97 T97_12 (by decide)

theorem hcardT97_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK97 ⟨12, by decide⟩ R97 hpxR97 hcardq97 (by decide)).symm

/-- **Cell (97, 12).** -/
theorem cell97_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK97) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK97) (charOfVec rK97 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK97 e (h : Coordinate 1) T97_12 i :=
  species_entry_eq_sum rK97 ⟨12, by decide⟩ e heK h T97_12 hfix97_12 hinj97_12 hcardT97_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK97) (T97_12 i) (hfix97_12 i) h)

/-! ## Cell (97, 35): |T| = 25 -/

def T97_35list : List Coordinates := [(0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0)]
def T97_35 : Fin 25 → Coordinate 1 := fun i => T97_35list.getD i.val (0,0,0,0,0)

theorem hfix97_35 : ∀ i, ((T97_35 i : Coordinate 1) : Coordinate 1 ⧸ reps rK97)
    ∈ fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97) :=
  repsFix_of_siftB rK97 ⟨35, by decide⟩ T97_35 (by decide)

theorem hinj97_35 : Function.Injective
    (fun i => ((T97_35 i : Coordinate 1) : Coordinate 1 ⧸ reps rK97)) :=
  repsInj_of_reduceAux rK97 T97_35 (by decide)

theorem hcardT97_35 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK97 ⟨35, by decide⟩ R97 hpxR97 hcardq97 (by decide)).symm

/-- **Cell (97, 35).** -/
theorem cell97_35 (e : List (ZMod 25)) (heK : charOK (basisAt rK97) e = true)
    (h : ↥(reps (⟨35, by decide⟩ : Fin 148))) :
    species (reps (⟨35, by decide⟩ : Fin 148)) h (basisElt (reps rK97) (charOfVec rK97 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK97 e (h : Coordinate 1) T97_35 i :=
  species_entry_eq_sum rK97 ⟨35, by decide⟩ e heK h T97_35 hfix97_35 hinj97_35 hcardT97_35
    (fun i => conj_mem_of_fixedPoints (reps ⟨35, by decide⟩) (reps rK97) (T97_35 i) (hfix97_35 i) h)

/-! ## Cell (97, 53): |T| = 25 -/

def T97_53list : List Coordinates := [(0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0)]
def T97_53 : Fin 25 → Coordinate 1 := fun i => T97_53list.getD i.val (0,0,0,0,0)

theorem hfix97_53 : ∀ i, ((T97_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK97)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97) :=
  repsFix_of_siftB rK97 ⟨53, by decide⟩ T97_53 (by decide)

theorem hinj97_53 : Function.Injective
    (fun i => ((T97_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK97)) :=
  repsInj_of_reduceAux rK97 T97_53 (by decide)

theorem hcardT97_53 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK97 ⟨53, by decide⟩ R97 hpxR97 hcardq97 (by decide)).symm

/-- **Cell (97, 53).** -/
theorem cell97_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK97) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK97) (charOfVec rK97 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK97 e (h : Coordinate 1) T97_53 i :=
  species_entry_eq_sum rK97 ⟨53, by decide⟩ e heK h T97_53 hfix97_53 hinj97_53 hcardT97_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK97) (T97_53 i) (hfix97_53 i) h)

/-! ## Cell (97, 97): |T| = 25 -/

def T97_97list : List Coordinates := [(0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0)]
def T97_97 : Fin 25 → Coordinate 1 := fun i => T97_97list.getD i.val (0,0,0,0,0)

theorem hfix97_97 : ∀ i, ((T97_97 i : Coordinate 1) : Coordinate 1 ⧸ reps rK97)
    ∈ fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97) :=
  repsFix_of_siftB rK97 ⟨97, by decide⟩ T97_97 (by decide)

theorem hinj97_97 : Function.Injective
    (fun i => ((T97_97 i : Coordinate 1) : Coordinate 1 ⧸ reps rK97)) :=
  repsInj_of_reduceAux rK97 T97_97 (by decide)

theorem hcardT97_97 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK97 ⟨97, by decide⟩ R97 hpxR97 hcardq97 (by decide)).symm

/-- **Cell (97, 97).** -/
theorem cell97_97 (e : List (ZMod 25)) (heK : charOK (basisAt rK97) e = true)
    (h : ↥(reps (⟨97, by decide⟩ : Fin 148))) :
    species (reps (⟨97, by decide⟩ : Fin 148)) h (basisElt (reps rK97) (charOfVec rK97 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK97 e (h : Coordinate 1) T97_97 i :=
  species_entry_eq_sum rK97 ⟨97, by decide⟩ e heK h T97_97 hfix97_97 hinj97_97 hcardT97_97
    (fun i => conj_mem_of_fixedPoints (reps ⟨97, by decide⟩) (reps rK97) (T97_97 i) (hfix97_97 i) h)

namespace Q2

def R97_2 : Fin 25 → Coordinate 2 := fun i => R97list.getD i.val (0,0,0,0,0)
theorem hpxR97_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK97) (R97_2 i)) := by decide
theorem hcardq97_2 : Nat.card (Coordinate 2 ⧸ reps rK97) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (97, 0) twin -/

def T97_0_2 : Fin 25 → Coordinate 2 := fun i => T97_0list.getD i.val (0,0,0,0,0)

theorem hfix97_0_2 : ∀ i, ((T97_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK97)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK97) :=
  repsFix_of_siftB2 rK97 ⟨0, by decide⟩ T97_0_2 (by decide)

theorem hinj97_0_2 : Function.Injective
    (fun i => ((T97_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK97)) :=
  repsInj_of_reduceAux2 rK97 T97_0_2 (by decide)

theorem hcardT97_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK97)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK97 ⟨0, by decide⟩ R97_2 hpxR97_2 hcardq97_2 (by decide)).symm

/-- **Cell (97, 0) twin (q=2).** -/
theorem cell97_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK97) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK97) (charOfVec2 rK97 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK97 e (h : Coordinate 2) T97_0_2 i :=
  species_entry_eq_sum rK97 ⟨0, by decide⟩ e heK h T97_0_2 hfix97_0_2 hinj97_0_2 hcardT97_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK97) (T97_0_2 i) (hfix97_0_2 i) h)

/-! ### Cell (97, 10) twin -/

def T97_10_2 : Fin 25 → Coordinate 2 := fun i => T97_10list.getD i.val (0,0,0,0,0)

theorem hfix97_10_2 : ∀ i, ((T97_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK97)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK97) :=
  repsFix_of_siftB2 rK97 ⟨10, by decide⟩ T97_10_2 (by decide)

theorem hinj97_10_2 : Function.Injective
    (fun i => ((T97_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK97)) :=
  repsInj_of_reduceAux2 rK97 T97_10_2 (by decide)

theorem hcardT97_10_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK97)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK97 ⟨10, by decide⟩ R97_2 hpxR97_2 hcardq97_2 (by decide)).symm

/-- **Cell (97, 10) twin (q=2).** -/
theorem cell97_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK97) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK97) (charOfVec2 rK97 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK97 e (h : Coordinate 2) T97_10_2 i :=
  species_entry_eq_sum rK97 ⟨10, by decide⟩ e heK h T97_10_2 hfix97_10_2 hinj97_10_2 hcardT97_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK97) (T97_10_2 i) (hfix97_10_2 i) h)

/-! ### Cell (97, 12) twin -/

def T97_12_2 : Fin 25 → Coordinate 2 := fun i => T97_12list.getD i.val (0,0,0,0,0)

theorem hfix97_12_2 : ∀ i, ((T97_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK97)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK97) :=
  repsFix_of_siftB2 rK97 ⟨12, by decide⟩ T97_12_2 (by decide)

theorem hinj97_12_2 : Function.Injective
    (fun i => ((T97_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK97)) :=
  repsInj_of_reduceAux2 rK97 T97_12_2 (by decide)

theorem hcardT97_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK97)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK97 ⟨12, by decide⟩ R97_2 hpxR97_2 hcardq97_2 (by decide)).symm

/-- **Cell (97, 12) twin (q=2).** -/
theorem cell97_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK97) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK97) (charOfVec2 rK97 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK97 e (h : Coordinate 2) T97_12_2 i :=
  species_entry_eq_sum rK97 ⟨12, by decide⟩ e heK h T97_12_2 hfix97_12_2 hinj97_12_2 hcardT97_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK97) (T97_12_2 i) (hfix97_12_2 i) h)

/-! ### Cell (97, 35) twin -/

def T97_35_2 : Fin 25 → Coordinate 2 := fun i => T97_35list.getD i.val (0,0,0,0,0)

theorem hfix97_35_2 : ∀ i, ((T97_35_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK97)
    ∈ fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK97) :=
  repsFix_of_siftB2 rK97 ⟨35, by decide⟩ T97_35_2 (by decide)

theorem hinj97_35_2 : Function.Injective
    (fun i => ((T97_35_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK97)) :=
  repsInj_of_reduceAux2 rK97 T97_35_2 (by decide)

theorem hcardT97_35_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK97)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK97 ⟨35, by decide⟩ R97_2 hpxR97_2 hcardq97_2 (by decide)).symm

/-- **Cell (97, 35) twin (q=2).** -/
theorem cell97_35_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK97) e = true)
    (h : ↥(reps (⟨35, by decide⟩ : Fin 148))) :
    species (reps (⟨35, by decide⟩ : Fin 148)) h (basisElt (reps rK97) (charOfVec2 rK97 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK97 e (h : Coordinate 2) T97_35_2 i :=
  species_entry_eq_sum rK97 ⟨35, by decide⟩ e heK h T97_35_2 hfix97_35_2 hinj97_35_2 hcardT97_35_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨35, by decide⟩) (reps rK97) (T97_35_2 i) (hfix97_35_2 i) h)

/-! ### Cell (97, 53) twin -/

def T97_53_2 : Fin 25 → Coordinate 2 := fun i => T97_53list.getD i.val (0,0,0,0,0)

theorem hfix97_53_2 : ∀ i, ((T97_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK97)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK97) :=
  repsFix_of_siftB2 rK97 ⟨53, by decide⟩ T97_53_2 (by decide)

theorem hinj97_53_2 : Function.Injective
    (fun i => ((T97_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK97)) :=
  repsInj_of_reduceAux2 rK97 T97_53_2 (by decide)

theorem hcardT97_53_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK97)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK97 ⟨53, by decide⟩ R97_2 hpxR97_2 hcardq97_2 (by decide)).symm

/-- **Cell (97, 53) twin (q=2).** -/
theorem cell97_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK97) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK97) (charOfVec2 rK97 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK97 e (h : Coordinate 2) T97_53_2 i :=
  species_entry_eq_sum rK97 ⟨53, by decide⟩ e heK h T97_53_2 hfix97_53_2 hinj97_53_2 hcardT97_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK97) (T97_53_2 i) (hfix97_53_2 i) h)

/-! ### Cell (97, 97) twin -/

def T97_97_2 : Fin 25 → Coordinate 2 := fun i => T97_97list.getD i.val (0,0,0,0,0)

theorem hfix97_97_2 : ∀ i, ((T97_97_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK97)
    ∈ fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK97) :=
  repsFix_of_siftB2 rK97 ⟨97, by decide⟩ T97_97_2 (by decide)

theorem hinj97_97_2 : Function.Injective
    (fun i => ((T97_97_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK97)) :=
  repsInj_of_reduceAux2 rK97 T97_97_2 (by decide)

theorem hcardT97_97_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK97)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK97 ⟨97, by decide⟩ R97_2 hpxR97_2 hcardq97_2 (by decide)).symm

/-- **Cell (97, 97) twin (q=2).** -/
theorem cell97_97_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK97) e = true)
    (h : ↥(reps (⟨97, by decide⟩ : Fin 148))) :
    species (reps (⟨97, by decide⟩ : Fin 148)) h (basisElt (reps rK97) (charOfVec2 rK97 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK97 e (h : Coordinate 2) T97_97_2 i :=
  species_entry_eq_sum rK97 ⟨97, by decide⟩ e heK h T97_97_2 hfix97_97_2 hinj97_97_2 hcardT97_97_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨97, by decide⟩) (reps rK97) (T97_97_2 i) (hfix97_97_2 i) h)

end Q2

/-! # K-class rK = 98  (|G/K| = 25) -/

def rK98 : Fin 148 := ⟨98, by decide⟩

def R98list : List Coordinates := [(0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0)]
def R98 : Fin 25 → Coordinate 1 := fun i => R98list.getD i.val (0,0,0,0,0)

theorem hpxR98 : Function.Injective (fun i => reduceAux 1 (basisAt rK98) (R98 i)) := by decide
theorem hcardq98 : Nat.card (Coordinate 1 ⧸ reps rK98) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (98, 0): |T| = 25 -/

def T98_0list : List Coordinates := [(0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0)]
def T98_0 : Fin 25 → Coordinate 1 := fun i => T98_0list.getD i.val (0,0,0,0,0)

theorem hfix98_0 : ∀ i, ((T98_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK98)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98) :=
  repsFix_of_siftB rK98 ⟨0, by decide⟩ T98_0 (by decide)

theorem hinj98_0 : Function.Injective
    (fun i => ((T98_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK98)) :=
  repsInj_of_reduceAux rK98 T98_0 (by decide)

theorem hcardT98_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK98 ⟨0, by decide⟩ R98 hpxR98 hcardq98 (by decide)).symm

/-- **Cell (98, 0).** -/
theorem cell98_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK98) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK98) (charOfVec rK98 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK98 e (h : Coordinate 1) T98_0 i :=
  species_entry_eq_sum rK98 ⟨0, by decide⟩ e heK h T98_0 hfix98_0 hinj98_0 hcardT98_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK98) (T98_0 i) (hfix98_0 i) h)

/-! ## Cell (98, 10): |T| = 25 -/

def T98_10list : List Coordinates := [(0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0)]
def T98_10 : Fin 25 → Coordinate 1 := fun i => T98_10list.getD i.val (0,0,0,0,0)

theorem hfix98_10 : ∀ i, ((T98_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK98)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98) :=
  repsFix_of_siftB rK98 ⟨10, by decide⟩ T98_10 (by decide)

theorem hinj98_10 : Function.Injective
    (fun i => ((T98_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK98)) :=
  repsInj_of_reduceAux rK98 T98_10 (by decide)

theorem hcardT98_10 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK98 ⟨10, by decide⟩ R98 hpxR98 hcardq98 (by decide)).symm

/-- **Cell (98, 10).** -/
theorem cell98_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK98) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK98) (charOfVec rK98 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK98 e (h : Coordinate 1) T98_10 i :=
  species_entry_eq_sum rK98 ⟨10, by decide⟩ e heK h T98_10 hfix98_10 hinj98_10 hcardT98_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK98) (T98_10 i) (hfix98_10 i) h)

/-! ## Cell (98, 12): |T| = 25 -/

def T98_12list : List Coordinates := [(0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0)]
def T98_12 : Fin 25 → Coordinate 1 := fun i => T98_12list.getD i.val (0,0,0,0,0)

theorem hfix98_12 : ∀ i, ((T98_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK98)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98) :=
  repsFix_of_siftB rK98 ⟨12, by decide⟩ T98_12 (by decide)

theorem hinj98_12 : Function.Injective
    (fun i => ((T98_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK98)) :=
  repsInj_of_reduceAux rK98 T98_12 (by decide)

theorem hcardT98_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK98 ⟨12, by decide⟩ R98 hpxR98 hcardq98 (by decide)).symm

/-- **Cell (98, 12).** -/
theorem cell98_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK98) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK98) (charOfVec rK98 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK98 e (h : Coordinate 1) T98_12 i :=
  species_entry_eq_sum rK98 ⟨12, by decide⟩ e heK h T98_12 hfix98_12 hinj98_12 hcardT98_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK98) (T98_12 i) (hfix98_12 i) h)

/-! ## Cell (98, 36): |T| = 25 -/

def T98_36list : List Coordinates := [(0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0)]
def T98_36 : Fin 25 → Coordinate 1 := fun i => T98_36list.getD i.val (0,0,0,0,0)

theorem hfix98_36 : ∀ i, ((T98_36 i : Coordinate 1) : Coordinate 1 ⧸ reps rK98)
    ∈ fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98) :=
  repsFix_of_siftB rK98 ⟨36, by decide⟩ T98_36 (by decide)

theorem hinj98_36 : Function.Injective
    (fun i => ((T98_36 i : Coordinate 1) : Coordinate 1 ⧸ reps rK98)) :=
  repsInj_of_reduceAux rK98 T98_36 (by decide)

theorem hcardT98_36 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK98 ⟨36, by decide⟩ R98 hpxR98 hcardq98 (by decide)).symm

/-- **Cell (98, 36).** -/
theorem cell98_36 (e : List (ZMod 25)) (heK : charOK (basisAt rK98) e = true)
    (h : ↥(reps (⟨36, by decide⟩ : Fin 148))) :
    species (reps (⟨36, by decide⟩ : Fin 148)) h (basisElt (reps rK98) (charOfVec rK98 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK98 e (h : Coordinate 1) T98_36 i :=
  species_entry_eq_sum rK98 ⟨36, by decide⟩ e heK h T98_36 hfix98_36 hinj98_36 hcardT98_36
    (fun i => conj_mem_of_fixedPoints (reps ⟨36, by decide⟩) (reps rK98) (T98_36 i) (hfix98_36 i) h)

/-! ## Cell (98, 53): |T| = 25 -/

def T98_53list : List Coordinates := [(0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0)]
def T98_53 : Fin 25 → Coordinate 1 := fun i => T98_53list.getD i.val (0,0,0,0,0)

theorem hfix98_53 : ∀ i, ((T98_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK98)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98) :=
  repsFix_of_siftB rK98 ⟨53, by decide⟩ T98_53 (by decide)

theorem hinj98_53 : Function.Injective
    (fun i => ((T98_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK98)) :=
  repsInj_of_reduceAux rK98 T98_53 (by decide)

theorem hcardT98_53 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK98 ⟨53, by decide⟩ R98 hpxR98 hcardq98 (by decide)).symm

/-- **Cell (98, 53).** -/
theorem cell98_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK98) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK98) (charOfVec rK98 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK98 e (h : Coordinate 1) T98_53 i :=
  species_entry_eq_sum rK98 ⟨53, by decide⟩ e heK h T98_53 hfix98_53 hinj98_53 hcardT98_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK98) (T98_53 i) (hfix98_53 i) h)

/-! ## Cell (98, 98): |T| = 25 -/

def T98_98list : List Coordinates := [(0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0)]
def T98_98 : Fin 25 → Coordinate 1 := fun i => T98_98list.getD i.val (0,0,0,0,0)

theorem hfix98_98 : ∀ i, ((T98_98 i : Coordinate 1) : Coordinate 1 ⧸ reps rK98)
    ∈ fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98) :=
  repsFix_of_siftB rK98 ⟨98, by decide⟩ T98_98 (by decide)

theorem hinj98_98 : Function.Injective
    (fun i => ((T98_98 i : Coordinate 1) : Coordinate 1 ⧸ reps rK98)) :=
  repsInj_of_reduceAux rK98 T98_98 (by decide)

theorem hcardT98_98 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK98 ⟨98, by decide⟩ R98 hpxR98 hcardq98 (by decide)).symm

/-- **Cell (98, 98).** -/
theorem cell98_98 (e : List (ZMod 25)) (heK : charOK (basisAt rK98) e = true)
    (h : ↥(reps (⟨98, by decide⟩ : Fin 148))) :
    species (reps (⟨98, by decide⟩ : Fin 148)) h (basisElt (reps rK98) (charOfVec rK98 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK98 e (h : Coordinate 1) T98_98 i :=
  species_entry_eq_sum rK98 ⟨98, by decide⟩ e heK h T98_98 hfix98_98 hinj98_98 hcardT98_98
    (fun i => conj_mem_of_fixedPoints (reps ⟨98, by decide⟩) (reps rK98) (T98_98 i) (hfix98_98 i) h)

namespace Q2

def R98_2 : Fin 25 → Coordinate 2 := fun i => R98list.getD i.val (0,0,0,0,0)
theorem hpxR98_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK98) (R98_2 i)) := by decide
theorem hcardq98_2 : Nat.card (Coordinate 2 ⧸ reps rK98) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (98, 0) twin -/

def T98_0_2 : Fin 25 → Coordinate 2 := fun i => T98_0list.getD i.val (0,0,0,0,0)

theorem hfix98_0_2 : ∀ i, ((T98_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK98)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK98) :=
  repsFix_of_siftB2 rK98 ⟨0, by decide⟩ T98_0_2 (by decide)

theorem hinj98_0_2 : Function.Injective
    (fun i => ((T98_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK98)) :=
  repsInj_of_reduceAux2 rK98 T98_0_2 (by decide)

theorem hcardT98_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK98)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK98 ⟨0, by decide⟩ R98_2 hpxR98_2 hcardq98_2 (by decide)).symm

/-- **Cell (98, 0) twin (q=2).** -/
theorem cell98_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK98) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK98) (charOfVec2 rK98 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK98 e (h : Coordinate 2) T98_0_2 i :=
  species_entry_eq_sum rK98 ⟨0, by decide⟩ e heK h T98_0_2 hfix98_0_2 hinj98_0_2 hcardT98_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK98) (T98_0_2 i) (hfix98_0_2 i) h)

/-! ### Cell (98, 10) twin -/

def T98_10_2 : Fin 25 → Coordinate 2 := fun i => T98_10list.getD i.val (0,0,0,0,0)

theorem hfix98_10_2 : ∀ i, ((T98_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK98)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK98) :=
  repsFix_of_siftB2 rK98 ⟨10, by decide⟩ T98_10_2 (by decide)

theorem hinj98_10_2 : Function.Injective
    (fun i => ((T98_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK98)) :=
  repsInj_of_reduceAux2 rK98 T98_10_2 (by decide)

theorem hcardT98_10_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK98)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK98 ⟨10, by decide⟩ R98_2 hpxR98_2 hcardq98_2 (by decide)).symm

/-- **Cell (98, 10) twin (q=2).** -/
theorem cell98_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK98) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK98) (charOfVec2 rK98 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK98 e (h : Coordinate 2) T98_10_2 i :=
  species_entry_eq_sum rK98 ⟨10, by decide⟩ e heK h T98_10_2 hfix98_10_2 hinj98_10_2 hcardT98_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK98) (T98_10_2 i) (hfix98_10_2 i) h)

/-! ### Cell (98, 12) twin -/

def T98_12_2 : Fin 25 → Coordinate 2 := fun i => T98_12list.getD i.val (0,0,0,0,0)

theorem hfix98_12_2 : ∀ i, ((T98_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK98)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK98) :=
  repsFix_of_siftB2 rK98 ⟨12, by decide⟩ T98_12_2 (by decide)

theorem hinj98_12_2 : Function.Injective
    (fun i => ((T98_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK98)) :=
  repsInj_of_reduceAux2 rK98 T98_12_2 (by decide)

theorem hcardT98_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK98)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK98 ⟨12, by decide⟩ R98_2 hpxR98_2 hcardq98_2 (by decide)).symm

/-- **Cell (98, 12) twin (q=2).** -/
theorem cell98_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK98) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK98) (charOfVec2 rK98 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK98 e (h : Coordinate 2) T98_12_2 i :=
  species_entry_eq_sum rK98 ⟨12, by decide⟩ e heK h T98_12_2 hfix98_12_2 hinj98_12_2 hcardT98_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK98) (T98_12_2 i) (hfix98_12_2 i) h)

/-! ### Cell (98, 36) twin -/

def T98_36_2 : Fin 25 → Coordinate 2 := fun i => T98_36list.getD i.val (0,0,0,0,0)

theorem hfix98_36_2 : ∀ i, ((T98_36_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK98)
    ∈ fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK98) :=
  repsFix_of_siftB2 rK98 ⟨36, by decide⟩ T98_36_2 (by decide)

theorem hinj98_36_2 : Function.Injective
    (fun i => ((T98_36_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK98)) :=
  repsInj_of_reduceAux2 rK98 T98_36_2 (by decide)

theorem hcardT98_36_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK98)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK98 ⟨36, by decide⟩ R98_2 hpxR98_2 hcardq98_2 (by decide)).symm

/-- **Cell (98, 36) twin (q=2).** -/
theorem cell98_36_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK98) e = true)
    (h : ↥(reps (⟨36, by decide⟩ : Fin 148))) :
    species (reps (⟨36, by decide⟩ : Fin 148)) h (basisElt (reps rK98) (charOfVec2 rK98 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK98 e (h : Coordinate 2) T98_36_2 i :=
  species_entry_eq_sum rK98 ⟨36, by decide⟩ e heK h T98_36_2 hfix98_36_2 hinj98_36_2 hcardT98_36_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨36, by decide⟩) (reps rK98) (T98_36_2 i) (hfix98_36_2 i) h)

/-! ### Cell (98, 53) twin -/

def T98_53_2 : Fin 25 → Coordinate 2 := fun i => T98_53list.getD i.val (0,0,0,0,0)

theorem hfix98_53_2 : ∀ i, ((T98_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK98)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK98) :=
  repsFix_of_siftB2 rK98 ⟨53, by decide⟩ T98_53_2 (by decide)

theorem hinj98_53_2 : Function.Injective
    (fun i => ((T98_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK98)) :=
  repsInj_of_reduceAux2 rK98 T98_53_2 (by decide)

theorem hcardT98_53_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK98)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK98 ⟨53, by decide⟩ R98_2 hpxR98_2 hcardq98_2 (by decide)).symm

/-- **Cell (98, 53) twin (q=2).** -/
theorem cell98_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK98) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK98) (charOfVec2 rK98 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK98 e (h : Coordinate 2) T98_53_2 i :=
  species_entry_eq_sum rK98 ⟨53, by decide⟩ e heK h T98_53_2 hfix98_53_2 hinj98_53_2 hcardT98_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK98) (T98_53_2 i) (hfix98_53_2 i) h)

/-! ### Cell (98, 98) twin -/

def T98_98_2 : Fin 25 → Coordinate 2 := fun i => T98_98list.getD i.val (0,0,0,0,0)

theorem hfix98_98_2 : ∀ i, ((T98_98_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK98)
    ∈ fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK98) :=
  repsFix_of_siftB2 rK98 ⟨98, by decide⟩ T98_98_2 (by decide)

theorem hinj98_98_2 : Function.Injective
    (fun i => ((T98_98_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK98)) :=
  repsInj_of_reduceAux2 rK98 T98_98_2 (by decide)

theorem hcardT98_98_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK98)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK98 ⟨98, by decide⟩ R98_2 hpxR98_2 hcardq98_2 (by decide)).symm

/-- **Cell (98, 98) twin (q=2).** -/
theorem cell98_98_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK98) e = true)
    (h : ↥(reps (⟨98, by decide⟩ : Fin 148))) :
    species (reps (⟨98, by decide⟩ : Fin 148)) h (basisElt (reps rK98) (charOfVec2 rK98 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK98 e (h : Coordinate 2) T98_98_2 i :=
  species_entry_eq_sum rK98 ⟨98, by decide⟩ e heK h T98_98_2 hfix98_98_2 hinj98_98_2 hcardT98_98_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨98, by decide⟩) (reps rK98) (T98_98_2 i) (hfix98_98_2 i) h)

end Q2

/-! # K-class rK = 99  (|G/K| = 25) -/

def rK99 : Fin 148 := ⟨99, by decide⟩

def R99list : List Coordinates := [(0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def R99 : Fin 25 → Coordinate 1 := fun i => R99list.getD i.val (0,0,0,0,0)

theorem hpxR99 : Function.Injective (fun i => reduceAux 1 (basisAt rK99) (R99 i)) := by decide
theorem hcardq99 : Nat.card (Coordinate 1 ⧸ reps rK99) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (99, 0): |T| = 25 -/

def T99_0list : List Coordinates := [(0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T99_0 : Fin 25 → Coordinate 1 := fun i => T99_0list.getD i.val (0,0,0,0,0)

theorem hfix99_0 : ∀ i, ((T99_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK99)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99) :=
  repsFix_of_siftB rK99 ⟨0, by decide⟩ T99_0 (by decide)

theorem hinj99_0 : Function.Injective
    (fun i => ((T99_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK99)) :=
  repsInj_of_reduceAux rK99 T99_0 (by decide)

theorem hcardT99_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK99 ⟨0, by decide⟩ R99 hpxR99 hcardq99 (by decide)).symm

/-- **Cell (99, 0).** -/
theorem cell99_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK99) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK99) (charOfVec rK99 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK99 e (h : Coordinate 1) T99_0 i :=
  species_entry_eq_sum rK99 ⟨0, by decide⟩ e heK h T99_0 hfix99_0 hinj99_0 hcardT99_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK99) (T99_0 i) (hfix99_0 i) h)

/-! ## Cell (99, 10): |T| = 25 -/

def T99_10list : List Coordinates := [(0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T99_10 : Fin 25 → Coordinate 1 := fun i => T99_10list.getD i.val (0,0,0,0,0)

theorem hfix99_10 : ∀ i, ((T99_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK99)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99) :=
  repsFix_of_siftB rK99 ⟨10, by decide⟩ T99_10 (by decide)

theorem hinj99_10 : Function.Injective
    (fun i => ((T99_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK99)) :=
  repsInj_of_reduceAux rK99 T99_10 (by decide)

theorem hcardT99_10 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK99 ⟨10, by decide⟩ R99 hpxR99 hcardq99 (by decide)).symm

/-- **Cell (99, 10).** -/
theorem cell99_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK99) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK99) (charOfVec rK99 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK99 e (h : Coordinate 1) T99_10 i :=
  species_entry_eq_sum rK99 ⟨10, by decide⟩ e heK h T99_10 hfix99_10 hinj99_10 hcardT99_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK99) (T99_10 i) (hfix99_10 i) h)

/-! ## Cell (99, 12): |T| = 25 -/

def T99_12list : List Coordinates := [(0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T99_12 : Fin 25 → Coordinate 1 := fun i => T99_12list.getD i.val (0,0,0,0,0)

theorem hfix99_12 : ∀ i, ((T99_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK99)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99) :=
  repsFix_of_siftB rK99 ⟨12, by decide⟩ T99_12 (by decide)

theorem hinj99_12 : Function.Injective
    (fun i => ((T99_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK99)) :=
  repsInj_of_reduceAux rK99 T99_12 (by decide)

theorem hcardT99_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK99 ⟨12, by decide⟩ R99 hpxR99 hcardq99 (by decide)).symm

/-- **Cell (99, 12).** -/
theorem cell99_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK99) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK99) (charOfVec rK99 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK99 e (h : Coordinate 1) T99_12 i :=
  species_entry_eq_sum rK99 ⟨12, by decide⟩ e heK h T99_12 hfix99_12 hinj99_12 hcardT99_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK99) (T99_12 i) (hfix99_12 i) h)

/-! ## Cell (99, 37): |T| = 25 -/

def T99_37list : List Coordinates := [(0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T99_37 : Fin 25 → Coordinate 1 := fun i => T99_37list.getD i.val (0,0,0,0,0)

theorem hfix99_37 : ∀ i, ((T99_37 i : Coordinate 1) : Coordinate 1 ⧸ reps rK99)
    ∈ fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99) :=
  repsFix_of_siftB rK99 ⟨37, by decide⟩ T99_37 (by decide)

theorem hinj99_37 : Function.Injective
    (fun i => ((T99_37 i : Coordinate 1) : Coordinate 1 ⧸ reps rK99)) :=
  repsInj_of_reduceAux rK99 T99_37 (by decide)

theorem hcardT99_37 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK99 ⟨37, by decide⟩ R99 hpxR99 hcardq99 (by decide)).symm

/-- **Cell (99, 37).** -/
theorem cell99_37 (e : List (ZMod 25)) (heK : charOK (basisAt rK99) e = true)
    (h : ↥(reps (⟨37, by decide⟩ : Fin 148))) :
    species (reps (⟨37, by decide⟩ : Fin 148)) h (basisElt (reps rK99) (charOfVec rK99 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK99 e (h : Coordinate 1) T99_37 i :=
  species_entry_eq_sum rK99 ⟨37, by decide⟩ e heK h T99_37 hfix99_37 hinj99_37 hcardT99_37
    (fun i => conj_mem_of_fixedPoints (reps ⟨37, by decide⟩) (reps rK99) (T99_37 i) (hfix99_37 i) h)

/-! ## Cell (99, 53): |T| = 25 -/

def T99_53list : List Coordinates := [(0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T99_53 : Fin 25 → Coordinate 1 := fun i => T99_53list.getD i.val (0,0,0,0,0)

theorem hfix99_53 : ∀ i, ((T99_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK99)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99) :=
  repsFix_of_siftB rK99 ⟨53, by decide⟩ T99_53 (by decide)

theorem hinj99_53 : Function.Injective
    (fun i => ((T99_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK99)) :=
  repsInj_of_reduceAux rK99 T99_53 (by decide)

theorem hcardT99_53 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK99 ⟨53, by decide⟩ R99 hpxR99 hcardq99 (by decide)).symm

/-- **Cell (99, 53).** -/
theorem cell99_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK99) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK99) (charOfVec rK99 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK99 e (h : Coordinate 1) T99_53 i :=
  species_entry_eq_sum rK99 ⟨53, by decide⟩ e heK h T99_53 hfix99_53 hinj99_53 hcardT99_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK99) (T99_53 i) (hfix99_53 i) h)

/-! ## Cell (99, 99): |T| = 25 -/

def T99_99list : List Coordinates := [(0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T99_99 : Fin 25 → Coordinate 1 := fun i => T99_99list.getD i.val (0,0,0,0,0)

theorem hfix99_99 : ∀ i, ((T99_99 i : Coordinate 1) : Coordinate 1 ⧸ reps rK99)
    ∈ fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99) :=
  repsFix_of_siftB rK99 ⟨99, by decide⟩ T99_99 (by decide)

theorem hinj99_99 : Function.Injective
    (fun i => ((T99_99 i : Coordinate 1) : Coordinate 1 ⧸ reps rK99)) :=
  repsInj_of_reduceAux rK99 T99_99 (by decide)

theorem hcardT99_99 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK99 ⟨99, by decide⟩ R99 hpxR99 hcardq99 (by decide)).symm

/-- **Cell (99, 99).** -/
theorem cell99_99 (e : List (ZMod 25)) (heK : charOK (basisAt rK99) e = true)
    (h : ↥(reps (⟨99, by decide⟩ : Fin 148))) :
    species (reps (⟨99, by decide⟩ : Fin 148)) h (basisElt (reps rK99) (charOfVec rK99 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK99 e (h : Coordinate 1) T99_99 i :=
  species_entry_eq_sum rK99 ⟨99, by decide⟩ e heK h T99_99 hfix99_99 hinj99_99 hcardT99_99
    (fun i => conj_mem_of_fixedPoints (reps ⟨99, by decide⟩) (reps rK99) (T99_99 i) (hfix99_99 i) h)

namespace Q2

def R99_2 : Fin 25 → Coordinate 2 := fun i => R99list.getD i.val (0,0,0,0,0)
theorem hpxR99_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK99) (R99_2 i)) := by decide
theorem hcardq99_2 : Nat.card (Coordinate 2 ⧸ reps rK99) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (99, 0) twin -/

def T99_0_2 : Fin 25 → Coordinate 2 := fun i => T99_0list.getD i.val (0,0,0,0,0)

theorem hfix99_0_2 : ∀ i, ((T99_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK99)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK99) :=
  repsFix_of_siftB2 rK99 ⟨0, by decide⟩ T99_0_2 (by decide)

theorem hinj99_0_2 : Function.Injective
    (fun i => ((T99_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK99)) :=
  repsInj_of_reduceAux2 rK99 T99_0_2 (by decide)

theorem hcardT99_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK99)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK99 ⟨0, by decide⟩ R99_2 hpxR99_2 hcardq99_2 (by decide)).symm

/-- **Cell (99, 0) twin (q=2).** -/
theorem cell99_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK99) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK99) (charOfVec2 rK99 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK99 e (h : Coordinate 2) T99_0_2 i :=
  species_entry_eq_sum rK99 ⟨0, by decide⟩ e heK h T99_0_2 hfix99_0_2 hinj99_0_2 hcardT99_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK99) (T99_0_2 i) (hfix99_0_2 i) h)

/-! ### Cell (99, 10) twin -/

def T99_10_2 : Fin 25 → Coordinate 2 := fun i => T99_10list.getD i.val (0,0,0,0,0)

theorem hfix99_10_2 : ∀ i, ((T99_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK99)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK99) :=
  repsFix_of_siftB2 rK99 ⟨10, by decide⟩ T99_10_2 (by decide)

theorem hinj99_10_2 : Function.Injective
    (fun i => ((T99_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK99)) :=
  repsInj_of_reduceAux2 rK99 T99_10_2 (by decide)

theorem hcardT99_10_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK99)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK99 ⟨10, by decide⟩ R99_2 hpxR99_2 hcardq99_2 (by decide)).symm

/-- **Cell (99, 10) twin (q=2).** -/
theorem cell99_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK99) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK99) (charOfVec2 rK99 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK99 e (h : Coordinate 2) T99_10_2 i :=
  species_entry_eq_sum rK99 ⟨10, by decide⟩ e heK h T99_10_2 hfix99_10_2 hinj99_10_2 hcardT99_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK99) (T99_10_2 i) (hfix99_10_2 i) h)

/-! ### Cell (99, 12) twin -/

def T99_12_2 : Fin 25 → Coordinate 2 := fun i => T99_12list.getD i.val (0,0,0,0,0)

theorem hfix99_12_2 : ∀ i, ((T99_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK99)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK99) :=
  repsFix_of_siftB2 rK99 ⟨12, by decide⟩ T99_12_2 (by decide)

theorem hinj99_12_2 : Function.Injective
    (fun i => ((T99_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK99)) :=
  repsInj_of_reduceAux2 rK99 T99_12_2 (by decide)

theorem hcardT99_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK99)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK99 ⟨12, by decide⟩ R99_2 hpxR99_2 hcardq99_2 (by decide)).symm

/-- **Cell (99, 12) twin (q=2).** -/
theorem cell99_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK99) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK99) (charOfVec2 rK99 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK99 e (h : Coordinate 2) T99_12_2 i :=
  species_entry_eq_sum rK99 ⟨12, by decide⟩ e heK h T99_12_2 hfix99_12_2 hinj99_12_2 hcardT99_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK99) (T99_12_2 i) (hfix99_12_2 i) h)

/-! ### Cell (99, 37) twin -/

def T99_37_2 : Fin 25 → Coordinate 2 := fun i => T99_37list.getD i.val (0,0,0,0,0)

theorem hfix99_37_2 : ∀ i, ((T99_37_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK99)
    ∈ fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK99) :=
  repsFix_of_siftB2 rK99 ⟨37, by decide⟩ T99_37_2 (by decide)

theorem hinj99_37_2 : Function.Injective
    (fun i => ((T99_37_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK99)) :=
  repsInj_of_reduceAux2 rK99 T99_37_2 (by decide)

theorem hcardT99_37_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK99)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK99 ⟨37, by decide⟩ R99_2 hpxR99_2 hcardq99_2 (by decide)).symm

/-- **Cell (99, 37) twin (q=2).** -/
theorem cell99_37_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK99) e = true)
    (h : ↥(reps (⟨37, by decide⟩ : Fin 148))) :
    species (reps (⟨37, by decide⟩ : Fin 148)) h (basisElt (reps rK99) (charOfVec2 rK99 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK99 e (h : Coordinate 2) T99_37_2 i :=
  species_entry_eq_sum rK99 ⟨37, by decide⟩ e heK h T99_37_2 hfix99_37_2 hinj99_37_2 hcardT99_37_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨37, by decide⟩) (reps rK99) (T99_37_2 i) (hfix99_37_2 i) h)

/-! ### Cell (99, 53) twin -/

def T99_53_2 : Fin 25 → Coordinate 2 := fun i => T99_53list.getD i.val (0,0,0,0,0)

theorem hfix99_53_2 : ∀ i, ((T99_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK99)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK99) :=
  repsFix_of_siftB2 rK99 ⟨53, by decide⟩ T99_53_2 (by decide)

theorem hinj99_53_2 : Function.Injective
    (fun i => ((T99_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK99)) :=
  repsInj_of_reduceAux2 rK99 T99_53_2 (by decide)

theorem hcardT99_53_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK99)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK99 ⟨53, by decide⟩ R99_2 hpxR99_2 hcardq99_2 (by decide)).symm

/-- **Cell (99, 53) twin (q=2).** -/
theorem cell99_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK99) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK99) (charOfVec2 rK99 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK99 e (h : Coordinate 2) T99_53_2 i :=
  species_entry_eq_sum rK99 ⟨53, by decide⟩ e heK h T99_53_2 hfix99_53_2 hinj99_53_2 hcardT99_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK99) (T99_53_2 i) (hfix99_53_2 i) h)

/-! ### Cell (99, 99) twin -/

def T99_99_2 : Fin 25 → Coordinate 2 := fun i => T99_99list.getD i.val (0,0,0,0,0)

theorem hfix99_99_2 : ∀ i, ((T99_99_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK99)
    ∈ fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK99) :=
  repsFix_of_siftB2 rK99 ⟨99, by decide⟩ T99_99_2 (by decide)

theorem hinj99_99_2 : Function.Injective
    (fun i => ((T99_99_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK99)) :=
  repsInj_of_reduceAux2 rK99 T99_99_2 (by decide)

theorem hcardT99_99_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK99)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK99 ⟨99, by decide⟩ R99_2 hpxR99_2 hcardq99_2 (by decide)).symm

/-- **Cell (99, 99) twin (q=2).** -/
theorem cell99_99_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK99) e = true)
    (h : ↥(reps (⟨99, by decide⟩ : Fin 148))) :
    species (reps (⟨99, by decide⟩ : Fin 148)) h (basisElt (reps rK99) (charOfVec2 rK99 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK99 e (h : Coordinate 2) T99_99_2 i :=
  species_entry_eq_sum rK99 ⟨99, by decide⟩ e heK h T99_99_2 hfix99_99_2 hinj99_99_2 hcardT99_99_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨99, by decide⟩) (reps rK99) (T99_99_2 i) (hfix99_99_2 i) h)

end Q2

/-! # K-class rK = 100  (|G/K| = 25) -/

def rK100 : Fin 148 := ⟨100, by decide⟩

def R100list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (1,0,3,0,0), (1,0,4,0,0), (1,0,0,0,0), (1,0,1,0,0), (1,0,2,0,0), (2,0,3,0,0), (2,0,4,0,0), (2,0,0,0,0), (2,0,1,0,0), (2,0,2,0,0), (3,0,3,0,0), (3,0,4,0,0), (3,0,0,0,0), (3,0,1,0,0), (3,0,2,0,0), (4,0,3,0,0), (4,0,4,0,0), (4,0,0,0,0), (4,0,1,0,0), (4,0,2,0,0)]
def R100 : Fin 25 → Coordinate 1 := fun i => R100list.getD i.val (0,0,0,0,0)

theorem hpxR100 : Function.Injective (fun i => reduceAux 1 (basisAt rK100) (R100 i)) := by decide
theorem hcardq100 : Nat.card (Coordinate 1 ⧸ reps rK100) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (100, 0): |T| = 25 -/

def T100_0list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (1,0,3,0,0), (1,0,4,0,0), (1,0,0,0,0), (1,0,1,0,0), (1,0,2,0,0), (2,0,3,0,0), (2,0,4,0,0), (2,0,0,0,0), (2,0,1,0,0), (2,0,2,0,0), (3,0,3,0,0), (3,0,4,0,0), (3,0,0,0,0), (3,0,1,0,0), (3,0,2,0,0), (4,0,3,0,0), (4,0,4,0,0), (4,0,0,0,0), (4,0,1,0,0), (4,0,2,0,0)]
def T100_0 : Fin 25 → Coordinate 1 := fun i => T100_0list.getD i.val (0,0,0,0,0)

theorem hfix100_0 : ∀ i, ((T100_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK100)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100) :=
  repsFix_of_siftB rK100 ⟨0, by decide⟩ T100_0 (by decide)

theorem hinj100_0 : Function.Injective
    (fun i => ((T100_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK100)) :=
  repsInj_of_reduceAux rK100 T100_0 (by decide)

theorem hcardT100_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK100 ⟨0, by decide⟩ R100 hpxR100 hcardq100 (by decide)).symm

/-- **Cell (100, 0).** -/
theorem cell100_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK100) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK100) (charOfVec rK100 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK100 e (h : Coordinate 1) T100_0 i :=
  species_entry_eq_sum rK100 ⟨0, by decide⟩ e heK h T100_0 hfix100_0 hinj100_0 hcardT100_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK100) (T100_0 i) (hfix100_0 i) h)

/-! ## Cell (100, 10): |T| = 25 -/

def T100_10list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (1,0,3,0,0), (1,0,4,0,0), (1,0,0,0,0), (1,0,1,0,0), (1,0,2,0,0), (2,0,3,0,0), (2,0,4,0,0), (2,0,0,0,0), (2,0,1,0,0), (2,0,2,0,0), (3,0,3,0,0), (3,0,4,0,0), (3,0,0,0,0), (3,0,1,0,0), (3,0,2,0,0), (4,0,3,0,0), (4,0,4,0,0), (4,0,0,0,0), (4,0,1,0,0), (4,0,2,0,0)]
def T100_10 : Fin 25 → Coordinate 1 := fun i => T100_10list.getD i.val (0,0,0,0,0)

theorem hfix100_10 : ∀ i, ((T100_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK100)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100) :=
  repsFix_of_siftB rK100 ⟨10, by decide⟩ T100_10 (by decide)

theorem hinj100_10 : Function.Injective
    (fun i => ((T100_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK100)) :=
  repsInj_of_reduceAux rK100 T100_10 (by decide)

theorem hcardT100_10 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK100 ⟨10, by decide⟩ R100 hpxR100 hcardq100 (by decide)).symm

/-- **Cell (100, 10).** -/
theorem cell100_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK100) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK100) (charOfVec rK100 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK100 e (h : Coordinate 1) T100_10 i :=
  species_entry_eq_sum rK100 ⟨10, by decide⟩ e heK h T100_10 hfix100_10 hinj100_10 hcardT100_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK100) (T100_10 i) (hfix100_10 i) h)

/-! ## Cell (100, 12): |T| = 25 -/

def T100_12list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (1,0,3,0,0), (1,0,4,0,0), (1,0,0,0,0), (1,0,1,0,0), (1,0,2,0,0), (2,0,3,0,0), (2,0,4,0,0), (2,0,0,0,0), (2,0,1,0,0), (2,0,2,0,0), (3,0,3,0,0), (3,0,4,0,0), (3,0,0,0,0), (3,0,1,0,0), (3,0,2,0,0), (4,0,3,0,0), (4,0,4,0,0), (4,0,0,0,0), (4,0,1,0,0), (4,0,2,0,0)]
def T100_12 : Fin 25 → Coordinate 1 := fun i => T100_12list.getD i.val (0,0,0,0,0)

theorem hfix100_12 : ∀ i, ((T100_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK100)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100) :=
  repsFix_of_siftB rK100 ⟨12, by decide⟩ T100_12 (by decide)

theorem hinj100_12 : Function.Injective
    (fun i => ((T100_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK100)) :=
  repsInj_of_reduceAux rK100 T100_12 (by decide)

theorem hcardT100_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK100 ⟨12, by decide⟩ R100 hpxR100 hcardq100 (by decide)).symm

/-- **Cell (100, 12).** -/
theorem cell100_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK100) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK100) (charOfVec rK100 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK100 e (h : Coordinate 1) T100_12 i :=
  species_entry_eq_sum rK100 ⟨12, by decide⟩ e heK h T100_12 hfix100_12 hinj100_12 hcardT100_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK100) (T100_12 i) (hfix100_12 i) h)

/-! ## Cell (100, 38): |T| = 25 -/

def T100_38list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (1,0,3,0,0), (1,0,4,0,0), (1,0,0,0,0), (1,0,1,0,0), (1,0,2,0,0), (2,0,3,0,0), (2,0,4,0,0), (2,0,0,0,0), (2,0,1,0,0), (2,0,2,0,0), (3,0,3,0,0), (3,0,4,0,0), (3,0,0,0,0), (3,0,1,0,0), (3,0,2,0,0), (4,0,3,0,0), (4,0,4,0,0), (4,0,0,0,0), (4,0,1,0,0), (4,0,2,0,0)]
def T100_38 : Fin 25 → Coordinate 1 := fun i => T100_38list.getD i.val (0,0,0,0,0)

theorem hfix100_38 : ∀ i, ((T100_38 i : Coordinate 1) : Coordinate 1 ⧸ reps rK100)
    ∈ fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100) :=
  repsFix_of_siftB rK100 ⟨38, by decide⟩ T100_38 (by decide)

theorem hinj100_38 : Function.Injective
    (fun i => ((T100_38 i : Coordinate 1) : Coordinate 1 ⧸ reps rK100)) :=
  repsInj_of_reduceAux rK100 T100_38 (by decide)

theorem hcardT100_38 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK100 ⟨38, by decide⟩ R100 hpxR100 hcardq100 (by decide)).symm

/-- **Cell (100, 38).** -/
theorem cell100_38 (e : List (ZMod 25)) (heK : charOK (basisAt rK100) e = true)
    (h : ↥(reps (⟨38, by decide⟩ : Fin 148))) :
    species (reps (⟨38, by decide⟩ : Fin 148)) h (basisElt (reps rK100) (charOfVec rK100 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK100 e (h : Coordinate 1) T100_38 i :=
  species_entry_eq_sum rK100 ⟨38, by decide⟩ e heK h T100_38 hfix100_38 hinj100_38 hcardT100_38
    (fun i => conj_mem_of_fixedPoints (reps ⟨38, by decide⟩) (reps rK100) (T100_38 i) (hfix100_38 i) h)

/-! ## Cell (100, 53): |T| = 25 -/

def T100_53list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (1,0,3,0,0), (1,0,4,0,0), (1,0,0,0,0), (1,0,1,0,0), (1,0,2,0,0), (2,0,3,0,0), (2,0,4,0,0), (2,0,0,0,0), (2,0,1,0,0), (2,0,2,0,0), (3,0,3,0,0), (3,0,4,0,0), (3,0,0,0,0), (3,0,1,0,0), (3,0,2,0,0), (4,0,3,0,0), (4,0,4,0,0), (4,0,0,0,0), (4,0,1,0,0), (4,0,2,0,0)]
def T100_53 : Fin 25 → Coordinate 1 := fun i => T100_53list.getD i.val (0,0,0,0,0)

theorem hfix100_53 : ∀ i, ((T100_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK100)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100) :=
  repsFix_of_siftB rK100 ⟨53, by decide⟩ T100_53 (by decide)

theorem hinj100_53 : Function.Injective
    (fun i => ((T100_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK100)) :=
  repsInj_of_reduceAux rK100 T100_53 (by decide)

theorem hcardT100_53 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK100 ⟨53, by decide⟩ R100 hpxR100 hcardq100 (by decide)).symm

/-- **Cell (100, 53).** -/
theorem cell100_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK100) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK100) (charOfVec rK100 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK100 e (h : Coordinate 1) T100_53 i :=
  species_entry_eq_sum rK100 ⟨53, by decide⟩ e heK h T100_53 hfix100_53 hinj100_53 hcardT100_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK100) (T100_53 i) (hfix100_53 i) h)

/-! ## Cell (100, 100): |T| = 25 -/

def T100_100list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (1,0,3,0,0), (1,0,4,0,0), (1,0,0,0,0), (1,0,1,0,0), (1,0,2,0,0), (2,0,3,0,0), (2,0,4,0,0), (2,0,0,0,0), (2,0,1,0,0), (2,0,2,0,0), (3,0,3,0,0), (3,0,4,0,0), (3,0,0,0,0), (3,0,1,0,0), (3,0,2,0,0), (4,0,3,0,0), (4,0,4,0,0), (4,0,0,0,0), (4,0,1,0,0), (4,0,2,0,0)]
def T100_100 : Fin 25 → Coordinate 1 := fun i => T100_100list.getD i.val (0,0,0,0,0)

theorem hfix100_100 : ∀ i, ((T100_100 i : Coordinate 1) : Coordinate 1 ⧸ reps rK100)
    ∈ fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100) :=
  repsFix_of_siftB rK100 ⟨100, by decide⟩ T100_100 (by decide)

theorem hinj100_100 : Function.Injective
    (fun i => ((T100_100 i : Coordinate 1) : Coordinate 1 ⧸ reps rK100)) :=
  repsInj_of_reduceAux rK100 T100_100 (by decide)

theorem hcardT100_100 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK100 ⟨100, by decide⟩ R100 hpxR100 hcardq100 (by decide)).symm

/-- **Cell (100, 100).** -/
theorem cell100_100 (e : List (ZMod 25)) (heK : charOK (basisAt rK100) e = true)
    (h : ↥(reps (⟨100, by decide⟩ : Fin 148))) :
    species (reps (⟨100, by decide⟩ : Fin 148)) h (basisElt (reps rK100) (charOfVec rK100 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK100 e (h : Coordinate 1) T100_100 i :=
  species_entry_eq_sum rK100 ⟨100, by decide⟩ e heK h T100_100 hfix100_100 hinj100_100 hcardT100_100
    (fun i => conj_mem_of_fixedPoints (reps ⟨100, by decide⟩) (reps rK100) (T100_100 i) (hfix100_100 i) h)

namespace Q2

def R100_2 : Fin 25 → Coordinate 2 := fun i => R100list.getD i.val (0,0,0,0,0)
theorem hpxR100_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK100) (R100_2 i)) := by decide
theorem hcardq100_2 : Nat.card (Coordinate 2 ⧸ reps rK100) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (100, 0) twin -/

def T100_0_2 : Fin 25 → Coordinate 2 := fun i => T100_0list.getD i.val (0,0,0,0,0)

theorem hfix100_0_2 : ∀ i, ((T100_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK100)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK100) :=
  repsFix_of_siftB2 rK100 ⟨0, by decide⟩ T100_0_2 (by decide)

theorem hinj100_0_2 : Function.Injective
    (fun i => ((T100_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK100)) :=
  repsInj_of_reduceAux2 rK100 T100_0_2 (by decide)

theorem hcardT100_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK100)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK100 ⟨0, by decide⟩ R100_2 hpxR100_2 hcardq100_2 (by decide)).symm

/-- **Cell (100, 0) twin (q=2).** -/
theorem cell100_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK100) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK100) (charOfVec2 rK100 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK100 e (h : Coordinate 2) T100_0_2 i :=
  species_entry_eq_sum rK100 ⟨0, by decide⟩ e heK h T100_0_2 hfix100_0_2 hinj100_0_2 hcardT100_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK100) (T100_0_2 i) (hfix100_0_2 i) h)

/-! ### Cell (100, 10) twin -/

def T100_10_2 : Fin 25 → Coordinate 2 := fun i => T100_10list.getD i.val (0,0,0,0,0)

theorem hfix100_10_2 : ∀ i, ((T100_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK100)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK100) :=
  repsFix_of_siftB2 rK100 ⟨10, by decide⟩ T100_10_2 (by decide)

theorem hinj100_10_2 : Function.Injective
    (fun i => ((T100_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK100)) :=
  repsInj_of_reduceAux2 rK100 T100_10_2 (by decide)

theorem hcardT100_10_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK100)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK100 ⟨10, by decide⟩ R100_2 hpxR100_2 hcardq100_2 (by decide)).symm

/-- **Cell (100, 10) twin (q=2).** -/
theorem cell100_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK100) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK100) (charOfVec2 rK100 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK100 e (h : Coordinate 2) T100_10_2 i :=
  species_entry_eq_sum rK100 ⟨10, by decide⟩ e heK h T100_10_2 hfix100_10_2 hinj100_10_2 hcardT100_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK100) (T100_10_2 i) (hfix100_10_2 i) h)

/-! ### Cell (100, 12) twin -/

def T100_12_2 : Fin 25 → Coordinate 2 := fun i => T100_12list.getD i.val (0,0,0,0,0)

theorem hfix100_12_2 : ∀ i, ((T100_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK100)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK100) :=
  repsFix_of_siftB2 rK100 ⟨12, by decide⟩ T100_12_2 (by decide)

theorem hinj100_12_2 : Function.Injective
    (fun i => ((T100_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK100)) :=
  repsInj_of_reduceAux2 rK100 T100_12_2 (by decide)

theorem hcardT100_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK100)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK100 ⟨12, by decide⟩ R100_2 hpxR100_2 hcardq100_2 (by decide)).symm

/-- **Cell (100, 12) twin (q=2).** -/
theorem cell100_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK100) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK100) (charOfVec2 rK100 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK100 e (h : Coordinate 2) T100_12_2 i :=
  species_entry_eq_sum rK100 ⟨12, by decide⟩ e heK h T100_12_2 hfix100_12_2 hinj100_12_2 hcardT100_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK100) (T100_12_2 i) (hfix100_12_2 i) h)

/-! ### Cell (100, 38) twin -/

def T100_38_2 : Fin 25 → Coordinate 2 := fun i => T100_38list.getD i.val (0,0,0,0,0)

theorem hfix100_38_2 : ∀ i, ((T100_38_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK100)
    ∈ fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK100) :=
  repsFix_of_siftB2 rK100 ⟨38, by decide⟩ T100_38_2 (by decide)

theorem hinj100_38_2 : Function.Injective
    (fun i => ((T100_38_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK100)) :=
  repsInj_of_reduceAux2 rK100 T100_38_2 (by decide)

theorem hcardT100_38_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK100)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK100 ⟨38, by decide⟩ R100_2 hpxR100_2 hcardq100_2 (by decide)).symm

/-- **Cell (100, 38) twin (q=2).** -/
theorem cell100_38_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK100) e = true)
    (h : ↥(reps (⟨38, by decide⟩ : Fin 148))) :
    species (reps (⟨38, by decide⟩ : Fin 148)) h (basisElt (reps rK100) (charOfVec2 rK100 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK100 e (h : Coordinate 2) T100_38_2 i :=
  species_entry_eq_sum rK100 ⟨38, by decide⟩ e heK h T100_38_2 hfix100_38_2 hinj100_38_2 hcardT100_38_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨38, by decide⟩) (reps rK100) (T100_38_2 i) (hfix100_38_2 i) h)

/-! ### Cell (100, 53) twin -/

def T100_53_2 : Fin 25 → Coordinate 2 := fun i => T100_53list.getD i.val (0,0,0,0,0)

theorem hfix100_53_2 : ∀ i, ((T100_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK100)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK100) :=
  repsFix_of_siftB2 rK100 ⟨53, by decide⟩ T100_53_2 (by decide)

theorem hinj100_53_2 : Function.Injective
    (fun i => ((T100_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK100)) :=
  repsInj_of_reduceAux2 rK100 T100_53_2 (by decide)

theorem hcardT100_53_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK100)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK100 ⟨53, by decide⟩ R100_2 hpxR100_2 hcardq100_2 (by decide)).symm

/-- **Cell (100, 53) twin (q=2).** -/
theorem cell100_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK100) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK100) (charOfVec2 rK100 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK100 e (h : Coordinate 2) T100_53_2 i :=
  species_entry_eq_sum rK100 ⟨53, by decide⟩ e heK h T100_53_2 hfix100_53_2 hinj100_53_2 hcardT100_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK100) (T100_53_2 i) (hfix100_53_2 i) h)

/-! ### Cell (100, 100) twin -/

def T100_100_2 : Fin 25 → Coordinate 2 := fun i => T100_100list.getD i.val (0,0,0,0,0)

theorem hfix100_100_2 : ∀ i, ((T100_100_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK100)
    ∈ fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK100) :=
  repsFix_of_siftB2 rK100 ⟨100, by decide⟩ T100_100_2 (by decide)

theorem hinj100_100_2 : Function.Injective
    (fun i => ((T100_100_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK100)) :=
  repsInj_of_reduceAux2 rK100 T100_100_2 (by decide)

theorem hcardT100_100_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK100)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK100 ⟨100, by decide⟩ R100_2 hpxR100_2 hcardq100_2 (by decide)).symm

/-- **Cell (100, 100) twin (q=2).** -/
theorem cell100_100_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK100) e = true)
    (h : ↥(reps (⟨100, by decide⟩ : Fin 148))) :
    species (reps (⟨100, by decide⟩ : Fin 148)) h (basisElt (reps rK100) (charOfVec2 rK100 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK100 e (h : Coordinate 2) T100_100_2 i :=
  species_entry_eq_sum rK100 ⟨100, by decide⟩ e heK h T100_100_2 hfix100_100_2 hinj100_100_2 hcardT100_100_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨100, by decide⟩) (reps rK100) (T100_100_2 i) (hfix100_100_2 i) h)

end Q2

end LeanDring.P5Presentation
