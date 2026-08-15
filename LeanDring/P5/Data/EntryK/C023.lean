/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, K-strata data (5^3 stratum, rK 101-108): certified per-cell species-entry instantiations, both
twins.

Covers K-classes 101, 102, 103, 104, 105, 106, 107, 108 (order-5^3 K, |R|=25).  For each nonzero
`H`-column
(`(G/K)^H ≠ ∅`), the full coset transversal `R101..` and each `H`-fixed
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

/-! # K-class rK = 101  (|G/K| = 25) -/

def rK101 : Fin 148 := ⟨101, by decide⟩

def R101list : List Coordinates := [(0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0)]
def R101 : Fin 25 → Coordinate 1 := fun i => R101list.getD i.val (0,0,0,0,0)

theorem hpxR101 : Function.Injective (fun i => reduceAux 1 (basisAt rK101) (R101 i)) := by decide
theorem hcardq101 : Nat.card (Coordinate 1 ⧸ reps rK101) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (101, 0): |T| = 25 -/

def T101_0list : List Coordinates := [(0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0)]
def T101_0 : Fin 25 → Coordinate 1 := fun i => T101_0list.getD i.val (0,0,0,0,0)

theorem hfix101_0 : ∀ i, ((T101_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK101)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101) :=
  repsFix_of_siftB rK101 ⟨0, by decide⟩ T101_0 (by decide)

theorem hinj101_0 : Function.Injective
    (fun i => ((T101_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK101)) :=
  repsInj_of_reduceAux rK101 T101_0 (by decide)

theorem hcardT101_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK101 ⟨0, by decide⟩ R101 hpxR101 hcardq101 (by decide)).symm

/-- **Cell (101, 0).** -/
theorem cell101_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK101) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK101) (charOfVec rK101 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK101 e (h : Coordinate 1) T101_0 i :=
  species_entry_eq_sum rK101 ⟨0, by decide⟩ e heK h T101_0 hfix101_0 hinj101_0 hcardT101_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK101) (T101_0 i) (hfix101_0 i) h)

/-! ## Cell (101, 10): |T| = 25 -/

def T101_10list : List Coordinates := [(0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0)]
def T101_10 : Fin 25 → Coordinate 1 := fun i => T101_10list.getD i.val (0,0,0,0,0)

theorem hfix101_10 : ∀ i, ((T101_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK101)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101) :=
  repsFix_of_siftB rK101 ⟨10, by decide⟩ T101_10 (by decide)

theorem hinj101_10 : Function.Injective
    (fun i => ((T101_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK101)) :=
  repsInj_of_reduceAux rK101 T101_10 (by decide)

theorem hcardT101_10 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK101 ⟨10, by decide⟩ R101 hpxR101 hcardq101 (by decide)).symm

/-- **Cell (101, 10).** -/
theorem cell101_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK101) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK101) (charOfVec rK101 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK101 e (h : Coordinate 1) T101_10 i :=
  species_entry_eq_sum rK101 ⟨10, by decide⟩ e heK h T101_10 hfix101_10 hinj101_10 hcardT101_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK101) (T101_10 i) (hfix101_10 i) h)

/-! ## Cell (101, 12): |T| = 25 -/

def T101_12list : List Coordinates := [(0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0)]
def T101_12 : Fin 25 → Coordinate 1 := fun i => T101_12list.getD i.val (0,0,0,0,0)

theorem hfix101_12 : ∀ i, ((T101_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK101)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101) :=
  repsFix_of_siftB rK101 ⟨12, by decide⟩ T101_12 (by decide)

theorem hinj101_12 : Function.Injective
    (fun i => ((T101_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK101)) :=
  repsInj_of_reduceAux rK101 T101_12 (by decide)

theorem hcardT101_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK101 ⟨12, by decide⟩ R101 hpxR101 hcardq101 (by decide)).symm

/-- **Cell (101, 12).** -/
theorem cell101_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK101) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK101) (charOfVec rK101 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK101 e (h : Coordinate 1) T101_12 i :=
  species_entry_eq_sum rK101 ⟨12, by decide⟩ e heK h T101_12 hfix101_12 hinj101_12 hcardT101_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK101) (T101_12 i) (hfix101_12 i) h)

/-! ## Cell (101, 39): |T| = 25 -/

def T101_39list : List Coordinates := [(0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0)]
def T101_39 : Fin 25 → Coordinate 1 := fun i => T101_39list.getD i.val (0,0,0,0,0)

theorem hfix101_39 : ∀ i, ((T101_39 i : Coordinate 1) : Coordinate 1 ⧸ reps rK101)
    ∈ fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101) :=
  repsFix_of_siftB rK101 ⟨39, by decide⟩ T101_39 (by decide)

theorem hinj101_39 : Function.Injective
    (fun i => ((T101_39 i : Coordinate 1) : Coordinate 1 ⧸ reps rK101)) :=
  repsInj_of_reduceAux rK101 T101_39 (by decide)

theorem hcardT101_39 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK101 ⟨39, by decide⟩ R101 hpxR101 hcardq101 (by decide)).symm

/-- **Cell (101, 39).** -/
theorem cell101_39 (e : List (ZMod 25)) (heK : charOK (basisAt rK101) e = true)
    (h : ↥(reps (⟨39, by decide⟩ : Fin 148))) :
    species (reps (⟨39, by decide⟩ : Fin 148)) h (basisElt (reps rK101) (charOfVec rK101 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK101 e (h : Coordinate 1) T101_39 i :=
  species_entry_eq_sum rK101 ⟨39, by decide⟩ e heK h T101_39 hfix101_39 hinj101_39 hcardT101_39
    (fun i => conj_mem_of_fixedPoints (reps ⟨39, by decide⟩) (reps rK101) (T101_39 i) (hfix101_39 i) h)

/-! ## Cell (101, 53): |T| = 25 -/

def T101_53list : List Coordinates := [(0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0)]
def T101_53 : Fin 25 → Coordinate 1 := fun i => T101_53list.getD i.val (0,0,0,0,0)

theorem hfix101_53 : ∀ i, ((T101_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK101)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101) :=
  repsFix_of_siftB rK101 ⟨53, by decide⟩ T101_53 (by decide)

theorem hinj101_53 : Function.Injective
    (fun i => ((T101_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK101)) :=
  repsInj_of_reduceAux rK101 T101_53 (by decide)

theorem hcardT101_53 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK101 ⟨53, by decide⟩ R101 hpxR101 hcardq101 (by decide)).symm

/-- **Cell (101, 53).** -/
theorem cell101_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK101) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK101) (charOfVec rK101 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK101 e (h : Coordinate 1) T101_53 i :=
  species_entry_eq_sum rK101 ⟨53, by decide⟩ e heK h T101_53 hfix101_53 hinj101_53 hcardT101_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK101) (T101_53 i) (hfix101_53 i) h)

/-! ## Cell (101, 101): |T| = 25 -/

def T101_101list : List Coordinates := [(0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0)]
def T101_101 : Fin 25 → Coordinate 1 := fun i => T101_101list.getD i.val (0,0,0,0,0)

theorem hfix101_101 : ∀ i, ((T101_101 i : Coordinate 1) : Coordinate 1 ⧸ reps rK101)
    ∈ fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101) :=
  repsFix_of_siftB rK101 ⟨101, by decide⟩ T101_101 (by decide)

theorem hinj101_101 : Function.Injective
    (fun i => ((T101_101 i : Coordinate 1) : Coordinate 1 ⧸ reps rK101)) :=
  repsInj_of_reduceAux rK101 T101_101 (by decide)

theorem hcardT101_101 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK101 ⟨101, by decide⟩ R101 hpxR101 hcardq101 (by decide)).symm

/-- **Cell (101, 101).** -/
theorem cell101_101 (e : List (ZMod 25)) (heK : charOK (basisAt rK101) e = true)
    (h : ↥(reps (⟨101, by decide⟩ : Fin 148))) :
    species (reps (⟨101, by decide⟩ : Fin 148)) h (basisElt (reps rK101) (charOfVec rK101 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK101 e (h : Coordinate 1) T101_101 i :=
  species_entry_eq_sum rK101 ⟨101, by decide⟩ e heK h T101_101 hfix101_101 hinj101_101 hcardT101_101
    (fun i => conj_mem_of_fixedPoints (reps ⟨101, by decide⟩) (reps rK101) (T101_101 i) (hfix101_101 i) h)

namespace Q2

def R101_2 : Fin 25 → Coordinate 2 := fun i => R101list.getD i.val (0,0,0,0,0)
theorem hpxR101_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK101) (R101_2 i)) := by decide
theorem hcardq101_2 : Nat.card (Coordinate 2 ⧸ reps rK101) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (101, 0) twin -/

def T101_0_2 : Fin 25 → Coordinate 2 := fun i => T101_0list.getD i.val (0,0,0,0,0)

theorem hfix101_0_2 : ∀ i, ((T101_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK101)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK101) :=
  repsFix_of_siftB2 rK101 ⟨0, by decide⟩ T101_0_2 (by decide)

theorem hinj101_0_2 : Function.Injective
    (fun i => ((T101_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK101)) :=
  repsInj_of_reduceAux2 rK101 T101_0_2 (by decide)

theorem hcardT101_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK101)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK101 ⟨0, by decide⟩ R101_2 hpxR101_2 hcardq101_2 (by decide)).symm

/-- **Cell (101, 0) twin (q=2).** -/
theorem cell101_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK101) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK101) (charOfVec2 rK101 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK101 e (h : Coordinate 2) T101_0_2 i :=
  species_entry_eq_sum rK101 ⟨0, by decide⟩ e heK h T101_0_2 hfix101_0_2 hinj101_0_2 hcardT101_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK101) (T101_0_2 i) (hfix101_0_2 i) h)

/-! ### Cell (101, 10) twin -/

def T101_10_2 : Fin 25 → Coordinate 2 := fun i => T101_10list.getD i.val (0,0,0,0,0)

theorem hfix101_10_2 : ∀ i, ((T101_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK101)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK101) :=
  repsFix_of_siftB2 rK101 ⟨10, by decide⟩ T101_10_2 (by decide)

theorem hinj101_10_2 : Function.Injective
    (fun i => ((T101_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK101)) :=
  repsInj_of_reduceAux2 rK101 T101_10_2 (by decide)

theorem hcardT101_10_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK101)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK101 ⟨10, by decide⟩ R101_2 hpxR101_2 hcardq101_2 (by decide)).symm

/-- **Cell (101, 10) twin (q=2).** -/
theorem cell101_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK101) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK101) (charOfVec2 rK101 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK101 e (h : Coordinate 2) T101_10_2 i :=
  species_entry_eq_sum rK101 ⟨10, by decide⟩ e heK h T101_10_2 hfix101_10_2 hinj101_10_2 hcardT101_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK101) (T101_10_2 i) (hfix101_10_2 i) h)

/-! ### Cell (101, 12) twin -/

def T101_12_2 : Fin 25 → Coordinate 2 := fun i => T101_12list.getD i.val (0,0,0,0,0)

theorem hfix101_12_2 : ∀ i, ((T101_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK101)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK101) :=
  repsFix_of_siftB2 rK101 ⟨12, by decide⟩ T101_12_2 (by decide)

theorem hinj101_12_2 : Function.Injective
    (fun i => ((T101_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK101)) :=
  repsInj_of_reduceAux2 rK101 T101_12_2 (by decide)

theorem hcardT101_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK101)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK101 ⟨12, by decide⟩ R101_2 hpxR101_2 hcardq101_2 (by decide)).symm

/-- **Cell (101, 12) twin (q=2).** -/
theorem cell101_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK101) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK101) (charOfVec2 rK101 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK101 e (h : Coordinate 2) T101_12_2 i :=
  species_entry_eq_sum rK101 ⟨12, by decide⟩ e heK h T101_12_2 hfix101_12_2 hinj101_12_2 hcardT101_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK101) (T101_12_2 i) (hfix101_12_2 i) h)

/-! ### Cell (101, 39) twin -/

def T101_39_2 : Fin 25 → Coordinate 2 := fun i => T101_39list.getD i.val (0,0,0,0,0)

theorem hfix101_39_2 : ∀ i, ((T101_39_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK101)
    ∈ fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK101) :=
  repsFix_of_siftB2 rK101 ⟨39, by decide⟩ T101_39_2 (by decide)

theorem hinj101_39_2 : Function.Injective
    (fun i => ((T101_39_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK101)) :=
  repsInj_of_reduceAux2 rK101 T101_39_2 (by decide)

theorem hcardT101_39_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK101)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK101 ⟨39, by decide⟩ R101_2 hpxR101_2 hcardq101_2 (by decide)).symm

/-- **Cell (101, 39) twin (q=2).** -/
theorem cell101_39_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK101) e = true)
    (h : ↥(reps (⟨39, by decide⟩ : Fin 148))) :
    species (reps (⟨39, by decide⟩ : Fin 148)) h (basisElt (reps rK101) (charOfVec2 rK101 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK101 e (h : Coordinate 2) T101_39_2 i :=
  species_entry_eq_sum rK101 ⟨39, by decide⟩ e heK h T101_39_2 hfix101_39_2 hinj101_39_2 hcardT101_39_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨39, by decide⟩) (reps rK101) (T101_39_2 i) (hfix101_39_2 i) h)

/-! ### Cell (101, 53) twin -/

def T101_53_2 : Fin 25 → Coordinate 2 := fun i => T101_53list.getD i.val (0,0,0,0,0)

theorem hfix101_53_2 : ∀ i, ((T101_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK101)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK101) :=
  repsFix_of_siftB2 rK101 ⟨53, by decide⟩ T101_53_2 (by decide)

theorem hinj101_53_2 : Function.Injective
    (fun i => ((T101_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK101)) :=
  repsInj_of_reduceAux2 rK101 T101_53_2 (by decide)

theorem hcardT101_53_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK101)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK101 ⟨53, by decide⟩ R101_2 hpxR101_2 hcardq101_2 (by decide)).symm

/-- **Cell (101, 53) twin (q=2).** -/
theorem cell101_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK101) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK101) (charOfVec2 rK101 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK101 e (h : Coordinate 2) T101_53_2 i :=
  species_entry_eq_sum rK101 ⟨53, by decide⟩ e heK h T101_53_2 hfix101_53_2 hinj101_53_2 hcardT101_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK101) (T101_53_2 i) (hfix101_53_2 i) h)

/-! ### Cell (101, 101) twin -/

def T101_101_2 : Fin 25 → Coordinate 2 := fun i => T101_101list.getD i.val (0,0,0,0,0)

theorem hfix101_101_2 : ∀ i, ((T101_101_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK101)
    ∈ fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK101) :=
  repsFix_of_siftB2 rK101 ⟨101, by decide⟩ T101_101_2 (by decide)

theorem hinj101_101_2 : Function.Injective
    (fun i => ((T101_101_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK101)) :=
  repsInj_of_reduceAux2 rK101 T101_101_2 (by decide)

theorem hcardT101_101_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK101)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK101 ⟨101, by decide⟩ R101_2 hpxR101_2 hcardq101_2 (by decide)).symm

/-- **Cell (101, 101) twin (q=2).** -/
theorem cell101_101_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK101) e = true)
    (h : ↥(reps (⟨101, by decide⟩ : Fin 148))) :
    species (reps (⟨101, by decide⟩ : Fin 148)) h (basisElt (reps rK101) (charOfVec2 rK101 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK101 e (h : Coordinate 2) T101_101_2 i :=
  species_entry_eq_sum rK101 ⟨101, by decide⟩ e heK h T101_101_2 hfix101_101_2 hinj101_101_2 hcardT101_101_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨101, by decide⟩) (reps rK101) (T101_101_2 i) (hfix101_101_2 i) h)

end Q2

/-! # K-class rK = 102  (|G/K| = 25) -/

def rK102 : Fin 148 := ⟨102, by decide⟩

def R102list : List Coordinates := [(0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0)]
def R102 : Fin 25 → Coordinate 1 := fun i => R102list.getD i.val (0,0,0,0,0)

theorem hpxR102 : Function.Injective (fun i => reduceAux 1 (basisAt rK102) (R102 i)) := by decide
theorem hcardq102 : Nat.card (Coordinate 1 ⧸ reps rK102) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (102, 0): |T| = 25 -/

def T102_0list : List Coordinates := [(0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0)]
def T102_0 : Fin 25 → Coordinate 1 := fun i => T102_0list.getD i.val (0,0,0,0,0)

theorem hfix102_0 : ∀ i, ((T102_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK102)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102) :=
  repsFix_of_siftB rK102 ⟨0, by decide⟩ T102_0 (by decide)

theorem hinj102_0 : Function.Injective
    (fun i => ((T102_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK102)) :=
  repsInj_of_reduceAux rK102 T102_0 (by decide)

theorem hcardT102_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK102 ⟨0, by decide⟩ R102 hpxR102 hcardq102 (by decide)).symm

/-- **Cell (102, 0).** -/
theorem cell102_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK102) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK102) (charOfVec rK102 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK102 e (h : Coordinate 1) T102_0 i :=
  species_entry_eq_sum rK102 ⟨0, by decide⟩ e heK h T102_0 hfix102_0 hinj102_0 hcardT102_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK102) (T102_0 i) (hfix102_0 i) h)

/-! ## Cell (102, 10): |T| = 25 -/

def T102_10list : List Coordinates := [(0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0)]
def T102_10 : Fin 25 → Coordinate 1 := fun i => T102_10list.getD i.val (0,0,0,0,0)

theorem hfix102_10 : ∀ i, ((T102_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK102)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102) :=
  repsFix_of_siftB rK102 ⟨10, by decide⟩ T102_10 (by decide)

theorem hinj102_10 : Function.Injective
    (fun i => ((T102_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK102)) :=
  repsInj_of_reduceAux rK102 T102_10 (by decide)

theorem hcardT102_10 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK102 ⟨10, by decide⟩ R102 hpxR102 hcardq102 (by decide)).symm

/-- **Cell (102, 10).** -/
theorem cell102_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK102) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK102) (charOfVec rK102 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK102 e (h : Coordinate 1) T102_10 i :=
  species_entry_eq_sum rK102 ⟨10, by decide⟩ e heK h T102_10 hfix102_10 hinj102_10 hcardT102_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK102) (T102_10 i) (hfix102_10 i) h)

/-! ## Cell (102, 12): |T| = 25 -/

def T102_12list : List Coordinates := [(0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0)]
def T102_12 : Fin 25 → Coordinate 1 := fun i => T102_12list.getD i.val (0,0,0,0,0)

theorem hfix102_12 : ∀ i, ((T102_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK102)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102) :=
  repsFix_of_siftB rK102 ⟨12, by decide⟩ T102_12 (by decide)

theorem hinj102_12 : Function.Injective
    (fun i => ((T102_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK102)) :=
  repsInj_of_reduceAux rK102 T102_12 (by decide)

theorem hcardT102_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK102 ⟨12, by decide⟩ R102 hpxR102 hcardq102 (by decide)).symm

/-- **Cell (102, 12).** -/
theorem cell102_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK102) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK102) (charOfVec rK102 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK102 e (h : Coordinate 1) T102_12 i :=
  species_entry_eq_sum rK102 ⟨12, by decide⟩ e heK h T102_12 hfix102_12 hinj102_12 hcardT102_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK102) (T102_12 i) (hfix102_12 i) h)

/-! ## Cell (102, 40): |T| = 25 -/

def T102_40list : List Coordinates := [(0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0)]
def T102_40 : Fin 25 → Coordinate 1 := fun i => T102_40list.getD i.val (0,0,0,0,0)

theorem hfix102_40 : ∀ i, ((T102_40 i : Coordinate 1) : Coordinate 1 ⧸ reps rK102)
    ∈ fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102) :=
  repsFix_of_siftB rK102 ⟨40, by decide⟩ T102_40 (by decide)

theorem hinj102_40 : Function.Injective
    (fun i => ((T102_40 i : Coordinate 1) : Coordinate 1 ⧸ reps rK102)) :=
  repsInj_of_reduceAux rK102 T102_40 (by decide)

theorem hcardT102_40 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK102 ⟨40, by decide⟩ R102 hpxR102 hcardq102 (by decide)).symm

/-- **Cell (102, 40).** -/
theorem cell102_40 (e : List (ZMod 25)) (heK : charOK (basisAt rK102) e = true)
    (h : ↥(reps (⟨40, by decide⟩ : Fin 148))) :
    species (reps (⟨40, by decide⟩ : Fin 148)) h (basisElt (reps rK102) (charOfVec rK102 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK102 e (h : Coordinate 1) T102_40 i :=
  species_entry_eq_sum rK102 ⟨40, by decide⟩ e heK h T102_40 hfix102_40 hinj102_40 hcardT102_40
    (fun i => conj_mem_of_fixedPoints (reps ⟨40, by decide⟩) (reps rK102) (T102_40 i) (hfix102_40 i) h)

/-! ## Cell (102, 53): |T| = 25 -/

def T102_53list : List Coordinates := [(0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0)]
def T102_53 : Fin 25 → Coordinate 1 := fun i => T102_53list.getD i.val (0,0,0,0,0)

theorem hfix102_53 : ∀ i, ((T102_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK102)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102) :=
  repsFix_of_siftB rK102 ⟨53, by decide⟩ T102_53 (by decide)

theorem hinj102_53 : Function.Injective
    (fun i => ((T102_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK102)) :=
  repsInj_of_reduceAux rK102 T102_53 (by decide)

theorem hcardT102_53 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK102 ⟨53, by decide⟩ R102 hpxR102 hcardq102 (by decide)).symm

/-- **Cell (102, 53).** -/
theorem cell102_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK102) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK102) (charOfVec rK102 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK102 e (h : Coordinate 1) T102_53 i :=
  species_entry_eq_sum rK102 ⟨53, by decide⟩ e heK h T102_53 hfix102_53 hinj102_53 hcardT102_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK102) (T102_53 i) (hfix102_53 i) h)

/-! ## Cell (102, 102): |T| = 25 -/

def T102_102list : List Coordinates := [(0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0)]
def T102_102 : Fin 25 → Coordinate 1 := fun i => T102_102list.getD i.val (0,0,0,0,0)

theorem hfix102_102 : ∀ i, ((T102_102 i : Coordinate 1) : Coordinate 1 ⧸ reps rK102)
    ∈ fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102) :=
  repsFix_of_siftB rK102 ⟨102, by decide⟩ T102_102 (by decide)

theorem hinj102_102 : Function.Injective
    (fun i => ((T102_102 i : Coordinate 1) : Coordinate 1 ⧸ reps rK102)) :=
  repsInj_of_reduceAux rK102 T102_102 (by decide)

theorem hcardT102_102 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK102 ⟨102, by decide⟩ R102 hpxR102 hcardq102 (by decide)).symm

/-- **Cell (102, 102).** -/
theorem cell102_102 (e : List (ZMod 25)) (heK : charOK (basisAt rK102) e = true)
    (h : ↥(reps (⟨102, by decide⟩ : Fin 148))) :
    species (reps (⟨102, by decide⟩ : Fin 148)) h (basisElt (reps rK102) (charOfVec rK102 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK102 e (h : Coordinate 1) T102_102 i :=
  species_entry_eq_sum rK102 ⟨102, by decide⟩ e heK h T102_102 hfix102_102 hinj102_102 hcardT102_102
    (fun i => conj_mem_of_fixedPoints (reps ⟨102, by decide⟩) (reps rK102) (T102_102 i) (hfix102_102 i) h)

namespace Q2

def R102_2 : Fin 25 → Coordinate 2 := fun i => R102list.getD i.val (0,0,0,0,0)
theorem hpxR102_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK102) (R102_2 i)) := by decide
theorem hcardq102_2 : Nat.card (Coordinate 2 ⧸ reps rK102) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (102, 0) twin -/

def T102_0_2 : Fin 25 → Coordinate 2 := fun i => T102_0list.getD i.val (0,0,0,0,0)

theorem hfix102_0_2 : ∀ i, ((T102_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK102)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK102) :=
  repsFix_of_siftB2 rK102 ⟨0, by decide⟩ T102_0_2 (by decide)

theorem hinj102_0_2 : Function.Injective
    (fun i => ((T102_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK102)) :=
  repsInj_of_reduceAux2 rK102 T102_0_2 (by decide)

theorem hcardT102_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK102)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK102 ⟨0, by decide⟩ R102_2 hpxR102_2 hcardq102_2 (by decide)).symm

/-- **Cell (102, 0) twin (q=2).** -/
theorem cell102_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK102) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK102) (charOfVec2 rK102 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK102 e (h : Coordinate 2) T102_0_2 i :=
  species_entry_eq_sum rK102 ⟨0, by decide⟩ e heK h T102_0_2 hfix102_0_2 hinj102_0_2 hcardT102_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK102) (T102_0_2 i) (hfix102_0_2 i) h)

/-! ### Cell (102, 10) twin -/

def T102_10_2 : Fin 25 → Coordinate 2 := fun i => T102_10list.getD i.val (0,0,0,0,0)

theorem hfix102_10_2 : ∀ i, ((T102_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK102)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK102) :=
  repsFix_of_siftB2 rK102 ⟨10, by decide⟩ T102_10_2 (by decide)

theorem hinj102_10_2 : Function.Injective
    (fun i => ((T102_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK102)) :=
  repsInj_of_reduceAux2 rK102 T102_10_2 (by decide)

theorem hcardT102_10_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK102)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK102 ⟨10, by decide⟩ R102_2 hpxR102_2 hcardq102_2 (by decide)).symm

/-- **Cell (102, 10) twin (q=2).** -/
theorem cell102_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK102) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK102) (charOfVec2 rK102 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK102 e (h : Coordinate 2) T102_10_2 i :=
  species_entry_eq_sum rK102 ⟨10, by decide⟩ e heK h T102_10_2 hfix102_10_2 hinj102_10_2 hcardT102_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK102) (T102_10_2 i) (hfix102_10_2 i) h)

/-! ### Cell (102, 12) twin -/

def T102_12_2 : Fin 25 → Coordinate 2 := fun i => T102_12list.getD i.val (0,0,0,0,0)

theorem hfix102_12_2 : ∀ i, ((T102_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK102)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK102) :=
  repsFix_of_siftB2 rK102 ⟨12, by decide⟩ T102_12_2 (by decide)

theorem hinj102_12_2 : Function.Injective
    (fun i => ((T102_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK102)) :=
  repsInj_of_reduceAux2 rK102 T102_12_2 (by decide)

theorem hcardT102_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK102)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK102 ⟨12, by decide⟩ R102_2 hpxR102_2 hcardq102_2 (by decide)).symm

/-- **Cell (102, 12) twin (q=2).** -/
theorem cell102_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK102) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK102) (charOfVec2 rK102 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK102 e (h : Coordinate 2) T102_12_2 i :=
  species_entry_eq_sum rK102 ⟨12, by decide⟩ e heK h T102_12_2 hfix102_12_2 hinj102_12_2 hcardT102_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK102) (T102_12_2 i) (hfix102_12_2 i) h)

/-! ### Cell (102, 40) twin -/

def T102_40_2 : Fin 25 → Coordinate 2 := fun i => T102_40list.getD i.val (0,0,0,0,0)

theorem hfix102_40_2 : ∀ i, ((T102_40_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK102)
    ∈ fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK102) :=
  repsFix_of_siftB2 rK102 ⟨40, by decide⟩ T102_40_2 (by decide)

theorem hinj102_40_2 : Function.Injective
    (fun i => ((T102_40_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK102)) :=
  repsInj_of_reduceAux2 rK102 T102_40_2 (by decide)

theorem hcardT102_40_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK102)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK102 ⟨40, by decide⟩ R102_2 hpxR102_2 hcardq102_2 (by decide)).symm

/-- **Cell (102, 40) twin (q=2).** -/
theorem cell102_40_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK102) e = true)
    (h : ↥(reps (⟨40, by decide⟩ : Fin 148))) :
    species (reps (⟨40, by decide⟩ : Fin 148)) h (basisElt (reps rK102) (charOfVec2 rK102 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK102 e (h : Coordinate 2) T102_40_2 i :=
  species_entry_eq_sum rK102 ⟨40, by decide⟩ e heK h T102_40_2 hfix102_40_2 hinj102_40_2 hcardT102_40_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨40, by decide⟩) (reps rK102) (T102_40_2 i) (hfix102_40_2 i) h)

/-! ### Cell (102, 53) twin -/

def T102_53_2 : Fin 25 → Coordinate 2 := fun i => T102_53list.getD i.val (0,0,0,0,0)

theorem hfix102_53_2 : ∀ i, ((T102_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK102)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK102) :=
  repsFix_of_siftB2 rK102 ⟨53, by decide⟩ T102_53_2 (by decide)

theorem hinj102_53_2 : Function.Injective
    (fun i => ((T102_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK102)) :=
  repsInj_of_reduceAux2 rK102 T102_53_2 (by decide)

theorem hcardT102_53_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK102)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK102 ⟨53, by decide⟩ R102_2 hpxR102_2 hcardq102_2 (by decide)).symm

/-- **Cell (102, 53) twin (q=2).** -/
theorem cell102_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK102) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK102) (charOfVec2 rK102 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK102 e (h : Coordinate 2) T102_53_2 i :=
  species_entry_eq_sum rK102 ⟨53, by decide⟩ e heK h T102_53_2 hfix102_53_2 hinj102_53_2 hcardT102_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK102) (T102_53_2 i) (hfix102_53_2 i) h)

/-! ### Cell (102, 102) twin -/

def T102_102_2 : Fin 25 → Coordinate 2 := fun i => T102_102list.getD i.val (0,0,0,0,0)

theorem hfix102_102_2 : ∀ i, ((T102_102_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK102)
    ∈ fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK102) :=
  repsFix_of_siftB2 rK102 ⟨102, by decide⟩ T102_102_2 (by decide)

theorem hinj102_102_2 : Function.Injective
    (fun i => ((T102_102_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK102)) :=
  repsInj_of_reduceAux2 rK102 T102_102_2 (by decide)

theorem hcardT102_102_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK102)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK102 ⟨102, by decide⟩ R102_2 hpxR102_2 hcardq102_2 (by decide)).symm

/-- **Cell (102, 102) twin (q=2).** -/
theorem cell102_102_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK102) e = true)
    (h : ↥(reps (⟨102, by decide⟩ : Fin 148))) :
    species (reps (⟨102, by decide⟩ : Fin 148)) h (basisElt (reps rK102) (charOfVec2 rK102 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK102 e (h : Coordinate 2) T102_102_2 i :=
  species_entry_eq_sum rK102 ⟨102, by decide⟩ e heK h T102_102_2 hfix102_102_2 hinj102_102_2 hcardT102_102_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨102, by decide⟩) (reps rK102) (T102_102_2 i) (hfix102_102_2 i) h)

end Q2

/-! # K-class rK = 103  (|G/K| = 25) -/

def rK103 : Fin 148 := ⟨103, by decide⟩

def R103list : List Coordinates := [(0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0)]
def R103 : Fin 25 → Coordinate 1 := fun i => R103list.getD i.val (0,0,0,0,0)

theorem hpxR103 : Function.Injective (fun i => reduceAux 1 (basisAt rK103) (R103 i)) := by decide
theorem hcardq103 : Nat.card (Coordinate 1 ⧸ reps rK103) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (103, 0): |T| = 25 -/

def T103_0list : List Coordinates := [(0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0)]
def T103_0 : Fin 25 → Coordinate 1 := fun i => T103_0list.getD i.val (0,0,0,0,0)

theorem hfix103_0 : ∀ i, ((T103_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK103)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103) :=
  repsFix_of_siftB rK103 ⟨0, by decide⟩ T103_0 (by decide)

theorem hinj103_0 : Function.Injective
    (fun i => ((T103_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK103)) :=
  repsInj_of_reduceAux rK103 T103_0 (by decide)

theorem hcardT103_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK103 ⟨0, by decide⟩ R103 hpxR103 hcardq103 (by decide)).symm

/-- **Cell (103, 0).** -/
theorem cell103_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK103) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK103) (charOfVec rK103 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK103 e (h : Coordinate 1) T103_0 i :=
  species_entry_eq_sum rK103 ⟨0, by decide⟩ e heK h T103_0 hfix103_0 hinj103_0 hcardT103_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK103) (T103_0 i) (hfix103_0 i) h)

/-! ## Cell (103, 10): |T| = 25 -/

def T103_10list : List Coordinates := [(0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0)]
def T103_10 : Fin 25 → Coordinate 1 := fun i => T103_10list.getD i.val (0,0,0,0,0)

theorem hfix103_10 : ∀ i, ((T103_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK103)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103) :=
  repsFix_of_siftB rK103 ⟨10, by decide⟩ T103_10 (by decide)

theorem hinj103_10 : Function.Injective
    (fun i => ((T103_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK103)) :=
  repsInj_of_reduceAux rK103 T103_10 (by decide)

theorem hcardT103_10 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK103 ⟨10, by decide⟩ R103 hpxR103 hcardq103 (by decide)).symm

/-- **Cell (103, 10).** -/
theorem cell103_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK103) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK103) (charOfVec rK103 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK103 e (h : Coordinate 1) T103_10 i :=
  species_entry_eq_sum rK103 ⟨10, by decide⟩ e heK h T103_10 hfix103_10 hinj103_10 hcardT103_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK103) (T103_10 i) (hfix103_10 i) h)

/-! ## Cell (103, 12): |T| = 25 -/

def T103_12list : List Coordinates := [(0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0)]
def T103_12 : Fin 25 → Coordinate 1 := fun i => T103_12list.getD i.val (0,0,0,0,0)

theorem hfix103_12 : ∀ i, ((T103_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK103)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103) :=
  repsFix_of_siftB rK103 ⟨12, by decide⟩ T103_12 (by decide)

theorem hinj103_12 : Function.Injective
    (fun i => ((T103_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK103)) :=
  repsInj_of_reduceAux rK103 T103_12 (by decide)

theorem hcardT103_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK103 ⟨12, by decide⟩ R103 hpxR103 hcardq103 (by decide)).symm

/-- **Cell (103, 12).** -/
theorem cell103_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK103) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK103) (charOfVec rK103 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK103 e (h : Coordinate 1) T103_12 i :=
  species_entry_eq_sum rK103 ⟨12, by decide⟩ e heK h T103_12 hfix103_12 hinj103_12 hcardT103_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK103) (T103_12 i) (hfix103_12 i) h)

/-! ## Cell (103, 41): |T| = 25 -/

def T103_41list : List Coordinates := [(0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0)]
def T103_41 : Fin 25 → Coordinate 1 := fun i => T103_41list.getD i.val (0,0,0,0,0)

theorem hfix103_41 : ∀ i, ((T103_41 i : Coordinate 1) : Coordinate 1 ⧸ reps rK103)
    ∈ fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103) :=
  repsFix_of_siftB rK103 ⟨41, by decide⟩ T103_41 (by decide)

theorem hinj103_41 : Function.Injective
    (fun i => ((T103_41 i : Coordinate 1) : Coordinate 1 ⧸ reps rK103)) :=
  repsInj_of_reduceAux rK103 T103_41 (by decide)

theorem hcardT103_41 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK103 ⟨41, by decide⟩ R103 hpxR103 hcardq103 (by decide)).symm

/-- **Cell (103, 41).** -/
theorem cell103_41 (e : List (ZMod 25)) (heK : charOK (basisAt rK103) e = true)
    (h : ↥(reps (⟨41, by decide⟩ : Fin 148))) :
    species (reps (⟨41, by decide⟩ : Fin 148)) h (basisElt (reps rK103) (charOfVec rK103 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK103 e (h : Coordinate 1) T103_41 i :=
  species_entry_eq_sum rK103 ⟨41, by decide⟩ e heK h T103_41 hfix103_41 hinj103_41 hcardT103_41
    (fun i => conj_mem_of_fixedPoints (reps ⟨41, by decide⟩) (reps rK103) (T103_41 i) (hfix103_41 i) h)

/-! ## Cell (103, 53): |T| = 25 -/

def T103_53list : List Coordinates := [(0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0)]
def T103_53 : Fin 25 → Coordinate 1 := fun i => T103_53list.getD i.val (0,0,0,0,0)

theorem hfix103_53 : ∀ i, ((T103_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK103)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103) :=
  repsFix_of_siftB rK103 ⟨53, by decide⟩ T103_53 (by decide)

theorem hinj103_53 : Function.Injective
    (fun i => ((T103_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK103)) :=
  repsInj_of_reduceAux rK103 T103_53 (by decide)

theorem hcardT103_53 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK103 ⟨53, by decide⟩ R103 hpxR103 hcardq103 (by decide)).symm

/-- **Cell (103, 53).** -/
theorem cell103_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK103) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK103) (charOfVec rK103 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK103 e (h : Coordinate 1) T103_53 i :=
  species_entry_eq_sum rK103 ⟨53, by decide⟩ e heK h T103_53 hfix103_53 hinj103_53 hcardT103_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK103) (T103_53 i) (hfix103_53 i) h)

/-! ## Cell (103, 103): |T| = 25 -/

def T103_103list : List Coordinates := [(0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0)]
def T103_103 : Fin 25 → Coordinate 1 := fun i => T103_103list.getD i.val (0,0,0,0,0)

theorem hfix103_103 : ∀ i, ((T103_103 i : Coordinate 1) : Coordinate 1 ⧸ reps rK103)
    ∈ fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103) :=
  repsFix_of_siftB rK103 ⟨103, by decide⟩ T103_103 (by decide)

theorem hinj103_103 : Function.Injective
    (fun i => ((T103_103 i : Coordinate 1) : Coordinate 1 ⧸ reps rK103)) :=
  repsInj_of_reduceAux rK103 T103_103 (by decide)

theorem hcardT103_103 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK103 ⟨103, by decide⟩ R103 hpxR103 hcardq103 (by decide)).symm

/-- **Cell (103, 103).** -/
theorem cell103_103 (e : List (ZMod 25)) (heK : charOK (basisAt rK103) e = true)
    (h : ↥(reps (⟨103, by decide⟩ : Fin 148))) :
    species (reps (⟨103, by decide⟩ : Fin 148)) h (basisElt (reps rK103) (charOfVec rK103 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK103 e (h : Coordinate 1) T103_103 i :=
  species_entry_eq_sum rK103 ⟨103, by decide⟩ e heK h T103_103 hfix103_103 hinj103_103 hcardT103_103
    (fun i => conj_mem_of_fixedPoints (reps ⟨103, by decide⟩) (reps rK103) (T103_103 i) (hfix103_103 i) h)

namespace Q2

def R103_2 : Fin 25 → Coordinate 2 := fun i => R103list.getD i.val (0,0,0,0,0)
theorem hpxR103_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK103) (R103_2 i)) := by decide
theorem hcardq103_2 : Nat.card (Coordinate 2 ⧸ reps rK103) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (103, 0) twin -/

def T103_0_2 : Fin 25 → Coordinate 2 := fun i => T103_0list.getD i.val (0,0,0,0,0)

theorem hfix103_0_2 : ∀ i, ((T103_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK103)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK103) :=
  repsFix_of_siftB2 rK103 ⟨0, by decide⟩ T103_0_2 (by decide)

theorem hinj103_0_2 : Function.Injective
    (fun i => ((T103_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK103)) :=
  repsInj_of_reduceAux2 rK103 T103_0_2 (by decide)

theorem hcardT103_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK103)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK103 ⟨0, by decide⟩ R103_2 hpxR103_2 hcardq103_2 (by decide)).symm

/-- **Cell (103, 0) twin (q=2).** -/
theorem cell103_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK103) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK103) (charOfVec2 rK103 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK103 e (h : Coordinate 2) T103_0_2 i :=
  species_entry_eq_sum rK103 ⟨0, by decide⟩ e heK h T103_0_2 hfix103_0_2 hinj103_0_2 hcardT103_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK103) (T103_0_2 i) (hfix103_0_2 i) h)

/-! ### Cell (103, 10) twin -/

def T103_10_2 : Fin 25 → Coordinate 2 := fun i => T103_10list.getD i.val (0,0,0,0,0)

theorem hfix103_10_2 : ∀ i, ((T103_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK103)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK103) :=
  repsFix_of_siftB2 rK103 ⟨10, by decide⟩ T103_10_2 (by decide)

theorem hinj103_10_2 : Function.Injective
    (fun i => ((T103_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK103)) :=
  repsInj_of_reduceAux2 rK103 T103_10_2 (by decide)

theorem hcardT103_10_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK103)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK103 ⟨10, by decide⟩ R103_2 hpxR103_2 hcardq103_2 (by decide)).symm

/-- **Cell (103, 10) twin (q=2).** -/
theorem cell103_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK103) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK103) (charOfVec2 rK103 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK103 e (h : Coordinate 2) T103_10_2 i :=
  species_entry_eq_sum rK103 ⟨10, by decide⟩ e heK h T103_10_2 hfix103_10_2 hinj103_10_2 hcardT103_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK103) (T103_10_2 i) (hfix103_10_2 i) h)

/-! ### Cell (103, 12) twin -/

def T103_12_2 : Fin 25 → Coordinate 2 := fun i => T103_12list.getD i.val (0,0,0,0,0)

theorem hfix103_12_2 : ∀ i, ((T103_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK103)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK103) :=
  repsFix_of_siftB2 rK103 ⟨12, by decide⟩ T103_12_2 (by decide)

theorem hinj103_12_2 : Function.Injective
    (fun i => ((T103_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK103)) :=
  repsInj_of_reduceAux2 rK103 T103_12_2 (by decide)

theorem hcardT103_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK103)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK103 ⟨12, by decide⟩ R103_2 hpxR103_2 hcardq103_2 (by decide)).symm

/-- **Cell (103, 12) twin (q=2).** -/
theorem cell103_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK103) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK103) (charOfVec2 rK103 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK103 e (h : Coordinate 2) T103_12_2 i :=
  species_entry_eq_sum rK103 ⟨12, by decide⟩ e heK h T103_12_2 hfix103_12_2 hinj103_12_2 hcardT103_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK103) (T103_12_2 i) (hfix103_12_2 i) h)

/-! ### Cell (103, 41) twin -/

def T103_41_2 : Fin 25 → Coordinate 2 := fun i => T103_41list.getD i.val (0,0,0,0,0)

theorem hfix103_41_2 : ∀ i, ((T103_41_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK103)
    ∈ fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK103) :=
  repsFix_of_siftB2 rK103 ⟨41, by decide⟩ T103_41_2 (by decide)

theorem hinj103_41_2 : Function.Injective
    (fun i => ((T103_41_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK103)) :=
  repsInj_of_reduceAux2 rK103 T103_41_2 (by decide)

theorem hcardT103_41_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK103)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK103 ⟨41, by decide⟩ R103_2 hpxR103_2 hcardq103_2 (by decide)).symm

/-- **Cell (103, 41) twin (q=2).** -/
theorem cell103_41_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK103) e = true)
    (h : ↥(reps (⟨41, by decide⟩ : Fin 148))) :
    species (reps (⟨41, by decide⟩ : Fin 148)) h (basisElt (reps rK103) (charOfVec2 rK103 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK103 e (h : Coordinate 2) T103_41_2 i :=
  species_entry_eq_sum rK103 ⟨41, by decide⟩ e heK h T103_41_2 hfix103_41_2 hinj103_41_2 hcardT103_41_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨41, by decide⟩) (reps rK103) (T103_41_2 i) (hfix103_41_2 i) h)

/-! ### Cell (103, 53) twin -/

def T103_53_2 : Fin 25 → Coordinate 2 := fun i => T103_53list.getD i.val (0,0,0,0,0)

theorem hfix103_53_2 : ∀ i, ((T103_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK103)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK103) :=
  repsFix_of_siftB2 rK103 ⟨53, by decide⟩ T103_53_2 (by decide)

theorem hinj103_53_2 : Function.Injective
    (fun i => ((T103_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK103)) :=
  repsInj_of_reduceAux2 rK103 T103_53_2 (by decide)

theorem hcardT103_53_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK103)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK103 ⟨53, by decide⟩ R103_2 hpxR103_2 hcardq103_2 (by decide)).symm

/-- **Cell (103, 53) twin (q=2).** -/
theorem cell103_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK103) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK103) (charOfVec2 rK103 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK103 e (h : Coordinate 2) T103_53_2 i :=
  species_entry_eq_sum rK103 ⟨53, by decide⟩ e heK h T103_53_2 hfix103_53_2 hinj103_53_2 hcardT103_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK103) (T103_53_2 i) (hfix103_53_2 i) h)

/-! ### Cell (103, 103) twin -/

def T103_103_2 : Fin 25 → Coordinate 2 := fun i => T103_103list.getD i.val (0,0,0,0,0)

theorem hfix103_103_2 : ∀ i, ((T103_103_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK103)
    ∈ fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK103) :=
  repsFix_of_siftB2 rK103 ⟨103, by decide⟩ T103_103_2 (by decide)

theorem hinj103_103_2 : Function.Injective
    (fun i => ((T103_103_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK103)) :=
  repsInj_of_reduceAux2 rK103 T103_103_2 (by decide)

theorem hcardT103_103_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK103)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK103 ⟨103, by decide⟩ R103_2 hpxR103_2 hcardq103_2 (by decide)).symm

/-- **Cell (103, 103) twin (q=2).** -/
theorem cell103_103_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK103) e = true)
    (h : ↥(reps (⟨103, by decide⟩ : Fin 148))) :
    species (reps (⟨103, by decide⟩ : Fin 148)) h (basisElt (reps rK103) (charOfVec2 rK103 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK103 e (h : Coordinate 2) T103_103_2 i :=
  species_entry_eq_sum rK103 ⟨103, by decide⟩ e heK h T103_103_2 hfix103_103_2 hinj103_103_2 hcardT103_103_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨103, by decide⟩) (reps rK103) (T103_103_2 i) (hfix103_103_2 i) h)

end Q2

/-! # K-class rK = 104  (|G/K| = 25) -/

def rK104 : Fin 148 := ⟨104, by decide⟩

def R104list : List Coordinates := [(0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def R104 : Fin 25 → Coordinate 1 := fun i => R104list.getD i.val (0,0,0,0,0)

theorem hpxR104 : Function.Injective (fun i => reduceAux 1 (basisAt rK104) (R104 i)) := by decide
theorem hcardq104 : Nat.card (Coordinate 1 ⧸ reps rK104) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (104, 0): |T| = 25 -/

def T104_0list : List Coordinates := [(0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T104_0 : Fin 25 → Coordinate 1 := fun i => T104_0list.getD i.val (0,0,0,0,0)

theorem hfix104_0 : ∀ i, ((T104_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK104)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104) :=
  repsFix_of_siftB rK104 ⟨0, by decide⟩ T104_0 (by decide)

theorem hinj104_0 : Function.Injective
    (fun i => ((T104_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK104)) :=
  repsInj_of_reduceAux rK104 T104_0 (by decide)

theorem hcardT104_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK104 ⟨0, by decide⟩ R104 hpxR104 hcardq104 (by decide)).symm

/-- **Cell (104, 0).** -/
theorem cell104_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK104) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK104) (charOfVec rK104 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK104 e (h : Coordinate 1) T104_0 i :=
  species_entry_eq_sum rK104 ⟨0, by decide⟩ e heK h T104_0 hfix104_0 hinj104_0 hcardT104_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK104) (T104_0 i) (hfix104_0 i) h)

/-! ## Cell (104, 10): |T| = 25 -/

def T104_10list : List Coordinates := [(0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T104_10 : Fin 25 → Coordinate 1 := fun i => T104_10list.getD i.val (0,0,0,0,0)

theorem hfix104_10 : ∀ i, ((T104_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK104)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104) :=
  repsFix_of_siftB rK104 ⟨10, by decide⟩ T104_10 (by decide)

theorem hinj104_10 : Function.Injective
    (fun i => ((T104_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK104)) :=
  repsInj_of_reduceAux rK104 T104_10 (by decide)

theorem hcardT104_10 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK104 ⟨10, by decide⟩ R104 hpxR104 hcardq104 (by decide)).symm

/-- **Cell (104, 10).** -/
theorem cell104_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK104) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK104) (charOfVec rK104 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK104 e (h : Coordinate 1) T104_10 i :=
  species_entry_eq_sum rK104 ⟨10, by decide⟩ e heK h T104_10 hfix104_10 hinj104_10 hcardT104_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK104) (T104_10 i) (hfix104_10 i) h)

/-! ## Cell (104, 12): |T| = 25 -/

def T104_12list : List Coordinates := [(0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T104_12 : Fin 25 → Coordinate 1 := fun i => T104_12list.getD i.val (0,0,0,0,0)

theorem hfix104_12 : ∀ i, ((T104_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK104)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104) :=
  repsFix_of_siftB rK104 ⟨12, by decide⟩ T104_12 (by decide)

theorem hinj104_12 : Function.Injective
    (fun i => ((T104_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK104)) :=
  repsInj_of_reduceAux rK104 T104_12 (by decide)

theorem hcardT104_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK104 ⟨12, by decide⟩ R104 hpxR104 hcardq104 (by decide)).symm

/-- **Cell (104, 12).** -/
theorem cell104_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK104) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK104) (charOfVec rK104 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK104 e (h : Coordinate 1) T104_12 i :=
  species_entry_eq_sum rK104 ⟨12, by decide⟩ e heK h T104_12 hfix104_12 hinj104_12 hcardT104_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK104) (T104_12 i) (hfix104_12 i) h)

/-! ## Cell (104, 42): |T| = 25 -/

def T104_42list : List Coordinates := [(0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T104_42 : Fin 25 → Coordinate 1 := fun i => T104_42list.getD i.val (0,0,0,0,0)

theorem hfix104_42 : ∀ i, ((T104_42 i : Coordinate 1) : Coordinate 1 ⧸ reps rK104)
    ∈ fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104) :=
  repsFix_of_siftB rK104 ⟨42, by decide⟩ T104_42 (by decide)

theorem hinj104_42 : Function.Injective
    (fun i => ((T104_42 i : Coordinate 1) : Coordinate 1 ⧸ reps rK104)) :=
  repsInj_of_reduceAux rK104 T104_42 (by decide)

theorem hcardT104_42 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK104 ⟨42, by decide⟩ R104 hpxR104 hcardq104 (by decide)).symm

/-- **Cell (104, 42).** -/
theorem cell104_42 (e : List (ZMod 25)) (heK : charOK (basisAt rK104) e = true)
    (h : ↥(reps (⟨42, by decide⟩ : Fin 148))) :
    species (reps (⟨42, by decide⟩ : Fin 148)) h (basisElt (reps rK104) (charOfVec rK104 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK104 e (h : Coordinate 1) T104_42 i :=
  species_entry_eq_sum rK104 ⟨42, by decide⟩ e heK h T104_42 hfix104_42 hinj104_42 hcardT104_42
    (fun i => conj_mem_of_fixedPoints (reps ⟨42, by decide⟩) (reps rK104) (T104_42 i) (hfix104_42 i) h)

/-! ## Cell (104, 53): |T| = 25 -/

def T104_53list : List Coordinates := [(0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T104_53 : Fin 25 → Coordinate 1 := fun i => T104_53list.getD i.val (0,0,0,0,0)

theorem hfix104_53 : ∀ i, ((T104_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK104)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104) :=
  repsFix_of_siftB rK104 ⟨53, by decide⟩ T104_53 (by decide)

theorem hinj104_53 : Function.Injective
    (fun i => ((T104_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK104)) :=
  repsInj_of_reduceAux rK104 T104_53 (by decide)

theorem hcardT104_53 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK104 ⟨53, by decide⟩ R104 hpxR104 hcardq104 (by decide)).symm

/-- **Cell (104, 53).** -/
theorem cell104_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK104) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK104) (charOfVec rK104 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK104 e (h : Coordinate 1) T104_53 i :=
  species_entry_eq_sum rK104 ⟨53, by decide⟩ e heK h T104_53 hfix104_53 hinj104_53 hcardT104_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK104) (T104_53 i) (hfix104_53 i) h)

/-! ## Cell (104, 104): |T| = 25 -/

def T104_104list : List Coordinates := [(0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0)]
def T104_104 : Fin 25 → Coordinate 1 := fun i => T104_104list.getD i.val (0,0,0,0,0)

theorem hfix104_104 : ∀ i, ((T104_104 i : Coordinate 1) : Coordinate 1 ⧸ reps rK104)
    ∈ fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104) :=
  repsFix_of_siftB rK104 ⟨104, by decide⟩ T104_104 (by decide)

theorem hinj104_104 : Function.Injective
    (fun i => ((T104_104 i : Coordinate 1) : Coordinate 1 ⧸ reps rK104)) :=
  repsInj_of_reduceAux rK104 T104_104 (by decide)

theorem hcardT104_104 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK104 ⟨104, by decide⟩ R104 hpxR104 hcardq104 (by decide)).symm

/-- **Cell (104, 104).** -/
theorem cell104_104 (e : List (ZMod 25)) (heK : charOK (basisAt rK104) e = true)
    (h : ↥(reps (⟨104, by decide⟩ : Fin 148))) :
    species (reps (⟨104, by decide⟩ : Fin 148)) h (basisElt (reps rK104) (charOfVec rK104 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK104 e (h : Coordinate 1) T104_104 i :=
  species_entry_eq_sum rK104 ⟨104, by decide⟩ e heK h T104_104 hfix104_104 hinj104_104 hcardT104_104
    (fun i => conj_mem_of_fixedPoints (reps ⟨104, by decide⟩) (reps rK104) (T104_104 i) (hfix104_104 i) h)

namespace Q2

def R104_2 : Fin 25 → Coordinate 2 := fun i => R104list.getD i.val (0,0,0,0,0)
theorem hpxR104_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK104) (R104_2 i)) := by decide
theorem hcardq104_2 : Nat.card (Coordinate 2 ⧸ reps rK104) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (104, 0) twin -/

def T104_0_2 : Fin 25 → Coordinate 2 := fun i => T104_0list.getD i.val (0,0,0,0,0)

theorem hfix104_0_2 : ∀ i, ((T104_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK104)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK104) :=
  repsFix_of_siftB2 rK104 ⟨0, by decide⟩ T104_0_2 (by decide)

theorem hinj104_0_2 : Function.Injective
    (fun i => ((T104_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK104)) :=
  repsInj_of_reduceAux2 rK104 T104_0_2 (by decide)

theorem hcardT104_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK104)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK104 ⟨0, by decide⟩ R104_2 hpxR104_2 hcardq104_2 (by decide)).symm

/-- **Cell (104, 0) twin (q=2).** -/
theorem cell104_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK104) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK104) (charOfVec2 rK104 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK104 e (h : Coordinate 2) T104_0_2 i :=
  species_entry_eq_sum rK104 ⟨0, by decide⟩ e heK h T104_0_2 hfix104_0_2 hinj104_0_2 hcardT104_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK104) (T104_0_2 i) (hfix104_0_2 i) h)

/-! ### Cell (104, 10) twin -/

def T104_10_2 : Fin 25 → Coordinate 2 := fun i => T104_10list.getD i.val (0,0,0,0,0)

theorem hfix104_10_2 : ∀ i, ((T104_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK104)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK104) :=
  repsFix_of_siftB2 rK104 ⟨10, by decide⟩ T104_10_2 (by decide)

theorem hinj104_10_2 : Function.Injective
    (fun i => ((T104_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK104)) :=
  repsInj_of_reduceAux2 rK104 T104_10_2 (by decide)

theorem hcardT104_10_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK104)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK104 ⟨10, by decide⟩ R104_2 hpxR104_2 hcardq104_2 (by decide)).symm

/-- **Cell (104, 10) twin (q=2).** -/
theorem cell104_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK104) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK104) (charOfVec2 rK104 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK104 e (h : Coordinate 2) T104_10_2 i :=
  species_entry_eq_sum rK104 ⟨10, by decide⟩ e heK h T104_10_2 hfix104_10_2 hinj104_10_2 hcardT104_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK104) (T104_10_2 i) (hfix104_10_2 i) h)

/-! ### Cell (104, 12) twin -/

def T104_12_2 : Fin 25 → Coordinate 2 := fun i => T104_12list.getD i.val (0,0,0,0,0)

theorem hfix104_12_2 : ∀ i, ((T104_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK104)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK104) :=
  repsFix_of_siftB2 rK104 ⟨12, by decide⟩ T104_12_2 (by decide)

theorem hinj104_12_2 : Function.Injective
    (fun i => ((T104_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK104)) :=
  repsInj_of_reduceAux2 rK104 T104_12_2 (by decide)

theorem hcardT104_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK104)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK104 ⟨12, by decide⟩ R104_2 hpxR104_2 hcardq104_2 (by decide)).symm

/-- **Cell (104, 12) twin (q=2).** -/
theorem cell104_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK104) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK104) (charOfVec2 rK104 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK104 e (h : Coordinate 2) T104_12_2 i :=
  species_entry_eq_sum rK104 ⟨12, by decide⟩ e heK h T104_12_2 hfix104_12_2 hinj104_12_2 hcardT104_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK104) (T104_12_2 i) (hfix104_12_2 i) h)

/-! ### Cell (104, 42) twin -/

def T104_42_2 : Fin 25 → Coordinate 2 := fun i => T104_42list.getD i.val (0,0,0,0,0)

theorem hfix104_42_2 : ∀ i, ((T104_42_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK104)
    ∈ fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK104) :=
  repsFix_of_siftB2 rK104 ⟨42, by decide⟩ T104_42_2 (by decide)

theorem hinj104_42_2 : Function.Injective
    (fun i => ((T104_42_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK104)) :=
  repsInj_of_reduceAux2 rK104 T104_42_2 (by decide)

theorem hcardT104_42_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK104)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK104 ⟨42, by decide⟩ R104_2 hpxR104_2 hcardq104_2 (by decide)).symm

/-- **Cell (104, 42) twin (q=2).** -/
theorem cell104_42_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK104) e = true)
    (h : ↥(reps (⟨42, by decide⟩ : Fin 148))) :
    species (reps (⟨42, by decide⟩ : Fin 148)) h (basisElt (reps rK104) (charOfVec2 rK104 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK104 e (h : Coordinate 2) T104_42_2 i :=
  species_entry_eq_sum rK104 ⟨42, by decide⟩ e heK h T104_42_2 hfix104_42_2 hinj104_42_2 hcardT104_42_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨42, by decide⟩) (reps rK104) (T104_42_2 i) (hfix104_42_2 i) h)

/-! ### Cell (104, 53) twin -/

def T104_53_2 : Fin 25 → Coordinate 2 := fun i => T104_53list.getD i.val (0,0,0,0,0)

theorem hfix104_53_2 : ∀ i, ((T104_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK104)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK104) :=
  repsFix_of_siftB2 rK104 ⟨53, by decide⟩ T104_53_2 (by decide)

theorem hinj104_53_2 : Function.Injective
    (fun i => ((T104_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK104)) :=
  repsInj_of_reduceAux2 rK104 T104_53_2 (by decide)

theorem hcardT104_53_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK104)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK104 ⟨53, by decide⟩ R104_2 hpxR104_2 hcardq104_2 (by decide)).symm

/-- **Cell (104, 53) twin (q=2).** -/
theorem cell104_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK104) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK104) (charOfVec2 rK104 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK104 e (h : Coordinate 2) T104_53_2 i :=
  species_entry_eq_sum rK104 ⟨53, by decide⟩ e heK h T104_53_2 hfix104_53_2 hinj104_53_2 hcardT104_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK104) (T104_53_2 i) (hfix104_53_2 i) h)

/-! ### Cell (104, 104) twin -/

def T104_104_2 : Fin 25 → Coordinate 2 := fun i => T104_104list.getD i.val (0,0,0,0,0)

theorem hfix104_104_2 : ∀ i, ((T104_104_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK104)
    ∈ fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK104) :=
  repsFix_of_siftB2 rK104 ⟨104, by decide⟩ T104_104_2 (by decide)

theorem hinj104_104_2 : Function.Injective
    (fun i => ((T104_104_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK104)) :=
  repsInj_of_reduceAux2 rK104 T104_104_2 (by decide)

theorem hcardT104_104_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK104)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK104 ⟨104, by decide⟩ R104_2 hpxR104_2 hcardq104_2 (by decide)).symm

/-- **Cell (104, 104) twin (q=2).** -/
theorem cell104_104_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK104) e = true)
    (h : ↥(reps (⟨104, by decide⟩ : Fin 148))) :
    species (reps (⟨104, by decide⟩ : Fin 148)) h (basisElt (reps rK104) (charOfVec2 rK104 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK104 e (h : Coordinate 2) T104_104_2 i :=
  species_entry_eq_sum rK104 ⟨104, by decide⟩ e heK h T104_104_2 hfix104_104_2 hinj104_104_2 hcardT104_104_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨104, by decide⟩) (reps rK104) (T104_104_2 i) (hfix104_104_2 i) h)

end Q2

/-! # K-class rK = 105  (|G/K| = 25) -/

def rK105 : Fin 148 := ⟨105, by decide⟩

def R105list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (1,0,1,0,0), (1,0,2,0,0), (1,0,3,0,0), (1,0,4,0,0), (1,0,0,0,0), (2,0,1,0,0), (2,0,2,0,0), (2,0,3,0,0), (2,0,4,0,0), (2,0,0,0,0), (3,0,1,0,0), (3,0,2,0,0), (3,0,3,0,0), (3,0,4,0,0), (3,0,0,0,0), (4,0,1,0,0), (4,0,2,0,0), (4,0,3,0,0), (4,0,4,0,0), (4,0,0,0,0)]
def R105 : Fin 25 → Coordinate 1 := fun i => R105list.getD i.val (0,0,0,0,0)

theorem hpxR105 : Function.Injective (fun i => reduceAux 1 (basisAt rK105) (R105 i)) := by decide
theorem hcardq105 : Nat.card (Coordinate 1 ⧸ reps rK105) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (105, 0): |T| = 25 -/

def T105_0list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (1,0,1,0,0), (1,0,2,0,0), (1,0,3,0,0), (1,0,4,0,0), (1,0,0,0,0), (2,0,1,0,0), (2,0,2,0,0), (2,0,3,0,0), (2,0,4,0,0), (2,0,0,0,0), (3,0,1,0,0), (3,0,2,0,0), (3,0,3,0,0), (3,0,4,0,0), (3,0,0,0,0), (4,0,1,0,0), (4,0,2,0,0), (4,0,3,0,0), (4,0,4,0,0), (4,0,0,0,0)]
def T105_0 : Fin 25 → Coordinate 1 := fun i => T105_0list.getD i.val (0,0,0,0,0)

theorem hfix105_0 : ∀ i, ((T105_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK105)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105) :=
  repsFix_of_siftB rK105 ⟨0, by decide⟩ T105_0 (by decide)

theorem hinj105_0 : Function.Injective
    (fun i => ((T105_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK105)) :=
  repsInj_of_reduceAux rK105 T105_0 (by decide)

theorem hcardT105_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK105 ⟨0, by decide⟩ R105 hpxR105 hcardq105 (by decide)).symm

/-- **Cell (105, 0).** -/
theorem cell105_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK105) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK105) (charOfVec rK105 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK105 e (h : Coordinate 1) T105_0 i :=
  species_entry_eq_sum rK105 ⟨0, by decide⟩ e heK h T105_0 hfix105_0 hinj105_0 hcardT105_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK105) (T105_0 i) (hfix105_0 i) h)

/-! ## Cell (105, 10): |T| = 25 -/

def T105_10list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (1,0,1,0,0), (1,0,2,0,0), (1,0,3,0,0), (1,0,4,0,0), (1,0,0,0,0), (2,0,1,0,0), (2,0,2,0,0), (2,0,3,0,0), (2,0,4,0,0), (2,0,0,0,0), (3,0,1,0,0), (3,0,2,0,0), (3,0,3,0,0), (3,0,4,0,0), (3,0,0,0,0), (4,0,1,0,0), (4,0,2,0,0), (4,0,3,0,0), (4,0,4,0,0), (4,0,0,0,0)]
def T105_10 : Fin 25 → Coordinate 1 := fun i => T105_10list.getD i.val (0,0,0,0,0)

theorem hfix105_10 : ∀ i, ((T105_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK105)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105) :=
  repsFix_of_siftB rK105 ⟨10, by decide⟩ T105_10 (by decide)

theorem hinj105_10 : Function.Injective
    (fun i => ((T105_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK105)) :=
  repsInj_of_reduceAux rK105 T105_10 (by decide)

theorem hcardT105_10 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK105 ⟨10, by decide⟩ R105 hpxR105 hcardq105 (by decide)).symm

/-- **Cell (105, 10).** -/
theorem cell105_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK105) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK105) (charOfVec rK105 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK105 e (h : Coordinate 1) T105_10 i :=
  species_entry_eq_sum rK105 ⟨10, by decide⟩ e heK h T105_10 hfix105_10 hinj105_10 hcardT105_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK105) (T105_10 i) (hfix105_10 i) h)

/-! ## Cell (105, 12): |T| = 25 -/

def T105_12list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (1,0,1,0,0), (1,0,2,0,0), (1,0,3,0,0), (1,0,4,0,0), (1,0,0,0,0), (2,0,1,0,0), (2,0,2,0,0), (2,0,3,0,0), (2,0,4,0,0), (2,0,0,0,0), (3,0,1,0,0), (3,0,2,0,0), (3,0,3,0,0), (3,0,4,0,0), (3,0,0,0,0), (4,0,1,0,0), (4,0,2,0,0), (4,0,3,0,0), (4,0,4,0,0), (4,0,0,0,0)]
def T105_12 : Fin 25 → Coordinate 1 := fun i => T105_12list.getD i.val (0,0,0,0,0)

theorem hfix105_12 : ∀ i, ((T105_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK105)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105) :=
  repsFix_of_siftB rK105 ⟨12, by decide⟩ T105_12 (by decide)

theorem hinj105_12 : Function.Injective
    (fun i => ((T105_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK105)) :=
  repsInj_of_reduceAux rK105 T105_12 (by decide)

theorem hcardT105_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK105 ⟨12, by decide⟩ R105 hpxR105 hcardq105 (by decide)).symm

/-- **Cell (105, 12).** -/
theorem cell105_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK105) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK105) (charOfVec rK105 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK105 e (h : Coordinate 1) T105_12 i :=
  species_entry_eq_sum rK105 ⟨12, by decide⟩ e heK h T105_12 hfix105_12 hinj105_12 hcardT105_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK105) (T105_12 i) (hfix105_12 i) h)

/-! ## Cell (105, 43): |T| = 25 -/

def T105_43list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (1,0,1,0,0), (1,0,2,0,0), (1,0,3,0,0), (1,0,4,0,0), (1,0,0,0,0), (2,0,1,0,0), (2,0,2,0,0), (2,0,3,0,0), (2,0,4,0,0), (2,0,0,0,0), (3,0,1,0,0), (3,0,2,0,0), (3,0,3,0,0), (3,0,4,0,0), (3,0,0,0,0), (4,0,1,0,0), (4,0,2,0,0), (4,0,3,0,0), (4,0,4,0,0), (4,0,0,0,0)]
def T105_43 : Fin 25 → Coordinate 1 := fun i => T105_43list.getD i.val (0,0,0,0,0)

theorem hfix105_43 : ∀ i, ((T105_43 i : Coordinate 1) : Coordinate 1 ⧸ reps rK105)
    ∈ fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105) :=
  repsFix_of_siftB rK105 ⟨43, by decide⟩ T105_43 (by decide)

theorem hinj105_43 : Function.Injective
    (fun i => ((T105_43 i : Coordinate 1) : Coordinate 1 ⧸ reps rK105)) :=
  repsInj_of_reduceAux rK105 T105_43 (by decide)

theorem hcardT105_43 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK105 ⟨43, by decide⟩ R105 hpxR105 hcardq105 (by decide)).symm

/-- **Cell (105, 43).** -/
theorem cell105_43 (e : List (ZMod 25)) (heK : charOK (basisAt rK105) e = true)
    (h : ↥(reps (⟨43, by decide⟩ : Fin 148))) :
    species (reps (⟨43, by decide⟩ : Fin 148)) h (basisElt (reps rK105) (charOfVec rK105 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK105 e (h : Coordinate 1) T105_43 i :=
  species_entry_eq_sum rK105 ⟨43, by decide⟩ e heK h T105_43 hfix105_43 hinj105_43 hcardT105_43
    (fun i => conj_mem_of_fixedPoints (reps ⟨43, by decide⟩) (reps rK105) (T105_43 i) (hfix105_43 i) h)

/-! ## Cell (105, 53): |T| = 25 -/

def T105_53list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (1,0,1,0,0), (1,0,2,0,0), (1,0,3,0,0), (1,0,4,0,0), (1,0,0,0,0), (2,0,1,0,0), (2,0,2,0,0), (2,0,3,0,0), (2,0,4,0,0), (2,0,0,0,0), (3,0,1,0,0), (3,0,2,0,0), (3,0,3,0,0), (3,0,4,0,0), (3,0,0,0,0), (4,0,1,0,0), (4,0,2,0,0), (4,0,3,0,0), (4,0,4,0,0), (4,0,0,0,0)]
def T105_53 : Fin 25 → Coordinate 1 := fun i => T105_53list.getD i.val (0,0,0,0,0)

theorem hfix105_53 : ∀ i, ((T105_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK105)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105) :=
  repsFix_of_siftB rK105 ⟨53, by decide⟩ T105_53 (by decide)

theorem hinj105_53 : Function.Injective
    (fun i => ((T105_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK105)) :=
  repsInj_of_reduceAux rK105 T105_53 (by decide)

theorem hcardT105_53 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK105 ⟨53, by decide⟩ R105 hpxR105 hcardq105 (by decide)).symm

/-- **Cell (105, 53).** -/
theorem cell105_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK105) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK105) (charOfVec rK105 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK105 e (h : Coordinate 1) T105_53 i :=
  species_entry_eq_sum rK105 ⟨53, by decide⟩ e heK h T105_53 hfix105_53 hinj105_53 hcardT105_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK105) (T105_53 i) (hfix105_53 i) h)

/-! ## Cell (105, 105): |T| = 25 -/

def T105_105list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (1,0,1,0,0), (1,0,2,0,0), (1,0,3,0,0), (1,0,4,0,0), (1,0,0,0,0), (2,0,1,0,0), (2,0,2,0,0), (2,0,3,0,0), (2,0,4,0,0), (2,0,0,0,0), (3,0,1,0,0), (3,0,2,0,0), (3,0,3,0,0), (3,0,4,0,0), (3,0,0,0,0), (4,0,1,0,0), (4,0,2,0,0), (4,0,3,0,0), (4,0,4,0,0), (4,0,0,0,0)]
def T105_105 : Fin 25 → Coordinate 1 := fun i => T105_105list.getD i.val (0,0,0,0,0)

theorem hfix105_105 : ∀ i, ((T105_105 i : Coordinate 1) : Coordinate 1 ⧸ reps rK105)
    ∈ fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105) :=
  repsFix_of_siftB rK105 ⟨105, by decide⟩ T105_105 (by decide)

theorem hinj105_105 : Function.Injective
    (fun i => ((T105_105 i : Coordinate 1) : Coordinate 1 ⧸ reps rK105)) :=
  repsInj_of_reduceAux rK105 T105_105 (by decide)

theorem hcardT105_105 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK105 ⟨105, by decide⟩ R105 hpxR105 hcardq105 (by decide)).symm

/-- **Cell (105, 105).** -/
theorem cell105_105 (e : List (ZMod 25)) (heK : charOK (basisAt rK105) e = true)
    (h : ↥(reps (⟨105, by decide⟩ : Fin 148))) :
    species (reps (⟨105, by decide⟩ : Fin 148)) h (basisElt (reps rK105) (charOfVec rK105 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK105 e (h : Coordinate 1) T105_105 i :=
  species_entry_eq_sum rK105 ⟨105, by decide⟩ e heK h T105_105 hfix105_105 hinj105_105 hcardT105_105
    (fun i => conj_mem_of_fixedPoints (reps ⟨105, by decide⟩) (reps rK105) (T105_105 i) (hfix105_105 i) h)

namespace Q2

def R105_2 : Fin 25 → Coordinate 2 := fun i => R105list.getD i.val (0,0,0,0,0)
theorem hpxR105_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK105) (R105_2 i)) := by decide
theorem hcardq105_2 : Nat.card (Coordinate 2 ⧸ reps rK105) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (105, 0) twin -/

def T105_0_2 : Fin 25 → Coordinate 2 := fun i => T105_0list.getD i.val (0,0,0,0,0)

theorem hfix105_0_2 : ∀ i, ((T105_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK105)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK105) :=
  repsFix_of_siftB2 rK105 ⟨0, by decide⟩ T105_0_2 (by decide)

theorem hinj105_0_2 : Function.Injective
    (fun i => ((T105_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK105)) :=
  repsInj_of_reduceAux2 rK105 T105_0_2 (by decide)

theorem hcardT105_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK105)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK105 ⟨0, by decide⟩ R105_2 hpxR105_2 hcardq105_2 (by decide)).symm

/-- **Cell (105, 0) twin (q=2).** -/
theorem cell105_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK105) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK105) (charOfVec2 rK105 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK105 e (h : Coordinate 2) T105_0_2 i :=
  species_entry_eq_sum rK105 ⟨0, by decide⟩ e heK h T105_0_2 hfix105_0_2 hinj105_0_2 hcardT105_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK105) (T105_0_2 i) (hfix105_0_2 i) h)

/-! ### Cell (105, 10) twin -/

def T105_10_2 : Fin 25 → Coordinate 2 := fun i => T105_10list.getD i.val (0,0,0,0,0)

theorem hfix105_10_2 : ∀ i, ((T105_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK105)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK105) :=
  repsFix_of_siftB2 rK105 ⟨10, by decide⟩ T105_10_2 (by decide)

theorem hinj105_10_2 : Function.Injective
    (fun i => ((T105_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK105)) :=
  repsInj_of_reduceAux2 rK105 T105_10_2 (by decide)

theorem hcardT105_10_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK105)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK105 ⟨10, by decide⟩ R105_2 hpxR105_2 hcardq105_2 (by decide)).symm

/-- **Cell (105, 10) twin (q=2).** -/
theorem cell105_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK105) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK105) (charOfVec2 rK105 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK105 e (h : Coordinate 2) T105_10_2 i :=
  species_entry_eq_sum rK105 ⟨10, by decide⟩ e heK h T105_10_2 hfix105_10_2 hinj105_10_2 hcardT105_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK105) (T105_10_2 i) (hfix105_10_2 i) h)

/-! ### Cell (105, 12) twin -/

def T105_12_2 : Fin 25 → Coordinate 2 := fun i => T105_12list.getD i.val (0,0,0,0,0)

theorem hfix105_12_2 : ∀ i, ((T105_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK105)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK105) :=
  repsFix_of_siftB2 rK105 ⟨12, by decide⟩ T105_12_2 (by decide)

theorem hinj105_12_2 : Function.Injective
    (fun i => ((T105_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK105)) :=
  repsInj_of_reduceAux2 rK105 T105_12_2 (by decide)

theorem hcardT105_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK105)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK105 ⟨12, by decide⟩ R105_2 hpxR105_2 hcardq105_2 (by decide)).symm

/-- **Cell (105, 12) twin (q=2).** -/
theorem cell105_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK105) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK105) (charOfVec2 rK105 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK105 e (h : Coordinate 2) T105_12_2 i :=
  species_entry_eq_sum rK105 ⟨12, by decide⟩ e heK h T105_12_2 hfix105_12_2 hinj105_12_2 hcardT105_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK105) (T105_12_2 i) (hfix105_12_2 i) h)

/-! ### Cell (105, 43) twin -/

def T105_43_2 : Fin 25 → Coordinate 2 := fun i => T105_43list.getD i.val (0,0,0,0,0)

theorem hfix105_43_2 : ∀ i, ((T105_43_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK105)
    ∈ fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK105) :=
  repsFix_of_siftB2 rK105 ⟨43, by decide⟩ T105_43_2 (by decide)

theorem hinj105_43_2 : Function.Injective
    (fun i => ((T105_43_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK105)) :=
  repsInj_of_reduceAux2 rK105 T105_43_2 (by decide)

theorem hcardT105_43_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK105)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK105 ⟨43, by decide⟩ R105_2 hpxR105_2 hcardq105_2 (by decide)).symm

/-- **Cell (105, 43) twin (q=2).** -/
theorem cell105_43_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK105) e = true)
    (h : ↥(reps (⟨43, by decide⟩ : Fin 148))) :
    species (reps (⟨43, by decide⟩ : Fin 148)) h (basisElt (reps rK105) (charOfVec2 rK105 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK105 e (h : Coordinate 2) T105_43_2 i :=
  species_entry_eq_sum rK105 ⟨43, by decide⟩ e heK h T105_43_2 hfix105_43_2 hinj105_43_2 hcardT105_43_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨43, by decide⟩) (reps rK105) (T105_43_2 i) (hfix105_43_2 i) h)

/-! ### Cell (105, 53) twin -/

def T105_53_2 : Fin 25 → Coordinate 2 := fun i => T105_53list.getD i.val (0,0,0,0,0)

theorem hfix105_53_2 : ∀ i, ((T105_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK105)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK105) :=
  repsFix_of_siftB2 rK105 ⟨53, by decide⟩ T105_53_2 (by decide)

theorem hinj105_53_2 : Function.Injective
    (fun i => ((T105_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK105)) :=
  repsInj_of_reduceAux2 rK105 T105_53_2 (by decide)

theorem hcardT105_53_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK105)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK105 ⟨53, by decide⟩ R105_2 hpxR105_2 hcardq105_2 (by decide)).symm

/-- **Cell (105, 53) twin (q=2).** -/
theorem cell105_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK105) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK105) (charOfVec2 rK105 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK105 e (h : Coordinate 2) T105_53_2 i :=
  species_entry_eq_sum rK105 ⟨53, by decide⟩ e heK h T105_53_2 hfix105_53_2 hinj105_53_2 hcardT105_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK105) (T105_53_2 i) (hfix105_53_2 i) h)

/-! ### Cell (105, 105) twin -/

def T105_105_2 : Fin 25 → Coordinate 2 := fun i => T105_105list.getD i.val (0,0,0,0,0)

theorem hfix105_105_2 : ∀ i, ((T105_105_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK105)
    ∈ fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK105) :=
  repsFix_of_siftB2 rK105 ⟨105, by decide⟩ T105_105_2 (by decide)

theorem hinj105_105_2 : Function.Injective
    (fun i => ((T105_105_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK105)) :=
  repsInj_of_reduceAux2 rK105 T105_105_2 (by decide)

theorem hcardT105_105_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK105)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK105 ⟨105, by decide⟩ R105_2 hpxR105_2 hcardq105_2 (by decide)).symm

/-- **Cell (105, 105) twin (q=2).** -/
theorem cell105_105_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK105) e = true)
    (h : ↥(reps (⟨105, by decide⟩ : Fin 148))) :
    species (reps (⟨105, by decide⟩ : Fin 148)) h (basisElt (reps rK105) (charOfVec2 rK105 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK105 e (h : Coordinate 2) T105_105_2 i :=
  species_entry_eq_sum rK105 ⟨105, by decide⟩ e heK h T105_105_2 hfix105_105_2 hinj105_105_2 hcardT105_105_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨105, by decide⟩) (reps rK105) (T105_105_2 i) (hfix105_105_2 i) h)

end Q2

/-! # K-class rK = 106  (|G/K| = 25) -/

def rK106 : Fin 148 := ⟨106, by decide⟩

def R106list : List Coordinates := [(0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0)]
def R106 : Fin 25 → Coordinate 1 := fun i => R106list.getD i.val (0,0,0,0,0)

theorem hpxR106 : Function.Injective (fun i => reduceAux 1 (basisAt rK106) (R106 i)) := by decide
theorem hcardq106 : Nat.card (Coordinate 1 ⧸ reps rK106) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (106, 0): |T| = 25 -/

def T106_0list : List Coordinates := [(0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0)]
def T106_0 : Fin 25 → Coordinate 1 := fun i => T106_0list.getD i.val (0,0,0,0,0)

theorem hfix106_0 : ∀ i, ((T106_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK106)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106) :=
  repsFix_of_siftB rK106 ⟨0, by decide⟩ T106_0 (by decide)

theorem hinj106_0 : Function.Injective
    (fun i => ((T106_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK106)) :=
  repsInj_of_reduceAux rK106 T106_0 (by decide)

theorem hcardT106_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK106 ⟨0, by decide⟩ R106 hpxR106 hcardq106 (by decide)).symm

/-- **Cell (106, 0).** -/
theorem cell106_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK106) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK106) (charOfVec rK106 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK106 e (h : Coordinate 1) T106_0 i :=
  species_entry_eq_sum rK106 ⟨0, by decide⟩ e heK h T106_0 hfix106_0 hinj106_0 hcardT106_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK106) (T106_0 i) (hfix106_0 i) h)

/-! ## Cell (106, 10): |T| = 25 -/

def T106_10list : List Coordinates := [(0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0)]
def T106_10 : Fin 25 → Coordinate 1 := fun i => T106_10list.getD i.val (0,0,0,0,0)

theorem hfix106_10 : ∀ i, ((T106_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK106)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106) :=
  repsFix_of_siftB rK106 ⟨10, by decide⟩ T106_10 (by decide)

theorem hinj106_10 : Function.Injective
    (fun i => ((T106_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK106)) :=
  repsInj_of_reduceAux rK106 T106_10 (by decide)

theorem hcardT106_10 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK106 ⟨10, by decide⟩ R106 hpxR106 hcardq106 (by decide)).symm

/-- **Cell (106, 10).** -/
theorem cell106_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK106) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK106) (charOfVec rK106 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK106 e (h : Coordinate 1) T106_10 i :=
  species_entry_eq_sum rK106 ⟨10, by decide⟩ e heK h T106_10 hfix106_10 hinj106_10 hcardT106_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK106) (T106_10 i) (hfix106_10 i) h)

/-! ## Cell (106, 12): |T| = 25 -/

def T106_12list : List Coordinates := [(0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0)]
def T106_12 : Fin 25 → Coordinate 1 := fun i => T106_12list.getD i.val (0,0,0,0,0)

theorem hfix106_12 : ∀ i, ((T106_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK106)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106) :=
  repsFix_of_siftB rK106 ⟨12, by decide⟩ T106_12 (by decide)

theorem hinj106_12 : Function.Injective
    (fun i => ((T106_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK106)) :=
  repsInj_of_reduceAux rK106 T106_12 (by decide)

theorem hcardT106_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK106 ⟨12, by decide⟩ R106 hpxR106 hcardq106 (by decide)).symm

/-- **Cell (106, 12).** -/
theorem cell106_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK106) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK106) (charOfVec rK106 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK106 e (h : Coordinate 1) T106_12 i :=
  species_entry_eq_sum rK106 ⟨12, by decide⟩ e heK h T106_12 hfix106_12 hinj106_12 hcardT106_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK106) (T106_12 i) (hfix106_12 i) h)

/-! ## Cell (106, 44): |T| = 25 -/

def T106_44list : List Coordinates := [(0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0)]
def T106_44 : Fin 25 → Coordinate 1 := fun i => T106_44list.getD i.val (0,0,0,0,0)

theorem hfix106_44 : ∀ i, ((T106_44 i : Coordinate 1) : Coordinate 1 ⧸ reps rK106)
    ∈ fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106) :=
  repsFix_of_siftB rK106 ⟨44, by decide⟩ T106_44 (by decide)

theorem hinj106_44 : Function.Injective
    (fun i => ((T106_44 i : Coordinate 1) : Coordinate 1 ⧸ reps rK106)) :=
  repsInj_of_reduceAux rK106 T106_44 (by decide)

theorem hcardT106_44 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK106 ⟨44, by decide⟩ R106 hpxR106 hcardq106 (by decide)).symm

/-- **Cell (106, 44).** -/
theorem cell106_44 (e : List (ZMod 25)) (heK : charOK (basisAt rK106) e = true)
    (h : ↥(reps (⟨44, by decide⟩ : Fin 148))) :
    species (reps (⟨44, by decide⟩ : Fin 148)) h (basisElt (reps rK106) (charOfVec rK106 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK106 e (h : Coordinate 1) T106_44 i :=
  species_entry_eq_sum rK106 ⟨44, by decide⟩ e heK h T106_44 hfix106_44 hinj106_44 hcardT106_44
    (fun i => conj_mem_of_fixedPoints (reps ⟨44, by decide⟩) (reps rK106) (T106_44 i) (hfix106_44 i) h)

/-! ## Cell (106, 53): |T| = 25 -/

def T106_53list : List Coordinates := [(0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0)]
def T106_53 : Fin 25 → Coordinate 1 := fun i => T106_53list.getD i.val (0,0,0,0,0)

theorem hfix106_53 : ∀ i, ((T106_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK106)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106) :=
  repsFix_of_siftB rK106 ⟨53, by decide⟩ T106_53 (by decide)

theorem hinj106_53 : Function.Injective
    (fun i => ((T106_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK106)) :=
  repsInj_of_reduceAux rK106 T106_53 (by decide)

theorem hcardT106_53 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK106 ⟨53, by decide⟩ R106 hpxR106 hcardq106 (by decide)).symm

/-- **Cell (106, 53).** -/
theorem cell106_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK106) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK106) (charOfVec rK106 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK106 e (h : Coordinate 1) T106_53 i :=
  species_entry_eq_sum rK106 ⟨53, by decide⟩ e heK h T106_53 hfix106_53 hinj106_53 hcardT106_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK106) (T106_53 i) (hfix106_53 i) h)

/-! ## Cell (106, 106): |T| = 25 -/

def T106_106list : List Coordinates := [(0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0)]
def T106_106 : Fin 25 → Coordinate 1 := fun i => T106_106list.getD i.val (0,0,0,0,0)

theorem hfix106_106 : ∀ i, ((T106_106 i : Coordinate 1) : Coordinate 1 ⧸ reps rK106)
    ∈ fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106) :=
  repsFix_of_siftB rK106 ⟨106, by decide⟩ T106_106 (by decide)

theorem hinj106_106 : Function.Injective
    (fun i => ((T106_106 i : Coordinate 1) : Coordinate 1 ⧸ reps rK106)) :=
  repsInj_of_reduceAux rK106 T106_106 (by decide)

theorem hcardT106_106 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK106 ⟨106, by decide⟩ R106 hpxR106 hcardq106 (by decide)).symm

/-- **Cell (106, 106).** -/
theorem cell106_106 (e : List (ZMod 25)) (heK : charOK (basisAt rK106) e = true)
    (h : ↥(reps (⟨106, by decide⟩ : Fin 148))) :
    species (reps (⟨106, by decide⟩ : Fin 148)) h (basisElt (reps rK106) (charOfVec rK106 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK106 e (h : Coordinate 1) T106_106 i :=
  species_entry_eq_sum rK106 ⟨106, by decide⟩ e heK h T106_106 hfix106_106 hinj106_106 hcardT106_106
    (fun i => conj_mem_of_fixedPoints (reps ⟨106, by decide⟩) (reps rK106) (T106_106 i) (hfix106_106 i) h)

namespace Q2

def R106_2 : Fin 25 → Coordinate 2 := fun i => R106list.getD i.val (0,0,0,0,0)
theorem hpxR106_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK106) (R106_2 i)) := by decide
theorem hcardq106_2 : Nat.card (Coordinate 2 ⧸ reps rK106) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (106, 0) twin -/

def T106_0_2 : Fin 25 → Coordinate 2 := fun i => T106_0list.getD i.val (0,0,0,0,0)

theorem hfix106_0_2 : ∀ i, ((T106_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK106)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK106) :=
  repsFix_of_siftB2 rK106 ⟨0, by decide⟩ T106_0_2 (by decide)

theorem hinj106_0_2 : Function.Injective
    (fun i => ((T106_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK106)) :=
  repsInj_of_reduceAux2 rK106 T106_0_2 (by decide)

theorem hcardT106_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK106)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK106 ⟨0, by decide⟩ R106_2 hpxR106_2 hcardq106_2 (by decide)).symm

/-- **Cell (106, 0) twin (q=2).** -/
theorem cell106_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK106) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK106) (charOfVec2 rK106 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK106 e (h : Coordinate 2) T106_0_2 i :=
  species_entry_eq_sum rK106 ⟨0, by decide⟩ e heK h T106_0_2 hfix106_0_2 hinj106_0_2 hcardT106_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK106) (T106_0_2 i) (hfix106_0_2 i) h)

/-! ### Cell (106, 10) twin -/

def T106_10_2 : Fin 25 → Coordinate 2 := fun i => T106_10list.getD i.val (0,0,0,0,0)

theorem hfix106_10_2 : ∀ i, ((T106_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK106)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK106) :=
  repsFix_of_siftB2 rK106 ⟨10, by decide⟩ T106_10_2 (by decide)

theorem hinj106_10_2 : Function.Injective
    (fun i => ((T106_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK106)) :=
  repsInj_of_reduceAux2 rK106 T106_10_2 (by decide)

theorem hcardT106_10_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK106)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK106 ⟨10, by decide⟩ R106_2 hpxR106_2 hcardq106_2 (by decide)).symm

/-- **Cell (106, 10) twin (q=2).** -/
theorem cell106_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK106) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK106) (charOfVec2 rK106 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK106 e (h : Coordinate 2) T106_10_2 i :=
  species_entry_eq_sum rK106 ⟨10, by decide⟩ e heK h T106_10_2 hfix106_10_2 hinj106_10_2 hcardT106_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK106) (T106_10_2 i) (hfix106_10_2 i) h)

/-! ### Cell (106, 12) twin -/

def T106_12_2 : Fin 25 → Coordinate 2 := fun i => T106_12list.getD i.val (0,0,0,0,0)

theorem hfix106_12_2 : ∀ i, ((T106_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK106)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK106) :=
  repsFix_of_siftB2 rK106 ⟨12, by decide⟩ T106_12_2 (by decide)

theorem hinj106_12_2 : Function.Injective
    (fun i => ((T106_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK106)) :=
  repsInj_of_reduceAux2 rK106 T106_12_2 (by decide)

theorem hcardT106_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK106)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK106 ⟨12, by decide⟩ R106_2 hpxR106_2 hcardq106_2 (by decide)).symm

/-- **Cell (106, 12) twin (q=2).** -/
theorem cell106_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK106) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK106) (charOfVec2 rK106 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK106 e (h : Coordinate 2) T106_12_2 i :=
  species_entry_eq_sum rK106 ⟨12, by decide⟩ e heK h T106_12_2 hfix106_12_2 hinj106_12_2 hcardT106_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK106) (T106_12_2 i) (hfix106_12_2 i) h)

/-! ### Cell (106, 44) twin -/

def T106_44_2 : Fin 25 → Coordinate 2 := fun i => T106_44list.getD i.val (0,0,0,0,0)

theorem hfix106_44_2 : ∀ i, ((T106_44_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK106)
    ∈ fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK106) :=
  repsFix_of_siftB2 rK106 ⟨44, by decide⟩ T106_44_2 (by decide)

theorem hinj106_44_2 : Function.Injective
    (fun i => ((T106_44_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK106)) :=
  repsInj_of_reduceAux2 rK106 T106_44_2 (by decide)

theorem hcardT106_44_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK106)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK106 ⟨44, by decide⟩ R106_2 hpxR106_2 hcardq106_2 (by decide)).symm

/-- **Cell (106, 44) twin (q=2).** -/
theorem cell106_44_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK106) e = true)
    (h : ↥(reps (⟨44, by decide⟩ : Fin 148))) :
    species (reps (⟨44, by decide⟩ : Fin 148)) h (basisElt (reps rK106) (charOfVec2 rK106 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK106 e (h : Coordinate 2) T106_44_2 i :=
  species_entry_eq_sum rK106 ⟨44, by decide⟩ e heK h T106_44_2 hfix106_44_2 hinj106_44_2 hcardT106_44_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨44, by decide⟩) (reps rK106) (T106_44_2 i) (hfix106_44_2 i) h)

/-! ### Cell (106, 53) twin -/

def T106_53_2 : Fin 25 → Coordinate 2 := fun i => T106_53list.getD i.val (0,0,0,0,0)

theorem hfix106_53_2 : ∀ i, ((T106_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK106)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK106) :=
  repsFix_of_siftB2 rK106 ⟨53, by decide⟩ T106_53_2 (by decide)

theorem hinj106_53_2 : Function.Injective
    (fun i => ((T106_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK106)) :=
  repsInj_of_reduceAux2 rK106 T106_53_2 (by decide)

theorem hcardT106_53_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK106)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK106 ⟨53, by decide⟩ R106_2 hpxR106_2 hcardq106_2 (by decide)).symm

/-- **Cell (106, 53) twin (q=2).** -/
theorem cell106_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK106) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK106) (charOfVec2 rK106 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK106 e (h : Coordinate 2) T106_53_2 i :=
  species_entry_eq_sum rK106 ⟨53, by decide⟩ e heK h T106_53_2 hfix106_53_2 hinj106_53_2 hcardT106_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK106) (T106_53_2 i) (hfix106_53_2 i) h)

/-! ### Cell (106, 106) twin -/

def T106_106_2 : Fin 25 → Coordinate 2 := fun i => T106_106list.getD i.val (0,0,0,0,0)

theorem hfix106_106_2 : ∀ i, ((T106_106_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK106)
    ∈ fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK106) :=
  repsFix_of_siftB2 rK106 ⟨106, by decide⟩ T106_106_2 (by decide)

theorem hinj106_106_2 : Function.Injective
    (fun i => ((T106_106_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK106)) :=
  repsInj_of_reduceAux2 rK106 T106_106_2 (by decide)

theorem hcardT106_106_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK106)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK106 ⟨106, by decide⟩ R106_2 hpxR106_2 hcardq106_2 (by decide)).symm

/-- **Cell (106, 106) twin (q=2).** -/
theorem cell106_106_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK106) e = true)
    (h : ↥(reps (⟨106, by decide⟩ : Fin 148))) :
    species (reps (⟨106, by decide⟩ : Fin 148)) h (basisElt (reps rK106) (charOfVec2 rK106 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK106 e (h : Coordinate 2) T106_106_2 i :=
  species_entry_eq_sum rK106 ⟨106, by decide⟩ e heK h T106_106_2 hfix106_106_2 hinj106_106_2 hcardT106_106_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨106, by decide⟩) (reps rK106) (T106_106_2 i) (hfix106_106_2 i) h)

end Q2

/-! # K-class rK = 107  (|G/K| = 25) -/

def rK107 : Fin 148 := ⟨107, by decide⟩

def R107list : List Coordinates := [(0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0)]
def R107 : Fin 25 → Coordinate 1 := fun i => R107list.getD i.val (0,0,0,0,0)

theorem hpxR107 : Function.Injective (fun i => reduceAux 1 (basisAt rK107) (R107 i)) := by decide
theorem hcardq107 : Nat.card (Coordinate 1 ⧸ reps rK107) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (107, 0): |T| = 25 -/

def T107_0list : List Coordinates := [(0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0)]
def T107_0 : Fin 25 → Coordinate 1 := fun i => T107_0list.getD i.val (0,0,0,0,0)

theorem hfix107_0 : ∀ i, ((T107_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK107)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107) :=
  repsFix_of_siftB rK107 ⟨0, by decide⟩ T107_0 (by decide)

theorem hinj107_0 : Function.Injective
    (fun i => ((T107_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK107)) :=
  repsInj_of_reduceAux rK107 T107_0 (by decide)

theorem hcardT107_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK107 ⟨0, by decide⟩ R107 hpxR107 hcardq107 (by decide)).symm

/-- **Cell (107, 0).** -/
theorem cell107_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK107) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK107) (charOfVec rK107 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK107 e (h : Coordinate 1) T107_0 i :=
  species_entry_eq_sum rK107 ⟨0, by decide⟩ e heK h T107_0 hfix107_0 hinj107_0 hcardT107_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK107) (T107_0 i) (hfix107_0 i) h)

/-! ## Cell (107, 10): |T| = 25 -/

def T107_10list : List Coordinates := [(0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0)]
def T107_10 : Fin 25 → Coordinate 1 := fun i => T107_10list.getD i.val (0,0,0,0,0)

theorem hfix107_10 : ∀ i, ((T107_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK107)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107) :=
  repsFix_of_siftB rK107 ⟨10, by decide⟩ T107_10 (by decide)

theorem hinj107_10 : Function.Injective
    (fun i => ((T107_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK107)) :=
  repsInj_of_reduceAux rK107 T107_10 (by decide)

theorem hcardT107_10 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK107 ⟨10, by decide⟩ R107 hpxR107 hcardq107 (by decide)).symm

/-- **Cell (107, 10).** -/
theorem cell107_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK107) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK107) (charOfVec rK107 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK107 e (h : Coordinate 1) T107_10 i :=
  species_entry_eq_sum rK107 ⟨10, by decide⟩ e heK h T107_10 hfix107_10 hinj107_10 hcardT107_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK107) (T107_10 i) (hfix107_10 i) h)

/-! ## Cell (107, 12): |T| = 25 -/

def T107_12list : List Coordinates := [(0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0)]
def T107_12 : Fin 25 → Coordinate 1 := fun i => T107_12list.getD i.val (0,0,0,0,0)

theorem hfix107_12 : ∀ i, ((T107_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK107)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107) :=
  repsFix_of_siftB rK107 ⟨12, by decide⟩ T107_12 (by decide)

theorem hinj107_12 : Function.Injective
    (fun i => ((T107_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK107)) :=
  repsInj_of_reduceAux rK107 T107_12 (by decide)

theorem hcardT107_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK107 ⟨12, by decide⟩ R107 hpxR107 hcardq107 (by decide)).symm

/-- **Cell (107, 12).** -/
theorem cell107_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK107) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK107) (charOfVec rK107 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK107 e (h : Coordinate 1) T107_12 i :=
  species_entry_eq_sum rK107 ⟨12, by decide⟩ e heK h T107_12 hfix107_12 hinj107_12 hcardT107_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK107) (T107_12 i) (hfix107_12 i) h)

/-! ## Cell (107, 45): |T| = 25 -/

def T107_45list : List Coordinates := [(0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0)]
def T107_45 : Fin 25 → Coordinate 1 := fun i => T107_45list.getD i.val (0,0,0,0,0)

theorem hfix107_45 : ∀ i, ((T107_45 i : Coordinate 1) : Coordinate 1 ⧸ reps rK107)
    ∈ fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107) :=
  repsFix_of_siftB rK107 ⟨45, by decide⟩ T107_45 (by decide)

theorem hinj107_45 : Function.Injective
    (fun i => ((T107_45 i : Coordinate 1) : Coordinate 1 ⧸ reps rK107)) :=
  repsInj_of_reduceAux rK107 T107_45 (by decide)

theorem hcardT107_45 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK107 ⟨45, by decide⟩ R107 hpxR107 hcardq107 (by decide)).symm

/-- **Cell (107, 45).** -/
theorem cell107_45 (e : List (ZMod 25)) (heK : charOK (basisAt rK107) e = true)
    (h : ↥(reps (⟨45, by decide⟩ : Fin 148))) :
    species (reps (⟨45, by decide⟩ : Fin 148)) h (basisElt (reps rK107) (charOfVec rK107 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK107 e (h : Coordinate 1) T107_45 i :=
  species_entry_eq_sum rK107 ⟨45, by decide⟩ e heK h T107_45 hfix107_45 hinj107_45 hcardT107_45
    (fun i => conj_mem_of_fixedPoints (reps ⟨45, by decide⟩) (reps rK107) (T107_45 i) (hfix107_45 i) h)

/-! ## Cell (107, 53): |T| = 25 -/

def T107_53list : List Coordinates := [(0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0)]
def T107_53 : Fin 25 → Coordinate 1 := fun i => T107_53list.getD i.val (0,0,0,0,0)

theorem hfix107_53 : ∀ i, ((T107_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK107)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107) :=
  repsFix_of_siftB rK107 ⟨53, by decide⟩ T107_53 (by decide)

theorem hinj107_53 : Function.Injective
    (fun i => ((T107_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK107)) :=
  repsInj_of_reduceAux rK107 T107_53 (by decide)

theorem hcardT107_53 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK107 ⟨53, by decide⟩ R107 hpxR107 hcardq107 (by decide)).symm

/-- **Cell (107, 53).** -/
theorem cell107_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK107) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK107) (charOfVec rK107 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK107 e (h : Coordinate 1) T107_53 i :=
  species_entry_eq_sum rK107 ⟨53, by decide⟩ e heK h T107_53 hfix107_53 hinj107_53 hcardT107_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK107) (T107_53 i) (hfix107_53 i) h)

/-! ## Cell (107, 107): |T| = 25 -/

def T107_107list : List Coordinates := [(0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0)]
def T107_107 : Fin 25 → Coordinate 1 := fun i => T107_107list.getD i.val (0,0,0,0,0)

theorem hfix107_107 : ∀ i, ((T107_107 i : Coordinate 1) : Coordinate 1 ⧸ reps rK107)
    ∈ fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107) :=
  repsFix_of_siftB rK107 ⟨107, by decide⟩ T107_107 (by decide)

theorem hinj107_107 : Function.Injective
    (fun i => ((T107_107 i : Coordinate 1) : Coordinate 1 ⧸ reps rK107)) :=
  repsInj_of_reduceAux rK107 T107_107 (by decide)

theorem hcardT107_107 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK107 ⟨107, by decide⟩ R107 hpxR107 hcardq107 (by decide)).symm

/-- **Cell (107, 107).** -/
theorem cell107_107 (e : List (ZMod 25)) (heK : charOK (basisAt rK107) e = true)
    (h : ↥(reps (⟨107, by decide⟩ : Fin 148))) :
    species (reps (⟨107, by decide⟩ : Fin 148)) h (basisElt (reps rK107) (charOfVec rK107 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK107 e (h : Coordinate 1) T107_107 i :=
  species_entry_eq_sum rK107 ⟨107, by decide⟩ e heK h T107_107 hfix107_107 hinj107_107 hcardT107_107
    (fun i => conj_mem_of_fixedPoints (reps ⟨107, by decide⟩) (reps rK107) (T107_107 i) (hfix107_107 i) h)

namespace Q2

def R107_2 : Fin 25 → Coordinate 2 := fun i => R107list.getD i.val (0,0,0,0,0)
theorem hpxR107_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK107) (R107_2 i)) := by decide
theorem hcardq107_2 : Nat.card (Coordinate 2 ⧸ reps rK107) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (107, 0) twin -/

def T107_0_2 : Fin 25 → Coordinate 2 := fun i => T107_0list.getD i.val (0,0,0,0,0)

theorem hfix107_0_2 : ∀ i, ((T107_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK107)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK107) :=
  repsFix_of_siftB2 rK107 ⟨0, by decide⟩ T107_0_2 (by decide)

theorem hinj107_0_2 : Function.Injective
    (fun i => ((T107_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK107)) :=
  repsInj_of_reduceAux2 rK107 T107_0_2 (by decide)

theorem hcardT107_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK107)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK107 ⟨0, by decide⟩ R107_2 hpxR107_2 hcardq107_2 (by decide)).symm

/-- **Cell (107, 0) twin (q=2).** -/
theorem cell107_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK107) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK107) (charOfVec2 rK107 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK107 e (h : Coordinate 2) T107_0_2 i :=
  species_entry_eq_sum rK107 ⟨0, by decide⟩ e heK h T107_0_2 hfix107_0_2 hinj107_0_2 hcardT107_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK107) (T107_0_2 i) (hfix107_0_2 i) h)

/-! ### Cell (107, 10) twin -/

def T107_10_2 : Fin 25 → Coordinate 2 := fun i => T107_10list.getD i.val (0,0,0,0,0)

theorem hfix107_10_2 : ∀ i, ((T107_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK107)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK107) :=
  repsFix_of_siftB2 rK107 ⟨10, by decide⟩ T107_10_2 (by decide)

theorem hinj107_10_2 : Function.Injective
    (fun i => ((T107_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK107)) :=
  repsInj_of_reduceAux2 rK107 T107_10_2 (by decide)

theorem hcardT107_10_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK107)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK107 ⟨10, by decide⟩ R107_2 hpxR107_2 hcardq107_2 (by decide)).symm

/-- **Cell (107, 10) twin (q=2).** -/
theorem cell107_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK107) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK107) (charOfVec2 rK107 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK107 e (h : Coordinate 2) T107_10_2 i :=
  species_entry_eq_sum rK107 ⟨10, by decide⟩ e heK h T107_10_2 hfix107_10_2 hinj107_10_2 hcardT107_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK107) (T107_10_2 i) (hfix107_10_2 i) h)

/-! ### Cell (107, 12) twin -/

def T107_12_2 : Fin 25 → Coordinate 2 := fun i => T107_12list.getD i.val (0,0,0,0,0)

theorem hfix107_12_2 : ∀ i, ((T107_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK107)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK107) :=
  repsFix_of_siftB2 rK107 ⟨12, by decide⟩ T107_12_2 (by decide)

theorem hinj107_12_2 : Function.Injective
    (fun i => ((T107_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK107)) :=
  repsInj_of_reduceAux2 rK107 T107_12_2 (by decide)

theorem hcardT107_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK107)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK107 ⟨12, by decide⟩ R107_2 hpxR107_2 hcardq107_2 (by decide)).symm

/-- **Cell (107, 12) twin (q=2).** -/
theorem cell107_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK107) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK107) (charOfVec2 rK107 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK107 e (h : Coordinate 2) T107_12_2 i :=
  species_entry_eq_sum rK107 ⟨12, by decide⟩ e heK h T107_12_2 hfix107_12_2 hinj107_12_2 hcardT107_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK107) (T107_12_2 i) (hfix107_12_2 i) h)

/-! ### Cell (107, 45) twin -/

def T107_45_2 : Fin 25 → Coordinate 2 := fun i => T107_45list.getD i.val (0,0,0,0,0)

theorem hfix107_45_2 : ∀ i, ((T107_45_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK107)
    ∈ fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK107) :=
  repsFix_of_siftB2 rK107 ⟨45, by decide⟩ T107_45_2 (by decide)

theorem hinj107_45_2 : Function.Injective
    (fun i => ((T107_45_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK107)) :=
  repsInj_of_reduceAux2 rK107 T107_45_2 (by decide)

theorem hcardT107_45_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK107)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK107 ⟨45, by decide⟩ R107_2 hpxR107_2 hcardq107_2 (by decide)).symm

/-- **Cell (107, 45) twin (q=2).** -/
theorem cell107_45_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK107) e = true)
    (h : ↥(reps (⟨45, by decide⟩ : Fin 148))) :
    species (reps (⟨45, by decide⟩ : Fin 148)) h (basisElt (reps rK107) (charOfVec2 rK107 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK107 e (h : Coordinate 2) T107_45_2 i :=
  species_entry_eq_sum rK107 ⟨45, by decide⟩ e heK h T107_45_2 hfix107_45_2 hinj107_45_2 hcardT107_45_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨45, by decide⟩) (reps rK107) (T107_45_2 i) (hfix107_45_2 i) h)

/-! ### Cell (107, 53) twin -/

def T107_53_2 : Fin 25 → Coordinate 2 := fun i => T107_53list.getD i.val (0,0,0,0,0)

theorem hfix107_53_2 : ∀ i, ((T107_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK107)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK107) :=
  repsFix_of_siftB2 rK107 ⟨53, by decide⟩ T107_53_2 (by decide)

theorem hinj107_53_2 : Function.Injective
    (fun i => ((T107_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK107)) :=
  repsInj_of_reduceAux2 rK107 T107_53_2 (by decide)

theorem hcardT107_53_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK107)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK107 ⟨53, by decide⟩ R107_2 hpxR107_2 hcardq107_2 (by decide)).symm

/-- **Cell (107, 53) twin (q=2).** -/
theorem cell107_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK107) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK107) (charOfVec2 rK107 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK107 e (h : Coordinate 2) T107_53_2 i :=
  species_entry_eq_sum rK107 ⟨53, by decide⟩ e heK h T107_53_2 hfix107_53_2 hinj107_53_2 hcardT107_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK107) (T107_53_2 i) (hfix107_53_2 i) h)

/-! ### Cell (107, 107) twin -/

def T107_107_2 : Fin 25 → Coordinate 2 := fun i => T107_107list.getD i.val (0,0,0,0,0)

theorem hfix107_107_2 : ∀ i, ((T107_107_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK107)
    ∈ fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK107) :=
  repsFix_of_siftB2 rK107 ⟨107, by decide⟩ T107_107_2 (by decide)

theorem hinj107_107_2 : Function.Injective
    (fun i => ((T107_107_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK107)) :=
  repsInj_of_reduceAux2 rK107 T107_107_2 (by decide)

theorem hcardT107_107_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK107)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK107 ⟨107, by decide⟩ R107_2 hpxR107_2 hcardq107_2 (by decide)).symm

/-- **Cell (107, 107) twin (q=2).** -/
theorem cell107_107_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK107) e = true)
    (h : ↥(reps (⟨107, by decide⟩ : Fin 148))) :
    species (reps (⟨107, by decide⟩ : Fin 148)) h (basisElt (reps rK107) (charOfVec2 rK107 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK107 e (h : Coordinate 2) T107_107_2 i :=
  species_entry_eq_sum rK107 ⟨107, by decide⟩ e heK h T107_107_2 hfix107_107_2 hinj107_107_2 hcardT107_107_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨107, by decide⟩) (reps rK107) (T107_107_2 i) (hfix107_107_2 i) h)

end Q2

/-! # K-class rK = 108  (|G/K| = 25) -/

def rK108 : Fin 148 := ⟨108, by decide⟩

def R108list : List Coordinates := [(0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0)]
def R108 : Fin 25 → Coordinate 1 := fun i => R108list.getD i.val (0,0,0,0,0)

theorem hpxR108 : Function.Injective (fun i => reduceAux 1 (basisAt rK108) (R108 i)) := by decide
theorem hcardq108 : Nat.card (Coordinate 1 ⧸ reps rK108) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (108, 0): |T| = 25 -/

def T108_0list : List Coordinates := [(0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0)]
def T108_0 : Fin 25 → Coordinate 1 := fun i => T108_0list.getD i.val (0,0,0,0,0)

theorem hfix108_0 : ∀ i, ((T108_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK108)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108) :=
  repsFix_of_siftB rK108 ⟨0, by decide⟩ T108_0 (by decide)

theorem hinj108_0 : Function.Injective
    (fun i => ((T108_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK108)) :=
  repsInj_of_reduceAux rK108 T108_0 (by decide)

theorem hcardT108_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK108 ⟨0, by decide⟩ R108 hpxR108 hcardq108 (by decide)).symm

/-- **Cell (108, 0).** -/
theorem cell108_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK108) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK108) (charOfVec rK108 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK108 e (h : Coordinate 1) T108_0 i :=
  species_entry_eq_sum rK108 ⟨0, by decide⟩ e heK h T108_0 hfix108_0 hinj108_0 hcardT108_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK108) (T108_0 i) (hfix108_0 i) h)

/-! ## Cell (108, 10): |T| = 25 -/

def T108_10list : List Coordinates := [(0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0)]
def T108_10 : Fin 25 → Coordinate 1 := fun i => T108_10list.getD i.val (0,0,0,0,0)

theorem hfix108_10 : ∀ i, ((T108_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK108)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108) :=
  repsFix_of_siftB rK108 ⟨10, by decide⟩ T108_10 (by decide)

theorem hinj108_10 : Function.Injective
    (fun i => ((T108_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK108)) :=
  repsInj_of_reduceAux rK108 T108_10 (by decide)

theorem hcardT108_10 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK108 ⟨10, by decide⟩ R108 hpxR108 hcardq108 (by decide)).symm

/-- **Cell (108, 10).** -/
theorem cell108_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK108) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK108) (charOfVec rK108 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK108 e (h : Coordinate 1) T108_10 i :=
  species_entry_eq_sum rK108 ⟨10, by decide⟩ e heK h T108_10 hfix108_10 hinj108_10 hcardT108_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK108) (T108_10 i) (hfix108_10 i) h)

/-! ## Cell (108, 12): |T| = 25 -/

def T108_12list : List Coordinates := [(0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0)]
def T108_12 : Fin 25 → Coordinate 1 := fun i => T108_12list.getD i.val (0,0,0,0,0)

theorem hfix108_12 : ∀ i, ((T108_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK108)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108) :=
  repsFix_of_siftB rK108 ⟨12, by decide⟩ T108_12 (by decide)

theorem hinj108_12 : Function.Injective
    (fun i => ((T108_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK108)) :=
  repsInj_of_reduceAux rK108 T108_12 (by decide)

theorem hcardT108_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK108 ⟨12, by decide⟩ R108 hpxR108 hcardq108 (by decide)).symm

/-- **Cell (108, 12).** -/
theorem cell108_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK108) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK108) (charOfVec rK108 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK108 e (h : Coordinate 1) T108_12 i :=
  species_entry_eq_sum rK108 ⟨12, by decide⟩ e heK h T108_12 hfix108_12 hinj108_12 hcardT108_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK108) (T108_12 i) (hfix108_12 i) h)

/-! ## Cell (108, 46): |T| = 25 -/

def T108_46list : List Coordinates := [(0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0)]
def T108_46 : Fin 25 → Coordinate 1 := fun i => T108_46list.getD i.val (0,0,0,0,0)

theorem hfix108_46 : ∀ i, ((T108_46 i : Coordinate 1) : Coordinate 1 ⧸ reps rK108)
    ∈ fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108) :=
  repsFix_of_siftB rK108 ⟨46, by decide⟩ T108_46 (by decide)

theorem hinj108_46 : Function.Injective
    (fun i => ((T108_46 i : Coordinate 1) : Coordinate 1 ⧸ reps rK108)) :=
  repsInj_of_reduceAux rK108 T108_46 (by decide)

theorem hcardT108_46 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK108 ⟨46, by decide⟩ R108 hpxR108 hcardq108 (by decide)).symm

/-- **Cell (108, 46).** -/
theorem cell108_46 (e : List (ZMod 25)) (heK : charOK (basisAt rK108) e = true)
    (h : ↥(reps (⟨46, by decide⟩ : Fin 148))) :
    species (reps (⟨46, by decide⟩ : Fin 148)) h (basisElt (reps rK108) (charOfVec rK108 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK108 e (h : Coordinate 1) T108_46 i :=
  species_entry_eq_sum rK108 ⟨46, by decide⟩ e heK h T108_46 hfix108_46 hinj108_46 hcardT108_46
    (fun i => conj_mem_of_fixedPoints (reps ⟨46, by decide⟩) (reps rK108) (T108_46 i) (hfix108_46 i) h)

/-! ## Cell (108, 53): |T| = 25 -/

def T108_53list : List Coordinates := [(0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0)]
def T108_53 : Fin 25 → Coordinate 1 := fun i => T108_53list.getD i.val (0,0,0,0,0)

theorem hfix108_53 : ∀ i, ((T108_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK108)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108) :=
  repsFix_of_siftB rK108 ⟨53, by decide⟩ T108_53 (by decide)

theorem hinj108_53 : Function.Injective
    (fun i => ((T108_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK108)) :=
  repsInj_of_reduceAux rK108 T108_53 (by decide)

theorem hcardT108_53 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK108 ⟨53, by decide⟩ R108 hpxR108 hcardq108 (by decide)).symm

/-- **Cell (108, 53).** -/
theorem cell108_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK108) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK108) (charOfVec rK108 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK108 e (h : Coordinate 1) T108_53 i :=
  species_entry_eq_sum rK108 ⟨53, by decide⟩ e heK h T108_53 hfix108_53 hinj108_53 hcardT108_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK108) (T108_53 i) (hfix108_53 i) h)

/-! ## Cell (108, 108): |T| = 25 -/

def T108_108list : List Coordinates := [(0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0)]
def T108_108 : Fin 25 → Coordinate 1 := fun i => T108_108list.getD i.val (0,0,0,0,0)

theorem hfix108_108 : ∀ i, ((T108_108 i : Coordinate 1) : Coordinate 1 ⧸ reps rK108)
    ∈ fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108) :=
  repsFix_of_siftB rK108 ⟨108, by decide⟩ T108_108 (by decide)

theorem hinj108_108 : Function.Injective
    (fun i => ((T108_108 i : Coordinate 1) : Coordinate 1 ⧸ reps rK108)) :=
  repsInj_of_reduceAux rK108 T108_108 (by decide)

theorem hcardT108_108 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK108 ⟨108, by decide⟩ R108 hpxR108 hcardq108 (by decide)).symm

/-- **Cell (108, 108).** -/
theorem cell108_108 (e : List (ZMod 25)) (heK : charOK (basisAt rK108) e = true)
    (h : ↥(reps (⟨108, by decide⟩ : Fin 148))) :
    species (reps (⟨108, by decide⟩ : Fin 148)) h (basisElt (reps rK108) (charOfVec rK108 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK108 e (h : Coordinate 1) T108_108 i :=
  species_entry_eq_sum rK108 ⟨108, by decide⟩ e heK h T108_108 hfix108_108 hinj108_108 hcardT108_108
    (fun i => conj_mem_of_fixedPoints (reps ⟨108, by decide⟩) (reps rK108) (T108_108 i) (hfix108_108 i) h)

namespace Q2

def R108_2 : Fin 25 → Coordinate 2 := fun i => R108list.getD i.val (0,0,0,0,0)
theorem hpxR108_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK108) (R108_2 i)) := by decide
theorem hcardq108_2 : Nat.card (Coordinate 2 ⧸ reps rK108) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (108, 0) twin -/

def T108_0_2 : Fin 25 → Coordinate 2 := fun i => T108_0list.getD i.val (0,0,0,0,0)

theorem hfix108_0_2 : ∀ i, ((T108_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK108)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK108) :=
  repsFix_of_siftB2 rK108 ⟨0, by decide⟩ T108_0_2 (by decide)

theorem hinj108_0_2 : Function.Injective
    (fun i => ((T108_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK108)) :=
  repsInj_of_reduceAux2 rK108 T108_0_2 (by decide)

theorem hcardT108_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK108)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK108 ⟨0, by decide⟩ R108_2 hpxR108_2 hcardq108_2 (by decide)).symm

/-- **Cell (108, 0) twin (q=2).** -/
theorem cell108_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK108) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK108) (charOfVec2 rK108 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK108 e (h : Coordinate 2) T108_0_2 i :=
  species_entry_eq_sum rK108 ⟨0, by decide⟩ e heK h T108_0_2 hfix108_0_2 hinj108_0_2 hcardT108_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK108) (T108_0_2 i) (hfix108_0_2 i) h)

/-! ### Cell (108, 10) twin -/

def T108_10_2 : Fin 25 → Coordinate 2 := fun i => T108_10list.getD i.val (0,0,0,0,0)

theorem hfix108_10_2 : ∀ i, ((T108_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK108)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK108) :=
  repsFix_of_siftB2 rK108 ⟨10, by decide⟩ T108_10_2 (by decide)

theorem hinj108_10_2 : Function.Injective
    (fun i => ((T108_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK108)) :=
  repsInj_of_reduceAux2 rK108 T108_10_2 (by decide)

theorem hcardT108_10_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK108)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK108 ⟨10, by decide⟩ R108_2 hpxR108_2 hcardq108_2 (by decide)).symm

/-- **Cell (108, 10) twin (q=2).** -/
theorem cell108_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK108) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK108) (charOfVec2 rK108 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK108 e (h : Coordinate 2) T108_10_2 i :=
  species_entry_eq_sum rK108 ⟨10, by decide⟩ e heK h T108_10_2 hfix108_10_2 hinj108_10_2 hcardT108_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK108) (T108_10_2 i) (hfix108_10_2 i) h)

/-! ### Cell (108, 12) twin -/

def T108_12_2 : Fin 25 → Coordinate 2 := fun i => T108_12list.getD i.val (0,0,0,0,0)

theorem hfix108_12_2 : ∀ i, ((T108_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK108)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK108) :=
  repsFix_of_siftB2 rK108 ⟨12, by decide⟩ T108_12_2 (by decide)

theorem hinj108_12_2 : Function.Injective
    (fun i => ((T108_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK108)) :=
  repsInj_of_reduceAux2 rK108 T108_12_2 (by decide)

theorem hcardT108_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK108)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK108 ⟨12, by decide⟩ R108_2 hpxR108_2 hcardq108_2 (by decide)).symm

/-- **Cell (108, 12) twin (q=2).** -/
theorem cell108_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK108) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK108) (charOfVec2 rK108 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK108 e (h : Coordinate 2) T108_12_2 i :=
  species_entry_eq_sum rK108 ⟨12, by decide⟩ e heK h T108_12_2 hfix108_12_2 hinj108_12_2 hcardT108_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK108) (T108_12_2 i) (hfix108_12_2 i) h)

/-! ### Cell (108, 46) twin -/

def T108_46_2 : Fin 25 → Coordinate 2 := fun i => T108_46list.getD i.val (0,0,0,0,0)

theorem hfix108_46_2 : ∀ i, ((T108_46_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK108)
    ∈ fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK108) :=
  repsFix_of_siftB2 rK108 ⟨46, by decide⟩ T108_46_2 (by decide)

theorem hinj108_46_2 : Function.Injective
    (fun i => ((T108_46_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK108)) :=
  repsInj_of_reduceAux2 rK108 T108_46_2 (by decide)

theorem hcardT108_46_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK108)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK108 ⟨46, by decide⟩ R108_2 hpxR108_2 hcardq108_2 (by decide)).symm

/-- **Cell (108, 46) twin (q=2).** -/
theorem cell108_46_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK108) e = true)
    (h : ↥(reps (⟨46, by decide⟩ : Fin 148))) :
    species (reps (⟨46, by decide⟩ : Fin 148)) h (basisElt (reps rK108) (charOfVec2 rK108 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK108 e (h : Coordinate 2) T108_46_2 i :=
  species_entry_eq_sum rK108 ⟨46, by decide⟩ e heK h T108_46_2 hfix108_46_2 hinj108_46_2 hcardT108_46_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨46, by decide⟩) (reps rK108) (T108_46_2 i) (hfix108_46_2 i) h)

/-! ### Cell (108, 53) twin -/

def T108_53_2 : Fin 25 → Coordinate 2 := fun i => T108_53list.getD i.val (0,0,0,0,0)

theorem hfix108_53_2 : ∀ i, ((T108_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK108)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK108) :=
  repsFix_of_siftB2 rK108 ⟨53, by decide⟩ T108_53_2 (by decide)

theorem hinj108_53_2 : Function.Injective
    (fun i => ((T108_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK108)) :=
  repsInj_of_reduceAux2 rK108 T108_53_2 (by decide)

theorem hcardT108_53_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK108)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK108 ⟨53, by decide⟩ R108_2 hpxR108_2 hcardq108_2 (by decide)).symm

/-- **Cell (108, 53) twin (q=2).** -/
theorem cell108_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK108) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK108) (charOfVec2 rK108 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK108 e (h : Coordinate 2) T108_53_2 i :=
  species_entry_eq_sum rK108 ⟨53, by decide⟩ e heK h T108_53_2 hfix108_53_2 hinj108_53_2 hcardT108_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK108) (T108_53_2 i) (hfix108_53_2 i) h)

/-! ### Cell (108, 108) twin -/

def T108_108_2 : Fin 25 → Coordinate 2 := fun i => T108_108list.getD i.val (0,0,0,0,0)

theorem hfix108_108_2 : ∀ i, ((T108_108_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK108)
    ∈ fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK108) :=
  repsFix_of_siftB2 rK108 ⟨108, by decide⟩ T108_108_2 (by decide)

theorem hinj108_108_2 : Function.Injective
    (fun i => ((T108_108_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK108)) :=
  repsInj_of_reduceAux2 rK108 T108_108_2 (by decide)

theorem hcardT108_108_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK108)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK108 ⟨108, by decide⟩ R108_2 hpxR108_2 hcardq108_2 (by decide)).symm

/-- **Cell (108, 108) twin (q=2).** -/
theorem cell108_108_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK108) e = true)
    (h : ↥(reps (⟨108, by decide⟩ : Fin 148))) :
    species (reps (⟨108, by decide⟩ : Fin 148)) h (basisElt (reps rK108) (charOfVec2 rK108 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK108 e (h : Coordinate 2) T108_108_2 i :=
  species_entry_eq_sum rK108 ⟨108, by decide⟩ e heK h T108_108_2 hfix108_108_2 hinj108_108_2 hcardT108_108_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨108, by decide⟩) (reps rK108) (T108_108_2 i) (hfix108_108_2 i) h)

end Q2

end LeanDring.P5Presentation
