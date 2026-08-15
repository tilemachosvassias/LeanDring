/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, K-strata data (5^3 stratum, rK 109-115): certified per-cell species-entry instantiations, both
twins.

Covers K-classes 109, 110, 111, 112, 113, 114, 115 (order-5^3 K, |R|=25).  For each nonzero
`H`-column
(`(G/K)^H ≠ ∅`), the full coset transversal `R109..` and each `H`-fixed
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

/-! # K-class rK = 109  (|G/K| = 25) -/

def rK109 : Fin 148 := ⟨109, by decide⟩

def R109list : List Coordinates := [(0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def R109 : Fin 25 → Coordinate 1 := fun i => R109list.getD i.val (0,0,0,0,0)

theorem hpxR109 : Function.Injective (fun i => reduceAux 1 (basisAt rK109) (R109 i)) := by decide
theorem hcardq109 : Nat.card (Coordinate 1 ⧸ reps rK109) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (109, 0): |T| = 25 -/

def T109_0list : List Coordinates := [(0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T109_0 : Fin 25 → Coordinate 1 := fun i => T109_0list.getD i.val (0,0,0,0,0)

theorem hfix109_0 : ∀ i, ((T109_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK109)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109) :=
  repsFix_of_siftB rK109 ⟨0, by decide⟩ T109_0 (by decide)

theorem hinj109_0 : Function.Injective
    (fun i => ((T109_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK109)) :=
  repsInj_of_reduceAux rK109 T109_0 (by decide)

theorem hcardT109_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK109 ⟨0, by decide⟩ R109 hpxR109 hcardq109 (by decide)).symm

/-- **Cell (109, 0).** -/
theorem cell109_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK109) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK109) (charOfVec rK109 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK109 e (h : Coordinate 1) T109_0 i :=
  species_entry_eq_sum rK109 ⟨0, by decide⟩ e heK h T109_0 hfix109_0 hinj109_0 hcardT109_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK109) (T109_0 i) (hfix109_0 i) h)

/-! ## Cell (109, 10): |T| = 25 -/

def T109_10list : List Coordinates := [(0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T109_10 : Fin 25 → Coordinate 1 := fun i => T109_10list.getD i.val (0,0,0,0,0)

theorem hfix109_10 : ∀ i, ((T109_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK109)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109) :=
  repsFix_of_siftB rK109 ⟨10, by decide⟩ T109_10 (by decide)

theorem hinj109_10 : Function.Injective
    (fun i => ((T109_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK109)) :=
  repsInj_of_reduceAux rK109 T109_10 (by decide)

theorem hcardT109_10 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK109 ⟨10, by decide⟩ R109 hpxR109 hcardq109 (by decide)).symm

/-- **Cell (109, 10).** -/
theorem cell109_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK109) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK109) (charOfVec rK109 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK109 e (h : Coordinate 1) T109_10 i :=
  species_entry_eq_sum rK109 ⟨10, by decide⟩ e heK h T109_10 hfix109_10 hinj109_10 hcardT109_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK109) (T109_10 i) (hfix109_10 i) h)

/-! ## Cell (109, 12): |T| = 25 -/

def T109_12list : List Coordinates := [(0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T109_12 : Fin 25 → Coordinate 1 := fun i => T109_12list.getD i.val (0,0,0,0,0)

theorem hfix109_12 : ∀ i, ((T109_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK109)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109) :=
  repsFix_of_siftB rK109 ⟨12, by decide⟩ T109_12 (by decide)

theorem hinj109_12 : Function.Injective
    (fun i => ((T109_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK109)) :=
  repsInj_of_reduceAux rK109 T109_12 (by decide)

theorem hcardT109_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK109 ⟨12, by decide⟩ R109 hpxR109 hcardq109 (by decide)).symm

/-- **Cell (109, 12).** -/
theorem cell109_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK109) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK109) (charOfVec rK109 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK109 e (h : Coordinate 1) T109_12 i :=
  species_entry_eq_sum rK109 ⟨12, by decide⟩ e heK h T109_12 hfix109_12 hinj109_12 hcardT109_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK109) (T109_12 i) (hfix109_12 i) h)

/-! ## Cell (109, 47): |T| = 25 -/

def T109_47list : List Coordinates := [(0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T109_47 : Fin 25 → Coordinate 1 := fun i => T109_47list.getD i.val (0,0,0,0,0)

theorem hfix109_47 : ∀ i, ((T109_47 i : Coordinate 1) : Coordinate 1 ⧸ reps rK109)
    ∈ fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109) :=
  repsFix_of_siftB rK109 ⟨47, by decide⟩ T109_47 (by decide)

theorem hinj109_47 : Function.Injective
    (fun i => ((T109_47 i : Coordinate 1) : Coordinate 1 ⧸ reps rK109)) :=
  repsInj_of_reduceAux rK109 T109_47 (by decide)

theorem hcardT109_47 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK109 ⟨47, by decide⟩ R109 hpxR109 hcardq109 (by decide)).symm

/-- **Cell (109, 47).** -/
theorem cell109_47 (e : List (ZMod 25)) (heK : charOK (basisAt rK109) e = true)
    (h : ↥(reps (⟨47, by decide⟩ : Fin 148))) :
    species (reps (⟨47, by decide⟩ : Fin 148)) h (basisElt (reps rK109) (charOfVec rK109 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK109 e (h : Coordinate 1) T109_47 i :=
  species_entry_eq_sum rK109 ⟨47, by decide⟩ e heK h T109_47 hfix109_47 hinj109_47 hcardT109_47
    (fun i => conj_mem_of_fixedPoints (reps ⟨47, by decide⟩) (reps rK109) (T109_47 i) (hfix109_47 i) h)

/-! ## Cell (109, 53): |T| = 25 -/

def T109_53list : List Coordinates := [(0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T109_53 : Fin 25 → Coordinate 1 := fun i => T109_53list.getD i.val (0,0,0,0,0)

theorem hfix109_53 : ∀ i, ((T109_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK109)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109) :=
  repsFix_of_siftB rK109 ⟨53, by decide⟩ T109_53 (by decide)

theorem hinj109_53 : Function.Injective
    (fun i => ((T109_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK109)) :=
  repsInj_of_reduceAux rK109 T109_53 (by decide)

theorem hcardT109_53 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK109 ⟨53, by decide⟩ R109 hpxR109 hcardq109 (by decide)).symm

/-- **Cell (109, 53).** -/
theorem cell109_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK109) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK109) (charOfVec rK109 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK109 e (h : Coordinate 1) T109_53 i :=
  species_entry_eq_sum rK109 ⟨53, by decide⟩ e heK h T109_53 hfix109_53 hinj109_53 hcardT109_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK109) (T109_53 i) (hfix109_53 i) h)

/-! ## Cell (109, 109): |T| = 25 -/

def T109_109list : List Coordinates := [(0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T109_109 : Fin 25 → Coordinate 1 := fun i => T109_109list.getD i.val (0,0,0,0,0)

theorem hfix109_109 : ∀ i, ((T109_109 i : Coordinate 1) : Coordinate 1 ⧸ reps rK109)
    ∈ fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109) :=
  repsFix_of_siftB rK109 ⟨109, by decide⟩ T109_109 (by decide)

theorem hinj109_109 : Function.Injective
    (fun i => ((T109_109 i : Coordinate 1) : Coordinate 1 ⧸ reps rK109)) :=
  repsInj_of_reduceAux rK109 T109_109 (by decide)

theorem hcardT109_109 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK109 ⟨109, by decide⟩ R109 hpxR109 hcardq109 (by decide)).symm

/-- **Cell (109, 109).** -/
theorem cell109_109 (e : List (ZMod 25)) (heK : charOK (basisAt rK109) e = true)
    (h : ↥(reps (⟨109, by decide⟩ : Fin 148))) :
    species (reps (⟨109, by decide⟩ : Fin 148)) h (basisElt (reps rK109) (charOfVec rK109 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK109 e (h : Coordinate 1) T109_109 i :=
  species_entry_eq_sum rK109 ⟨109, by decide⟩ e heK h T109_109 hfix109_109 hinj109_109 hcardT109_109
    (fun i => conj_mem_of_fixedPoints (reps ⟨109, by decide⟩) (reps rK109) (T109_109 i) (hfix109_109 i) h)

namespace Q2

def R109_2 : Fin 25 → Coordinate 2 := fun i => R109list.getD i.val (0,0,0,0,0)
theorem hpxR109_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK109) (R109_2 i)) := by decide
theorem hcardq109_2 : Nat.card (Coordinate 2 ⧸ reps rK109) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (109, 0) twin -/

def T109_0_2 : Fin 25 → Coordinate 2 := fun i => T109_0list.getD i.val (0,0,0,0,0)

theorem hfix109_0_2 : ∀ i, ((T109_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK109)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK109) :=
  repsFix_of_siftB2 rK109 ⟨0, by decide⟩ T109_0_2 (by decide)

theorem hinj109_0_2 : Function.Injective
    (fun i => ((T109_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK109)) :=
  repsInj_of_reduceAux2 rK109 T109_0_2 (by decide)

theorem hcardT109_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK109)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK109 ⟨0, by decide⟩ R109_2 hpxR109_2 hcardq109_2 (by decide)).symm

/-- **Cell (109, 0) twin (q=2).** -/
theorem cell109_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK109) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK109) (charOfVec2 rK109 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK109 e (h : Coordinate 2) T109_0_2 i :=
  species_entry_eq_sum rK109 ⟨0, by decide⟩ e heK h T109_0_2 hfix109_0_2 hinj109_0_2 hcardT109_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK109) (T109_0_2 i) (hfix109_0_2 i) h)

/-! ### Cell (109, 10) twin -/

def T109_10_2 : Fin 25 → Coordinate 2 := fun i => T109_10list.getD i.val (0,0,0,0,0)

theorem hfix109_10_2 : ∀ i, ((T109_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK109)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK109) :=
  repsFix_of_siftB2 rK109 ⟨10, by decide⟩ T109_10_2 (by decide)

theorem hinj109_10_2 : Function.Injective
    (fun i => ((T109_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK109)) :=
  repsInj_of_reduceAux2 rK109 T109_10_2 (by decide)

theorem hcardT109_10_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK109)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK109 ⟨10, by decide⟩ R109_2 hpxR109_2 hcardq109_2 (by decide)).symm

/-- **Cell (109, 10) twin (q=2).** -/
theorem cell109_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK109) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK109) (charOfVec2 rK109 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK109 e (h : Coordinate 2) T109_10_2 i :=
  species_entry_eq_sum rK109 ⟨10, by decide⟩ e heK h T109_10_2 hfix109_10_2 hinj109_10_2 hcardT109_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK109) (T109_10_2 i) (hfix109_10_2 i) h)

/-! ### Cell (109, 12) twin -/

def T109_12_2 : Fin 25 → Coordinate 2 := fun i => T109_12list.getD i.val (0,0,0,0,0)

theorem hfix109_12_2 : ∀ i, ((T109_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK109)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK109) :=
  repsFix_of_siftB2 rK109 ⟨12, by decide⟩ T109_12_2 (by decide)

theorem hinj109_12_2 : Function.Injective
    (fun i => ((T109_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK109)) :=
  repsInj_of_reduceAux2 rK109 T109_12_2 (by decide)

theorem hcardT109_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK109)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK109 ⟨12, by decide⟩ R109_2 hpxR109_2 hcardq109_2 (by decide)).symm

/-- **Cell (109, 12) twin (q=2).** -/
theorem cell109_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK109) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK109) (charOfVec2 rK109 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK109 e (h : Coordinate 2) T109_12_2 i :=
  species_entry_eq_sum rK109 ⟨12, by decide⟩ e heK h T109_12_2 hfix109_12_2 hinj109_12_2 hcardT109_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK109) (T109_12_2 i) (hfix109_12_2 i) h)

/-! ### Cell (109, 47) twin -/

def T109_47_2 : Fin 25 → Coordinate 2 := fun i => T109_47list.getD i.val (0,0,0,0,0)

theorem hfix109_47_2 : ∀ i, ((T109_47_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK109)
    ∈ fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK109) :=
  repsFix_of_siftB2 rK109 ⟨47, by decide⟩ T109_47_2 (by decide)

theorem hinj109_47_2 : Function.Injective
    (fun i => ((T109_47_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK109)) :=
  repsInj_of_reduceAux2 rK109 T109_47_2 (by decide)

theorem hcardT109_47_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK109)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK109 ⟨47, by decide⟩ R109_2 hpxR109_2 hcardq109_2 (by decide)).symm

/-- **Cell (109, 47) twin (q=2).** -/
theorem cell109_47_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK109) e = true)
    (h : ↥(reps (⟨47, by decide⟩ : Fin 148))) :
    species (reps (⟨47, by decide⟩ : Fin 148)) h (basisElt (reps rK109) (charOfVec2 rK109 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK109 e (h : Coordinate 2) T109_47_2 i :=
  species_entry_eq_sum rK109 ⟨47, by decide⟩ e heK h T109_47_2 hfix109_47_2 hinj109_47_2 hcardT109_47_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨47, by decide⟩) (reps rK109) (T109_47_2 i) (hfix109_47_2 i) h)

/-! ### Cell (109, 53) twin -/

def T109_53_2 : Fin 25 → Coordinate 2 := fun i => T109_53list.getD i.val (0,0,0,0,0)

theorem hfix109_53_2 : ∀ i, ((T109_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK109)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK109) :=
  repsFix_of_siftB2 rK109 ⟨53, by decide⟩ T109_53_2 (by decide)

theorem hinj109_53_2 : Function.Injective
    (fun i => ((T109_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK109)) :=
  repsInj_of_reduceAux2 rK109 T109_53_2 (by decide)

theorem hcardT109_53_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK109)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK109 ⟨53, by decide⟩ R109_2 hpxR109_2 hcardq109_2 (by decide)).symm

/-- **Cell (109, 53) twin (q=2).** -/
theorem cell109_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK109) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK109) (charOfVec2 rK109 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK109 e (h : Coordinate 2) T109_53_2 i :=
  species_entry_eq_sum rK109 ⟨53, by decide⟩ e heK h T109_53_2 hfix109_53_2 hinj109_53_2 hcardT109_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK109) (T109_53_2 i) (hfix109_53_2 i) h)

/-! ### Cell (109, 109) twin -/

def T109_109_2 : Fin 25 → Coordinate 2 := fun i => T109_109list.getD i.val (0,0,0,0,0)

theorem hfix109_109_2 : ∀ i, ((T109_109_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK109)
    ∈ fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK109) :=
  repsFix_of_siftB2 rK109 ⟨109, by decide⟩ T109_109_2 (by decide)

theorem hinj109_109_2 : Function.Injective
    (fun i => ((T109_109_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK109)) :=
  repsInj_of_reduceAux2 rK109 T109_109_2 (by decide)

theorem hcardT109_109_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK109)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK109 ⟨109, by decide⟩ R109_2 hpxR109_2 hcardq109_2 (by decide)).symm

/-- **Cell (109, 109) twin (q=2).** -/
theorem cell109_109_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK109) e = true)
    (h : ↥(reps (⟨109, by decide⟩ : Fin 148))) :
    species (reps (⟨109, by decide⟩ : Fin 148)) h (basisElt (reps rK109) (charOfVec2 rK109 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK109 e (h : Coordinate 2) T109_109_2 i :=
  species_entry_eq_sum rK109 ⟨109, by decide⟩ e heK h T109_109_2 hfix109_109_2 hinj109_109_2 hcardT109_109_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨109, by decide⟩) (reps rK109) (T109_109_2 i) (hfix109_109_2 i) h)

end Q2

/-! # K-class rK = 110  (|G/K| = 25) -/

def rK110 : Fin 148 := ⟨110, by decide⟩

def R110list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (1,0,0,0,0), (1,0,1,0,0), (1,0,2,0,0), (1,0,3,0,0), (1,0,4,0,0), (2,0,0,0,0), (2,0,1,0,0), (2,0,2,0,0), (2,0,3,0,0), (2,0,4,0,0), (3,0,0,0,0), (3,0,1,0,0), (3,0,2,0,0), (3,0,3,0,0), (3,0,4,0,0), (4,0,0,0,0), (4,0,1,0,0), (4,0,2,0,0), (4,0,3,0,0), (4,0,4,0,0)]
def R110 : Fin 25 → Coordinate 1 := fun i => R110list.getD i.val (0,0,0,0,0)

theorem hpxR110 : Function.Injective (fun i => reduceAux 1 (basisAt rK110) (R110 i)) := by decide
theorem hcardq110 : Nat.card (Coordinate 1 ⧸ reps rK110) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (110, 0): |T| = 25 -/

def T110_0list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (1,0,0,0,0), (1,0,1,0,0), (1,0,2,0,0), (1,0,3,0,0), (1,0,4,0,0), (2,0,0,0,0), (2,0,1,0,0), (2,0,2,0,0), (2,0,3,0,0), (2,0,4,0,0), (3,0,0,0,0), (3,0,1,0,0), (3,0,2,0,0), (3,0,3,0,0), (3,0,4,0,0), (4,0,0,0,0), (4,0,1,0,0), (4,0,2,0,0), (4,0,3,0,0), (4,0,4,0,0)]
def T110_0 : Fin 25 → Coordinate 1 := fun i => T110_0list.getD i.val (0,0,0,0,0)

theorem hfix110_0 : ∀ i, ((T110_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK110)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110) :=
  repsFix_of_siftB rK110 ⟨0, by decide⟩ T110_0 (by decide)

theorem hinj110_0 : Function.Injective
    (fun i => ((T110_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK110)) :=
  repsInj_of_reduceAux rK110 T110_0 (by decide)

theorem hcardT110_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK110 ⟨0, by decide⟩ R110 hpxR110 hcardq110 (by decide)).symm

/-- **Cell (110, 0).** -/
theorem cell110_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK110) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK110) (charOfVec rK110 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK110 e (h : Coordinate 1) T110_0 i :=
  species_entry_eq_sum rK110 ⟨0, by decide⟩ e heK h T110_0 hfix110_0 hinj110_0 hcardT110_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK110) (T110_0 i) (hfix110_0 i) h)

/-! ## Cell (110, 10): |T| = 25 -/

def T110_10list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (1,0,0,0,0), (1,0,1,0,0), (1,0,2,0,0), (1,0,3,0,0), (1,0,4,0,0), (2,0,0,0,0), (2,0,1,0,0), (2,0,2,0,0), (2,0,3,0,0), (2,0,4,0,0), (3,0,0,0,0), (3,0,1,0,0), (3,0,2,0,0), (3,0,3,0,0), (3,0,4,0,0), (4,0,0,0,0), (4,0,1,0,0), (4,0,2,0,0), (4,0,3,0,0), (4,0,4,0,0)]
def T110_10 : Fin 25 → Coordinate 1 := fun i => T110_10list.getD i.val (0,0,0,0,0)

theorem hfix110_10 : ∀ i, ((T110_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK110)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110) :=
  repsFix_of_siftB rK110 ⟨10, by decide⟩ T110_10 (by decide)

theorem hinj110_10 : Function.Injective
    (fun i => ((T110_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK110)) :=
  repsInj_of_reduceAux rK110 T110_10 (by decide)

theorem hcardT110_10 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK110 ⟨10, by decide⟩ R110 hpxR110 hcardq110 (by decide)).symm

/-- **Cell (110, 10).** -/
theorem cell110_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK110) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK110) (charOfVec rK110 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK110 e (h : Coordinate 1) T110_10 i :=
  species_entry_eq_sum rK110 ⟨10, by decide⟩ e heK h T110_10 hfix110_10 hinj110_10 hcardT110_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK110) (T110_10 i) (hfix110_10 i) h)

/-! ## Cell (110, 12): |T| = 25 -/

def T110_12list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (1,0,0,0,0), (1,0,1,0,0), (1,0,2,0,0), (1,0,3,0,0), (1,0,4,0,0), (2,0,0,0,0), (2,0,1,0,0), (2,0,2,0,0), (2,0,3,0,0), (2,0,4,0,0), (3,0,0,0,0), (3,0,1,0,0), (3,0,2,0,0), (3,0,3,0,0), (3,0,4,0,0), (4,0,0,0,0), (4,0,1,0,0), (4,0,2,0,0), (4,0,3,0,0), (4,0,4,0,0)]
def T110_12 : Fin 25 → Coordinate 1 := fun i => T110_12list.getD i.val (0,0,0,0,0)

theorem hfix110_12 : ∀ i, ((T110_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK110)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110) :=
  repsFix_of_siftB rK110 ⟨12, by decide⟩ T110_12 (by decide)

theorem hinj110_12 : Function.Injective
    (fun i => ((T110_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK110)) :=
  repsInj_of_reduceAux rK110 T110_12 (by decide)

theorem hcardT110_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK110 ⟨12, by decide⟩ R110 hpxR110 hcardq110 (by decide)).symm

/-- **Cell (110, 12).** -/
theorem cell110_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK110) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK110) (charOfVec rK110 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK110 e (h : Coordinate 1) T110_12 i :=
  species_entry_eq_sum rK110 ⟨12, by decide⟩ e heK h T110_12 hfix110_12 hinj110_12 hcardT110_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK110) (T110_12 i) (hfix110_12 i) h)

/-! ## Cell (110, 48): |T| = 25 -/

def T110_48list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (1,0,0,0,0), (1,0,1,0,0), (1,0,2,0,0), (1,0,3,0,0), (1,0,4,0,0), (2,0,0,0,0), (2,0,1,0,0), (2,0,2,0,0), (2,0,3,0,0), (2,0,4,0,0), (3,0,0,0,0), (3,0,1,0,0), (3,0,2,0,0), (3,0,3,0,0), (3,0,4,0,0), (4,0,0,0,0), (4,0,1,0,0), (4,0,2,0,0), (4,0,3,0,0), (4,0,4,0,0)]
def T110_48 : Fin 25 → Coordinate 1 := fun i => T110_48list.getD i.val (0,0,0,0,0)

theorem hfix110_48 : ∀ i, ((T110_48 i : Coordinate 1) : Coordinate 1 ⧸ reps rK110)
    ∈ fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110) :=
  repsFix_of_siftB rK110 ⟨48, by decide⟩ T110_48 (by decide)

theorem hinj110_48 : Function.Injective
    (fun i => ((T110_48 i : Coordinate 1) : Coordinate 1 ⧸ reps rK110)) :=
  repsInj_of_reduceAux rK110 T110_48 (by decide)

theorem hcardT110_48 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK110 ⟨48, by decide⟩ R110 hpxR110 hcardq110 (by decide)).symm

/-- **Cell (110, 48).** -/
theorem cell110_48 (e : List (ZMod 25)) (heK : charOK (basisAt rK110) e = true)
    (h : ↥(reps (⟨48, by decide⟩ : Fin 148))) :
    species (reps (⟨48, by decide⟩ : Fin 148)) h (basisElt (reps rK110) (charOfVec rK110 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK110 e (h : Coordinate 1) T110_48 i :=
  species_entry_eq_sum rK110 ⟨48, by decide⟩ e heK h T110_48 hfix110_48 hinj110_48 hcardT110_48
    (fun i => conj_mem_of_fixedPoints (reps ⟨48, by decide⟩) (reps rK110) (T110_48 i) (hfix110_48 i) h)

/-! ## Cell (110, 53): |T| = 25 -/

def T110_53list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (1,0,0,0,0), (1,0,1,0,0), (1,0,2,0,0), (1,0,3,0,0), (1,0,4,0,0), (2,0,0,0,0), (2,0,1,0,0), (2,0,2,0,0), (2,0,3,0,0), (2,0,4,0,0), (3,0,0,0,0), (3,0,1,0,0), (3,0,2,0,0), (3,0,3,0,0), (3,0,4,0,0), (4,0,0,0,0), (4,0,1,0,0), (4,0,2,0,0), (4,0,3,0,0), (4,0,4,0,0)]
def T110_53 : Fin 25 → Coordinate 1 := fun i => T110_53list.getD i.val (0,0,0,0,0)

theorem hfix110_53 : ∀ i, ((T110_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK110)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110) :=
  repsFix_of_siftB rK110 ⟨53, by decide⟩ T110_53 (by decide)

theorem hinj110_53 : Function.Injective
    (fun i => ((T110_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK110)) :=
  repsInj_of_reduceAux rK110 T110_53 (by decide)

theorem hcardT110_53 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK110 ⟨53, by decide⟩ R110 hpxR110 hcardq110 (by decide)).symm

/-- **Cell (110, 53).** -/
theorem cell110_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK110) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK110) (charOfVec rK110 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK110 e (h : Coordinate 1) T110_53 i :=
  species_entry_eq_sum rK110 ⟨53, by decide⟩ e heK h T110_53 hfix110_53 hinj110_53 hcardT110_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK110) (T110_53 i) (hfix110_53 i) h)

/-! ## Cell (110, 110): |T| = 25 -/

def T110_110list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (1,0,0,0,0), (1,0,1,0,0), (1,0,2,0,0), (1,0,3,0,0), (1,0,4,0,0), (2,0,0,0,0), (2,0,1,0,0), (2,0,2,0,0), (2,0,3,0,0), (2,0,4,0,0), (3,0,0,0,0), (3,0,1,0,0), (3,0,2,0,0), (3,0,3,0,0), (3,0,4,0,0), (4,0,0,0,0), (4,0,1,0,0), (4,0,2,0,0), (4,0,3,0,0), (4,0,4,0,0)]
def T110_110 : Fin 25 → Coordinate 1 := fun i => T110_110list.getD i.val (0,0,0,0,0)

theorem hfix110_110 : ∀ i, ((T110_110 i : Coordinate 1) : Coordinate 1 ⧸ reps rK110)
    ∈ fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110) :=
  repsFix_of_siftB rK110 ⟨110, by decide⟩ T110_110 (by decide)

theorem hinj110_110 : Function.Injective
    (fun i => ((T110_110 i : Coordinate 1) : Coordinate 1 ⧸ reps rK110)) :=
  repsInj_of_reduceAux rK110 T110_110 (by decide)

theorem hcardT110_110 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK110 ⟨110, by decide⟩ R110 hpxR110 hcardq110 (by decide)).symm

/-- **Cell (110, 110).** -/
theorem cell110_110 (e : List (ZMod 25)) (heK : charOK (basisAt rK110) e = true)
    (h : ↥(reps (⟨110, by decide⟩ : Fin 148))) :
    species (reps (⟨110, by decide⟩ : Fin 148)) h (basisElt (reps rK110) (charOfVec rK110 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK110 e (h : Coordinate 1) T110_110 i :=
  species_entry_eq_sum rK110 ⟨110, by decide⟩ e heK h T110_110 hfix110_110 hinj110_110 hcardT110_110
    (fun i => conj_mem_of_fixedPoints (reps ⟨110, by decide⟩) (reps rK110) (T110_110 i) (hfix110_110 i) h)

namespace Q2

def R110_2 : Fin 25 → Coordinate 2 := fun i => R110list.getD i.val (0,0,0,0,0)
theorem hpxR110_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK110) (R110_2 i)) := by decide
theorem hcardq110_2 : Nat.card (Coordinate 2 ⧸ reps rK110) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (110, 0) twin -/

def T110_0_2 : Fin 25 → Coordinate 2 := fun i => T110_0list.getD i.val (0,0,0,0,0)

theorem hfix110_0_2 : ∀ i, ((T110_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK110)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK110) :=
  repsFix_of_siftB2 rK110 ⟨0, by decide⟩ T110_0_2 (by decide)

theorem hinj110_0_2 : Function.Injective
    (fun i => ((T110_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK110)) :=
  repsInj_of_reduceAux2 rK110 T110_0_2 (by decide)

theorem hcardT110_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK110)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK110 ⟨0, by decide⟩ R110_2 hpxR110_2 hcardq110_2 (by decide)).symm

/-- **Cell (110, 0) twin (q=2).** -/
theorem cell110_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK110) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK110) (charOfVec2 rK110 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK110 e (h : Coordinate 2) T110_0_2 i :=
  species_entry_eq_sum rK110 ⟨0, by decide⟩ e heK h T110_0_2 hfix110_0_2 hinj110_0_2 hcardT110_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK110) (T110_0_2 i) (hfix110_0_2 i) h)

/-! ### Cell (110, 10) twin -/

def T110_10_2 : Fin 25 → Coordinate 2 := fun i => T110_10list.getD i.val (0,0,0,0,0)

theorem hfix110_10_2 : ∀ i, ((T110_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK110)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK110) :=
  repsFix_of_siftB2 rK110 ⟨10, by decide⟩ T110_10_2 (by decide)

theorem hinj110_10_2 : Function.Injective
    (fun i => ((T110_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK110)) :=
  repsInj_of_reduceAux2 rK110 T110_10_2 (by decide)

theorem hcardT110_10_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK110)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK110 ⟨10, by decide⟩ R110_2 hpxR110_2 hcardq110_2 (by decide)).symm

/-- **Cell (110, 10) twin (q=2).** -/
theorem cell110_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK110) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK110) (charOfVec2 rK110 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK110 e (h : Coordinate 2) T110_10_2 i :=
  species_entry_eq_sum rK110 ⟨10, by decide⟩ e heK h T110_10_2 hfix110_10_2 hinj110_10_2 hcardT110_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK110) (T110_10_2 i) (hfix110_10_2 i) h)

/-! ### Cell (110, 12) twin -/

def T110_12_2 : Fin 25 → Coordinate 2 := fun i => T110_12list.getD i.val (0,0,0,0,0)

theorem hfix110_12_2 : ∀ i, ((T110_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK110)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK110) :=
  repsFix_of_siftB2 rK110 ⟨12, by decide⟩ T110_12_2 (by decide)

theorem hinj110_12_2 : Function.Injective
    (fun i => ((T110_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK110)) :=
  repsInj_of_reduceAux2 rK110 T110_12_2 (by decide)

theorem hcardT110_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK110)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK110 ⟨12, by decide⟩ R110_2 hpxR110_2 hcardq110_2 (by decide)).symm

/-- **Cell (110, 12) twin (q=2).** -/
theorem cell110_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK110) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK110) (charOfVec2 rK110 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK110 e (h : Coordinate 2) T110_12_2 i :=
  species_entry_eq_sum rK110 ⟨12, by decide⟩ e heK h T110_12_2 hfix110_12_2 hinj110_12_2 hcardT110_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK110) (T110_12_2 i) (hfix110_12_2 i) h)

/-! ### Cell (110, 48) twin -/

def T110_48_2 : Fin 25 → Coordinate 2 := fun i => T110_48list.getD i.val (0,0,0,0,0)

theorem hfix110_48_2 : ∀ i, ((T110_48_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK110)
    ∈ fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK110) :=
  repsFix_of_siftB2 rK110 ⟨48, by decide⟩ T110_48_2 (by decide)

theorem hinj110_48_2 : Function.Injective
    (fun i => ((T110_48_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK110)) :=
  repsInj_of_reduceAux2 rK110 T110_48_2 (by decide)

theorem hcardT110_48_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK110)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK110 ⟨48, by decide⟩ R110_2 hpxR110_2 hcardq110_2 (by decide)).symm

/-- **Cell (110, 48) twin (q=2).** -/
theorem cell110_48_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK110) e = true)
    (h : ↥(reps (⟨48, by decide⟩ : Fin 148))) :
    species (reps (⟨48, by decide⟩ : Fin 148)) h (basisElt (reps rK110) (charOfVec2 rK110 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK110 e (h : Coordinate 2) T110_48_2 i :=
  species_entry_eq_sum rK110 ⟨48, by decide⟩ e heK h T110_48_2 hfix110_48_2 hinj110_48_2 hcardT110_48_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨48, by decide⟩) (reps rK110) (T110_48_2 i) (hfix110_48_2 i) h)

/-! ### Cell (110, 53) twin -/

def T110_53_2 : Fin 25 → Coordinate 2 := fun i => T110_53list.getD i.val (0,0,0,0,0)

theorem hfix110_53_2 : ∀ i, ((T110_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK110)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK110) :=
  repsFix_of_siftB2 rK110 ⟨53, by decide⟩ T110_53_2 (by decide)

theorem hinj110_53_2 : Function.Injective
    (fun i => ((T110_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK110)) :=
  repsInj_of_reduceAux2 rK110 T110_53_2 (by decide)

theorem hcardT110_53_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK110)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK110 ⟨53, by decide⟩ R110_2 hpxR110_2 hcardq110_2 (by decide)).symm

/-- **Cell (110, 53) twin (q=2).** -/
theorem cell110_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK110) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK110) (charOfVec2 rK110 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK110 e (h : Coordinate 2) T110_53_2 i :=
  species_entry_eq_sum rK110 ⟨53, by decide⟩ e heK h T110_53_2 hfix110_53_2 hinj110_53_2 hcardT110_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK110) (T110_53_2 i) (hfix110_53_2 i) h)

/-! ### Cell (110, 110) twin -/

def T110_110_2 : Fin 25 → Coordinate 2 := fun i => T110_110list.getD i.val (0,0,0,0,0)

theorem hfix110_110_2 : ∀ i, ((T110_110_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK110)
    ∈ fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK110) :=
  repsFix_of_siftB2 rK110 ⟨110, by decide⟩ T110_110_2 (by decide)

theorem hinj110_110_2 : Function.Injective
    (fun i => ((T110_110_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK110)) :=
  repsInj_of_reduceAux2 rK110 T110_110_2 (by decide)

theorem hcardT110_110_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK110)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK110 ⟨110, by decide⟩ R110_2 hpxR110_2 hcardq110_2 (by decide)).symm

/-- **Cell (110, 110) twin (q=2).** -/
theorem cell110_110_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK110) e = true)
    (h : ↥(reps (⟨110, by decide⟩ : Fin 148))) :
    species (reps (⟨110, by decide⟩ : Fin 148)) h (basisElt (reps rK110) (charOfVec2 rK110 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK110 e (h : Coordinate 2) T110_110_2 i :=
  species_entry_eq_sum rK110 ⟨110, by decide⟩ e heK h T110_110_2 hfix110_110_2 hinj110_110_2 hcardT110_110_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨110, by decide⟩) (reps rK110) (T110_110_2 i) (hfix110_110_2 i) h)

end Q2

/-! # K-class rK = 111  (|G/K| = 25) -/

def rK111 : Fin 148 := ⟨111, by decide⟩

def R111list : List Coordinates := [(0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0)]
def R111 : Fin 25 → Coordinate 1 := fun i => R111list.getD i.val (0,0,0,0,0)

theorem hpxR111 : Function.Injective (fun i => reduceAux 1 (basisAt rK111) (R111 i)) := by decide
theorem hcardq111 : Nat.card (Coordinate 1 ⧸ reps rK111) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (111, 0): |T| = 25 -/

def T111_0list : List Coordinates := [(0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0)]
def T111_0 : Fin 25 → Coordinate 1 := fun i => T111_0list.getD i.val (0,0,0,0,0)

theorem hfix111_0 : ∀ i, ((T111_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK111)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111) :=
  repsFix_of_siftB rK111 ⟨0, by decide⟩ T111_0 (by decide)

theorem hinj111_0 : Function.Injective
    (fun i => ((T111_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK111)) :=
  repsInj_of_reduceAux rK111 T111_0 (by decide)

theorem hcardT111_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK111 ⟨0, by decide⟩ R111 hpxR111 hcardq111 (by decide)).symm

/-- **Cell (111, 0).** -/
theorem cell111_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK111) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK111) (charOfVec rK111 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK111 e (h : Coordinate 1) T111_0 i :=
  species_entry_eq_sum rK111 ⟨0, by decide⟩ e heK h T111_0 hfix111_0 hinj111_0 hcardT111_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK111) (T111_0 i) (hfix111_0 i) h)

/-! ## Cell (111, 10): |T| = 25 -/

def T111_10list : List Coordinates := [(0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0)]
def T111_10 : Fin 25 → Coordinate 1 := fun i => T111_10list.getD i.val (0,0,0,0,0)

theorem hfix111_10 : ∀ i, ((T111_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK111)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111) :=
  repsFix_of_siftB rK111 ⟨10, by decide⟩ T111_10 (by decide)

theorem hinj111_10 : Function.Injective
    (fun i => ((T111_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK111)) :=
  repsInj_of_reduceAux rK111 T111_10 (by decide)

theorem hcardT111_10 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK111 ⟨10, by decide⟩ R111 hpxR111 hcardq111 (by decide)).symm

/-- **Cell (111, 10).** -/
theorem cell111_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK111) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK111) (charOfVec rK111 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK111 e (h : Coordinate 1) T111_10 i :=
  species_entry_eq_sum rK111 ⟨10, by decide⟩ e heK h T111_10 hfix111_10 hinj111_10 hcardT111_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK111) (T111_10 i) (hfix111_10 i) h)

/-! ## Cell (111, 12): |T| = 25 -/

def T111_12list : List Coordinates := [(0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0)]
def T111_12 : Fin 25 → Coordinate 1 := fun i => T111_12list.getD i.val (0,0,0,0,0)

theorem hfix111_12 : ∀ i, ((T111_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK111)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111) :=
  repsFix_of_siftB rK111 ⟨12, by decide⟩ T111_12 (by decide)

theorem hinj111_12 : Function.Injective
    (fun i => ((T111_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK111)) :=
  repsInj_of_reduceAux rK111 T111_12 (by decide)

theorem hcardT111_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK111 ⟨12, by decide⟩ R111 hpxR111 hcardq111 (by decide)).symm

/-- **Cell (111, 12).** -/
theorem cell111_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK111) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK111) (charOfVec rK111 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK111 e (h : Coordinate 1) T111_12 i :=
  species_entry_eq_sum rK111 ⟨12, by decide⟩ e heK h T111_12 hfix111_12 hinj111_12 hcardT111_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK111) (T111_12 i) (hfix111_12 i) h)

/-! ## Cell (111, 49): |T| = 25 -/

def T111_49list : List Coordinates := [(0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0)]
def T111_49 : Fin 25 → Coordinate 1 := fun i => T111_49list.getD i.val (0,0,0,0,0)

theorem hfix111_49 : ∀ i, ((T111_49 i : Coordinate 1) : Coordinate 1 ⧸ reps rK111)
    ∈ fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111) :=
  repsFix_of_siftB rK111 ⟨49, by decide⟩ T111_49 (by decide)

theorem hinj111_49 : Function.Injective
    (fun i => ((T111_49 i : Coordinate 1) : Coordinate 1 ⧸ reps rK111)) :=
  repsInj_of_reduceAux rK111 T111_49 (by decide)

theorem hcardT111_49 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK111 ⟨49, by decide⟩ R111 hpxR111 hcardq111 (by decide)).symm

/-- **Cell (111, 49).** -/
theorem cell111_49 (e : List (ZMod 25)) (heK : charOK (basisAt rK111) e = true)
    (h : ↥(reps (⟨49, by decide⟩ : Fin 148))) :
    species (reps (⟨49, by decide⟩ : Fin 148)) h (basisElt (reps rK111) (charOfVec rK111 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK111 e (h : Coordinate 1) T111_49 i :=
  species_entry_eq_sum rK111 ⟨49, by decide⟩ e heK h T111_49 hfix111_49 hinj111_49 hcardT111_49
    (fun i => conj_mem_of_fixedPoints (reps ⟨49, by decide⟩) (reps rK111) (T111_49 i) (hfix111_49 i) h)

/-! ## Cell (111, 53): |T| = 25 -/

def T111_53list : List Coordinates := [(0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0)]
def T111_53 : Fin 25 → Coordinate 1 := fun i => T111_53list.getD i.val (0,0,0,0,0)

theorem hfix111_53 : ∀ i, ((T111_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK111)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111) :=
  repsFix_of_siftB rK111 ⟨53, by decide⟩ T111_53 (by decide)

theorem hinj111_53 : Function.Injective
    (fun i => ((T111_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK111)) :=
  repsInj_of_reduceAux rK111 T111_53 (by decide)

theorem hcardT111_53 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK111 ⟨53, by decide⟩ R111 hpxR111 hcardq111 (by decide)).symm

/-- **Cell (111, 53).** -/
theorem cell111_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK111) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK111) (charOfVec rK111 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK111 e (h : Coordinate 1) T111_53 i :=
  species_entry_eq_sum rK111 ⟨53, by decide⟩ e heK h T111_53 hfix111_53 hinj111_53 hcardT111_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK111) (T111_53 i) (hfix111_53 i) h)

/-! ## Cell (111, 111): |T| = 25 -/

def T111_111list : List Coordinates := [(0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0)]
def T111_111 : Fin 25 → Coordinate 1 := fun i => T111_111list.getD i.val (0,0,0,0,0)

theorem hfix111_111 : ∀ i, ((T111_111 i : Coordinate 1) : Coordinate 1 ⧸ reps rK111)
    ∈ fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111) :=
  repsFix_of_siftB rK111 ⟨111, by decide⟩ T111_111 (by decide)

theorem hinj111_111 : Function.Injective
    (fun i => ((T111_111 i : Coordinate 1) : Coordinate 1 ⧸ reps rK111)) :=
  repsInj_of_reduceAux rK111 T111_111 (by decide)

theorem hcardT111_111 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK111 ⟨111, by decide⟩ R111 hpxR111 hcardq111 (by decide)).symm

/-- **Cell (111, 111).** -/
theorem cell111_111 (e : List (ZMod 25)) (heK : charOK (basisAt rK111) e = true)
    (h : ↥(reps (⟨111, by decide⟩ : Fin 148))) :
    species (reps (⟨111, by decide⟩ : Fin 148)) h (basisElt (reps rK111) (charOfVec rK111 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK111 e (h : Coordinate 1) T111_111 i :=
  species_entry_eq_sum rK111 ⟨111, by decide⟩ e heK h T111_111 hfix111_111 hinj111_111 hcardT111_111
    (fun i => conj_mem_of_fixedPoints (reps ⟨111, by decide⟩) (reps rK111) (T111_111 i) (hfix111_111 i) h)

namespace Q2

def R111_2 : Fin 25 → Coordinate 2 := fun i => R111list.getD i.val (0,0,0,0,0)
theorem hpxR111_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK111) (R111_2 i)) := by decide
theorem hcardq111_2 : Nat.card (Coordinate 2 ⧸ reps rK111) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (111, 0) twin -/

def T111_0_2 : Fin 25 → Coordinate 2 := fun i => T111_0list.getD i.val (0,0,0,0,0)

theorem hfix111_0_2 : ∀ i, ((T111_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK111)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK111) :=
  repsFix_of_siftB2 rK111 ⟨0, by decide⟩ T111_0_2 (by decide)

theorem hinj111_0_2 : Function.Injective
    (fun i => ((T111_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK111)) :=
  repsInj_of_reduceAux2 rK111 T111_0_2 (by decide)

theorem hcardT111_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK111)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK111 ⟨0, by decide⟩ R111_2 hpxR111_2 hcardq111_2 (by decide)).symm

/-- **Cell (111, 0) twin (q=2).** -/
theorem cell111_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK111) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK111) (charOfVec2 rK111 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK111 e (h : Coordinate 2) T111_0_2 i :=
  species_entry_eq_sum rK111 ⟨0, by decide⟩ e heK h T111_0_2 hfix111_0_2 hinj111_0_2 hcardT111_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK111) (T111_0_2 i) (hfix111_0_2 i) h)

/-! ### Cell (111, 10) twin -/

def T111_10_2 : Fin 25 → Coordinate 2 := fun i => T111_10list.getD i.val (0,0,0,0,0)

theorem hfix111_10_2 : ∀ i, ((T111_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK111)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK111) :=
  repsFix_of_siftB2 rK111 ⟨10, by decide⟩ T111_10_2 (by decide)

theorem hinj111_10_2 : Function.Injective
    (fun i => ((T111_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK111)) :=
  repsInj_of_reduceAux2 rK111 T111_10_2 (by decide)

theorem hcardT111_10_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK111)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK111 ⟨10, by decide⟩ R111_2 hpxR111_2 hcardq111_2 (by decide)).symm

/-- **Cell (111, 10) twin (q=2).** -/
theorem cell111_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK111) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK111) (charOfVec2 rK111 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK111 e (h : Coordinate 2) T111_10_2 i :=
  species_entry_eq_sum rK111 ⟨10, by decide⟩ e heK h T111_10_2 hfix111_10_2 hinj111_10_2 hcardT111_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK111) (T111_10_2 i) (hfix111_10_2 i) h)

/-! ### Cell (111, 12) twin -/

def T111_12_2 : Fin 25 → Coordinate 2 := fun i => T111_12list.getD i.val (0,0,0,0,0)

theorem hfix111_12_2 : ∀ i, ((T111_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK111)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK111) :=
  repsFix_of_siftB2 rK111 ⟨12, by decide⟩ T111_12_2 (by decide)

theorem hinj111_12_2 : Function.Injective
    (fun i => ((T111_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK111)) :=
  repsInj_of_reduceAux2 rK111 T111_12_2 (by decide)

theorem hcardT111_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK111)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK111 ⟨12, by decide⟩ R111_2 hpxR111_2 hcardq111_2 (by decide)).symm

/-- **Cell (111, 12) twin (q=2).** -/
theorem cell111_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK111) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK111) (charOfVec2 rK111 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK111 e (h : Coordinate 2) T111_12_2 i :=
  species_entry_eq_sum rK111 ⟨12, by decide⟩ e heK h T111_12_2 hfix111_12_2 hinj111_12_2 hcardT111_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK111) (T111_12_2 i) (hfix111_12_2 i) h)

/-! ### Cell (111, 49) twin -/

def T111_49_2 : Fin 25 → Coordinate 2 := fun i => T111_49list.getD i.val (0,0,0,0,0)

theorem hfix111_49_2 : ∀ i, ((T111_49_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK111)
    ∈ fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK111) :=
  repsFix_of_siftB2 rK111 ⟨49, by decide⟩ T111_49_2 (by decide)

theorem hinj111_49_2 : Function.Injective
    (fun i => ((T111_49_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK111)) :=
  repsInj_of_reduceAux2 rK111 T111_49_2 (by decide)

theorem hcardT111_49_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK111)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK111 ⟨49, by decide⟩ R111_2 hpxR111_2 hcardq111_2 (by decide)).symm

/-- **Cell (111, 49) twin (q=2).** -/
theorem cell111_49_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK111) e = true)
    (h : ↥(reps (⟨49, by decide⟩ : Fin 148))) :
    species (reps (⟨49, by decide⟩ : Fin 148)) h (basisElt (reps rK111) (charOfVec2 rK111 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK111 e (h : Coordinate 2) T111_49_2 i :=
  species_entry_eq_sum rK111 ⟨49, by decide⟩ e heK h T111_49_2 hfix111_49_2 hinj111_49_2 hcardT111_49_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨49, by decide⟩) (reps rK111) (T111_49_2 i) (hfix111_49_2 i) h)

/-! ### Cell (111, 53) twin -/

def T111_53_2 : Fin 25 → Coordinate 2 := fun i => T111_53list.getD i.val (0,0,0,0,0)

theorem hfix111_53_2 : ∀ i, ((T111_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK111)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK111) :=
  repsFix_of_siftB2 rK111 ⟨53, by decide⟩ T111_53_2 (by decide)

theorem hinj111_53_2 : Function.Injective
    (fun i => ((T111_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK111)) :=
  repsInj_of_reduceAux2 rK111 T111_53_2 (by decide)

theorem hcardT111_53_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK111)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK111 ⟨53, by decide⟩ R111_2 hpxR111_2 hcardq111_2 (by decide)).symm

/-- **Cell (111, 53) twin (q=2).** -/
theorem cell111_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK111) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK111) (charOfVec2 rK111 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK111 e (h : Coordinate 2) T111_53_2 i :=
  species_entry_eq_sum rK111 ⟨53, by decide⟩ e heK h T111_53_2 hfix111_53_2 hinj111_53_2 hcardT111_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK111) (T111_53_2 i) (hfix111_53_2 i) h)

/-! ### Cell (111, 111) twin -/

def T111_111_2 : Fin 25 → Coordinate 2 := fun i => T111_111list.getD i.val (0,0,0,0,0)

theorem hfix111_111_2 : ∀ i, ((T111_111_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK111)
    ∈ fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK111) :=
  repsFix_of_siftB2 rK111 ⟨111, by decide⟩ T111_111_2 (by decide)

theorem hinj111_111_2 : Function.Injective
    (fun i => ((T111_111_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK111)) :=
  repsInj_of_reduceAux2 rK111 T111_111_2 (by decide)

theorem hcardT111_111_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK111)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK111 ⟨111, by decide⟩ R111_2 hpxR111_2 hcardq111_2 (by decide)).symm

/-- **Cell (111, 111) twin (q=2).** -/
theorem cell111_111_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK111) e = true)
    (h : ↥(reps (⟨111, by decide⟩ : Fin 148))) :
    species (reps (⟨111, by decide⟩ : Fin 148)) h (basisElt (reps rK111) (charOfVec2 rK111 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK111 e (h : Coordinate 2) T111_111_2 i :=
  species_entry_eq_sum rK111 ⟨111, by decide⟩ e heK h T111_111_2 hfix111_111_2 hinj111_111_2 hcardT111_111_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨111, by decide⟩) (reps rK111) (T111_111_2 i) (hfix111_111_2 i) h)

end Q2

/-! # K-class rK = 112  (|G/K| = 25) -/

def rK112 : Fin 148 := ⟨112, by decide⟩

def R112list : List Coordinates := [(0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0)]
def R112 : Fin 25 → Coordinate 1 := fun i => R112list.getD i.val (0,0,0,0,0)

theorem hpxR112 : Function.Injective (fun i => reduceAux 1 (basisAt rK112) (R112 i)) := by decide
theorem hcardq112 : Nat.card (Coordinate 1 ⧸ reps rK112) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (112, 0): |T| = 25 -/

def T112_0list : List Coordinates := [(0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0)]
def T112_0 : Fin 25 → Coordinate 1 := fun i => T112_0list.getD i.val (0,0,0,0,0)

theorem hfix112_0 : ∀ i, ((T112_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK112)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112) :=
  repsFix_of_siftB rK112 ⟨0, by decide⟩ T112_0 (by decide)

theorem hinj112_0 : Function.Injective
    (fun i => ((T112_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK112)) :=
  repsInj_of_reduceAux rK112 T112_0 (by decide)

theorem hcardT112_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK112 ⟨0, by decide⟩ R112 hpxR112 hcardq112 (by decide)).symm

/-- **Cell (112, 0).** -/
theorem cell112_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK112) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK112) (charOfVec rK112 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK112 e (h : Coordinate 1) T112_0 i :=
  species_entry_eq_sum rK112 ⟨0, by decide⟩ e heK h T112_0 hfix112_0 hinj112_0 hcardT112_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK112) (T112_0 i) (hfix112_0 i) h)

/-! ## Cell (112, 10): |T| = 25 -/

def T112_10list : List Coordinates := [(0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0)]
def T112_10 : Fin 25 → Coordinate 1 := fun i => T112_10list.getD i.val (0,0,0,0,0)

theorem hfix112_10 : ∀ i, ((T112_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK112)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112) :=
  repsFix_of_siftB rK112 ⟨10, by decide⟩ T112_10 (by decide)

theorem hinj112_10 : Function.Injective
    (fun i => ((T112_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK112)) :=
  repsInj_of_reduceAux rK112 T112_10 (by decide)

theorem hcardT112_10 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK112 ⟨10, by decide⟩ R112 hpxR112 hcardq112 (by decide)).symm

/-- **Cell (112, 10).** -/
theorem cell112_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK112) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK112) (charOfVec rK112 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK112 e (h : Coordinate 1) T112_10 i :=
  species_entry_eq_sum rK112 ⟨10, by decide⟩ e heK h T112_10 hfix112_10 hinj112_10 hcardT112_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK112) (T112_10 i) (hfix112_10 i) h)

/-! ## Cell (112, 12): |T| = 25 -/

def T112_12list : List Coordinates := [(0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0)]
def T112_12 : Fin 25 → Coordinate 1 := fun i => T112_12list.getD i.val (0,0,0,0,0)

theorem hfix112_12 : ∀ i, ((T112_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK112)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112) :=
  repsFix_of_siftB rK112 ⟨12, by decide⟩ T112_12 (by decide)

theorem hinj112_12 : Function.Injective
    (fun i => ((T112_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK112)) :=
  repsInj_of_reduceAux rK112 T112_12 (by decide)

theorem hcardT112_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK112 ⟨12, by decide⟩ R112 hpxR112 hcardq112 (by decide)).symm

/-- **Cell (112, 12).** -/
theorem cell112_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK112) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK112) (charOfVec rK112 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK112 e (h : Coordinate 1) T112_12 i :=
  species_entry_eq_sum rK112 ⟨12, by decide⟩ e heK h T112_12 hfix112_12 hinj112_12 hcardT112_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK112) (T112_12 i) (hfix112_12 i) h)

/-! ## Cell (112, 50): |T| = 25 -/

def T112_50list : List Coordinates := [(0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0)]
def T112_50 : Fin 25 → Coordinate 1 := fun i => T112_50list.getD i.val (0,0,0,0,0)

theorem hfix112_50 : ∀ i, ((T112_50 i : Coordinate 1) : Coordinate 1 ⧸ reps rK112)
    ∈ fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112) :=
  repsFix_of_siftB rK112 ⟨50, by decide⟩ T112_50 (by decide)

theorem hinj112_50 : Function.Injective
    (fun i => ((T112_50 i : Coordinate 1) : Coordinate 1 ⧸ reps rK112)) :=
  repsInj_of_reduceAux rK112 T112_50 (by decide)

theorem hcardT112_50 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK112 ⟨50, by decide⟩ R112 hpxR112 hcardq112 (by decide)).symm

/-- **Cell (112, 50).** -/
theorem cell112_50 (e : List (ZMod 25)) (heK : charOK (basisAt rK112) e = true)
    (h : ↥(reps (⟨50, by decide⟩ : Fin 148))) :
    species (reps (⟨50, by decide⟩ : Fin 148)) h (basisElt (reps rK112) (charOfVec rK112 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK112 e (h : Coordinate 1) T112_50 i :=
  species_entry_eq_sum rK112 ⟨50, by decide⟩ e heK h T112_50 hfix112_50 hinj112_50 hcardT112_50
    (fun i => conj_mem_of_fixedPoints (reps ⟨50, by decide⟩) (reps rK112) (T112_50 i) (hfix112_50 i) h)

/-! ## Cell (112, 53): |T| = 25 -/

def T112_53list : List Coordinates := [(0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0)]
def T112_53 : Fin 25 → Coordinate 1 := fun i => T112_53list.getD i.val (0,0,0,0,0)

theorem hfix112_53 : ∀ i, ((T112_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK112)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112) :=
  repsFix_of_siftB rK112 ⟨53, by decide⟩ T112_53 (by decide)

theorem hinj112_53 : Function.Injective
    (fun i => ((T112_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK112)) :=
  repsInj_of_reduceAux rK112 T112_53 (by decide)

theorem hcardT112_53 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK112 ⟨53, by decide⟩ R112 hpxR112 hcardq112 (by decide)).symm

/-- **Cell (112, 53).** -/
theorem cell112_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK112) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK112) (charOfVec rK112 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK112 e (h : Coordinate 1) T112_53 i :=
  species_entry_eq_sum rK112 ⟨53, by decide⟩ e heK h T112_53 hfix112_53 hinj112_53 hcardT112_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK112) (T112_53 i) (hfix112_53 i) h)

/-! ## Cell (112, 112): |T| = 25 -/

def T112_112list : List Coordinates := [(0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0)]
def T112_112 : Fin 25 → Coordinate 1 := fun i => T112_112list.getD i.val (0,0,0,0,0)

theorem hfix112_112 : ∀ i, ((T112_112 i : Coordinate 1) : Coordinate 1 ⧸ reps rK112)
    ∈ fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112) :=
  repsFix_of_siftB rK112 ⟨112, by decide⟩ T112_112 (by decide)

theorem hinj112_112 : Function.Injective
    (fun i => ((T112_112 i : Coordinate 1) : Coordinate 1 ⧸ reps rK112)) :=
  repsInj_of_reduceAux rK112 T112_112 (by decide)

theorem hcardT112_112 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK112 ⟨112, by decide⟩ R112 hpxR112 hcardq112 (by decide)).symm

/-- **Cell (112, 112).** -/
theorem cell112_112 (e : List (ZMod 25)) (heK : charOK (basisAt rK112) e = true)
    (h : ↥(reps (⟨112, by decide⟩ : Fin 148))) :
    species (reps (⟨112, by decide⟩ : Fin 148)) h (basisElt (reps rK112) (charOfVec rK112 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK112 e (h : Coordinate 1) T112_112 i :=
  species_entry_eq_sum rK112 ⟨112, by decide⟩ e heK h T112_112 hfix112_112 hinj112_112 hcardT112_112
    (fun i => conj_mem_of_fixedPoints (reps ⟨112, by decide⟩) (reps rK112) (T112_112 i) (hfix112_112 i) h)

namespace Q2

def R112_2 : Fin 25 → Coordinate 2 := fun i => R112list.getD i.val (0,0,0,0,0)
theorem hpxR112_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK112) (R112_2 i)) := by decide
theorem hcardq112_2 : Nat.card (Coordinate 2 ⧸ reps rK112) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (112, 0) twin -/

def T112_0_2 : Fin 25 → Coordinate 2 := fun i => T112_0list.getD i.val (0,0,0,0,0)

theorem hfix112_0_2 : ∀ i, ((T112_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK112)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK112) :=
  repsFix_of_siftB2 rK112 ⟨0, by decide⟩ T112_0_2 (by decide)

theorem hinj112_0_2 : Function.Injective
    (fun i => ((T112_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK112)) :=
  repsInj_of_reduceAux2 rK112 T112_0_2 (by decide)

theorem hcardT112_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK112)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK112 ⟨0, by decide⟩ R112_2 hpxR112_2 hcardq112_2 (by decide)).symm

/-- **Cell (112, 0) twin (q=2).** -/
theorem cell112_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK112) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK112) (charOfVec2 rK112 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK112 e (h : Coordinate 2) T112_0_2 i :=
  species_entry_eq_sum rK112 ⟨0, by decide⟩ e heK h T112_0_2 hfix112_0_2 hinj112_0_2 hcardT112_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK112) (T112_0_2 i) (hfix112_0_2 i) h)

/-! ### Cell (112, 10) twin -/

def T112_10_2 : Fin 25 → Coordinate 2 := fun i => T112_10list.getD i.val (0,0,0,0,0)

theorem hfix112_10_2 : ∀ i, ((T112_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK112)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK112) :=
  repsFix_of_siftB2 rK112 ⟨10, by decide⟩ T112_10_2 (by decide)

theorem hinj112_10_2 : Function.Injective
    (fun i => ((T112_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK112)) :=
  repsInj_of_reduceAux2 rK112 T112_10_2 (by decide)

theorem hcardT112_10_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK112)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK112 ⟨10, by decide⟩ R112_2 hpxR112_2 hcardq112_2 (by decide)).symm

/-- **Cell (112, 10) twin (q=2).** -/
theorem cell112_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK112) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK112) (charOfVec2 rK112 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK112 e (h : Coordinate 2) T112_10_2 i :=
  species_entry_eq_sum rK112 ⟨10, by decide⟩ e heK h T112_10_2 hfix112_10_2 hinj112_10_2 hcardT112_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK112) (T112_10_2 i) (hfix112_10_2 i) h)

/-! ### Cell (112, 12) twin -/

def T112_12_2 : Fin 25 → Coordinate 2 := fun i => T112_12list.getD i.val (0,0,0,0,0)

theorem hfix112_12_2 : ∀ i, ((T112_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK112)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK112) :=
  repsFix_of_siftB2 rK112 ⟨12, by decide⟩ T112_12_2 (by decide)

theorem hinj112_12_2 : Function.Injective
    (fun i => ((T112_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK112)) :=
  repsInj_of_reduceAux2 rK112 T112_12_2 (by decide)

theorem hcardT112_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK112)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK112 ⟨12, by decide⟩ R112_2 hpxR112_2 hcardq112_2 (by decide)).symm

/-- **Cell (112, 12) twin (q=2).** -/
theorem cell112_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK112) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK112) (charOfVec2 rK112 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK112 e (h : Coordinate 2) T112_12_2 i :=
  species_entry_eq_sum rK112 ⟨12, by decide⟩ e heK h T112_12_2 hfix112_12_2 hinj112_12_2 hcardT112_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK112) (T112_12_2 i) (hfix112_12_2 i) h)

/-! ### Cell (112, 50) twin -/

def T112_50_2 : Fin 25 → Coordinate 2 := fun i => T112_50list.getD i.val (0,0,0,0,0)

theorem hfix112_50_2 : ∀ i, ((T112_50_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK112)
    ∈ fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK112) :=
  repsFix_of_siftB2 rK112 ⟨50, by decide⟩ T112_50_2 (by decide)

theorem hinj112_50_2 : Function.Injective
    (fun i => ((T112_50_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK112)) :=
  repsInj_of_reduceAux2 rK112 T112_50_2 (by decide)

theorem hcardT112_50_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK112)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK112 ⟨50, by decide⟩ R112_2 hpxR112_2 hcardq112_2 (by decide)).symm

/-- **Cell (112, 50) twin (q=2).** -/
theorem cell112_50_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK112) e = true)
    (h : ↥(reps (⟨50, by decide⟩ : Fin 148))) :
    species (reps (⟨50, by decide⟩ : Fin 148)) h (basisElt (reps rK112) (charOfVec2 rK112 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK112 e (h : Coordinate 2) T112_50_2 i :=
  species_entry_eq_sum rK112 ⟨50, by decide⟩ e heK h T112_50_2 hfix112_50_2 hinj112_50_2 hcardT112_50_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨50, by decide⟩) (reps rK112) (T112_50_2 i) (hfix112_50_2 i) h)

/-! ### Cell (112, 53) twin -/

def T112_53_2 : Fin 25 → Coordinate 2 := fun i => T112_53list.getD i.val (0,0,0,0,0)

theorem hfix112_53_2 : ∀ i, ((T112_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK112)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK112) :=
  repsFix_of_siftB2 rK112 ⟨53, by decide⟩ T112_53_2 (by decide)

theorem hinj112_53_2 : Function.Injective
    (fun i => ((T112_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK112)) :=
  repsInj_of_reduceAux2 rK112 T112_53_2 (by decide)

theorem hcardT112_53_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK112)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK112 ⟨53, by decide⟩ R112_2 hpxR112_2 hcardq112_2 (by decide)).symm

/-- **Cell (112, 53) twin (q=2).** -/
theorem cell112_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK112) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK112) (charOfVec2 rK112 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK112 e (h : Coordinate 2) T112_53_2 i :=
  species_entry_eq_sum rK112 ⟨53, by decide⟩ e heK h T112_53_2 hfix112_53_2 hinj112_53_2 hcardT112_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK112) (T112_53_2 i) (hfix112_53_2 i) h)

/-! ### Cell (112, 112) twin -/

def T112_112_2 : Fin 25 → Coordinate 2 := fun i => T112_112list.getD i.val (0,0,0,0,0)

theorem hfix112_112_2 : ∀ i, ((T112_112_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK112)
    ∈ fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK112) :=
  repsFix_of_siftB2 rK112 ⟨112, by decide⟩ T112_112_2 (by decide)

theorem hinj112_112_2 : Function.Injective
    (fun i => ((T112_112_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK112)) :=
  repsInj_of_reduceAux2 rK112 T112_112_2 (by decide)

theorem hcardT112_112_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK112)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK112 ⟨112, by decide⟩ R112_2 hpxR112_2 hcardq112_2 (by decide)).symm

/-- **Cell (112, 112) twin (q=2).** -/
theorem cell112_112_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK112) e = true)
    (h : ↥(reps (⟨112, by decide⟩ : Fin 148))) :
    species (reps (⟨112, by decide⟩ : Fin 148)) h (basisElt (reps rK112) (charOfVec2 rK112 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK112 e (h : Coordinate 2) T112_112_2 i :=
  species_entry_eq_sum rK112 ⟨112, by decide⟩ e heK h T112_112_2 hfix112_112_2 hinj112_112_2 hcardT112_112_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨112, by decide⟩) (reps rK112) (T112_112_2 i) (hfix112_112_2 i) h)

end Q2

/-! # K-class rK = 113  (|G/K| = 25) -/

def rK113 : Fin 148 := ⟨113, by decide⟩

def R113list : List Coordinates := [(0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0)]
def R113 : Fin 25 → Coordinate 1 := fun i => R113list.getD i.val (0,0,0,0,0)

theorem hpxR113 : Function.Injective (fun i => reduceAux 1 (basisAt rK113) (R113 i)) := by decide
theorem hcardq113 : Nat.card (Coordinate 1 ⧸ reps rK113) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (113, 0): |T| = 25 -/

def T113_0list : List Coordinates := [(0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0)]
def T113_0 : Fin 25 → Coordinate 1 := fun i => T113_0list.getD i.val (0,0,0,0,0)

theorem hfix113_0 : ∀ i, ((T113_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK113)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113) :=
  repsFix_of_siftB rK113 ⟨0, by decide⟩ T113_0 (by decide)

theorem hinj113_0 : Function.Injective
    (fun i => ((T113_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK113)) :=
  repsInj_of_reduceAux rK113 T113_0 (by decide)

theorem hcardT113_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK113 ⟨0, by decide⟩ R113 hpxR113 hcardq113 (by decide)).symm

/-- **Cell (113, 0).** -/
theorem cell113_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK113) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK113) (charOfVec rK113 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK113 e (h : Coordinate 1) T113_0 i :=
  species_entry_eq_sum rK113 ⟨0, by decide⟩ e heK h T113_0 hfix113_0 hinj113_0 hcardT113_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK113) (T113_0 i) (hfix113_0 i) h)

/-! ## Cell (113, 10): |T| = 25 -/

def T113_10list : List Coordinates := [(0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0)]
def T113_10 : Fin 25 → Coordinate 1 := fun i => T113_10list.getD i.val (0,0,0,0,0)

theorem hfix113_10 : ∀ i, ((T113_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK113)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113) :=
  repsFix_of_siftB rK113 ⟨10, by decide⟩ T113_10 (by decide)

theorem hinj113_10 : Function.Injective
    (fun i => ((T113_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK113)) :=
  repsInj_of_reduceAux rK113 T113_10 (by decide)

theorem hcardT113_10 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK113 ⟨10, by decide⟩ R113 hpxR113 hcardq113 (by decide)).symm

/-- **Cell (113, 10).** -/
theorem cell113_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK113) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK113) (charOfVec rK113 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK113 e (h : Coordinate 1) T113_10 i :=
  species_entry_eq_sum rK113 ⟨10, by decide⟩ e heK h T113_10 hfix113_10 hinj113_10 hcardT113_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK113) (T113_10 i) (hfix113_10 i) h)

/-! ## Cell (113, 12): |T| = 25 -/

def T113_12list : List Coordinates := [(0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0)]
def T113_12 : Fin 25 → Coordinate 1 := fun i => T113_12list.getD i.val (0,0,0,0,0)

theorem hfix113_12 : ∀ i, ((T113_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK113)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113) :=
  repsFix_of_siftB rK113 ⟨12, by decide⟩ T113_12 (by decide)

theorem hinj113_12 : Function.Injective
    (fun i => ((T113_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK113)) :=
  repsInj_of_reduceAux rK113 T113_12 (by decide)

theorem hcardT113_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK113 ⟨12, by decide⟩ R113 hpxR113 hcardq113 (by decide)).symm

/-- **Cell (113, 12).** -/
theorem cell113_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK113) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK113) (charOfVec rK113 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK113 e (h : Coordinate 1) T113_12 i :=
  species_entry_eq_sum rK113 ⟨12, by decide⟩ e heK h T113_12 hfix113_12 hinj113_12 hcardT113_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK113) (T113_12 i) (hfix113_12 i) h)

/-! ## Cell (113, 51): |T| = 25 -/

def T113_51list : List Coordinates := [(0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0)]
def T113_51 : Fin 25 → Coordinate 1 := fun i => T113_51list.getD i.val (0,0,0,0,0)

theorem hfix113_51 : ∀ i, ((T113_51 i : Coordinate 1) : Coordinate 1 ⧸ reps rK113)
    ∈ fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113) :=
  repsFix_of_siftB rK113 ⟨51, by decide⟩ T113_51 (by decide)

theorem hinj113_51 : Function.Injective
    (fun i => ((T113_51 i : Coordinate 1) : Coordinate 1 ⧸ reps rK113)) :=
  repsInj_of_reduceAux rK113 T113_51 (by decide)

theorem hcardT113_51 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK113 ⟨51, by decide⟩ R113 hpxR113 hcardq113 (by decide)).symm

/-- **Cell (113, 51).** -/
theorem cell113_51 (e : List (ZMod 25)) (heK : charOK (basisAt rK113) e = true)
    (h : ↥(reps (⟨51, by decide⟩ : Fin 148))) :
    species (reps (⟨51, by decide⟩ : Fin 148)) h (basisElt (reps rK113) (charOfVec rK113 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK113 e (h : Coordinate 1) T113_51 i :=
  species_entry_eq_sum rK113 ⟨51, by decide⟩ e heK h T113_51 hfix113_51 hinj113_51 hcardT113_51
    (fun i => conj_mem_of_fixedPoints (reps ⟨51, by decide⟩) (reps rK113) (T113_51 i) (hfix113_51 i) h)

/-! ## Cell (113, 53): |T| = 25 -/

def T113_53list : List Coordinates := [(0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0)]
def T113_53 : Fin 25 → Coordinate 1 := fun i => T113_53list.getD i.val (0,0,0,0,0)

theorem hfix113_53 : ∀ i, ((T113_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK113)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113) :=
  repsFix_of_siftB rK113 ⟨53, by decide⟩ T113_53 (by decide)

theorem hinj113_53 : Function.Injective
    (fun i => ((T113_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK113)) :=
  repsInj_of_reduceAux rK113 T113_53 (by decide)

theorem hcardT113_53 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK113 ⟨53, by decide⟩ R113 hpxR113 hcardq113 (by decide)).symm

/-- **Cell (113, 53).** -/
theorem cell113_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK113) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK113) (charOfVec rK113 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK113 e (h : Coordinate 1) T113_53 i :=
  species_entry_eq_sum rK113 ⟨53, by decide⟩ e heK h T113_53 hfix113_53 hinj113_53 hcardT113_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK113) (T113_53 i) (hfix113_53 i) h)

/-! ## Cell (113, 113): |T| = 25 -/

def T113_113list : List Coordinates := [(0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0)]
def T113_113 : Fin 25 → Coordinate 1 := fun i => T113_113list.getD i.val (0,0,0,0,0)

theorem hfix113_113 : ∀ i, ((T113_113 i : Coordinate 1) : Coordinate 1 ⧸ reps rK113)
    ∈ fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113) :=
  repsFix_of_siftB rK113 ⟨113, by decide⟩ T113_113 (by decide)

theorem hinj113_113 : Function.Injective
    (fun i => ((T113_113 i : Coordinate 1) : Coordinate 1 ⧸ reps rK113)) :=
  repsInj_of_reduceAux rK113 T113_113 (by decide)

theorem hcardT113_113 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK113 ⟨113, by decide⟩ R113 hpxR113 hcardq113 (by decide)).symm

/-- **Cell (113, 113).** -/
theorem cell113_113 (e : List (ZMod 25)) (heK : charOK (basisAt rK113) e = true)
    (h : ↥(reps (⟨113, by decide⟩ : Fin 148))) :
    species (reps (⟨113, by decide⟩ : Fin 148)) h (basisElt (reps rK113) (charOfVec rK113 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK113 e (h : Coordinate 1) T113_113 i :=
  species_entry_eq_sum rK113 ⟨113, by decide⟩ e heK h T113_113 hfix113_113 hinj113_113 hcardT113_113
    (fun i => conj_mem_of_fixedPoints (reps ⟨113, by decide⟩) (reps rK113) (T113_113 i) (hfix113_113 i) h)

namespace Q2

def R113_2 : Fin 25 → Coordinate 2 := fun i => R113list.getD i.val (0,0,0,0,0)
theorem hpxR113_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK113) (R113_2 i)) := by decide
theorem hcardq113_2 : Nat.card (Coordinate 2 ⧸ reps rK113) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (113, 0) twin -/

def T113_0_2 : Fin 25 → Coordinate 2 := fun i => T113_0list.getD i.val (0,0,0,0,0)

theorem hfix113_0_2 : ∀ i, ((T113_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK113)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK113) :=
  repsFix_of_siftB2 rK113 ⟨0, by decide⟩ T113_0_2 (by decide)

theorem hinj113_0_2 : Function.Injective
    (fun i => ((T113_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK113)) :=
  repsInj_of_reduceAux2 rK113 T113_0_2 (by decide)

theorem hcardT113_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK113)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK113 ⟨0, by decide⟩ R113_2 hpxR113_2 hcardq113_2 (by decide)).symm

/-- **Cell (113, 0) twin (q=2).** -/
theorem cell113_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK113) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK113) (charOfVec2 rK113 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK113 e (h : Coordinate 2) T113_0_2 i :=
  species_entry_eq_sum rK113 ⟨0, by decide⟩ e heK h T113_0_2 hfix113_0_2 hinj113_0_2 hcardT113_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK113) (T113_0_2 i) (hfix113_0_2 i) h)

/-! ### Cell (113, 10) twin -/

def T113_10_2 : Fin 25 → Coordinate 2 := fun i => T113_10list.getD i.val (0,0,0,0,0)

theorem hfix113_10_2 : ∀ i, ((T113_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK113)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK113) :=
  repsFix_of_siftB2 rK113 ⟨10, by decide⟩ T113_10_2 (by decide)

theorem hinj113_10_2 : Function.Injective
    (fun i => ((T113_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK113)) :=
  repsInj_of_reduceAux2 rK113 T113_10_2 (by decide)

theorem hcardT113_10_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK113)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK113 ⟨10, by decide⟩ R113_2 hpxR113_2 hcardq113_2 (by decide)).symm

/-- **Cell (113, 10) twin (q=2).** -/
theorem cell113_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK113) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK113) (charOfVec2 rK113 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK113 e (h : Coordinate 2) T113_10_2 i :=
  species_entry_eq_sum rK113 ⟨10, by decide⟩ e heK h T113_10_2 hfix113_10_2 hinj113_10_2 hcardT113_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK113) (T113_10_2 i) (hfix113_10_2 i) h)

/-! ### Cell (113, 12) twin -/

def T113_12_2 : Fin 25 → Coordinate 2 := fun i => T113_12list.getD i.val (0,0,0,0,0)

theorem hfix113_12_2 : ∀ i, ((T113_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK113)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK113) :=
  repsFix_of_siftB2 rK113 ⟨12, by decide⟩ T113_12_2 (by decide)

theorem hinj113_12_2 : Function.Injective
    (fun i => ((T113_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK113)) :=
  repsInj_of_reduceAux2 rK113 T113_12_2 (by decide)

theorem hcardT113_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK113)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK113 ⟨12, by decide⟩ R113_2 hpxR113_2 hcardq113_2 (by decide)).symm

/-- **Cell (113, 12) twin (q=2).** -/
theorem cell113_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK113) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK113) (charOfVec2 rK113 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK113 e (h : Coordinate 2) T113_12_2 i :=
  species_entry_eq_sum rK113 ⟨12, by decide⟩ e heK h T113_12_2 hfix113_12_2 hinj113_12_2 hcardT113_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK113) (T113_12_2 i) (hfix113_12_2 i) h)

/-! ### Cell (113, 51) twin -/

def T113_51_2 : Fin 25 → Coordinate 2 := fun i => T113_51list.getD i.val (0,0,0,0,0)

theorem hfix113_51_2 : ∀ i, ((T113_51_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK113)
    ∈ fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK113) :=
  repsFix_of_siftB2 rK113 ⟨51, by decide⟩ T113_51_2 (by decide)

theorem hinj113_51_2 : Function.Injective
    (fun i => ((T113_51_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK113)) :=
  repsInj_of_reduceAux2 rK113 T113_51_2 (by decide)

theorem hcardT113_51_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK113)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK113 ⟨51, by decide⟩ R113_2 hpxR113_2 hcardq113_2 (by decide)).symm

/-- **Cell (113, 51) twin (q=2).** -/
theorem cell113_51_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK113) e = true)
    (h : ↥(reps (⟨51, by decide⟩ : Fin 148))) :
    species (reps (⟨51, by decide⟩ : Fin 148)) h (basisElt (reps rK113) (charOfVec2 rK113 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK113 e (h : Coordinate 2) T113_51_2 i :=
  species_entry_eq_sum rK113 ⟨51, by decide⟩ e heK h T113_51_2 hfix113_51_2 hinj113_51_2 hcardT113_51_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨51, by decide⟩) (reps rK113) (T113_51_2 i) (hfix113_51_2 i) h)

/-! ### Cell (113, 53) twin -/

def T113_53_2 : Fin 25 → Coordinate 2 := fun i => T113_53list.getD i.val (0,0,0,0,0)

theorem hfix113_53_2 : ∀ i, ((T113_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK113)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK113) :=
  repsFix_of_siftB2 rK113 ⟨53, by decide⟩ T113_53_2 (by decide)

theorem hinj113_53_2 : Function.Injective
    (fun i => ((T113_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK113)) :=
  repsInj_of_reduceAux2 rK113 T113_53_2 (by decide)

theorem hcardT113_53_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK113)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK113 ⟨53, by decide⟩ R113_2 hpxR113_2 hcardq113_2 (by decide)).symm

/-- **Cell (113, 53) twin (q=2).** -/
theorem cell113_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK113) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK113) (charOfVec2 rK113 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK113 e (h : Coordinate 2) T113_53_2 i :=
  species_entry_eq_sum rK113 ⟨53, by decide⟩ e heK h T113_53_2 hfix113_53_2 hinj113_53_2 hcardT113_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK113) (T113_53_2 i) (hfix113_53_2 i) h)

/-! ### Cell (113, 113) twin -/

def T113_113_2 : Fin 25 → Coordinate 2 := fun i => T113_113list.getD i.val (0,0,0,0,0)

theorem hfix113_113_2 : ∀ i, ((T113_113_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK113)
    ∈ fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK113) :=
  repsFix_of_siftB2 rK113 ⟨113, by decide⟩ T113_113_2 (by decide)

theorem hinj113_113_2 : Function.Injective
    (fun i => ((T113_113_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK113)) :=
  repsInj_of_reduceAux2 rK113 T113_113_2 (by decide)

theorem hcardT113_113_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK113)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK113 ⟨113, by decide⟩ R113_2 hpxR113_2 hcardq113_2 (by decide)).symm

/-- **Cell (113, 113) twin (q=2).** -/
theorem cell113_113_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK113) e = true)
    (h : ↥(reps (⟨113, by decide⟩ : Fin 148))) :
    species (reps (⟨113, by decide⟩ : Fin 148)) h (basisElt (reps rK113) (charOfVec2 rK113 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK113 e (h : Coordinate 2) T113_113_2 i :=
  species_entry_eq_sum rK113 ⟨113, by decide⟩ e heK h T113_113_2 hfix113_113_2 hinj113_113_2 hcardT113_113_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨113, by decide⟩) (reps rK113) (T113_113_2 i) (hfix113_113_2 i) h)

end Q2

/-! # K-class rK = 114  (|G/K| = 25) -/

def rK114 : Fin 148 := ⟨114, by decide⟩

def R114list : List Coordinates := [(0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def R114 : Fin 25 → Coordinate 1 := fun i => R114list.getD i.val (0,0,0,0,0)

theorem hpxR114 : Function.Injective (fun i => reduceAux 1 (basisAt rK114) (R114 i)) := by decide
theorem hcardq114 : Nat.card (Coordinate 1 ⧸ reps rK114) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (114, 0): |T| = 25 -/

def T114_0list : List Coordinates := [(0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T114_0 : Fin 25 → Coordinate 1 := fun i => T114_0list.getD i.val (0,0,0,0,0)

theorem hfix114_0 : ∀ i, ((T114_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK114)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114) :=
  repsFix_of_siftB rK114 ⟨0, by decide⟩ T114_0 (by decide)

theorem hinj114_0 : Function.Injective
    (fun i => ((T114_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK114)) :=
  repsInj_of_reduceAux rK114 T114_0 (by decide)

theorem hcardT114_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK114 ⟨0, by decide⟩ R114 hpxR114 hcardq114 (by decide)).symm

/-- **Cell (114, 0).** -/
theorem cell114_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK114) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK114) (charOfVec rK114 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK114 e (h : Coordinate 1) T114_0 i :=
  species_entry_eq_sum rK114 ⟨0, by decide⟩ e heK h T114_0 hfix114_0 hinj114_0 hcardT114_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK114) (T114_0 i) (hfix114_0 i) h)

/-! ## Cell (114, 10): |T| = 25 -/

def T114_10list : List Coordinates := [(0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T114_10 : Fin 25 → Coordinate 1 := fun i => T114_10list.getD i.val (0,0,0,0,0)

theorem hfix114_10 : ∀ i, ((T114_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK114)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114) :=
  repsFix_of_siftB rK114 ⟨10, by decide⟩ T114_10 (by decide)

theorem hinj114_10 : Function.Injective
    (fun i => ((T114_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK114)) :=
  repsInj_of_reduceAux rK114 T114_10 (by decide)

theorem hcardT114_10 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK114 ⟨10, by decide⟩ R114 hpxR114 hcardq114 (by decide)).symm

/-- **Cell (114, 10).** -/
theorem cell114_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK114) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK114) (charOfVec rK114 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK114 e (h : Coordinate 1) T114_10 i :=
  species_entry_eq_sum rK114 ⟨10, by decide⟩ e heK h T114_10 hfix114_10 hinj114_10 hcardT114_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK114) (T114_10 i) (hfix114_10 i) h)

/-! ## Cell (114, 12): |T| = 25 -/

def T114_12list : List Coordinates := [(0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T114_12 : Fin 25 → Coordinate 1 := fun i => T114_12list.getD i.val (0,0,0,0,0)

theorem hfix114_12 : ∀ i, ((T114_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK114)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114) :=
  repsFix_of_siftB rK114 ⟨12, by decide⟩ T114_12 (by decide)

theorem hinj114_12 : Function.Injective
    (fun i => ((T114_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK114)) :=
  repsInj_of_reduceAux rK114 T114_12 (by decide)

theorem hcardT114_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK114 ⟨12, by decide⟩ R114 hpxR114 hcardq114 (by decide)).symm

/-- **Cell (114, 12).** -/
theorem cell114_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK114) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK114) (charOfVec rK114 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK114 e (h : Coordinate 1) T114_12 i :=
  species_entry_eq_sum rK114 ⟨12, by decide⟩ e heK h T114_12 hfix114_12 hinj114_12 hcardT114_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK114) (T114_12 i) (hfix114_12 i) h)

/-! ## Cell (114, 52): |T| = 25 -/

def T114_52list : List Coordinates := [(0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T114_52 : Fin 25 → Coordinate 1 := fun i => T114_52list.getD i.val (0,0,0,0,0)

theorem hfix114_52 : ∀ i, ((T114_52 i : Coordinate 1) : Coordinate 1 ⧸ reps rK114)
    ∈ fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114) :=
  repsFix_of_siftB rK114 ⟨52, by decide⟩ T114_52 (by decide)

theorem hinj114_52 : Function.Injective
    (fun i => ((T114_52 i : Coordinate 1) : Coordinate 1 ⧸ reps rK114)) :=
  repsInj_of_reduceAux rK114 T114_52 (by decide)

theorem hcardT114_52 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK114 ⟨52, by decide⟩ R114 hpxR114 hcardq114 (by decide)).symm

/-- **Cell (114, 52).** -/
theorem cell114_52 (e : List (ZMod 25)) (heK : charOK (basisAt rK114) e = true)
    (h : ↥(reps (⟨52, by decide⟩ : Fin 148))) :
    species (reps (⟨52, by decide⟩ : Fin 148)) h (basisElt (reps rK114) (charOfVec rK114 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK114 e (h : Coordinate 1) T114_52 i :=
  species_entry_eq_sum rK114 ⟨52, by decide⟩ e heK h T114_52 hfix114_52 hinj114_52 hcardT114_52
    (fun i => conj_mem_of_fixedPoints (reps ⟨52, by decide⟩) (reps rK114) (T114_52 i) (hfix114_52 i) h)

/-! ## Cell (114, 53): |T| = 25 -/

def T114_53list : List Coordinates := [(0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T114_53 : Fin 25 → Coordinate 1 := fun i => T114_53list.getD i.val (0,0,0,0,0)

theorem hfix114_53 : ∀ i, ((T114_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK114)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114) :=
  repsFix_of_siftB rK114 ⟨53, by decide⟩ T114_53 (by decide)

theorem hinj114_53 : Function.Injective
    (fun i => ((T114_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK114)) :=
  repsInj_of_reduceAux rK114 T114_53 (by decide)

theorem hcardT114_53 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK114 ⟨53, by decide⟩ R114 hpxR114 hcardq114 (by decide)).symm

/-- **Cell (114, 53).** -/
theorem cell114_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK114) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK114) (charOfVec rK114 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK114 e (h : Coordinate 1) T114_53 i :=
  species_entry_eq_sum rK114 ⟨53, by decide⟩ e heK h T114_53 hfix114_53 hinj114_53 hcardT114_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK114) (T114_53 i) (hfix114_53 i) h)

/-! ## Cell (114, 114): |T| = 25 -/

def T114_114list : List Coordinates := [(0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T114_114 : Fin 25 → Coordinate 1 := fun i => T114_114list.getD i.val (0,0,0,0,0)

theorem hfix114_114 : ∀ i, ((T114_114 i : Coordinate 1) : Coordinate 1 ⧸ reps rK114)
    ∈ fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114) :=
  repsFix_of_siftB rK114 ⟨114, by decide⟩ T114_114 (by decide)

theorem hinj114_114 : Function.Injective
    (fun i => ((T114_114 i : Coordinate 1) : Coordinate 1 ⧸ reps rK114)) :=
  repsInj_of_reduceAux rK114 T114_114 (by decide)

theorem hcardT114_114 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK114 ⟨114, by decide⟩ R114 hpxR114 hcardq114 (by decide)).symm

/-- **Cell (114, 114).** -/
theorem cell114_114 (e : List (ZMod 25)) (heK : charOK (basisAt rK114) e = true)
    (h : ↥(reps (⟨114, by decide⟩ : Fin 148))) :
    species (reps (⟨114, by decide⟩ : Fin 148)) h (basisElt (reps rK114) (charOfVec rK114 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK114 e (h : Coordinate 1) T114_114 i :=
  species_entry_eq_sum rK114 ⟨114, by decide⟩ e heK h T114_114 hfix114_114 hinj114_114 hcardT114_114
    (fun i => conj_mem_of_fixedPoints (reps ⟨114, by decide⟩) (reps rK114) (T114_114 i) (hfix114_114 i) h)

namespace Q2

def R114_2 : Fin 25 → Coordinate 2 := fun i => R114list.getD i.val (0,0,0,0,0)
theorem hpxR114_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK114) (R114_2 i)) := by decide
theorem hcardq114_2 : Nat.card (Coordinate 2 ⧸ reps rK114) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (114, 0) twin -/

def T114_0_2 : Fin 25 → Coordinate 2 := fun i => T114_0list.getD i.val (0,0,0,0,0)

theorem hfix114_0_2 : ∀ i, ((T114_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK114)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK114) :=
  repsFix_of_siftB2 rK114 ⟨0, by decide⟩ T114_0_2 (by decide)

theorem hinj114_0_2 : Function.Injective
    (fun i => ((T114_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK114)) :=
  repsInj_of_reduceAux2 rK114 T114_0_2 (by decide)

theorem hcardT114_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK114)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK114 ⟨0, by decide⟩ R114_2 hpxR114_2 hcardq114_2 (by decide)).symm

/-- **Cell (114, 0) twin (q=2).** -/
theorem cell114_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK114) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK114) (charOfVec2 rK114 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK114 e (h : Coordinate 2) T114_0_2 i :=
  species_entry_eq_sum rK114 ⟨0, by decide⟩ e heK h T114_0_2 hfix114_0_2 hinj114_0_2 hcardT114_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK114) (T114_0_2 i) (hfix114_0_2 i) h)

/-! ### Cell (114, 10) twin -/

def T114_10_2 : Fin 25 → Coordinate 2 := fun i => T114_10list.getD i.val (0,0,0,0,0)

theorem hfix114_10_2 : ∀ i, ((T114_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK114)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK114) :=
  repsFix_of_siftB2 rK114 ⟨10, by decide⟩ T114_10_2 (by decide)

theorem hinj114_10_2 : Function.Injective
    (fun i => ((T114_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK114)) :=
  repsInj_of_reduceAux2 rK114 T114_10_2 (by decide)

theorem hcardT114_10_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK114)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK114 ⟨10, by decide⟩ R114_2 hpxR114_2 hcardq114_2 (by decide)).symm

/-- **Cell (114, 10) twin (q=2).** -/
theorem cell114_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK114) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK114) (charOfVec2 rK114 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK114 e (h : Coordinate 2) T114_10_2 i :=
  species_entry_eq_sum rK114 ⟨10, by decide⟩ e heK h T114_10_2 hfix114_10_2 hinj114_10_2 hcardT114_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK114) (T114_10_2 i) (hfix114_10_2 i) h)

/-! ### Cell (114, 12) twin -/

def T114_12_2 : Fin 25 → Coordinate 2 := fun i => T114_12list.getD i.val (0,0,0,0,0)

theorem hfix114_12_2 : ∀ i, ((T114_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK114)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK114) :=
  repsFix_of_siftB2 rK114 ⟨12, by decide⟩ T114_12_2 (by decide)

theorem hinj114_12_2 : Function.Injective
    (fun i => ((T114_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK114)) :=
  repsInj_of_reduceAux2 rK114 T114_12_2 (by decide)

theorem hcardT114_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK114)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK114 ⟨12, by decide⟩ R114_2 hpxR114_2 hcardq114_2 (by decide)).symm

/-- **Cell (114, 12) twin (q=2).** -/
theorem cell114_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK114) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK114) (charOfVec2 rK114 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK114 e (h : Coordinate 2) T114_12_2 i :=
  species_entry_eq_sum rK114 ⟨12, by decide⟩ e heK h T114_12_2 hfix114_12_2 hinj114_12_2 hcardT114_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK114) (T114_12_2 i) (hfix114_12_2 i) h)

/-! ### Cell (114, 52) twin -/

def T114_52_2 : Fin 25 → Coordinate 2 := fun i => T114_52list.getD i.val (0,0,0,0,0)

theorem hfix114_52_2 : ∀ i, ((T114_52_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK114)
    ∈ fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK114) :=
  repsFix_of_siftB2 rK114 ⟨52, by decide⟩ T114_52_2 (by decide)

theorem hinj114_52_2 : Function.Injective
    (fun i => ((T114_52_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK114)) :=
  repsInj_of_reduceAux2 rK114 T114_52_2 (by decide)

theorem hcardT114_52_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK114)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK114 ⟨52, by decide⟩ R114_2 hpxR114_2 hcardq114_2 (by decide)).symm

/-- **Cell (114, 52) twin (q=2).** -/
theorem cell114_52_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK114) e = true)
    (h : ↥(reps (⟨52, by decide⟩ : Fin 148))) :
    species (reps (⟨52, by decide⟩ : Fin 148)) h (basisElt (reps rK114) (charOfVec2 rK114 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK114 e (h : Coordinate 2) T114_52_2 i :=
  species_entry_eq_sum rK114 ⟨52, by decide⟩ e heK h T114_52_2 hfix114_52_2 hinj114_52_2 hcardT114_52_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨52, by decide⟩) (reps rK114) (T114_52_2 i) (hfix114_52_2 i) h)

/-! ### Cell (114, 53) twin -/

def T114_53_2 : Fin 25 → Coordinate 2 := fun i => T114_53list.getD i.val (0,0,0,0,0)

theorem hfix114_53_2 : ∀ i, ((T114_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK114)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK114) :=
  repsFix_of_siftB2 rK114 ⟨53, by decide⟩ T114_53_2 (by decide)

theorem hinj114_53_2 : Function.Injective
    (fun i => ((T114_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK114)) :=
  repsInj_of_reduceAux2 rK114 T114_53_2 (by decide)

theorem hcardT114_53_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK114)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK114 ⟨53, by decide⟩ R114_2 hpxR114_2 hcardq114_2 (by decide)).symm

/-- **Cell (114, 53) twin (q=2).** -/
theorem cell114_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK114) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK114) (charOfVec2 rK114 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK114 e (h : Coordinate 2) T114_53_2 i :=
  species_entry_eq_sum rK114 ⟨53, by decide⟩ e heK h T114_53_2 hfix114_53_2 hinj114_53_2 hcardT114_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK114) (T114_53_2 i) (hfix114_53_2 i) h)

/-! ### Cell (114, 114) twin -/

def T114_114_2 : Fin 25 → Coordinate 2 := fun i => T114_114list.getD i.val (0,0,0,0,0)

theorem hfix114_114_2 : ∀ i, ((T114_114_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK114)
    ∈ fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK114) :=
  repsFix_of_siftB2 rK114 ⟨114, by decide⟩ T114_114_2 (by decide)

theorem hinj114_114_2 : Function.Injective
    (fun i => ((T114_114_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK114)) :=
  repsInj_of_reduceAux2 rK114 T114_114_2 (by decide)

theorem hcardT114_114_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK114)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK114 ⟨114, by decide⟩ R114_2 hpxR114_2 hcardq114_2 (by decide)).symm

/-- **Cell (114, 114) twin (q=2).** -/
theorem cell114_114_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK114) e = true)
    (h : ↥(reps (⟨114, by decide⟩ : Fin 148))) :
    species (reps (⟨114, by decide⟩ : Fin 148)) h (basisElt (reps rK114) (charOfVec2 rK114 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK114 e (h : Coordinate 2) T114_114_2 i :=
  species_entry_eq_sum rK114 ⟨114, by decide⟩ e heK h T114_114_2 hfix114_114_2 hinj114_114_2 hcardT114_114_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨114, by decide⟩) (reps rK114) (T114_114_2 i) (hfix114_114_2 i) h)

end Q2

/-! # K-class rK = 115  (|G/K| = 25) -/

def rK115 : Fin 148 := ⟨115, by decide⟩

def R115list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0)]
def R115 : Fin 25 → Coordinate 1 := fun i => R115list.getD i.val (0,0,0,0,0)

theorem hpxR115 : Function.Injective (fun i => reduceAux 1 (basisAt rK115) (R115 i)) := by decide
theorem hcardq115 : Nat.card (Coordinate 1 ⧸ reps rK115) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (115, 0): |T| = 25 -/

def T115_0list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0)]
def T115_0 : Fin 25 → Coordinate 1 := fun i => T115_0list.getD i.val (0,0,0,0,0)

theorem hfix115_0 : ∀ i, ((T115_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK115)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115) :=
  repsFix_of_siftB rK115 ⟨0, by decide⟩ T115_0 (by decide)

theorem hinj115_0 : Function.Injective
    (fun i => ((T115_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK115)) :=
  repsInj_of_reduceAux rK115 T115_0 (by decide)

theorem hcardT115_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK115 ⟨0, by decide⟩ R115 hpxR115 hcardq115 (by decide)).symm

/-- **Cell (115, 0).** -/
theorem cell115_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK115) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK115) (charOfVec rK115 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK115 e (h : Coordinate 1) T115_0 i :=
  species_entry_eq_sum rK115 ⟨0, by decide⟩ e heK h T115_0 hfix115_0 hinj115_0 hcardT115_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK115) (T115_0 i) (hfix115_0 i) h)

/-! ## Cell (115, 10): |T| = 25 -/

def T115_10list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0)]
def T115_10 : Fin 25 → Coordinate 1 := fun i => T115_10list.getD i.val (0,0,0,0,0)

theorem hfix115_10 : ∀ i, ((T115_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK115)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115) :=
  repsFix_of_siftB rK115 ⟨10, by decide⟩ T115_10 (by decide)

theorem hinj115_10 : Function.Injective
    (fun i => ((T115_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK115)) :=
  repsInj_of_reduceAux rK115 T115_10 (by decide)

theorem hcardT115_10 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK115 ⟨10, by decide⟩ R115 hpxR115 hcardq115 (by decide)).symm

/-- **Cell (115, 10).** -/
theorem cell115_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK115) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK115) (charOfVec rK115 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK115 e (h : Coordinate 1) T115_10 i :=
  species_entry_eq_sum rK115 ⟨10, by decide⟩ e heK h T115_10 hfix115_10 hinj115_10 hcardT115_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK115) (T115_10 i) (hfix115_10 i) h)

/-! ## Cell (115, 11): |T| = 25 -/

def T115_11list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0)]
def T115_11 : Fin 25 → Coordinate 1 := fun i => T115_11list.getD i.val (0,0,0,0,0)

theorem hfix115_11 : ∀ i, ((T115_11 i : Coordinate 1) : Coordinate 1 ⧸ reps rK115)
    ∈ fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115) :=
  repsFix_of_siftB rK115 ⟨11, by decide⟩ T115_11 (by decide)

theorem hinj115_11 : Function.Injective
    (fun i => ((T115_11 i : Coordinate 1) : Coordinate 1 ⧸ reps rK115)) :=
  repsInj_of_reduceAux rK115 T115_11 (by decide)

theorem hcardT115_11 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK115 ⟨11, by decide⟩ R115 hpxR115 hcardq115 (by decide)).symm

/-- **Cell (115, 11).** -/
theorem cell115_11 (e : List (ZMod 25)) (heK : charOK (basisAt rK115) e = true)
    (h : ↥(reps (⟨11, by decide⟩ : Fin 148))) :
    species (reps (⟨11, by decide⟩ : Fin 148)) h (basisElt (reps rK115) (charOfVec rK115 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK115 e (h : Coordinate 1) T115_11 i :=
  species_entry_eq_sum rK115 ⟨11, by decide⟩ e heK h T115_11 hfix115_11 hinj115_11 hcardT115_11
    (fun i => conj_mem_of_fixedPoints (reps ⟨11, by decide⟩) (reps rK115) (T115_11 i) (hfix115_11 i) h)

/-! ## Cell (115, 12): |T| = 25 -/

def T115_12list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0)]
def T115_12 : Fin 25 → Coordinate 1 := fun i => T115_12list.getD i.val (0,0,0,0,0)

theorem hfix115_12 : ∀ i, ((T115_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK115)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115) :=
  repsFix_of_siftB rK115 ⟨12, by decide⟩ T115_12 (by decide)

theorem hinj115_12 : Function.Injective
    (fun i => ((T115_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK115)) :=
  repsInj_of_reduceAux rK115 T115_12 (by decide)

theorem hcardT115_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK115 ⟨12, by decide⟩ R115 hpxR115 hcardq115 (by decide)).symm

/-- **Cell (115, 12).** -/
theorem cell115_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK115) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK115) (charOfVec rK115 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK115 e (h : Coordinate 1) T115_12 i :=
  species_entry_eq_sum rK115 ⟨12, by decide⟩ e heK h T115_12 hfix115_12 hinj115_12 hcardT115_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK115) (T115_12 i) (hfix115_12 i) h)

/-! ## Cell (115, 53): |T| = 25 -/

def T115_53list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0)]
def T115_53 : Fin 25 → Coordinate 1 := fun i => T115_53list.getD i.val (0,0,0,0,0)

theorem hfix115_53 : ∀ i, ((T115_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK115)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115) :=
  repsFix_of_siftB rK115 ⟨53, by decide⟩ T115_53 (by decide)

theorem hinj115_53 : Function.Injective
    (fun i => ((T115_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK115)) :=
  repsInj_of_reduceAux rK115 T115_53 (by decide)

theorem hcardT115_53 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK115 ⟨53, by decide⟩ R115 hpxR115 hcardq115 (by decide)).symm

/-- **Cell (115, 53).** -/
theorem cell115_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK115) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK115) (charOfVec rK115 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK115 e (h : Coordinate 1) T115_53 i :=
  species_entry_eq_sum rK115 ⟨53, by decide⟩ e heK h T115_53 hfix115_53 hinj115_53 hcardT115_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK115) (T115_53 i) (hfix115_53 i) h)

/-! ## Cell (115, 54): |T| = 25 -/

def T115_54list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0)]
def T115_54 : Fin 25 → Coordinate 1 := fun i => T115_54list.getD i.val (0,0,0,0,0)

theorem hfix115_54 : ∀ i, ((T115_54 i : Coordinate 1) : Coordinate 1 ⧸ reps rK115)
    ∈ fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115) :=
  repsFix_of_siftB rK115 ⟨54, by decide⟩ T115_54 (by decide)

theorem hinj115_54 : Function.Injective
    (fun i => ((T115_54 i : Coordinate 1) : Coordinate 1 ⧸ reps rK115)) :=
  repsInj_of_reduceAux rK115 T115_54 (by decide)

theorem hcardT115_54 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK115 ⟨54, by decide⟩ R115 hpxR115 hcardq115 (by decide)).symm

/-- **Cell (115, 54).** -/
theorem cell115_54 (e : List (ZMod 25)) (heK : charOK (basisAt rK115) e = true)
    (h : ↥(reps (⟨54, by decide⟩ : Fin 148))) :
    species (reps (⟨54, by decide⟩ : Fin 148)) h (basisElt (reps rK115) (charOfVec rK115 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK115 e (h : Coordinate 1) T115_54 i :=
  species_entry_eq_sum rK115 ⟨54, by decide⟩ e heK h T115_54 hfix115_54 hinj115_54 hcardT115_54
    (fun i => conj_mem_of_fixedPoints (reps ⟨54, by decide⟩) (reps rK115) (T115_54 i) (hfix115_54 i) h)

/-! ## Cell (115, 115): |T| = 25 -/

def T115_115list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0)]
def T115_115 : Fin 25 → Coordinate 1 := fun i => T115_115list.getD i.val (0,0,0,0,0)

theorem hfix115_115 : ∀ i, ((T115_115 i : Coordinate 1) : Coordinate 1 ⧸ reps rK115)
    ∈ fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115) :=
  repsFix_of_siftB rK115 ⟨115, by decide⟩ T115_115 (by decide)

theorem hinj115_115 : Function.Injective
    (fun i => ((T115_115 i : Coordinate 1) : Coordinate 1 ⧸ reps rK115)) :=
  repsInj_of_reduceAux rK115 T115_115 (by decide)

theorem hcardT115_115 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK115 ⟨115, by decide⟩ R115 hpxR115 hcardq115 (by decide)).symm

/-- **Cell (115, 115).** -/
theorem cell115_115 (e : List (ZMod 25)) (heK : charOK (basisAt rK115) e = true)
    (h : ↥(reps (⟨115, by decide⟩ : Fin 148))) :
    species (reps (⟨115, by decide⟩ : Fin 148)) h (basisElt (reps rK115) (charOfVec rK115 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK115 e (h : Coordinate 1) T115_115 i :=
  species_entry_eq_sum rK115 ⟨115, by decide⟩ e heK h T115_115 hfix115_115 hinj115_115 hcardT115_115
    (fun i => conj_mem_of_fixedPoints (reps ⟨115, by decide⟩) (reps rK115) (T115_115 i) (hfix115_115 i) h)

namespace Q2

def R115_2 : Fin 25 → Coordinate 2 := fun i => R115list.getD i.val (0,0,0,0,0)
theorem hpxR115_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK115) (R115_2 i)) := by decide
theorem hcardq115_2 : Nat.card (Coordinate 2 ⧸ reps rK115) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (115, 0) twin -/

def T115_0_2 : Fin 25 → Coordinate 2 := fun i => T115_0list.getD i.val (0,0,0,0,0)

theorem hfix115_0_2 : ∀ i, ((T115_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK115)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK115) :=
  repsFix_of_siftB2 rK115 ⟨0, by decide⟩ T115_0_2 (by decide)

theorem hinj115_0_2 : Function.Injective
    (fun i => ((T115_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK115)) :=
  repsInj_of_reduceAux2 rK115 T115_0_2 (by decide)

theorem hcardT115_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK115)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK115 ⟨0, by decide⟩ R115_2 hpxR115_2 hcardq115_2 (by decide)).symm

/-- **Cell (115, 0) twin (q=2).** -/
theorem cell115_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK115) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK115) (charOfVec2 rK115 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK115 e (h : Coordinate 2) T115_0_2 i :=
  species_entry_eq_sum rK115 ⟨0, by decide⟩ e heK h T115_0_2 hfix115_0_2 hinj115_0_2 hcardT115_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK115) (T115_0_2 i) (hfix115_0_2 i) h)

/-! ### Cell (115, 10) twin -/

def T115_10_2 : Fin 25 → Coordinate 2 := fun i => T115_10list.getD i.val (0,0,0,0,0)

theorem hfix115_10_2 : ∀ i, ((T115_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK115)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK115) :=
  repsFix_of_siftB2 rK115 ⟨10, by decide⟩ T115_10_2 (by decide)

theorem hinj115_10_2 : Function.Injective
    (fun i => ((T115_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK115)) :=
  repsInj_of_reduceAux2 rK115 T115_10_2 (by decide)

theorem hcardT115_10_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK115)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK115 ⟨10, by decide⟩ R115_2 hpxR115_2 hcardq115_2 (by decide)).symm

/-- **Cell (115, 10) twin (q=2).** -/
theorem cell115_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK115) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK115) (charOfVec2 rK115 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK115 e (h : Coordinate 2) T115_10_2 i :=
  species_entry_eq_sum rK115 ⟨10, by decide⟩ e heK h T115_10_2 hfix115_10_2 hinj115_10_2 hcardT115_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK115) (T115_10_2 i) (hfix115_10_2 i) h)

/-! ### Cell (115, 11) twin -/

def T115_11_2 : Fin 25 → Coordinate 2 := fun i => T115_11list.getD i.val (0,0,0,0,0)

theorem hfix115_11_2 : ∀ i, ((T115_11_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK115)
    ∈ fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK115) :=
  repsFix_of_siftB2 rK115 ⟨11, by decide⟩ T115_11_2 (by decide)

theorem hinj115_11_2 : Function.Injective
    (fun i => ((T115_11_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK115)) :=
  repsInj_of_reduceAux2 rK115 T115_11_2 (by decide)

theorem hcardT115_11_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK115)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK115 ⟨11, by decide⟩ R115_2 hpxR115_2 hcardq115_2 (by decide)).symm

/-- **Cell (115, 11) twin (q=2).** -/
theorem cell115_11_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK115) e = true)
    (h : ↥(reps (⟨11, by decide⟩ : Fin 148))) :
    species (reps (⟨11, by decide⟩ : Fin 148)) h (basisElt (reps rK115) (charOfVec2 rK115 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK115 e (h : Coordinate 2) T115_11_2 i :=
  species_entry_eq_sum rK115 ⟨11, by decide⟩ e heK h T115_11_2 hfix115_11_2 hinj115_11_2 hcardT115_11_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨11, by decide⟩) (reps rK115) (T115_11_2 i) (hfix115_11_2 i) h)

/-! ### Cell (115, 12) twin -/

def T115_12_2 : Fin 25 → Coordinate 2 := fun i => T115_12list.getD i.val (0,0,0,0,0)

theorem hfix115_12_2 : ∀ i, ((T115_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK115)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK115) :=
  repsFix_of_siftB2 rK115 ⟨12, by decide⟩ T115_12_2 (by decide)

theorem hinj115_12_2 : Function.Injective
    (fun i => ((T115_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK115)) :=
  repsInj_of_reduceAux2 rK115 T115_12_2 (by decide)

theorem hcardT115_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK115)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK115 ⟨12, by decide⟩ R115_2 hpxR115_2 hcardq115_2 (by decide)).symm

/-- **Cell (115, 12) twin (q=2).** -/
theorem cell115_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK115) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK115) (charOfVec2 rK115 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK115 e (h : Coordinate 2) T115_12_2 i :=
  species_entry_eq_sum rK115 ⟨12, by decide⟩ e heK h T115_12_2 hfix115_12_2 hinj115_12_2 hcardT115_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK115) (T115_12_2 i) (hfix115_12_2 i) h)

/-! ### Cell (115, 53) twin -/

def T115_53_2 : Fin 25 → Coordinate 2 := fun i => T115_53list.getD i.val (0,0,0,0,0)

theorem hfix115_53_2 : ∀ i, ((T115_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK115)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK115) :=
  repsFix_of_siftB2 rK115 ⟨53, by decide⟩ T115_53_2 (by decide)

theorem hinj115_53_2 : Function.Injective
    (fun i => ((T115_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK115)) :=
  repsInj_of_reduceAux2 rK115 T115_53_2 (by decide)

theorem hcardT115_53_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK115)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK115 ⟨53, by decide⟩ R115_2 hpxR115_2 hcardq115_2 (by decide)).symm

/-- **Cell (115, 53) twin (q=2).** -/
theorem cell115_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK115) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK115) (charOfVec2 rK115 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK115 e (h : Coordinate 2) T115_53_2 i :=
  species_entry_eq_sum rK115 ⟨53, by decide⟩ e heK h T115_53_2 hfix115_53_2 hinj115_53_2 hcardT115_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK115) (T115_53_2 i) (hfix115_53_2 i) h)

/-! ### Cell (115, 54) twin -/

def T115_54_2 : Fin 25 → Coordinate 2 := fun i => T115_54list.getD i.val (0,0,0,0,0)

theorem hfix115_54_2 : ∀ i, ((T115_54_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK115)
    ∈ fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK115) :=
  repsFix_of_siftB2 rK115 ⟨54, by decide⟩ T115_54_2 (by decide)

theorem hinj115_54_2 : Function.Injective
    (fun i => ((T115_54_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK115)) :=
  repsInj_of_reduceAux2 rK115 T115_54_2 (by decide)

theorem hcardT115_54_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK115)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK115 ⟨54, by decide⟩ R115_2 hpxR115_2 hcardq115_2 (by decide)).symm

/-- **Cell (115, 54) twin (q=2).** -/
theorem cell115_54_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK115) e = true)
    (h : ↥(reps (⟨54, by decide⟩ : Fin 148))) :
    species (reps (⟨54, by decide⟩ : Fin 148)) h (basisElt (reps rK115) (charOfVec2 rK115 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK115 e (h : Coordinate 2) T115_54_2 i :=
  species_entry_eq_sum rK115 ⟨54, by decide⟩ e heK h T115_54_2 hfix115_54_2 hinj115_54_2 hcardT115_54_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨54, by decide⟩) (reps rK115) (T115_54_2 i) (hfix115_54_2 i) h)

/-! ### Cell (115, 115) twin -/

def T115_115_2 : Fin 25 → Coordinate 2 := fun i => T115_115list.getD i.val (0,0,0,0,0)

theorem hfix115_115_2 : ∀ i, ((T115_115_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK115)
    ∈ fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK115) :=
  repsFix_of_siftB2 rK115 ⟨115, by decide⟩ T115_115_2 (by decide)

theorem hinj115_115_2 : Function.Injective
    (fun i => ((T115_115_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK115)) :=
  repsInj_of_reduceAux2 rK115 T115_115_2 (by decide)

theorem hcardT115_115_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK115)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK115 ⟨115, by decide⟩ R115_2 hpxR115_2 hcardq115_2 (by decide)).symm

/-- **Cell (115, 115) twin (q=2).** -/
theorem cell115_115_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK115) e = true)
    (h : ↥(reps (⟨115, by decide⟩ : Fin 148))) :
    species (reps (⟨115, by decide⟩ : Fin 148)) h (basisElt (reps rK115) (charOfVec2 rK115 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK115 e (h : Coordinate 2) T115_115_2 i :=
  species_entry_eq_sum rK115 ⟨115, by decide⟩ e heK h T115_115_2 hfix115_115_2 hinj115_115_2 hcardT115_115_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨115, by decide⟩) (reps rK115) (T115_115_2 i) (hfix115_115_2 i) h)

end Q2

end LeanDring.P5Presentation
