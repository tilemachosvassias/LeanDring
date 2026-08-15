/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, K-strata data (5^4 stratum, rK 124-125): certified per-cell species-entry instantiations, both
twins.

Covers K-classes 124, 125 (order-5^4 K, |R|=5).  For each nonzero `H`-column
(`(G/K)^H ≠ ∅`), the full coset transversal `R124..` and each `H`-fixed
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

/-! # K-class rK = 124  (|G/K| = 5) -/

def rK124 : Fin 148 := ⟨124, by decide⟩

def R124list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def R124 : Fin 5 → Coordinate 1 := fun i => R124list.getD i.val (0,0,0,0,0)

theorem hpxR124 : Function.Injective (fun i => reduceAux 1 (basisAt rK124) (R124 i)) := by decide
theorem hcardq124 : Nat.card (Coordinate 1 ⧸ reps rK124) = 5 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (124, 0): |T| = 5 -/

def T124_0list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T124_0 : Fin 5 → Coordinate 1 := fun i => T124_0list.getD i.val (0,0,0,0,0)

theorem hfix124_0 : ∀ i, ((T124_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK124)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124) :=
  repsFix_of_siftB rK124 ⟨0, by decide⟩ T124_0 (by decide)

theorem hinj124_0 : Function.Injective
    (fun i => ((T124_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK124)) :=
  repsInj_of_reduceAux rK124 T124_0 (by decide)

theorem hcardT124_0 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK124 ⟨0, by decide⟩ R124 hpxR124 hcardq124 (by decide)).symm

/-- **Cell (124, 0).** -/
theorem cell124_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK124) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK124) (charOfVec rK124 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK124 e (h : Coordinate 1) T124_0 i :=
  species_entry_eq_sum rK124 ⟨0, by decide⟩ e heK h T124_0 hfix124_0 hinj124_0 hcardT124_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK124) (T124_0 i) (hfix124_0 i) h)

/-! ## Cell (124, 2): |T| = 5 -/

def T124_2list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T124_2 : Fin 5 → Coordinate 1 := fun i => T124_2list.getD i.val (0,0,0,0,0)

theorem hfix124_2 : ∀ i, ((T124_2 i : Coordinate 1) : Coordinate 1 ⧸ reps rK124)
    ∈ fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124) :=
  repsFix_of_siftB rK124 ⟨2, by decide⟩ T124_2 (by decide)

theorem hinj124_2 : Function.Injective
    (fun i => ((T124_2 i : Coordinate 1) : Coordinate 1 ⧸ reps rK124)) :=
  repsInj_of_reduceAux rK124 T124_2 (by decide)

theorem hcardT124_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK124 ⟨2, by decide⟩ R124 hpxR124 hcardq124 (by decide)).symm

/-- **Cell (124, 2).** -/
theorem cell124_2 (e : List (ZMod 25)) (heK : charOK (basisAt rK124) e = true)
    (h : ↥(reps (⟨2, by decide⟩ : Fin 148))) :
    species (reps (⟨2, by decide⟩ : Fin 148)) h (basisElt (reps rK124) (charOfVec rK124 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK124 e (h : Coordinate 1) T124_2 i :=
  species_entry_eq_sum rK124 ⟨2, by decide⟩ e heK h T124_2 hfix124_2 hinj124_2 hcardT124_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨2, by decide⟩) (reps rK124) (T124_2 i) (hfix124_2 i) h)

/-! ## Cell (124, 10): |T| = 5 -/

def T124_10list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T124_10 : Fin 5 → Coordinate 1 := fun i => T124_10list.getD i.val (0,0,0,0,0)

theorem hfix124_10 : ∀ i, ((T124_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK124)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124) :=
  repsFix_of_siftB rK124 ⟨10, by decide⟩ T124_10 (by decide)

theorem hinj124_10 : Function.Injective
    (fun i => ((T124_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK124)) :=
  repsInj_of_reduceAux rK124 T124_10 (by decide)

theorem hcardT124_10 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK124 ⟨10, by decide⟩ R124 hpxR124 hcardq124 (by decide)).symm

/-- **Cell (124, 10).** -/
theorem cell124_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK124) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK124) (charOfVec rK124 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK124 e (h : Coordinate 1) T124_10 i :=
  species_entry_eq_sum rK124 ⟨10, by decide⟩ e heK h T124_10 hfix124_10 hinj124_10 hcardT124_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK124) (T124_10 i) (hfix124_10 i) h)

/-! ## Cell (124, 12): |T| = 5 -/

def T124_12list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T124_12 : Fin 5 → Coordinate 1 := fun i => T124_12list.getD i.val (0,0,0,0,0)

theorem hfix124_12 : ∀ i, ((T124_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK124)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124) :=
  repsFix_of_siftB rK124 ⟨12, by decide⟩ T124_12 (by decide)

theorem hinj124_12 : Function.Injective
    (fun i => ((T124_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK124)) :=
  repsInj_of_reduceAux rK124 T124_12 (by decide)

theorem hcardT124_12 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK124 ⟨12, by decide⟩ R124 hpxR124 hcardq124 (by decide)).symm

/-- **Cell (124, 12).** -/
theorem cell124_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK124) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK124) (charOfVec rK124 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK124 e (h : Coordinate 1) T124_12 i :=
  species_entry_eq_sum rK124 ⟨12, by decide⟩ e heK h T124_12 hfix124_12 hinj124_12 hcardT124_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK124) (T124_12 i) (hfix124_12 i) h)

/-! ## Cell (124, 20): |T| = 5 -/

def T124_20list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T124_20 : Fin 5 → Coordinate 1 := fun i => T124_20list.getD i.val (0,0,0,0,0)

theorem hfix124_20 : ∀ i, ((T124_20 i : Coordinate 1) : Coordinate 1 ⧸ reps rK124)
    ∈ fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124) :=
  repsFix_of_siftB rK124 ⟨20, by decide⟩ T124_20 (by decide)

theorem hinj124_20 : Function.Injective
    (fun i => ((T124_20 i : Coordinate 1) : Coordinate 1 ⧸ reps rK124)) :=
  repsInj_of_reduceAux rK124 T124_20 (by decide)

theorem hcardT124_20 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK124 ⟨20, by decide⟩ R124 hpxR124 hcardq124 (by decide)).symm

/-- **Cell (124, 20).** -/
theorem cell124_20 (e : List (ZMod 25)) (heK : charOK (basisAt rK124) e = true)
    (h : ↥(reps (⟨20, by decide⟩ : Fin 148))) :
    species (reps (⟨20, by decide⟩ : Fin 148)) h (basisElt (reps rK124) (charOfVec rK124 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK124 e (h : Coordinate 1) T124_20 i :=
  species_entry_eq_sum rK124 ⟨20, by decide⟩ e heK h T124_20 hfix124_20 hinj124_20 hcardT124_20
    (fun i => conj_mem_of_fixedPoints (reps ⟨20, by decide⟩) (reps rK124) (T124_20 i) (hfix124_20 i) h)

/-! ## Cell (124, 30): |T| = 5 -/

def T124_30list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T124_30 : Fin 5 → Coordinate 1 := fun i => T124_30list.getD i.val (0,0,0,0,0)

theorem hfix124_30 : ∀ i, ((T124_30 i : Coordinate 1) : Coordinate 1 ⧸ reps rK124)
    ∈ fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124) :=
  repsFix_of_siftB rK124 ⟨30, by decide⟩ T124_30 (by decide)

theorem hinj124_30 : Function.Injective
    (fun i => ((T124_30 i : Coordinate 1) : Coordinate 1 ⧸ reps rK124)) :=
  repsInj_of_reduceAux rK124 T124_30 (by decide)

theorem hcardT124_30 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK124 ⟨30, by decide⟩ R124 hpxR124 hcardq124 (by decide)).symm

/-- **Cell (124, 30).** -/
theorem cell124_30 (e : List (ZMod 25)) (heK : charOK (basisAt rK124) e = true)
    (h : ↥(reps (⟨30, by decide⟩ : Fin 148))) :
    species (reps (⟨30, by decide⟩ : Fin 148)) h (basisElt (reps rK124) (charOfVec rK124 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK124 e (h : Coordinate 1) T124_30 i :=
  species_entry_eq_sum rK124 ⟨30, by decide⟩ e heK h T124_30 hfix124_30 hinj124_30 hcardT124_30
    (fun i => conj_mem_of_fixedPoints (reps ⟨30, by decide⟩) (reps rK124) (T124_30 i) (hfix124_30 i) h)

/-! ## Cell (124, 33): |T| = 5 -/

def T124_33list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T124_33 : Fin 5 → Coordinate 1 := fun i => T124_33list.getD i.val (0,0,0,0,0)

theorem hfix124_33 : ∀ i, ((T124_33 i : Coordinate 1) : Coordinate 1 ⧸ reps rK124)
    ∈ fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124) :=
  repsFix_of_siftB rK124 ⟨33, by decide⟩ T124_33 (by decide)

theorem hinj124_33 : Function.Injective
    (fun i => ((T124_33 i : Coordinate 1) : Coordinate 1 ⧸ reps rK124)) :=
  repsInj_of_reduceAux rK124 T124_33 (by decide)

theorem hcardT124_33 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK124 ⟨33, by decide⟩ R124 hpxR124 hcardq124 (by decide)).symm

/-- **Cell (124, 33).** -/
theorem cell124_33 (e : List (ZMod 25)) (heK : charOK (basisAt rK124) e = true)
    (h : ↥(reps (⟨33, by decide⟩ : Fin 148))) :
    species (reps (⟨33, by decide⟩ : Fin 148)) h (basisElt (reps rK124) (charOfVec rK124 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK124 e (h : Coordinate 1) T124_33 i :=
  species_entry_eq_sum rK124 ⟨33, by decide⟩ e heK h T124_33 hfix124_33 hinj124_33 hcardT124_33
    (fun i => conj_mem_of_fixedPoints (reps ⟨33, by decide⟩) (reps rK124) (T124_33 i) (hfix124_33 i) h)

/-! ## Cell (124, 39): |T| = 5 -/

def T124_39list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T124_39 : Fin 5 → Coordinate 1 := fun i => T124_39list.getD i.val (0,0,0,0,0)

theorem hfix124_39 : ∀ i, ((T124_39 i : Coordinate 1) : Coordinate 1 ⧸ reps rK124)
    ∈ fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124) :=
  repsFix_of_siftB rK124 ⟨39, by decide⟩ T124_39 (by decide)

theorem hinj124_39 : Function.Injective
    (fun i => ((T124_39 i : Coordinate 1) : Coordinate 1 ⧸ reps rK124)) :=
  repsInj_of_reduceAux rK124 T124_39 (by decide)

theorem hcardT124_39 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK124 ⟨39, by decide⟩ R124 hpxR124 hcardq124 (by decide)).symm

/-- **Cell (124, 39).** -/
theorem cell124_39 (e : List (ZMod 25)) (heK : charOK (basisAt rK124) e = true)
    (h : ↥(reps (⟨39, by decide⟩ : Fin 148))) :
    species (reps (⟨39, by decide⟩ : Fin 148)) h (basisElt (reps rK124) (charOfVec rK124 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK124 e (h : Coordinate 1) T124_39 i :=
  species_entry_eq_sum rK124 ⟨39, by decide⟩ e heK h T124_39 hfix124_39 hinj124_39 hcardT124_39
    (fun i => conj_mem_of_fixedPoints (reps ⟨39, by decide⟩) (reps rK124) (T124_39 i) (hfix124_39 i) h)

/-! ## Cell (124, 47): |T| = 5 -/

def T124_47list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T124_47 : Fin 5 → Coordinate 1 := fun i => T124_47list.getD i.val (0,0,0,0,0)

theorem hfix124_47 : ∀ i, ((T124_47 i : Coordinate 1) : Coordinate 1 ⧸ reps rK124)
    ∈ fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124) :=
  repsFix_of_siftB rK124 ⟨47, by decide⟩ T124_47 (by decide)

theorem hinj124_47 : Function.Injective
    (fun i => ((T124_47 i : Coordinate 1) : Coordinate 1 ⧸ reps rK124)) :=
  repsInj_of_reduceAux rK124 T124_47 (by decide)

theorem hcardT124_47 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK124 ⟨47, by decide⟩ R124 hpxR124 hcardq124 (by decide)).symm

/-- **Cell (124, 47).** -/
theorem cell124_47 (e : List (ZMod 25)) (heK : charOK (basisAt rK124) e = true)
    (h : ↥(reps (⟨47, by decide⟩ : Fin 148))) :
    species (reps (⟨47, by decide⟩ : Fin 148)) h (basisElt (reps rK124) (charOfVec rK124 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK124 e (h : Coordinate 1) T124_47 i :=
  species_entry_eq_sum rK124 ⟨47, by decide⟩ e heK h T124_47 hfix124_47 hinj124_47 hcardT124_47
    (fun i => conj_mem_of_fixedPoints (reps ⟨47, by decide⟩) (reps rK124) (T124_47 i) (hfix124_47 i) h)

/-! ## Cell (124, 51): |T| = 5 -/

def T124_51list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T124_51 : Fin 5 → Coordinate 1 := fun i => T124_51list.getD i.val (0,0,0,0,0)

theorem hfix124_51 : ∀ i, ((T124_51 i : Coordinate 1) : Coordinate 1 ⧸ reps rK124)
    ∈ fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124) :=
  repsFix_of_siftB rK124 ⟨51, by decide⟩ T124_51 (by decide)

theorem hinj124_51 : Function.Injective
    (fun i => ((T124_51 i : Coordinate 1) : Coordinate 1 ⧸ reps rK124)) :=
  repsInj_of_reduceAux rK124 T124_51 (by decide)

theorem hcardT124_51 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK124 ⟨51, by decide⟩ R124 hpxR124 hcardq124 (by decide)).symm

/-- **Cell (124, 51).** -/
theorem cell124_51 (e : List (ZMod 25)) (heK : charOK (basisAt rK124) e = true)
    (h : ↥(reps (⟨51, by decide⟩ : Fin 148))) :
    species (reps (⟨51, by decide⟩ : Fin 148)) h (basisElt (reps rK124) (charOfVec rK124 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK124 e (h : Coordinate 1) T124_51 i :=
  species_entry_eq_sum rK124 ⟨51, by decide⟩ e heK h T124_51 hfix124_51 hinj124_51 hcardT124_51
    (fun i => conj_mem_of_fixedPoints (reps ⟨51, by decide⟩) (reps rK124) (T124_51 i) (hfix124_51 i) h)

/-! ## Cell (124, 53): |T| = 5 -/

def T124_53list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T124_53 : Fin 5 → Coordinate 1 := fun i => T124_53list.getD i.val (0,0,0,0,0)

theorem hfix124_53 : ∀ i, ((T124_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK124)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124) :=
  repsFix_of_siftB rK124 ⟨53, by decide⟩ T124_53 (by decide)

theorem hinj124_53 : Function.Injective
    (fun i => ((T124_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK124)) :=
  repsInj_of_reduceAux rK124 T124_53 (by decide)

theorem hcardT124_53 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK124 ⟨53, by decide⟩ R124 hpxR124 hcardq124 (by decide)).symm

/-- **Cell (124, 53).** -/
theorem cell124_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK124) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK124) (charOfVec rK124 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK124 e (h : Coordinate 1) T124_53 i :=
  species_entry_eq_sum rK124 ⟨53, by decide⟩ e heK h T124_53 hfix124_53 hinj124_53 hcardT124_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK124) (T124_53 i) (hfix124_53 i) h)

/-! ## Cell (124, 81): |T| = 5 -/

def T124_81list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T124_81 : Fin 5 → Coordinate 1 := fun i => T124_81list.getD i.val (0,0,0,0,0)

theorem hfix124_81 : ∀ i, ((T124_81 i : Coordinate 1) : Coordinate 1 ⧸ reps rK124)
    ∈ fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124) :=
  repsFix_of_siftB rK124 ⟨81, by decide⟩ T124_81 (by decide)

theorem hinj124_81 : Function.Injective
    (fun i => ((T124_81 i : Coordinate 1) : Coordinate 1 ⧸ reps rK124)) :=
  repsInj_of_reduceAux rK124 T124_81 (by decide)

theorem hcardT124_81 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK124 ⟨81, by decide⟩ R124 hpxR124 hcardq124 (by decide)).symm

/-- **Cell (124, 81).** -/
theorem cell124_81 (e : List (ZMod 25)) (heK : charOK (basisAt rK124) e = true)
    (h : ↥(reps (⟨81, by decide⟩ : Fin 148))) :
    species (reps (⟨81, by decide⟩ : Fin 148)) h (basisElt (reps rK124) (charOfVec rK124 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK124 e (h : Coordinate 1) T124_81 i :=
  species_entry_eq_sum rK124 ⟨81, by decide⟩ e heK h T124_81 hfix124_81 hinj124_81 hcardT124_81
    (fun i => conj_mem_of_fixedPoints (reps ⟨81, by decide⟩) (reps rK124) (T124_81 i) (hfix124_81 i) h)

/-! ## Cell (124, 92): |T| = 5 -/

def T124_92list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T124_92 : Fin 5 → Coordinate 1 := fun i => T124_92list.getD i.val (0,0,0,0,0)

theorem hfix124_92 : ∀ i, ((T124_92 i : Coordinate 1) : Coordinate 1 ⧸ reps rK124)
    ∈ fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124) :=
  repsFix_of_siftB rK124 ⟨92, by decide⟩ T124_92 (by decide)

theorem hinj124_92 : Function.Injective
    (fun i => ((T124_92 i : Coordinate 1) : Coordinate 1 ⧸ reps rK124)) :=
  repsInj_of_reduceAux rK124 T124_92 (by decide)

theorem hcardT124_92 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK124 ⟨92, by decide⟩ R124 hpxR124 hcardq124 (by decide)).symm

/-- **Cell (124, 92).** -/
theorem cell124_92 (e : List (ZMod 25)) (heK : charOK (basisAt rK124) e = true)
    (h : ↥(reps (⟨92, by decide⟩ : Fin 148))) :
    species (reps (⟨92, by decide⟩ : Fin 148)) h (basisElt (reps rK124) (charOfVec rK124 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK124 e (h : Coordinate 1) T124_92 i :=
  species_entry_eq_sum rK124 ⟨92, by decide⟩ e heK h T124_92 hfix124_92 hinj124_92 hcardT124_92
    (fun i => conj_mem_of_fixedPoints (reps ⟨92, by decide⟩) (reps rK124) (T124_92 i) (hfix124_92 i) h)

/-! ## Cell (124, 95): |T| = 5 -/

def T124_95list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T124_95 : Fin 5 → Coordinate 1 := fun i => T124_95list.getD i.val (0,0,0,0,0)

theorem hfix124_95 : ∀ i, ((T124_95 i : Coordinate 1) : Coordinate 1 ⧸ reps rK124)
    ∈ fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124) :=
  repsFix_of_siftB rK124 ⟨95, by decide⟩ T124_95 (by decide)

theorem hinj124_95 : Function.Injective
    (fun i => ((T124_95 i : Coordinate 1) : Coordinate 1 ⧸ reps rK124)) :=
  repsInj_of_reduceAux rK124 T124_95 (by decide)

theorem hcardT124_95 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK124 ⟨95, by decide⟩ R124 hpxR124 hcardq124 (by decide)).symm

/-- **Cell (124, 95).** -/
theorem cell124_95 (e : List (ZMod 25)) (heK : charOK (basisAt rK124) e = true)
    (h : ↥(reps (⟨95, by decide⟩ : Fin 148))) :
    species (reps (⟨95, by decide⟩ : Fin 148)) h (basisElt (reps rK124) (charOfVec rK124 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK124 e (h : Coordinate 1) T124_95 i :=
  species_entry_eq_sum rK124 ⟨95, by decide⟩ e heK h T124_95 hfix124_95 hinj124_95 hcardT124_95
    (fun i => conj_mem_of_fixedPoints (reps ⟨95, by decide⟩) (reps rK124) (T124_95 i) (hfix124_95 i) h)

/-! ## Cell (124, 101): |T| = 5 -/

def T124_101list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T124_101 : Fin 5 → Coordinate 1 := fun i => T124_101list.getD i.val (0,0,0,0,0)

theorem hfix124_101 : ∀ i, ((T124_101 i : Coordinate 1) : Coordinate 1 ⧸ reps rK124)
    ∈ fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124) :=
  repsFix_of_siftB rK124 ⟨101, by decide⟩ T124_101 (by decide)

theorem hinj124_101 : Function.Injective
    (fun i => ((T124_101 i : Coordinate 1) : Coordinate 1 ⧸ reps rK124)) :=
  repsInj_of_reduceAux rK124 T124_101 (by decide)

theorem hcardT124_101 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK124 ⟨101, by decide⟩ R124 hpxR124 hcardq124 (by decide)).symm

/-- **Cell (124, 101).** -/
theorem cell124_101 (e : List (ZMod 25)) (heK : charOK (basisAt rK124) e = true)
    (h : ↥(reps (⟨101, by decide⟩ : Fin 148))) :
    species (reps (⟨101, by decide⟩ : Fin 148)) h (basisElt (reps rK124) (charOfVec rK124 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK124 e (h : Coordinate 1) T124_101 i :=
  species_entry_eq_sum rK124 ⟨101, by decide⟩ e heK h T124_101 hfix124_101 hinj124_101 hcardT124_101
    (fun i => conj_mem_of_fixedPoints (reps ⟨101, by decide⟩) (reps rK124) (T124_101 i) (hfix124_101 i) h)

/-! ## Cell (124, 109): |T| = 5 -/

def T124_109list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T124_109 : Fin 5 → Coordinate 1 := fun i => T124_109list.getD i.val (0,0,0,0,0)

theorem hfix124_109 : ∀ i, ((T124_109 i : Coordinate 1) : Coordinate 1 ⧸ reps rK124)
    ∈ fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124) :=
  repsFix_of_siftB rK124 ⟨109, by decide⟩ T124_109 (by decide)

theorem hinj124_109 : Function.Injective
    (fun i => ((T124_109 i : Coordinate 1) : Coordinate 1 ⧸ reps rK124)) :=
  repsInj_of_reduceAux rK124 T124_109 (by decide)

theorem hcardT124_109 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK124 ⟨109, by decide⟩ R124 hpxR124 hcardq124 (by decide)).symm

/-- **Cell (124, 109).** -/
theorem cell124_109 (e : List (ZMod 25)) (heK : charOK (basisAt rK124) e = true)
    (h : ↥(reps (⟨109, by decide⟩ : Fin 148))) :
    species (reps (⟨109, by decide⟩ : Fin 148)) h (basisElt (reps rK124) (charOfVec rK124 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK124 e (h : Coordinate 1) T124_109 i :=
  species_entry_eq_sum rK124 ⟨109, by decide⟩ e heK h T124_109 hfix124_109 hinj124_109 hcardT124_109
    (fun i => conj_mem_of_fixedPoints (reps ⟨109, by decide⟩) (reps rK124) (T124_109 i) (hfix124_109 i) h)

/-! ## Cell (124, 113): |T| = 5 -/

def T124_113list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T124_113 : Fin 5 → Coordinate 1 := fun i => T124_113list.getD i.val (0,0,0,0,0)

theorem hfix124_113 : ∀ i, ((T124_113 i : Coordinate 1) : Coordinate 1 ⧸ reps rK124)
    ∈ fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124) :=
  repsFix_of_siftB rK124 ⟨113, by decide⟩ T124_113 (by decide)

theorem hinj124_113 : Function.Injective
    (fun i => ((T124_113 i : Coordinate 1) : Coordinate 1 ⧸ reps rK124)) :=
  repsInj_of_reduceAux rK124 T124_113 (by decide)

theorem hcardT124_113 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK124 ⟨113, by decide⟩ R124 hpxR124 hcardq124 (by decide)).symm

/-- **Cell (124, 113).** -/
theorem cell124_113 (e : List (ZMod 25)) (heK : charOK (basisAt rK124) e = true)
    (h : ↥(reps (⟨113, by decide⟩ : Fin 148))) :
    species (reps (⟨113, by decide⟩ : Fin 148)) h (basisElt (reps rK124) (charOfVec rK124 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK124 e (h : Coordinate 1) T124_113 i :=
  species_entry_eq_sum rK124 ⟨113, by decide⟩ e heK h T124_113 hfix124_113 hinj124_113 hcardT124_113
    (fun i => conj_mem_of_fixedPoints (reps ⟨113, by decide⟩) (reps rK124) (T124_113 i) (hfix124_113 i) h)

/-! ## Cell (124, 124): |T| = 5 -/

def T124_124list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T124_124 : Fin 5 → Coordinate 1 := fun i => T124_124list.getD i.val (0,0,0,0,0)

theorem hfix124_124 : ∀ i, ((T124_124 i : Coordinate 1) : Coordinate 1 ⧸ reps rK124)
    ∈ fixedPoints (reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124) :=
  repsFix_of_siftB rK124 ⟨124, by decide⟩ T124_124 (by decide)

theorem hinj124_124 : Function.Injective
    (fun i => ((T124_124 i : Coordinate 1) : Coordinate 1 ⧸ reps rK124)) :=
  repsInj_of_reduceAux rK124 T124_124 (by decide)

theorem hcardT124_124 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK124 ⟨124, by decide⟩ R124 hpxR124 hcardq124 (by decide)).symm

/-- **Cell (124, 124).** -/
theorem cell124_124 (e : List (ZMod 25)) (heK : charOK (basisAt rK124) e = true)
    (h : ↥(reps (⟨124, by decide⟩ : Fin 148))) :
    species (reps (⟨124, by decide⟩ : Fin 148)) h (basisElt (reps rK124) (charOfVec rK124 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK124 e (h : Coordinate 1) T124_124 i :=
  species_entry_eq_sum rK124 ⟨124, by decide⟩ e heK h T124_124 hfix124_124 hinj124_124 hcardT124_124
    (fun i => conj_mem_of_fixedPoints (reps ⟨124, by decide⟩) (reps rK124) (T124_124 i) (hfix124_124 i) h)

namespace Q2

def R124_2 : Fin 5 → Coordinate 2 := fun i => R124list.getD i.val (0,0,0,0,0)
theorem hpxR124_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK124) (R124_2 i)) := by decide
theorem hcardq124_2 : Nat.card (Coordinate 2 ⧸ reps rK124) = 5 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (124, 0) twin -/

def T124_0_2 : Fin 5 → Coordinate 2 := fun i => T124_0list.getD i.val (0,0,0,0,0)

theorem hfix124_0_2 : ∀ i, ((T124_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK124)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK124) :=
  repsFix_of_siftB2 rK124 ⟨0, by decide⟩ T124_0_2 (by decide)

theorem hinj124_0_2 : Function.Injective
    (fun i => ((T124_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK124)) :=
  repsInj_of_reduceAux2 rK124 T124_0_2 (by decide)

theorem hcardT124_0_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK124)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK124 ⟨0, by decide⟩ R124_2 hpxR124_2 hcardq124_2 (by decide)).symm

/-- **Cell (124, 0) twin (q=2).** -/
theorem cell124_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK124) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK124) (charOfVec2 rK124 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK124 e (h : Coordinate 2) T124_0_2 i :=
  species_entry_eq_sum rK124 ⟨0, by decide⟩ e heK h T124_0_2 hfix124_0_2 hinj124_0_2 hcardT124_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK124) (T124_0_2 i) (hfix124_0_2 i) h)

/-! ### Cell (124, 2) twin -/

def T124_2_2 : Fin 5 → Coordinate 2 := fun i => T124_2list.getD i.val (0,0,0,0,0)

theorem hfix124_2_2 : ∀ i, ((T124_2_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK124)
    ∈ fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK124) :=
  repsFix_of_siftB2 rK124 ⟨2, by decide⟩ T124_2_2 (by decide)

theorem hinj124_2_2 : Function.Injective
    (fun i => ((T124_2_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK124)) :=
  repsInj_of_reduceAux2 rK124 T124_2_2 (by decide)

theorem hcardT124_2_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK124)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK124 ⟨2, by decide⟩ R124_2 hpxR124_2 hcardq124_2 (by decide)).symm

/-- **Cell (124, 2) twin (q=2).** -/
theorem cell124_2_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK124) e = true)
    (h : ↥(reps (⟨2, by decide⟩ : Fin 148))) :
    species (reps (⟨2, by decide⟩ : Fin 148)) h (basisElt (reps rK124) (charOfVec2 rK124 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK124 e (h : Coordinate 2) T124_2_2 i :=
  species_entry_eq_sum rK124 ⟨2, by decide⟩ e heK h T124_2_2 hfix124_2_2 hinj124_2_2 hcardT124_2_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨2, by decide⟩) (reps rK124) (T124_2_2 i) (hfix124_2_2 i) h)

/-! ### Cell (124, 10) twin -/

def T124_10_2 : Fin 5 → Coordinate 2 := fun i => T124_10list.getD i.val (0,0,0,0,0)

theorem hfix124_10_2 : ∀ i, ((T124_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK124)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK124) :=
  repsFix_of_siftB2 rK124 ⟨10, by decide⟩ T124_10_2 (by decide)

theorem hinj124_10_2 : Function.Injective
    (fun i => ((T124_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK124)) :=
  repsInj_of_reduceAux2 rK124 T124_10_2 (by decide)

theorem hcardT124_10_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK124)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK124 ⟨10, by decide⟩ R124_2 hpxR124_2 hcardq124_2 (by decide)).symm

/-- **Cell (124, 10) twin (q=2).** -/
theorem cell124_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK124) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK124) (charOfVec2 rK124 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK124 e (h : Coordinate 2) T124_10_2 i :=
  species_entry_eq_sum rK124 ⟨10, by decide⟩ e heK h T124_10_2 hfix124_10_2 hinj124_10_2 hcardT124_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK124) (T124_10_2 i) (hfix124_10_2 i) h)

/-! ### Cell (124, 12) twin -/

def T124_12_2 : Fin 5 → Coordinate 2 := fun i => T124_12list.getD i.val (0,0,0,0,0)

theorem hfix124_12_2 : ∀ i, ((T124_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK124)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK124) :=
  repsFix_of_siftB2 rK124 ⟨12, by decide⟩ T124_12_2 (by decide)

theorem hinj124_12_2 : Function.Injective
    (fun i => ((T124_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK124)) :=
  repsInj_of_reduceAux2 rK124 T124_12_2 (by decide)

theorem hcardT124_12_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK124)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK124 ⟨12, by decide⟩ R124_2 hpxR124_2 hcardq124_2 (by decide)).symm

/-- **Cell (124, 12) twin (q=2).** -/
theorem cell124_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK124) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK124) (charOfVec2 rK124 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK124 e (h : Coordinate 2) T124_12_2 i :=
  species_entry_eq_sum rK124 ⟨12, by decide⟩ e heK h T124_12_2 hfix124_12_2 hinj124_12_2 hcardT124_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK124) (T124_12_2 i) (hfix124_12_2 i) h)

/-! ### Cell (124, 20) twin -/

def T124_20_2 : Fin 5 → Coordinate 2 := fun i => T124_20list.getD i.val (0,0,0,0,0)

theorem hfix124_20_2 : ∀ i, ((T124_20_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK124)
    ∈ fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK124) :=
  repsFix_of_siftB2 rK124 ⟨20, by decide⟩ T124_20_2 (by decide)

theorem hinj124_20_2 : Function.Injective
    (fun i => ((T124_20_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK124)) :=
  repsInj_of_reduceAux2 rK124 T124_20_2 (by decide)

theorem hcardT124_20_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK124)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK124 ⟨20, by decide⟩ R124_2 hpxR124_2 hcardq124_2 (by decide)).symm

/-- **Cell (124, 20) twin (q=2).** -/
theorem cell124_20_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK124) e = true)
    (h : ↥(reps (⟨20, by decide⟩ : Fin 148))) :
    species (reps (⟨20, by decide⟩ : Fin 148)) h (basisElt (reps rK124) (charOfVec2 rK124 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK124 e (h : Coordinate 2) T124_20_2 i :=
  species_entry_eq_sum rK124 ⟨20, by decide⟩ e heK h T124_20_2 hfix124_20_2 hinj124_20_2 hcardT124_20_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨20, by decide⟩) (reps rK124) (T124_20_2 i) (hfix124_20_2 i) h)

/-! ### Cell (124, 30) twin -/

def T124_30_2 : Fin 5 → Coordinate 2 := fun i => T124_30list.getD i.val (0,0,0,0,0)

theorem hfix124_30_2 : ∀ i, ((T124_30_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK124)
    ∈ fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK124) :=
  repsFix_of_siftB2 rK124 ⟨30, by decide⟩ T124_30_2 (by decide)

theorem hinj124_30_2 : Function.Injective
    (fun i => ((T124_30_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK124)) :=
  repsInj_of_reduceAux2 rK124 T124_30_2 (by decide)

theorem hcardT124_30_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK124)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK124 ⟨30, by decide⟩ R124_2 hpxR124_2 hcardq124_2 (by decide)).symm

/-- **Cell (124, 30) twin (q=2).** -/
theorem cell124_30_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK124) e = true)
    (h : ↥(reps (⟨30, by decide⟩ : Fin 148))) :
    species (reps (⟨30, by decide⟩ : Fin 148)) h (basisElt (reps rK124) (charOfVec2 rK124 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK124 e (h : Coordinate 2) T124_30_2 i :=
  species_entry_eq_sum rK124 ⟨30, by decide⟩ e heK h T124_30_2 hfix124_30_2 hinj124_30_2 hcardT124_30_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨30, by decide⟩) (reps rK124) (T124_30_2 i) (hfix124_30_2 i) h)

/-! ### Cell (124, 33) twin -/

def T124_33_2 : Fin 5 → Coordinate 2 := fun i => T124_33list.getD i.val (0,0,0,0,0)

theorem hfix124_33_2 : ∀ i, ((T124_33_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK124)
    ∈ fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK124) :=
  repsFix_of_siftB2 rK124 ⟨33, by decide⟩ T124_33_2 (by decide)

theorem hinj124_33_2 : Function.Injective
    (fun i => ((T124_33_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK124)) :=
  repsInj_of_reduceAux2 rK124 T124_33_2 (by decide)

theorem hcardT124_33_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK124)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK124 ⟨33, by decide⟩ R124_2 hpxR124_2 hcardq124_2 (by decide)).symm

/-- **Cell (124, 33) twin (q=2).** -/
theorem cell124_33_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK124) e = true)
    (h : ↥(reps (⟨33, by decide⟩ : Fin 148))) :
    species (reps (⟨33, by decide⟩ : Fin 148)) h (basisElt (reps rK124) (charOfVec2 rK124 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK124 e (h : Coordinate 2) T124_33_2 i :=
  species_entry_eq_sum rK124 ⟨33, by decide⟩ e heK h T124_33_2 hfix124_33_2 hinj124_33_2 hcardT124_33_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨33, by decide⟩) (reps rK124) (T124_33_2 i) (hfix124_33_2 i) h)

/-! ### Cell (124, 39) twin -/

def T124_39_2 : Fin 5 → Coordinate 2 := fun i => T124_39list.getD i.val (0,0,0,0,0)

theorem hfix124_39_2 : ∀ i, ((T124_39_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK124)
    ∈ fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK124) :=
  repsFix_of_siftB2 rK124 ⟨39, by decide⟩ T124_39_2 (by decide)

theorem hinj124_39_2 : Function.Injective
    (fun i => ((T124_39_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK124)) :=
  repsInj_of_reduceAux2 rK124 T124_39_2 (by decide)

theorem hcardT124_39_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK124)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK124 ⟨39, by decide⟩ R124_2 hpxR124_2 hcardq124_2 (by decide)).symm

/-- **Cell (124, 39) twin (q=2).** -/
theorem cell124_39_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK124) e = true)
    (h : ↥(reps (⟨39, by decide⟩ : Fin 148))) :
    species (reps (⟨39, by decide⟩ : Fin 148)) h (basisElt (reps rK124) (charOfVec2 rK124 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK124 e (h : Coordinate 2) T124_39_2 i :=
  species_entry_eq_sum rK124 ⟨39, by decide⟩ e heK h T124_39_2 hfix124_39_2 hinj124_39_2 hcardT124_39_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨39, by decide⟩) (reps rK124) (T124_39_2 i) (hfix124_39_2 i) h)

/-! ### Cell (124, 47) twin -/

def T124_47_2 : Fin 5 → Coordinate 2 := fun i => T124_47list.getD i.val (0,0,0,0,0)

theorem hfix124_47_2 : ∀ i, ((T124_47_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK124)
    ∈ fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK124) :=
  repsFix_of_siftB2 rK124 ⟨47, by decide⟩ T124_47_2 (by decide)

theorem hinj124_47_2 : Function.Injective
    (fun i => ((T124_47_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK124)) :=
  repsInj_of_reduceAux2 rK124 T124_47_2 (by decide)

theorem hcardT124_47_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK124)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK124 ⟨47, by decide⟩ R124_2 hpxR124_2 hcardq124_2 (by decide)).symm

/-- **Cell (124, 47) twin (q=2).** -/
theorem cell124_47_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK124) e = true)
    (h : ↥(reps (⟨47, by decide⟩ : Fin 148))) :
    species (reps (⟨47, by decide⟩ : Fin 148)) h (basisElt (reps rK124) (charOfVec2 rK124 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK124 e (h : Coordinate 2) T124_47_2 i :=
  species_entry_eq_sum rK124 ⟨47, by decide⟩ e heK h T124_47_2 hfix124_47_2 hinj124_47_2 hcardT124_47_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨47, by decide⟩) (reps rK124) (T124_47_2 i) (hfix124_47_2 i) h)

/-! ### Cell (124, 51) twin -/

def T124_51_2 : Fin 5 → Coordinate 2 := fun i => T124_51list.getD i.val (0,0,0,0,0)

theorem hfix124_51_2 : ∀ i, ((T124_51_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK124)
    ∈ fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK124) :=
  repsFix_of_siftB2 rK124 ⟨51, by decide⟩ T124_51_2 (by decide)

theorem hinj124_51_2 : Function.Injective
    (fun i => ((T124_51_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK124)) :=
  repsInj_of_reduceAux2 rK124 T124_51_2 (by decide)

theorem hcardT124_51_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK124)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK124 ⟨51, by decide⟩ R124_2 hpxR124_2 hcardq124_2 (by decide)).symm

/-- **Cell (124, 51) twin (q=2).** -/
theorem cell124_51_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK124) e = true)
    (h : ↥(reps (⟨51, by decide⟩ : Fin 148))) :
    species (reps (⟨51, by decide⟩ : Fin 148)) h (basisElt (reps rK124) (charOfVec2 rK124 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK124 e (h : Coordinate 2) T124_51_2 i :=
  species_entry_eq_sum rK124 ⟨51, by decide⟩ e heK h T124_51_2 hfix124_51_2 hinj124_51_2 hcardT124_51_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨51, by decide⟩) (reps rK124) (T124_51_2 i) (hfix124_51_2 i) h)

/-! ### Cell (124, 53) twin -/

def T124_53_2 : Fin 5 → Coordinate 2 := fun i => T124_53list.getD i.val (0,0,0,0,0)

theorem hfix124_53_2 : ∀ i, ((T124_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK124)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK124) :=
  repsFix_of_siftB2 rK124 ⟨53, by decide⟩ T124_53_2 (by decide)

theorem hinj124_53_2 : Function.Injective
    (fun i => ((T124_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK124)) :=
  repsInj_of_reduceAux2 rK124 T124_53_2 (by decide)

theorem hcardT124_53_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK124)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK124 ⟨53, by decide⟩ R124_2 hpxR124_2 hcardq124_2 (by decide)).symm

/-- **Cell (124, 53) twin (q=2).** -/
theorem cell124_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK124) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK124) (charOfVec2 rK124 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK124 e (h : Coordinate 2) T124_53_2 i :=
  species_entry_eq_sum rK124 ⟨53, by decide⟩ e heK h T124_53_2 hfix124_53_2 hinj124_53_2 hcardT124_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK124) (T124_53_2 i) (hfix124_53_2 i) h)

/-! ### Cell (124, 81) twin -/

def T124_81_2 : Fin 5 → Coordinate 2 := fun i => T124_81list.getD i.val (0,0,0,0,0)

theorem hfix124_81_2 : ∀ i, ((T124_81_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK124)
    ∈ fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK124) :=
  repsFix_of_siftB2 rK124 ⟨81, by decide⟩ T124_81_2 (by decide)

theorem hinj124_81_2 : Function.Injective
    (fun i => ((T124_81_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK124)) :=
  repsInj_of_reduceAux2 rK124 T124_81_2 (by decide)

theorem hcardT124_81_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK124)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK124 ⟨81, by decide⟩ R124_2 hpxR124_2 hcardq124_2 (by decide)).symm

/-- **Cell (124, 81) twin (q=2).** -/
theorem cell124_81_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK124) e = true)
    (h : ↥(reps (⟨81, by decide⟩ : Fin 148))) :
    species (reps (⟨81, by decide⟩ : Fin 148)) h (basisElt (reps rK124) (charOfVec2 rK124 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK124 e (h : Coordinate 2) T124_81_2 i :=
  species_entry_eq_sum rK124 ⟨81, by decide⟩ e heK h T124_81_2 hfix124_81_2 hinj124_81_2 hcardT124_81_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨81, by decide⟩) (reps rK124) (T124_81_2 i) (hfix124_81_2 i) h)

/-! ### Cell (124, 92) twin -/

def T124_92_2 : Fin 5 → Coordinate 2 := fun i => T124_92list.getD i.val (0,0,0,0,0)

theorem hfix124_92_2 : ∀ i, ((T124_92_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK124)
    ∈ fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK124) :=
  repsFix_of_siftB2 rK124 ⟨92, by decide⟩ T124_92_2 (by decide)

theorem hinj124_92_2 : Function.Injective
    (fun i => ((T124_92_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK124)) :=
  repsInj_of_reduceAux2 rK124 T124_92_2 (by decide)

theorem hcardT124_92_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK124)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK124 ⟨92, by decide⟩ R124_2 hpxR124_2 hcardq124_2 (by decide)).symm

/-- **Cell (124, 92) twin (q=2).** -/
theorem cell124_92_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK124) e = true)
    (h : ↥(reps (⟨92, by decide⟩ : Fin 148))) :
    species (reps (⟨92, by decide⟩ : Fin 148)) h (basisElt (reps rK124) (charOfVec2 rK124 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK124 e (h : Coordinate 2) T124_92_2 i :=
  species_entry_eq_sum rK124 ⟨92, by decide⟩ e heK h T124_92_2 hfix124_92_2 hinj124_92_2 hcardT124_92_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨92, by decide⟩) (reps rK124) (T124_92_2 i) (hfix124_92_2 i) h)

/-! ### Cell (124, 95) twin -/

def T124_95_2 : Fin 5 → Coordinate 2 := fun i => T124_95list.getD i.val (0,0,0,0,0)

theorem hfix124_95_2 : ∀ i, ((T124_95_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK124)
    ∈ fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK124) :=
  repsFix_of_siftB2 rK124 ⟨95, by decide⟩ T124_95_2 (by decide)

theorem hinj124_95_2 : Function.Injective
    (fun i => ((T124_95_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK124)) :=
  repsInj_of_reduceAux2 rK124 T124_95_2 (by decide)

theorem hcardT124_95_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK124)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK124 ⟨95, by decide⟩ R124_2 hpxR124_2 hcardq124_2 (by decide)).symm

/-- **Cell (124, 95) twin (q=2).** -/
theorem cell124_95_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK124) e = true)
    (h : ↥(reps (⟨95, by decide⟩ : Fin 148))) :
    species (reps (⟨95, by decide⟩ : Fin 148)) h (basisElt (reps rK124) (charOfVec2 rK124 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK124 e (h : Coordinate 2) T124_95_2 i :=
  species_entry_eq_sum rK124 ⟨95, by decide⟩ e heK h T124_95_2 hfix124_95_2 hinj124_95_2 hcardT124_95_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨95, by decide⟩) (reps rK124) (T124_95_2 i) (hfix124_95_2 i) h)

/-! ### Cell (124, 101) twin -/

def T124_101_2 : Fin 5 → Coordinate 2 := fun i => T124_101list.getD i.val (0,0,0,0,0)

theorem hfix124_101_2 : ∀ i, ((T124_101_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK124)
    ∈ fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK124) :=
  repsFix_of_siftB2 rK124 ⟨101, by decide⟩ T124_101_2 (by decide)

theorem hinj124_101_2 : Function.Injective
    (fun i => ((T124_101_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK124)) :=
  repsInj_of_reduceAux2 rK124 T124_101_2 (by decide)

theorem hcardT124_101_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK124)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK124 ⟨101, by decide⟩ R124_2 hpxR124_2 hcardq124_2 (by decide)).symm

/-- **Cell (124, 101) twin (q=2).** -/
theorem cell124_101_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK124) e = true)
    (h : ↥(reps (⟨101, by decide⟩ : Fin 148))) :
    species (reps (⟨101, by decide⟩ : Fin 148)) h (basisElt (reps rK124) (charOfVec2 rK124 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK124 e (h : Coordinate 2) T124_101_2 i :=
  species_entry_eq_sum rK124 ⟨101, by decide⟩ e heK h T124_101_2 hfix124_101_2 hinj124_101_2 hcardT124_101_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨101, by decide⟩) (reps rK124) (T124_101_2 i) (hfix124_101_2 i) h)

/-! ### Cell (124, 109) twin -/

def T124_109_2 : Fin 5 → Coordinate 2 := fun i => T124_109list.getD i.val (0,0,0,0,0)

theorem hfix124_109_2 : ∀ i, ((T124_109_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK124)
    ∈ fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK124) :=
  repsFix_of_siftB2 rK124 ⟨109, by decide⟩ T124_109_2 (by decide)

theorem hinj124_109_2 : Function.Injective
    (fun i => ((T124_109_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK124)) :=
  repsInj_of_reduceAux2 rK124 T124_109_2 (by decide)

theorem hcardT124_109_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK124)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK124 ⟨109, by decide⟩ R124_2 hpxR124_2 hcardq124_2 (by decide)).symm

/-- **Cell (124, 109) twin (q=2).** -/
theorem cell124_109_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK124) e = true)
    (h : ↥(reps (⟨109, by decide⟩ : Fin 148))) :
    species (reps (⟨109, by decide⟩ : Fin 148)) h (basisElt (reps rK124) (charOfVec2 rK124 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK124 e (h : Coordinate 2) T124_109_2 i :=
  species_entry_eq_sum rK124 ⟨109, by decide⟩ e heK h T124_109_2 hfix124_109_2 hinj124_109_2 hcardT124_109_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨109, by decide⟩) (reps rK124) (T124_109_2 i) (hfix124_109_2 i) h)

/-! ### Cell (124, 113) twin -/

def T124_113_2 : Fin 5 → Coordinate 2 := fun i => T124_113list.getD i.val (0,0,0,0,0)

theorem hfix124_113_2 : ∀ i, ((T124_113_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK124)
    ∈ fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK124) :=
  repsFix_of_siftB2 rK124 ⟨113, by decide⟩ T124_113_2 (by decide)

theorem hinj124_113_2 : Function.Injective
    (fun i => ((T124_113_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK124)) :=
  repsInj_of_reduceAux2 rK124 T124_113_2 (by decide)

theorem hcardT124_113_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK124)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK124 ⟨113, by decide⟩ R124_2 hpxR124_2 hcardq124_2 (by decide)).symm

/-- **Cell (124, 113) twin (q=2).** -/
theorem cell124_113_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK124) e = true)
    (h : ↥(reps (⟨113, by decide⟩ : Fin 148))) :
    species (reps (⟨113, by decide⟩ : Fin 148)) h (basisElt (reps rK124) (charOfVec2 rK124 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK124 e (h : Coordinate 2) T124_113_2 i :=
  species_entry_eq_sum rK124 ⟨113, by decide⟩ e heK h T124_113_2 hfix124_113_2 hinj124_113_2 hcardT124_113_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨113, by decide⟩) (reps rK124) (T124_113_2 i) (hfix124_113_2 i) h)

/-! ### Cell (124, 124) twin -/

def T124_124_2 : Fin 5 → Coordinate 2 := fun i => T124_124list.getD i.val (0,0,0,0,0)

theorem hfix124_124_2 : ∀ i, ((T124_124_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK124)
    ∈ fixedPoints (reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK124) :=
  repsFix_of_siftB2 rK124 ⟨124, by decide⟩ T124_124_2 (by decide)

theorem hinj124_124_2 : Function.Injective
    (fun i => ((T124_124_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK124)) :=
  repsInj_of_reduceAux2 rK124 T124_124_2 (by decide)

theorem hcardT124_124_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK124)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK124 ⟨124, by decide⟩ R124_2 hpxR124_2 hcardq124_2 (by decide)).symm

/-- **Cell (124, 124) twin (q=2).** -/
theorem cell124_124_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK124) e = true)
    (h : ↥(reps (⟨124, by decide⟩ : Fin 148))) :
    species (reps (⟨124, by decide⟩ : Fin 148)) h (basisElt (reps rK124) (charOfVec2 rK124 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK124 e (h : Coordinate 2) T124_124_2 i :=
  species_entry_eq_sum rK124 ⟨124, by decide⟩ e heK h T124_124_2 hfix124_124_2 hinj124_124_2 hcardT124_124_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨124, by decide⟩) (reps rK124) (T124_124_2 i) (hfix124_124_2 i) h)

end Q2

/-! # K-class rK = 125  (|G/K| = 5) -/

def rK125 : Fin 148 := ⟨125, by decide⟩

def R125list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def R125 : Fin 5 → Coordinate 1 := fun i => R125list.getD i.val (0,0,0,0,0)

theorem hpxR125 : Function.Injective (fun i => reduceAux 1 (basisAt rK125) (R125 i)) := by decide
theorem hcardq125 : Nat.card (Coordinate 1 ⧸ reps rK125) = 5 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (125, 0): |T| = 5 -/

def T125_0list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T125_0 : Fin 5 → Coordinate 1 := fun i => T125_0list.getD i.val (0,0,0,0,0)

theorem hfix125_0 : ∀ i, ((T125_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK125)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125) :=
  repsFix_of_siftB rK125 ⟨0, by decide⟩ T125_0 (by decide)

theorem hinj125_0 : Function.Injective
    (fun i => ((T125_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK125)) :=
  repsInj_of_reduceAux rK125 T125_0 (by decide)

theorem hcardT125_0 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK125 ⟨0, by decide⟩ R125 hpxR125 hcardq125 (by decide)).symm

/-- **Cell (125, 0).** -/
theorem cell125_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK125) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK125) (charOfVec rK125 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK125 e (h : Coordinate 1) T125_0 i :=
  species_entry_eq_sum rK125 ⟨0, by decide⟩ e heK h T125_0 hfix125_0 hinj125_0 hcardT125_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK125) (T125_0 i) (hfix125_0 i) h)

/-! ## Cell (125, 2): |T| = 5 -/

def T125_2list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T125_2 : Fin 5 → Coordinate 1 := fun i => T125_2list.getD i.val (0,0,0,0,0)

theorem hfix125_2 : ∀ i, ((T125_2 i : Coordinate 1) : Coordinate 1 ⧸ reps rK125)
    ∈ fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125) :=
  repsFix_of_siftB rK125 ⟨2, by decide⟩ T125_2 (by decide)

theorem hinj125_2 : Function.Injective
    (fun i => ((T125_2 i : Coordinate 1) : Coordinate 1 ⧸ reps rK125)) :=
  repsInj_of_reduceAux rK125 T125_2 (by decide)

theorem hcardT125_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK125 ⟨2, by decide⟩ R125 hpxR125 hcardq125 (by decide)).symm

/-- **Cell (125, 2).** -/
theorem cell125_2 (e : List (ZMod 25)) (heK : charOK (basisAt rK125) e = true)
    (h : ↥(reps (⟨2, by decide⟩ : Fin 148))) :
    species (reps (⟨2, by decide⟩ : Fin 148)) h (basisElt (reps rK125) (charOfVec rK125 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK125 e (h : Coordinate 1) T125_2 i :=
  species_entry_eq_sum rK125 ⟨2, by decide⟩ e heK h T125_2 hfix125_2 hinj125_2 hcardT125_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨2, by decide⟩) (reps rK125) (T125_2 i) (hfix125_2 i) h)

/-! ## Cell (125, 10): |T| = 5 -/

def T125_10list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T125_10 : Fin 5 → Coordinate 1 := fun i => T125_10list.getD i.val (0,0,0,0,0)

theorem hfix125_10 : ∀ i, ((T125_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK125)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125) :=
  repsFix_of_siftB rK125 ⟨10, by decide⟩ T125_10 (by decide)

theorem hinj125_10 : Function.Injective
    (fun i => ((T125_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK125)) :=
  repsInj_of_reduceAux rK125 T125_10 (by decide)

theorem hcardT125_10 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK125 ⟨10, by decide⟩ R125 hpxR125 hcardq125 (by decide)).symm

/-- **Cell (125, 10).** -/
theorem cell125_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK125) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK125) (charOfVec rK125 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK125 e (h : Coordinate 1) T125_10 i :=
  species_entry_eq_sum rK125 ⟨10, by decide⟩ e heK h T125_10 hfix125_10 hinj125_10 hcardT125_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK125) (T125_10 i) (hfix125_10 i) h)

/-! ## Cell (125, 12): |T| = 5 -/

def T125_12list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T125_12 : Fin 5 → Coordinate 1 := fun i => T125_12list.getD i.val (0,0,0,0,0)

theorem hfix125_12 : ∀ i, ((T125_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK125)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125) :=
  repsFix_of_siftB rK125 ⟨12, by decide⟩ T125_12 (by decide)

theorem hinj125_12 : Function.Injective
    (fun i => ((T125_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK125)) :=
  repsInj_of_reduceAux rK125 T125_12 (by decide)

theorem hcardT125_12 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK125 ⟨12, by decide⟩ R125 hpxR125 hcardq125 (by decide)).symm

/-- **Cell (125, 12).** -/
theorem cell125_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK125) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK125) (charOfVec rK125 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK125 e (h : Coordinate 1) T125_12 i :=
  species_entry_eq_sum rK125 ⟨12, by decide⟩ e heK h T125_12 hfix125_12 hinj125_12 hcardT125_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK125) (T125_12 i) (hfix125_12 i) h)

/-! ## Cell (125, 20): |T| = 5 -/

def T125_20list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T125_20 : Fin 5 → Coordinate 1 := fun i => T125_20list.getD i.val (0,0,0,0,0)

theorem hfix125_20 : ∀ i, ((T125_20 i : Coordinate 1) : Coordinate 1 ⧸ reps rK125)
    ∈ fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125) :=
  repsFix_of_siftB rK125 ⟨20, by decide⟩ T125_20 (by decide)

theorem hinj125_20 : Function.Injective
    (fun i => ((T125_20 i : Coordinate 1) : Coordinate 1 ⧸ reps rK125)) :=
  repsInj_of_reduceAux rK125 T125_20 (by decide)

theorem hcardT125_20 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK125 ⟨20, by decide⟩ R125 hpxR125 hcardq125 (by decide)).symm

/-- **Cell (125, 20).** -/
theorem cell125_20 (e : List (ZMod 25)) (heK : charOK (basisAt rK125) e = true)
    (h : ↥(reps (⟨20, by decide⟩ : Fin 148))) :
    species (reps (⟨20, by decide⟩ : Fin 148)) h (basisElt (reps rK125) (charOfVec rK125 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK125 e (h : Coordinate 1) T125_20 i :=
  species_entry_eq_sum rK125 ⟨20, by decide⟩ e heK h T125_20 hfix125_20 hinj125_20 hcardT125_20
    (fun i => conj_mem_of_fixedPoints (reps ⟨20, by decide⟩) (reps rK125) (T125_20 i) (hfix125_20 i) h)

/-! ## Cell (125, 31): |T| = 5 -/

def T125_31list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T125_31 : Fin 5 → Coordinate 1 := fun i => T125_31list.getD i.val (0,0,0,0,0)

theorem hfix125_31 : ∀ i, ((T125_31 i : Coordinate 1) : Coordinate 1 ⧸ reps rK125)
    ∈ fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125) :=
  repsFix_of_siftB rK125 ⟨31, by decide⟩ T125_31 (by decide)

theorem hinj125_31 : Function.Injective
    (fun i => ((T125_31 i : Coordinate 1) : Coordinate 1 ⧸ reps rK125)) :=
  repsInj_of_reduceAux rK125 T125_31 (by decide)

theorem hcardT125_31 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK125 ⟨31, by decide⟩ R125 hpxR125 hcardq125 (by decide)).symm

/-- **Cell (125, 31).** -/
theorem cell125_31 (e : List (ZMod 25)) (heK : charOK (basisAt rK125) e = true)
    (h : ↥(reps (⟨31, by decide⟩ : Fin 148))) :
    species (reps (⟨31, by decide⟩ : Fin 148)) h (basisElt (reps rK125) (charOfVec rK125 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK125 e (h : Coordinate 1) T125_31 i :=
  species_entry_eq_sum rK125 ⟨31, by decide⟩ e heK h T125_31 hfix125_31 hinj125_31 hcardT125_31
    (fun i => conj_mem_of_fixedPoints (reps ⟨31, by decide⟩) (reps rK125) (T125_31 i) (hfix125_31 i) h)

/-! ## Cell (125, 34): |T| = 5 -/

def T125_34list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T125_34 : Fin 5 → Coordinate 1 := fun i => T125_34list.getD i.val (0,0,0,0,0)

theorem hfix125_34 : ∀ i, ((T125_34 i : Coordinate 1) : Coordinate 1 ⧸ reps rK125)
    ∈ fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125) :=
  repsFix_of_siftB rK125 ⟨34, by decide⟩ T125_34 (by decide)

theorem hinj125_34 : Function.Injective
    (fun i => ((T125_34 i : Coordinate 1) : Coordinate 1 ⧸ reps rK125)) :=
  repsInj_of_reduceAux rK125 T125_34 (by decide)

theorem hcardT125_34 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK125 ⟨34, by decide⟩ R125 hpxR125 hcardq125 (by decide)).symm

/-- **Cell (125, 34).** -/
theorem cell125_34 (e : List (ZMod 25)) (heK : charOK (basisAt rK125) e = true)
    (h : ↥(reps (⟨34, by decide⟩ : Fin 148))) :
    species (reps (⟨34, by decide⟩ : Fin 148)) h (basisElt (reps rK125) (charOfVec rK125 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK125 e (h : Coordinate 1) T125_34 i :=
  species_entry_eq_sum rK125 ⟨34, by decide⟩ e heK h T125_34 hfix125_34 hinj125_34 hcardT125_34
    (fun i => conj_mem_of_fixedPoints (reps ⟨34, by decide⟩) (reps rK125) (T125_34 i) (hfix125_34 i) h)

/-! ## Cell (125, 40): |T| = 5 -/

def T125_40list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T125_40 : Fin 5 → Coordinate 1 := fun i => T125_40list.getD i.val (0,0,0,0,0)

theorem hfix125_40 : ∀ i, ((T125_40 i : Coordinate 1) : Coordinate 1 ⧸ reps rK125)
    ∈ fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125) :=
  repsFix_of_siftB rK125 ⟨40, by decide⟩ T125_40 (by decide)

theorem hinj125_40 : Function.Injective
    (fun i => ((T125_40 i : Coordinate 1) : Coordinate 1 ⧸ reps rK125)) :=
  repsInj_of_reduceAux rK125 T125_40 (by decide)

theorem hcardT125_40 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK125 ⟨40, by decide⟩ R125 hpxR125 hcardq125 (by decide)).symm

/-- **Cell (125, 40).** -/
theorem cell125_40 (e : List (ZMod 25)) (heK : charOK (basisAt rK125) e = true)
    (h : ↥(reps (⟨40, by decide⟩ : Fin 148))) :
    species (reps (⟨40, by decide⟩ : Fin 148)) h (basisElt (reps rK125) (charOfVec rK125 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK125 e (h : Coordinate 1) T125_40 i :=
  species_entry_eq_sum rK125 ⟨40, by decide⟩ e heK h T125_40 hfix125_40 hinj125_40 hcardT125_40
    (fun i => conj_mem_of_fixedPoints (reps ⟨40, by decide⟩) (reps rK125) (T125_40 i) (hfix125_40 i) h)

/-! ## Cell (125, 43): |T| = 5 -/

def T125_43list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T125_43 : Fin 5 → Coordinate 1 := fun i => T125_43list.getD i.val (0,0,0,0,0)

theorem hfix125_43 : ∀ i, ((T125_43 i : Coordinate 1) : Coordinate 1 ⧸ reps rK125)
    ∈ fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125) :=
  repsFix_of_siftB rK125 ⟨43, by decide⟩ T125_43 (by decide)

theorem hinj125_43 : Function.Injective
    (fun i => ((T125_43 i : Coordinate 1) : Coordinate 1 ⧸ reps rK125)) :=
  repsInj_of_reduceAux rK125 T125_43 (by decide)

theorem hcardT125_43 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK125 ⟨43, by decide⟩ R125 hpxR125 hcardq125 (by decide)).symm

/-- **Cell (125, 43).** -/
theorem cell125_43 (e : List (ZMod 25)) (heK : charOK (basisAt rK125) e = true)
    (h : ↥(reps (⟨43, by decide⟩ : Fin 148))) :
    species (reps (⟨43, by decide⟩ : Fin 148)) h (basisElt (reps rK125) (charOfVec rK125 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK125 e (h : Coordinate 1) T125_43 i :=
  species_entry_eq_sum rK125 ⟨43, by decide⟩ e heK h T125_43 hfix125_43 hinj125_43 hcardT125_43
    (fun i => conj_mem_of_fixedPoints (reps ⟨43, by decide⟩) (reps rK125) (T125_43 i) (hfix125_43 i) h)

/-! ## Cell (125, 52): |T| = 5 -/

def T125_52list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T125_52 : Fin 5 → Coordinate 1 := fun i => T125_52list.getD i.val (0,0,0,0,0)

theorem hfix125_52 : ∀ i, ((T125_52 i : Coordinate 1) : Coordinate 1 ⧸ reps rK125)
    ∈ fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125) :=
  repsFix_of_siftB rK125 ⟨52, by decide⟩ T125_52 (by decide)

theorem hinj125_52 : Function.Injective
    (fun i => ((T125_52 i : Coordinate 1) : Coordinate 1 ⧸ reps rK125)) :=
  repsInj_of_reduceAux rK125 T125_52 (by decide)

theorem hcardT125_52 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK125 ⟨52, by decide⟩ R125 hpxR125 hcardq125 (by decide)).symm

/-- **Cell (125, 52).** -/
theorem cell125_52 (e : List (ZMod 25)) (heK : charOK (basisAt rK125) e = true)
    (h : ↥(reps (⟨52, by decide⟩ : Fin 148))) :
    species (reps (⟨52, by decide⟩ : Fin 148)) h (basisElt (reps rK125) (charOfVec rK125 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK125 e (h : Coordinate 1) T125_52 i :=
  species_entry_eq_sum rK125 ⟨52, by decide⟩ e heK h T125_52 hfix125_52 hinj125_52 hcardT125_52
    (fun i => conj_mem_of_fixedPoints (reps ⟨52, by decide⟩) (reps rK125) (T125_52 i) (hfix125_52 i) h)

/-! ## Cell (125, 53): |T| = 5 -/

def T125_53list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T125_53 : Fin 5 → Coordinate 1 := fun i => T125_53list.getD i.val (0,0,0,0,0)

theorem hfix125_53 : ∀ i, ((T125_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK125)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125) :=
  repsFix_of_siftB rK125 ⟨53, by decide⟩ T125_53 (by decide)

theorem hinj125_53 : Function.Injective
    (fun i => ((T125_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK125)) :=
  repsInj_of_reduceAux rK125 T125_53 (by decide)

theorem hcardT125_53 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK125 ⟨53, by decide⟩ R125 hpxR125 hcardq125 (by decide)).symm

/-- **Cell (125, 53).** -/
theorem cell125_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK125) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK125) (charOfVec rK125 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK125 e (h : Coordinate 1) T125_53 i :=
  species_entry_eq_sum rK125 ⟨53, by decide⟩ e heK h T125_53 hfix125_53 hinj125_53 hcardT125_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK125) (T125_53 i) (hfix125_53 i) h)

/-! ## Cell (125, 81): |T| = 5 -/

def T125_81list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T125_81 : Fin 5 → Coordinate 1 := fun i => T125_81list.getD i.val (0,0,0,0,0)

theorem hfix125_81 : ∀ i, ((T125_81 i : Coordinate 1) : Coordinate 1 ⧸ reps rK125)
    ∈ fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125) :=
  repsFix_of_siftB rK125 ⟨81, by decide⟩ T125_81 (by decide)

theorem hinj125_81 : Function.Injective
    (fun i => ((T125_81 i : Coordinate 1) : Coordinate 1 ⧸ reps rK125)) :=
  repsInj_of_reduceAux rK125 T125_81 (by decide)

theorem hcardT125_81 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK125 ⟨81, by decide⟩ R125 hpxR125 hcardq125 (by decide)).symm

/-- **Cell (125, 81).** -/
theorem cell125_81 (e : List (ZMod 25)) (heK : charOK (basisAt rK125) e = true)
    (h : ↥(reps (⟨81, by decide⟩ : Fin 148))) :
    species (reps (⟨81, by decide⟩ : Fin 148)) h (basisElt (reps rK125) (charOfVec rK125 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK125 e (h : Coordinate 1) T125_81 i :=
  species_entry_eq_sum rK125 ⟨81, by decide⟩ e heK h T125_81 hfix125_81 hinj125_81 hcardT125_81
    (fun i => conj_mem_of_fixedPoints (reps ⟨81, by decide⟩) (reps rK125) (T125_81 i) (hfix125_81 i) h)

/-! ## Cell (125, 93): |T| = 5 -/

def T125_93list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T125_93 : Fin 5 → Coordinate 1 := fun i => T125_93list.getD i.val (0,0,0,0,0)

theorem hfix125_93 : ∀ i, ((T125_93 i : Coordinate 1) : Coordinate 1 ⧸ reps rK125)
    ∈ fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125) :=
  repsFix_of_siftB rK125 ⟨93, by decide⟩ T125_93 (by decide)

theorem hinj125_93 : Function.Injective
    (fun i => ((T125_93 i : Coordinate 1) : Coordinate 1 ⧸ reps rK125)) :=
  repsInj_of_reduceAux rK125 T125_93 (by decide)

theorem hcardT125_93 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK125 ⟨93, by decide⟩ R125 hpxR125 hcardq125 (by decide)).symm

/-- **Cell (125, 93).** -/
theorem cell125_93 (e : List (ZMod 25)) (heK : charOK (basisAt rK125) e = true)
    (h : ↥(reps (⟨93, by decide⟩ : Fin 148))) :
    species (reps (⟨93, by decide⟩ : Fin 148)) h (basisElt (reps rK125) (charOfVec rK125 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK125 e (h : Coordinate 1) T125_93 i :=
  species_entry_eq_sum rK125 ⟨93, by decide⟩ e heK h T125_93 hfix125_93 hinj125_93 hcardT125_93
    (fun i => conj_mem_of_fixedPoints (reps ⟨93, by decide⟩) (reps rK125) (T125_93 i) (hfix125_93 i) h)

/-! ## Cell (125, 96): |T| = 5 -/

def T125_96list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T125_96 : Fin 5 → Coordinate 1 := fun i => T125_96list.getD i.val (0,0,0,0,0)

theorem hfix125_96 : ∀ i, ((T125_96 i : Coordinate 1) : Coordinate 1 ⧸ reps rK125)
    ∈ fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125) :=
  repsFix_of_siftB rK125 ⟨96, by decide⟩ T125_96 (by decide)

theorem hinj125_96 : Function.Injective
    (fun i => ((T125_96 i : Coordinate 1) : Coordinate 1 ⧸ reps rK125)) :=
  repsInj_of_reduceAux rK125 T125_96 (by decide)

theorem hcardT125_96 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK125 ⟨96, by decide⟩ R125 hpxR125 hcardq125 (by decide)).symm

/-- **Cell (125, 96).** -/
theorem cell125_96 (e : List (ZMod 25)) (heK : charOK (basisAt rK125) e = true)
    (h : ↥(reps (⟨96, by decide⟩ : Fin 148))) :
    species (reps (⟨96, by decide⟩ : Fin 148)) h (basisElt (reps rK125) (charOfVec rK125 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK125 e (h : Coordinate 1) T125_96 i :=
  species_entry_eq_sum rK125 ⟨96, by decide⟩ e heK h T125_96 hfix125_96 hinj125_96 hcardT125_96
    (fun i => conj_mem_of_fixedPoints (reps ⟨96, by decide⟩) (reps rK125) (T125_96 i) (hfix125_96 i) h)

/-! ## Cell (125, 102): |T| = 5 -/

def T125_102list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T125_102 : Fin 5 → Coordinate 1 := fun i => T125_102list.getD i.val (0,0,0,0,0)

theorem hfix125_102 : ∀ i, ((T125_102 i : Coordinate 1) : Coordinate 1 ⧸ reps rK125)
    ∈ fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125) :=
  repsFix_of_siftB rK125 ⟨102, by decide⟩ T125_102 (by decide)

theorem hinj125_102 : Function.Injective
    (fun i => ((T125_102 i : Coordinate 1) : Coordinate 1 ⧸ reps rK125)) :=
  repsInj_of_reduceAux rK125 T125_102 (by decide)

theorem hcardT125_102 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK125 ⟨102, by decide⟩ R125 hpxR125 hcardq125 (by decide)).symm

/-- **Cell (125, 102).** -/
theorem cell125_102 (e : List (ZMod 25)) (heK : charOK (basisAt rK125) e = true)
    (h : ↥(reps (⟨102, by decide⟩ : Fin 148))) :
    species (reps (⟨102, by decide⟩ : Fin 148)) h (basisElt (reps rK125) (charOfVec rK125 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK125 e (h : Coordinate 1) T125_102 i :=
  species_entry_eq_sum rK125 ⟨102, by decide⟩ e heK h T125_102 hfix125_102 hinj125_102 hcardT125_102
    (fun i => conj_mem_of_fixedPoints (reps ⟨102, by decide⟩) (reps rK125) (T125_102 i) (hfix125_102 i) h)

/-! ## Cell (125, 105): |T| = 5 -/

def T125_105list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T125_105 : Fin 5 → Coordinate 1 := fun i => T125_105list.getD i.val (0,0,0,0,0)

theorem hfix125_105 : ∀ i, ((T125_105 i : Coordinate 1) : Coordinate 1 ⧸ reps rK125)
    ∈ fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125) :=
  repsFix_of_siftB rK125 ⟨105, by decide⟩ T125_105 (by decide)

theorem hinj125_105 : Function.Injective
    (fun i => ((T125_105 i : Coordinate 1) : Coordinate 1 ⧸ reps rK125)) :=
  repsInj_of_reduceAux rK125 T125_105 (by decide)

theorem hcardT125_105 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK125 ⟨105, by decide⟩ R125 hpxR125 hcardq125 (by decide)).symm

/-- **Cell (125, 105).** -/
theorem cell125_105 (e : List (ZMod 25)) (heK : charOK (basisAt rK125) e = true)
    (h : ↥(reps (⟨105, by decide⟩ : Fin 148))) :
    species (reps (⟨105, by decide⟩ : Fin 148)) h (basisElt (reps rK125) (charOfVec rK125 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK125 e (h : Coordinate 1) T125_105 i :=
  species_entry_eq_sum rK125 ⟨105, by decide⟩ e heK h T125_105 hfix125_105 hinj125_105 hcardT125_105
    (fun i => conj_mem_of_fixedPoints (reps ⟨105, by decide⟩) (reps rK125) (T125_105 i) (hfix125_105 i) h)

/-! ## Cell (125, 114): |T| = 5 -/

def T125_114list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T125_114 : Fin 5 → Coordinate 1 := fun i => T125_114list.getD i.val (0,0,0,0,0)

theorem hfix125_114 : ∀ i, ((T125_114 i : Coordinate 1) : Coordinate 1 ⧸ reps rK125)
    ∈ fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125) :=
  repsFix_of_siftB rK125 ⟨114, by decide⟩ T125_114 (by decide)

theorem hinj125_114 : Function.Injective
    (fun i => ((T125_114 i : Coordinate 1) : Coordinate 1 ⧸ reps rK125)) :=
  repsInj_of_reduceAux rK125 T125_114 (by decide)

theorem hcardT125_114 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK125 ⟨114, by decide⟩ R125 hpxR125 hcardq125 (by decide)).symm

/-- **Cell (125, 114).** -/
theorem cell125_114 (e : List (ZMod 25)) (heK : charOK (basisAt rK125) e = true)
    (h : ↥(reps (⟨114, by decide⟩ : Fin 148))) :
    species (reps (⟨114, by decide⟩ : Fin 148)) h (basisElt (reps rK125) (charOfVec rK125 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK125 e (h : Coordinate 1) T125_114 i :=
  species_entry_eq_sum rK125 ⟨114, by decide⟩ e heK h T125_114 hfix125_114 hinj125_114 hcardT125_114
    (fun i => conj_mem_of_fixedPoints (reps ⟨114, by decide⟩) (reps rK125) (T125_114 i) (hfix125_114 i) h)

/-! ## Cell (125, 125): |T| = 5 -/

def T125_125list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T125_125 : Fin 5 → Coordinate 1 := fun i => T125_125list.getD i.val (0,0,0,0,0)

theorem hfix125_125 : ∀ i, ((T125_125 i : Coordinate 1) : Coordinate 1 ⧸ reps rK125)
    ∈ fixedPoints (reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125) :=
  repsFix_of_siftB rK125 ⟨125, by decide⟩ T125_125 (by decide)

theorem hinj125_125 : Function.Injective
    (fun i => ((T125_125 i : Coordinate 1) : Coordinate 1 ⧸ reps rK125)) :=
  repsInj_of_reduceAux rK125 T125_125 (by decide)

theorem hcardT125_125 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK125 ⟨125, by decide⟩ R125 hpxR125 hcardq125 (by decide)).symm

/-- **Cell (125, 125).** -/
theorem cell125_125 (e : List (ZMod 25)) (heK : charOK (basisAt rK125) e = true)
    (h : ↥(reps (⟨125, by decide⟩ : Fin 148))) :
    species (reps (⟨125, by decide⟩ : Fin 148)) h (basisElt (reps rK125) (charOfVec rK125 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK125 e (h : Coordinate 1) T125_125 i :=
  species_entry_eq_sum rK125 ⟨125, by decide⟩ e heK h T125_125 hfix125_125 hinj125_125 hcardT125_125
    (fun i => conj_mem_of_fixedPoints (reps ⟨125, by decide⟩) (reps rK125) (T125_125 i) (hfix125_125 i) h)

namespace Q2

def R125_2 : Fin 5 → Coordinate 2 := fun i => R125list.getD i.val (0,0,0,0,0)
theorem hpxR125_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK125) (R125_2 i)) := by decide
theorem hcardq125_2 : Nat.card (Coordinate 2 ⧸ reps rK125) = 5 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (125, 0) twin -/

def T125_0_2 : Fin 5 → Coordinate 2 := fun i => T125_0list.getD i.val (0,0,0,0,0)

theorem hfix125_0_2 : ∀ i, ((T125_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK125)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK125) :=
  repsFix_of_siftB2 rK125 ⟨0, by decide⟩ T125_0_2 (by decide)

theorem hinj125_0_2 : Function.Injective
    (fun i => ((T125_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK125)) :=
  repsInj_of_reduceAux2 rK125 T125_0_2 (by decide)

theorem hcardT125_0_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK125)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK125 ⟨0, by decide⟩ R125_2 hpxR125_2 hcardq125_2 (by decide)).symm

/-- **Cell (125, 0) twin (q=2).** -/
theorem cell125_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK125) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK125) (charOfVec2 rK125 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK125 e (h : Coordinate 2) T125_0_2 i :=
  species_entry_eq_sum rK125 ⟨0, by decide⟩ e heK h T125_0_2 hfix125_0_2 hinj125_0_2 hcardT125_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK125) (T125_0_2 i) (hfix125_0_2 i) h)

/-! ### Cell (125, 2) twin -/

def T125_2_2 : Fin 5 → Coordinate 2 := fun i => T125_2list.getD i.val (0,0,0,0,0)

theorem hfix125_2_2 : ∀ i, ((T125_2_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK125)
    ∈ fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK125) :=
  repsFix_of_siftB2 rK125 ⟨2, by decide⟩ T125_2_2 (by decide)

theorem hinj125_2_2 : Function.Injective
    (fun i => ((T125_2_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK125)) :=
  repsInj_of_reduceAux2 rK125 T125_2_2 (by decide)

theorem hcardT125_2_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK125)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK125 ⟨2, by decide⟩ R125_2 hpxR125_2 hcardq125_2 (by decide)).symm

/-- **Cell (125, 2) twin (q=2).** -/
theorem cell125_2_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK125) e = true)
    (h : ↥(reps (⟨2, by decide⟩ : Fin 148))) :
    species (reps (⟨2, by decide⟩ : Fin 148)) h (basisElt (reps rK125) (charOfVec2 rK125 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK125 e (h : Coordinate 2) T125_2_2 i :=
  species_entry_eq_sum rK125 ⟨2, by decide⟩ e heK h T125_2_2 hfix125_2_2 hinj125_2_2 hcardT125_2_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨2, by decide⟩) (reps rK125) (T125_2_2 i) (hfix125_2_2 i) h)

/-! ### Cell (125, 10) twin -/

def T125_10_2 : Fin 5 → Coordinate 2 := fun i => T125_10list.getD i.val (0,0,0,0,0)

theorem hfix125_10_2 : ∀ i, ((T125_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK125)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK125) :=
  repsFix_of_siftB2 rK125 ⟨10, by decide⟩ T125_10_2 (by decide)

theorem hinj125_10_2 : Function.Injective
    (fun i => ((T125_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK125)) :=
  repsInj_of_reduceAux2 rK125 T125_10_2 (by decide)

theorem hcardT125_10_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK125)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK125 ⟨10, by decide⟩ R125_2 hpxR125_2 hcardq125_2 (by decide)).symm

/-- **Cell (125, 10) twin (q=2).** -/
theorem cell125_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK125) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK125) (charOfVec2 rK125 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK125 e (h : Coordinate 2) T125_10_2 i :=
  species_entry_eq_sum rK125 ⟨10, by decide⟩ e heK h T125_10_2 hfix125_10_2 hinj125_10_2 hcardT125_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK125) (T125_10_2 i) (hfix125_10_2 i) h)

/-! ### Cell (125, 12) twin -/

def T125_12_2 : Fin 5 → Coordinate 2 := fun i => T125_12list.getD i.val (0,0,0,0,0)

theorem hfix125_12_2 : ∀ i, ((T125_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK125)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK125) :=
  repsFix_of_siftB2 rK125 ⟨12, by decide⟩ T125_12_2 (by decide)

theorem hinj125_12_2 : Function.Injective
    (fun i => ((T125_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK125)) :=
  repsInj_of_reduceAux2 rK125 T125_12_2 (by decide)

theorem hcardT125_12_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK125)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK125 ⟨12, by decide⟩ R125_2 hpxR125_2 hcardq125_2 (by decide)).symm

/-- **Cell (125, 12) twin (q=2).** -/
theorem cell125_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK125) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK125) (charOfVec2 rK125 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK125 e (h : Coordinate 2) T125_12_2 i :=
  species_entry_eq_sum rK125 ⟨12, by decide⟩ e heK h T125_12_2 hfix125_12_2 hinj125_12_2 hcardT125_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK125) (T125_12_2 i) (hfix125_12_2 i) h)

/-! ### Cell (125, 20) twin -/

def T125_20_2 : Fin 5 → Coordinate 2 := fun i => T125_20list.getD i.val (0,0,0,0,0)

theorem hfix125_20_2 : ∀ i, ((T125_20_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK125)
    ∈ fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK125) :=
  repsFix_of_siftB2 rK125 ⟨20, by decide⟩ T125_20_2 (by decide)

theorem hinj125_20_2 : Function.Injective
    (fun i => ((T125_20_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK125)) :=
  repsInj_of_reduceAux2 rK125 T125_20_2 (by decide)

theorem hcardT125_20_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK125)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK125 ⟨20, by decide⟩ R125_2 hpxR125_2 hcardq125_2 (by decide)).symm

/-- **Cell (125, 20) twin (q=2).** -/
theorem cell125_20_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK125) e = true)
    (h : ↥(reps (⟨20, by decide⟩ : Fin 148))) :
    species (reps (⟨20, by decide⟩ : Fin 148)) h (basisElt (reps rK125) (charOfVec2 rK125 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK125 e (h : Coordinate 2) T125_20_2 i :=
  species_entry_eq_sum rK125 ⟨20, by decide⟩ e heK h T125_20_2 hfix125_20_2 hinj125_20_2 hcardT125_20_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨20, by decide⟩) (reps rK125) (T125_20_2 i) (hfix125_20_2 i) h)

/-! ### Cell (125, 31) twin -/

def T125_31_2 : Fin 5 → Coordinate 2 := fun i => T125_31list.getD i.val (0,0,0,0,0)

theorem hfix125_31_2 : ∀ i, ((T125_31_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK125)
    ∈ fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK125) :=
  repsFix_of_siftB2 rK125 ⟨31, by decide⟩ T125_31_2 (by decide)

theorem hinj125_31_2 : Function.Injective
    (fun i => ((T125_31_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK125)) :=
  repsInj_of_reduceAux2 rK125 T125_31_2 (by decide)

theorem hcardT125_31_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK125)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK125 ⟨31, by decide⟩ R125_2 hpxR125_2 hcardq125_2 (by decide)).symm

/-- **Cell (125, 31) twin (q=2).** -/
theorem cell125_31_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK125) e = true)
    (h : ↥(reps (⟨31, by decide⟩ : Fin 148))) :
    species (reps (⟨31, by decide⟩ : Fin 148)) h (basisElt (reps rK125) (charOfVec2 rK125 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK125 e (h : Coordinate 2) T125_31_2 i :=
  species_entry_eq_sum rK125 ⟨31, by decide⟩ e heK h T125_31_2 hfix125_31_2 hinj125_31_2 hcardT125_31_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨31, by decide⟩) (reps rK125) (T125_31_2 i) (hfix125_31_2 i) h)

/-! ### Cell (125, 34) twin -/

def T125_34_2 : Fin 5 → Coordinate 2 := fun i => T125_34list.getD i.val (0,0,0,0,0)

theorem hfix125_34_2 : ∀ i, ((T125_34_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK125)
    ∈ fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK125) :=
  repsFix_of_siftB2 rK125 ⟨34, by decide⟩ T125_34_2 (by decide)

theorem hinj125_34_2 : Function.Injective
    (fun i => ((T125_34_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK125)) :=
  repsInj_of_reduceAux2 rK125 T125_34_2 (by decide)

theorem hcardT125_34_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK125)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK125 ⟨34, by decide⟩ R125_2 hpxR125_2 hcardq125_2 (by decide)).symm

/-- **Cell (125, 34) twin (q=2).** -/
theorem cell125_34_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK125) e = true)
    (h : ↥(reps (⟨34, by decide⟩ : Fin 148))) :
    species (reps (⟨34, by decide⟩ : Fin 148)) h (basisElt (reps rK125) (charOfVec2 rK125 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK125 e (h : Coordinate 2) T125_34_2 i :=
  species_entry_eq_sum rK125 ⟨34, by decide⟩ e heK h T125_34_2 hfix125_34_2 hinj125_34_2 hcardT125_34_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨34, by decide⟩) (reps rK125) (T125_34_2 i) (hfix125_34_2 i) h)

/-! ### Cell (125, 40) twin -/

def T125_40_2 : Fin 5 → Coordinate 2 := fun i => T125_40list.getD i.val (0,0,0,0,0)

theorem hfix125_40_2 : ∀ i, ((T125_40_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK125)
    ∈ fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK125) :=
  repsFix_of_siftB2 rK125 ⟨40, by decide⟩ T125_40_2 (by decide)

theorem hinj125_40_2 : Function.Injective
    (fun i => ((T125_40_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK125)) :=
  repsInj_of_reduceAux2 rK125 T125_40_2 (by decide)

theorem hcardT125_40_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK125)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK125 ⟨40, by decide⟩ R125_2 hpxR125_2 hcardq125_2 (by decide)).symm

/-- **Cell (125, 40) twin (q=2).** -/
theorem cell125_40_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK125) e = true)
    (h : ↥(reps (⟨40, by decide⟩ : Fin 148))) :
    species (reps (⟨40, by decide⟩ : Fin 148)) h (basisElt (reps rK125) (charOfVec2 rK125 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK125 e (h : Coordinate 2) T125_40_2 i :=
  species_entry_eq_sum rK125 ⟨40, by decide⟩ e heK h T125_40_2 hfix125_40_2 hinj125_40_2 hcardT125_40_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨40, by decide⟩) (reps rK125) (T125_40_2 i) (hfix125_40_2 i) h)

/-! ### Cell (125, 43) twin -/

def T125_43_2 : Fin 5 → Coordinate 2 := fun i => T125_43list.getD i.val (0,0,0,0,0)

theorem hfix125_43_2 : ∀ i, ((T125_43_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK125)
    ∈ fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK125) :=
  repsFix_of_siftB2 rK125 ⟨43, by decide⟩ T125_43_2 (by decide)

theorem hinj125_43_2 : Function.Injective
    (fun i => ((T125_43_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK125)) :=
  repsInj_of_reduceAux2 rK125 T125_43_2 (by decide)

theorem hcardT125_43_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK125)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK125 ⟨43, by decide⟩ R125_2 hpxR125_2 hcardq125_2 (by decide)).symm

/-- **Cell (125, 43) twin (q=2).** -/
theorem cell125_43_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK125) e = true)
    (h : ↥(reps (⟨43, by decide⟩ : Fin 148))) :
    species (reps (⟨43, by decide⟩ : Fin 148)) h (basisElt (reps rK125) (charOfVec2 rK125 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK125 e (h : Coordinate 2) T125_43_2 i :=
  species_entry_eq_sum rK125 ⟨43, by decide⟩ e heK h T125_43_2 hfix125_43_2 hinj125_43_2 hcardT125_43_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨43, by decide⟩) (reps rK125) (T125_43_2 i) (hfix125_43_2 i) h)

/-! ### Cell (125, 52) twin -/

def T125_52_2 : Fin 5 → Coordinate 2 := fun i => T125_52list.getD i.val (0,0,0,0,0)

theorem hfix125_52_2 : ∀ i, ((T125_52_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK125)
    ∈ fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK125) :=
  repsFix_of_siftB2 rK125 ⟨52, by decide⟩ T125_52_2 (by decide)

theorem hinj125_52_2 : Function.Injective
    (fun i => ((T125_52_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK125)) :=
  repsInj_of_reduceAux2 rK125 T125_52_2 (by decide)

theorem hcardT125_52_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK125)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK125 ⟨52, by decide⟩ R125_2 hpxR125_2 hcardq125_2 (by decide)).symm

/-- **Cell (125, 52) twin (q=2).** -/
theorem cell125_52_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK125) e = true)
    (h : ↥(reps (⟨52, by decide⟩ : Fin 148))) :
    species (reps (⟨52, by decide⟩ : Fin 148)) h (basisElt (reps rK125) (charOfVec2 rK125 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK125 e (h : Coordinate 2) T125_52_2 i :=
  species_entry_eq_sum rK125 ⟨52, by decide⟩ e heK h T125_52_2 hfix125_52_2 hinj125_52_2 hcardT125_52_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨52, by decide⟩) (reps rK125) (T125_52_2 i) (hfix125_52_2 i) h)

/-! ### Cell (125, 53) twin -/

def T125_53_2 : Fin 5 → Coordinate 2 := fun i => T125_53list.getD i.val (0,0,0,0,0)

theorem hfix125_53_2 : ∀ i, ((T125_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK125)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK125) :=
  repsFix_of_siftB2 rK125 ⟨53, by decide⟩ T125_53_2 (by decide)

theorem hinj125_53_2 : Function.Injective
    (fun i => ((T125_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK125)) :=
  repsInj_of_reduceAux2 rK125 T125_53_2 (by decide)

theorem hcardT125_53_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK125)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK125 ⟨53, by decide⟩ R125_2 hpxR125_2 hcardq125_2 (by decide)).symm

/-- **Cell (125, 53) twin (q=2).** -/
theorem cell125_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK125) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK125) (charOfVec2 rK125 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK125 e (h : Coordinate 2) T125_53_2 i :=
  species_entry_eq_sum rK125 ⟨53, by decide⟩ e heK h T125_53_2 hfix125_53_2 hinj125_53_2 hcardT125_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK125) (T125_53_2 i) (hfix125_53_2 i) h)

/-! ### Cell (125, 81) twin -/

def T125_81_2 : Fin 5 → Coordinate 2 := fun i => T125_81list.getD i.val (0,0,0,0,0)

theorem hfix125_81_2 : ∀ i, ((T125_81_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK125)
    ∈ fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK125) :=
  repsFix_of_siftB2 rK125 ⟨81, by decide⟩ T125_81_2 (by decide)

theorem hinj125_81_2 : Function.Injective
    (fun i => ((T125_81_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK125)) :=
  repsInj_of_reduceAux2 rK125 T125_81_2 (by decide)

theorem hcardT125_81_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK125)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK125 ⟨81, by decide⟩ R125_2 hpxR125_2 hcardq125_2 (by decide)).symm

/-- **Cell (125, 81) twin (q=2).** -/
theorem cell125_81_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK125) e = true)
    (h : ↥(reps (⟨81, by decide⟩ : Fin 148))) :
    species (reps (⟨81, by decide⟩ : Fin 148)) h (basisElt (reps rK125) (charOfVec2 rK125 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK125 e (h : Coordinate 2) T125_81_2 i :=
  species_entry_eq_sum rK125 ⟨81, by decide⟩ e heK h T125_81_2 hfix125_81_2 hinj125_81_2 hcardT125_81_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨81, by decide⟩) (reps rK125) (T125_81_2 i) (hfix125_81_2 i) h)

/-! ### Cell (125, 93) twin -/

def T125_93_2 : Fin 5 → Coordinate 2 := fun i => T125_93list.getD i.val (0,0,0,0,0)

theorem hfix125_93_2 : ∀ i, ((T125_93_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK125)
    ∈ fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK125) :=
  repsFix_of_siftB2 rK125 ⟨93, by decide⟩ T125_93_2 (by decide)

theorem hinj125_93_2 : Function.Injective
    (fun i => ((T125_93_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK125)) :=
  repsInj_of_reduceAux2 rK125 T125_93_2 (by decide)

theorem hcardT125_93_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK125)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK125 ⟨93, by decide⟩ R125_2 hpxR125_2 hcardq125_2 (by decide)).symm

/-- **Cell (125, 93) twin (q=2).** -/
theorem cell125_93_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK125) e = true)
    (h : ↥(reps (⟨93, by decide⟩ : Fin 148))) :
    species (reps (⟨93, by decide⟩ : Fin 148)) h (basisElt (reps rK125) (charOfVec2 rK125 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK125 e (h : Coordinate 2) T125_93_2 i :=
  species_entry_eq_sum rK125 ⟨93, by decide⟩ e heK h T125_93_2 hfix125_93_2 hinj125_93_2 hcardT125_93_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨93, by decide⟩) (reps rK125) (T125_93_2 i) (hfix125_93_2 i) h)

/-! ### Cell (125, 96) twin -/

def T125_96_2 : Fin 5 → Coordinate 2 := fun i => T125_96list.getD i.val (0,0,0,0,0)

theorem hfix125_96_2 : ∀ i, ((T125_96_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK125)
    ∈ fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK125) :=
  repsFix_of_siftB2 rK125 ⟨96, by decide⟩ T125_96_2 (by decide)

theorem hinj125_96_2 : Function.Injective
    (fun i => ((T125_96_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK125)) :=
  repsInj_of_reduceAux2 rK125 T125_96_2 (by decide)

theorem hcardT125_96_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK125)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK125 ⟨96, by decide⟩ R125_2 hpxR125_2 hcardq125_2 (by decide)).symm

/-- **Cell (125, 96) twin (q=2).** -/
theorem cell125_96_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK125) e = true)
    (h : ↥(reps (⟨96, by decide⟩ : Fin 148))) :
    species (reps (⟨96, by decide⟩ : Fin 148)) h (basisElt (reps rK125) (charOfVec2 rK125 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK125 e (h : Coordinate 2) T125_96_2 i :=
  species_entry_eq_sum rK125 ⟨96, by decide⟩ e heK h T125_96_2 hfix125_96_2 hinj125_96_2 hcardT125_96_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨96, by decide⟩) (reps rK125) (T125_96_2 i) (hfix125_96_2 i) h)

/-! ### Cell (125, 102) twin -/

def T125_102_2 : Fin 5 → Coordinate 2 := fun i => T125_102list.getD i.val (0,0,0,0,0)

theorem hfix125_102_2 : ∀ i, ((T125_102_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK125)
    ∈ fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK125) :=
  repsFix_of_siftB2 rK125 ⟨102, by decide⟩ T125_102_2 (by decide)

theorem hinj125_102_2 : Function.Injective
    (fun i => ((T125_102_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK125)) :=
  repsInj_of_reduceAux2 rK125 T125_102_2 (by decide)

theorem hcardT125_102_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK125)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK125 ⟨102, by decide⟩ R125_2 hpxR125_2 hcardq125_2 (by decide)).symm

/-- **Cell (125, 102) twin (q=2).** -/
theorem cell125_102_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK125) e = true)
    (h : ↥(reps (⟨102, by decide⟩ : Fin 148))) :
    species (reps (⟨102, by decide⟩ : Fin 148)) h (basisElt (reps rK125) (charOfVec2 rK125 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK125 e (h : Coordinate 2) T125_102_2 i :=
  species_entry_eq_sum rK125 ⟨102, by decide⟩ e heK h T125_102_2 hfix125_102_2 hinj125_102_2 hcardT125_102_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨102, by decide⟩) (reps rK125) (T125_102_2 i) (hfix125_102_2 i) h)

/-! ### Cell (125, 105) twin -/

def T125_105_2 : Fin 5 → Coordinate 2 := fun i => T125_105list.getD i.val (0,0,0,0,0)

theorem hfix125_105_2 : ∀ i, ((T125_105_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK125)
    ∈ fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK125) :=
  repsFix_of_siftB2 rK125 ⟨105, by decide⟩ T125_105_2 (by decide)

theorem hinj125_105_2 : Function.Injective
    (fun i => ((T125_105_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK125)) :=
  repsInj_of_reduceAux2 rK125 T125_105_2 (by decide)

theorem hcardT125_105_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK125)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK125 ⟨105, by decide⟩ R125_2 hpxR125_2 hcardq125_2 (by decide)).symm

/-- **Cell (125, 105) twin (q=2).** -/
theorem cell125_105_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK125) e = true)
    (h : ↥(reps (⟨105, by decide⟩ : Fin 148))) :
    species (reps (⟨105, by decide⟩ : Fin 148)) h (basisElt (reps rK125) (charOfVec2 rK125 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK125 e (h : Coordinate 2) T125_105_2 i :=
  species_entry_eq_sum rK125 ⟨105, by decide⟩ e heK h T125_105_2 hfix125_105_2 hinj125_105_2 hcardT125_105_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨105, by decide⟩) (reps rK125) (T125_105_2 i) (hfix125_105_2 i) h)

/-! ### Cell (125, 114) twin -/

def T125_114_2 : Fin 5 → Coordinate 2 := fun i => T125_114list.getD i.val (0,0,0,0,0)

theorem hfix125_114_2 : ∀ i, ((T125_114_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK125)
    ∈ fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK125) :=
  repsFix_of_siftB2 rK125 ⟨114, by decide⟩ T125_114_2 (by decide)

theorem hinj125_114_2 : Function.Injective
    (fun i => ((T125_114_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK125)) :=
  repsInj_of_reduceAux2 rK125 T125_114_2 (by decide)

theorem hcardT125_114_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK125)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK125 ⟨114, by decide⟩ R125_2 hpxR125_2 hcardq125_2 (by decide)).symm

/-- **Cell (125, 114) twin (q=2).** -/
theorem cell125_114_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK125) e = true)
    (h : ↥(reps (⟨114, by decide⟩ : Fin 148))) :
    species (reps (⟨114, by decide⟩ : Fin 148)) h (basisElt (reps rK125) (charOfVec2 rK125 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK125 e (h : Coordinate 2) T125_114_2 i :=
  species_entry_eq_sum rK125 ⟨114, by decide⟩ e heK h T125_114_2 hfix125_114_2 hinj125_114_2 hcardT125_114_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨114, by decide⟩) (reps rK125) (T125_114_2 i) (hfix125_114_2 i) h)

/-! ### Cell (125, 125) twin -/

def T125_125_2 : Fin 5 → Coordinate 2 := fun i => T125_125list.getD i.val (0,0,0,0,0)

theorem hfix125_125_2 : ∀ i, ((T125_125_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK125)
    ∈ fixedPoints (reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK125) :=
  repsFix_of_siftB2 rK125 ⟨125, by decide⟩ T125_125_2 (by decide)

theorem hinj125_125_2 : Function.Injective
    (fun i => ((T125_125_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK125)) :=
  repsInj_of_reduceAux2 rK125 T125_125_2 (by decide)

theorem hcardT125_125_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK125)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK125 ⟨125, by decide⟩ R125_2 hpxR125_2 hcardq125_2 (by decide)).symm

/-- **Cell (125, 125) twin (q=2).** -/
theorem cell125_125_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK125) e = true)
    (h : ↥(reps (⟨125, by decide⟩ : Fin 148))) :
    species (reps (⟨125, by decide⟩ : Fin 148)) h (basisElt (reps rK125) (charOfVec2 rK125 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK125 e (h : Coordinate 2) T125_125_2 i :=
  species_entry_eq_sum rK125 ⟨125, by decide⟩ e heK h T125_125_2 hfix125_125_2 hinj125_125_2 hcardT125_125_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨125, by decide⟩) (reps rK125) (T125_125_2 i) (hfix125_125_2 i) h)

end Q2

end LeanDring.P5Presentation
