/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, K-strata data (5^4 stratum, rK 132-133): certified per-cell species-entry instantiations, both
twins.

Covers K-classes 132, 133 (order-5^4 K, |R|=5).  For each nonzero `H`-column
(`(G/K)^H ≠ ∅`), the full coset transversal `R132..` and each `H`-fixed
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

/-! # K-class rK = 132  (|G/K| = 5) -/

def rK132 : Fin 148 := ⟨132, by decide⟩

def R132list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def R132 : Fin 5 → Coordinate 1 := fun i => R132list.getD i.val (0,0,0,0,0)

theorem hpxR132 : Function.Injective (fun i => reduceAux 1 (basisAt rK132) (R132 i)) := by decide
theorem hcardq132 : Nat.card (Coordinate 1 ⧸ reps rK132) = 5 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (132, 0): |T| = 5 -/

def T132_0list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T132_0 : Fin 5 → Coordinate 1 := fun i => T132_0list.getD i.val (0,0,0,0,0)

theorem hfix132_0 : ∀ i, ((T132_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK132)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132) :=
  repsFix_of_siftB rK132 ⟨0, by decide⟩ T132_0 (by decide)

theorem hinj132_0 : Function.Injective
    (fun i => ((T132_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK132)) :=
  repsInj_of_reduceAux rK132 T132_0 (by decide)

theorem hcardT132_0 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK132 ⟨0, by decide⟩ R132 hpxR132 hcardq132 (by decide)).symm

/-- **Cell (132, 0).** -/
theorem cell132_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK132) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK132) (charOfVec rK132 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK132 e (h : Coordinate 1) T132_0 i :=
  species_entry_eq_sum rK132 ⟨0, by decide⟩ e heK h T132_0 hfix132_0 hinj132_0 hcardT132_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK132) (T132_0 i) (hfix132_0 i) h)

/-! ## Cell (132, 4): |T| = 5 -/

def T132_4list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T132_4 : Fin 5 → Coordinate 1 := fun i => T132_4list.getD i.val (0,0,0,0,0)

theorem hfix132_4 : ∀ i, ((T132_4 i : Coordinate 1) : Coordinate 1 ⧸ reps rK132)
    ∈ fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132) :=
  repsFix_of_siftB rK132 ⟨4, by decide⟩ T132_4 (by decide)

theorem hinj132_4 : Function.Injective
    (fun i => ((T132_4 i : Coordinate 1) : Coordinate 1 ⧸ reps rK132)) :=
  repsInj_of_reduceAux rK132 T132_4 (by decide)

theorem hcardT132_4 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK132 ⟨4, by decide⟩ R132 hpxR132 hcardq132 (by decide)).symm

/-- **Cell (132, 4).** -/
theorem cell132_4 (e : List (ZMod 25)) (heK : charOK (basisAt rK132) e = true)
    (h : ↥(reps (⟨4, by decide⟩ : Fin 148))) :
    species (reps (⟨4, by decide⟩ : Fin 148)) h (basisElt (reps rK132) (charOfVec rK132 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK132 e (h : Coordinate 1) T132_4 i :=
  species_entry_eq_sum rK132 ⟨4, by decide⟩ e heK h T132_4 hfix132_4 hinj132_4 hcardT132_4
    (fun i => conj_mem_of_fixedPoints (reps ⟨4, by decide⟩) (reps rK132) (T132_4 i) (hfix132_4 i) h)

/-! ## Cell (132, 10): |T| = 5 -/

def T132_10list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T132_10 : Fin 5 → Coordinate 1 := fun i => T132_10list.getD i.val (0,0,0,0,0)

theorem hfix132_10 : ∀ i, ((T132_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK132)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132) :=
  repsFix_of_siftB rK132 ⟨10, by decide⟩ T132_10 (by decide)

theorem hinj132_10 : Function.Injective
    (fun i => ((T132_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK132)) :=
  repsInj_of_reduceAux rK132 T132_10 (by decide)

theorem hcardT132_10 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK132 ⟨10, by decide⟩ R132 hpxR132 hcardq132 (by decide)).symm

/-- **Cell (132, 10).** -/
theorem cell132_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK132) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK132) (charOfVec rK132 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK132 e (h : Coordinate 1) T132_10 i :=
  species_entry_eq_sum rK132 ⟨10, by decide⟩ e heK h T132_10 hfix132_10 hinj132_10 hcardT132_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK132) (T132_10 i) (hfix132_10 i) h)

/-! ## Cell (132, 12): |T| = 5 -/

def T132_12list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T132_12 : Fin 5 → Coordinate 1 := fun i => T132_12list.getD i.val (0,0,0,0,0)

theorem hfix132_12 : ∀ i, ((T132_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK132)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132) :=
  repsFix_of_siftB rK132 ⟨12, by decide⟩ T132_12 (by decide)

theorem hinj132_12 : Function.Injective
    (fun i => ((T132_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK132)) :=
  repsInj_of_reduceAux rK132 T132_12 (by decide)

theorem hcardT132_12 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK132 ⟨12, by decide⟩ R132 hpxR132 hcardq132 (by decide)).symm

/-- **Cell (132, 12).** -/
theorem cell132_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK132) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK132) (charOfVec rK132 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK132 e (h : Coordinate 1) T132_12 i :=
  species_entry_eq_sum rK132 ⟨12, by decide⟩ e heK h T132_12 hfix132_12 hinj132_12 hcardT132_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK132) (T132_12 i) (hfix132_12 i) h)

/-! ## Cell (132, 22): |T| = 5 -/

def T132_22list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T132_22 : Fin 5 → Coordinate 1 := fun i => T132_22list.getD i.val (0,0,0,0,0)

theorem hfix132_22 : ∀ i, ((T132_22 i : Coordinate 1) : Coordinate 1 ⧸ reps rK132)
    ∈ fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132) :=
  repsFix_of_siftB rK132 ⟨22, by decide⟩ T132_22 (by decide)

theorem hinj132_22 : Function.Injective
    (fun i => ((T132_22 i : Coordinate 1) : Coordinate 1 ⧸ reps rK132)) :=
  repsInj_of_reduceAux rK132 T132_22 (by decide)

theorem hcardT132_22 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK132 ⟨22, by decide⟩ R132 hpxR132 hcardq132 (by decide)).symm

/-- **Cell (132, 22).** -/
theorem cell132_22 (e : List (ZMod 25)) (heK : charOK (basisAt rK132) e = true)
    (h : ↥(reps (⟨22, by decide⟩ : Fin 148))) :
    species (reps (⟨22, by decide⟩ : Fin 148)) h (basisElt (reps rK132) (charOfVec rK132 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK132 e (h : Coordinate 1) T132_22 i :=
  species_entry_eq_sum rK132 ⟨22, by decide⟩ e heK h T132_22 hfix132_22 hinj132_22 hcardT132_22
    (fun i => conj_mem_of_fixedPoints (reps ⟨22, by decide⟩) (reps rK132) (T132_22 i) (hfix132_22 i) h)

/-! ## Cell (132, 31): |T| = 5 -/

def T132_31list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T132_31 : Fin 5 → Coordinate 1 := fun i => T132_31list.getD i.val (0,0,0,0,0)

theorem hfix132_31 : ∀ i, ((T132_31 i : Coordinate 1) : Coordinate 1 ⧸ reps rK132)
    ∈ fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132) :=
  repsFix_of_siftB rK132 ⟨31, by decide⟩ T132_31 (by decide)

theorem hinj132_31 : Function.Injective
    (fun i => ((T132_31 i : Coordinate 1) : Coordinate 1 ⧸ reps rK132)) :=
  repsInj_of_reduceAux rK132 T132_31 (by decide)

theorem hcardT132_31 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK132 ⟨31, by decide⟩ R132 hpxR132 hcardq132 (by decide)).symm

/-- **Cell (132, 31).** -/
theorem cell132_31 (e : List (ZMod 25)) (heK : charOK (basisAt rK132) e = true)
    (h : ↥(reps (⟨31, by decide⟩ : Fin 148))) :
    species (reps (⟨31, by decide⟩ : Fin 148)) h (basisElt (reps rK132) (charOfVec rK132 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK132 e (h : Coordinate 1) T132_31 i :=
  species_entry_eq_sum rK132 ⟨31, by decide⟩ e heK h T132_31 hfix132_31 hinj132_31 hcardT132_31
    (fun i => conj_mem_of_fixedPoints (reps ⟨31, by decide⟩) (reps rK132) (T132_31 i) (hfix132_31 i) h)

/-! ## Cell (132, 35): |T| = 5 -/

def T132_35list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T132_35 : Fin 5 → Coordinate 1 := fun i => T132_35list.getD i.val (0,0,0,0,0)

theorem hfix132_35 : ∀ i, ((T132_35 i : Coordinate 1) : Coordinate 1 ⧸ reps rK132)
    ∈ fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132) :=
  repsFix_of_siftB rK132 ⟨35, by decide⟩ T132_35 (by decide)

theorem hinj132_35 : Function.Injective
    (fun i => ((T132_35 i : Coordinate 1) : Coordinate 1 ⧸ reps rK132)) :=
  repsInj_of_reduceAux rK132 T132_35 (by decide)

theorem hcardT132_35 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK132 ⟨35, by decide⟩ R132 hpxR132 hcardq132 (by decide)).symm

/-- **Cell (132, 35).** -/
theorem cell132_35 (e : List (ZMod 25)) (heK : charOK (basisAt rK132) e = true)
    (h : ↥(reps (⟨35, by decide⟩ : Fin 148))) :
    species (reps (⟨35, by decide⟩ : Fin 148)) h (basisElt (reps rK132) (charOfVec rK132 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK132 e (h : Coordinate 1) T132_35 i :=
  species_entry_eq_sum rK132 ⟨35, by decide⟩ e heK h T132_35 hfix132_35 hinj132_35 hcardT132_35
    (fun i => conj_mem_of_fixedPoints (reps ⟨35, by decide⟩) (reps rK132) (T132_35 i) (hfix132_35 i) h)

/-! ## Cell (132, 38): |T| = 5 -/

def T132_38list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T132_38 : Fin 5 → Coordinate 1 := fun i => T132_38list.getD i.val (0,0,0,0,0)

theorem hfix132_38 : ∀ i, ((T132_38 i : Coordinate 1) : Coordinate 1 ⧸ reps rK132)
    ∈ fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132) :=
  repsFix_of_siftB rK132 ⟨38, by decide⟩ T132_38 (by decide)

theorem hinj132_38 : Function.Injective
    (fun i => ((T132_38 i : Coordinate 1) : Coordinate 1 ⧸ reps rK132)) :=
  repsInj_of_reduceAux rK132 T132_38 (by decide)

theorem hcardT132_38 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK132 ⟨38, by decide⟩ R132 hpxR132 hcardq132 (by decide)).symm

/-- **Cell (132, 38).** -/
theorem cell132_38 (e : List (ZMod 25)) (heK : charOK (basisAt rK132) e = true)
    (h : ↥(reps (⟨38, by decide⟩ : Fin 148))) :
    species (reps (⟨38, by decide⟩ : Fin 148)) h (basisElt (reps rK132) (charOfVec rK132 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK132 e (h : Coordinate 1) T132_38 i :=
  species_entry_eq_sum rK132 ⟨38, by decide⟩ e heK h T132_38 hfix132_38 hinj132_38 hcardT132_38
    (fun i => conj_mem_of_fixedPoints (reps ⟨38, by decide⟩) (reps rK132) (T132_38 i) (hfix132_38 i) h)

/-! ## Cell (132, 47): |T| = 5 -/

def T132_47list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T132_47 : Fin 5 → Coordinate 1 := fun i => T132_47list.getD i.val (0,0,0,0,0)

theorem hfix132_47 : ∀ i, ((T132_47 i : Coordinate 1) : Coordinate 1 ⧸ reps rK132)
    ∈ fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132) :=
  repsFix_of_siftB rK132 ⟨47, by decide⟩ T132_47 (by decide)

theorem hinj132_47 : Function.Injective
    (fun i => ((T132_47 i : Coordinate 1) : Coordinate 1 ⧸ reps rK132)) :=
  repsInj_of_reduceAux rK132 T132_47 (by decide)

theorem hcardT132_47 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK132 ⟨47, by decide⟩ R132 hpxR132 hcardq132 (by decide)).symm

/-- **Cell (132, 47).** -/
theorem cell132_47 (e : List (ZMod 25)) (heK : charOK (basisAt rK132) e = true)
    (h : ↥(reps (⟨47, by decide⟩ : Fin 148))) :
    species (reps (⟨47, by decide⟩ : Fin 148)) h (basisElt (reps rK132) (charOfVec rK132 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK132 e (h : Coordinate 1) T132_47 i :=
  species_entry_eq_sum rK132 ⟨47, by decide⟩ e heK h T132_47 hfix132_47 hinj132_47 hcardT132_47
    (fun i => conj_mem_of_fixedPoints (reps ⟨47, by decide⟩) (reps rK132) (T132_47 i) (hfix132_47 i) h)

/-! ## Cell (132, 49): |T| = 5 -/

def T132_49list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T132_49 : Fin 5 → Coordinate 1 := fun i => T132_49list.getD i.val (0,0,0,0,0)

theorem hfix132_49 : ∀ i, ((T132_49 i : Coordinate 1) : Coordinate 1 ⧸ reps rK132)
    ∈ fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132) :=
  repsFix_of_siftB rK132 ⟨49, by decide⟩ T132_49 (by decide)

theorem hinj132_49 : Function.Injective
    (fun i => ((T132_49 i : Coordinate 1) : Coordinate 1 ⧸ reps rK132)) :=
  repsInj_of_reduceAux rK132 T132_49 (by decide)

theorem hcardT132_49 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK132 ⟨49, by decide⟩ R132 hpxR132 hcardq132 (by decide)).symm

/-- **Cell (132, 49).** -/
theorem cell132_49 (e : List (ZMod 25)) (heK : charOK (basisAt rK132) e = true)
    (h : ↥(reps (⟨49, by decide⟩ : Fin 148))) :
    species (reps (⟨49, by decide⟩ : Fin 148)) h (basisElt (reps rK132) (charOfVec rK132 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK132 e (h : Coordinate 1) T132_49 i :=
  species_entry_eq_sum rK132 ⟨49, by decide⟩ e heK h T132_49 hfix132_49 hinj132_49 hcardT132_49
    (fun i => conj_mem_of_fixedPoints (reps ⟨49, by decide⟩) (reps rK132) (T132_49 i) (hfix132_49 i) h)

/-! ## Cell (132, 53): |T| = 5 -/

def T132_53list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T132_53 : Fin 5 → Coordinate 1 := fun i => T132_53list.getD i.val (0,0,0,0,0)

theorem hfix132_53 : ∀ i, ((T132_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK132)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132) :=
  repsFix_of_siftB rK132 ⟨53, by decide⟩ T132_53 (by decide)

theorem hinj132_53 : Function.Injective
    (fun i => ((T132_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK132)) :=
  repsInj_of_reduceAux rK132 T132_53 (by decide)

theorem hcardT132_53 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK132 ⟨53, by decide⟩ R132 hpxR132 hcardq132 (by decide)).symm

/-- **Cell (132, 53).** -/
theorem cell132_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK132) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK132) (charOfVec rK132 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK132 e (h : Coordinate 1) T132_53 i :=
  species_entry_eq_sum rK132 ⟨53, by decide⟩ e heK h T132_53 hfix132_53 hinj132_53 hcardT132_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK132) (T132_53 i) (hfix132_53 i) h)

/-! ## Cell (132, 83): |T| = 5 -/

def T132_83list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T132_83 : Fin 5 → Coordinate 1 := fun i => T132_83list.getD i.val (0,0,0,0,0)

theorem hfix132_83 : ∀ i, ((T132_83 i : Coordinate 1) : Coordinate 1 ⧸ reps rK132)
    ∈ fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132) :=
  repsFix_of_siftB rK132 ⟨83, by decide⟩ T132_83 (by decide)

theorem hinj132_83 : Function.Injective
    (fun i => ((T132_83 i : Coordinate 1) : Coordinate 1 ⧸ reps rK132)) :=
  repsInj_of_reduceAux rK132 T132_83 (by decide)

theorem hcardT132_83 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK132 ⟨83, by decide⟩ R132 hpxR132 hcardq132 (by decide)).symm

/-- **Cell (132, 83).** -/
theorem cell132_83 (e : List (ZMod 25)) (heK : charOK (basisAt rK132) e = true)
    (h : ↥(reps (⟨83, by decide⟩ : Fin 148))) :
    species (reps (⟨83, by decide⟩ : Fin 148)) h (basisElt (reps rK132) (charOfVec rK132 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK132 e (h : Coordinate 1) T132_83 i :=
  species_entry_eq_sum rK132 ⟨83, by decide⟩ e heK h T132_83 hfix132_83 hinj132_83 hcardT132_83
    (fun i => conj_mem_of_fixedPoints (reps ⟨83, by decide⟩) (reps rK132) (T132_83 i) (hfix132_83 i) h)

/-! ## Cell (132, 93): |T| = 5 -/

def T132_93list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T132_93 : Fin 5 → Coordinate 1 := fun i => T132_93list.getD i.val (0,0,0,0,0)

theorem hfix132_93 : ∀ i, ((T132_93 i : Coordinate 1) : Coordinate 1 ⧸ reps rK132)
    ∈ fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132) :=
  repsFix_of_siftB rK132 ⟨93, by decide⟩ T132_93 (by decide)

theorem hinj132_93 : Function.Injective
    (fun i => ((T132_93 i : Coordinate 1) : Coordinate 1 ⧸ reps rK132)) :=
  repsInj_of_reduceAux rK132 T132_93 (by decide)

theorem hcardT132_93 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK132 ⟨93, by decide⟩ R132 hpxR132 hcardq132 (by decide)).symm

/-- **Cell (132, 93).** -/
theorem cell132_93 (e : List (ZMod 25)) (heK : charOK (basisAt rK132) e = true)
    (h : ↥(reps (⟨93, by decide⟩ : Fin 148))) :
    species (reps (⟨93, by decide⟩ : Fin 148)) h (basisElt (reps rK132) (charOfVec rK132 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK132 e (h : Coordinate 1) T132_93 i :=
  species_entry_eq_sum rK132 ⟨93, by decide⟩ e heK h T132_93 hfix132_93 hinj132_93 hcardT132_93
    (fun i => conj_mem_of_fixedPoints (reps ⟨93, by decide⟩) (reps rK132) (T132_93 i) (hfix132_93 i) h)

/-! ## Cell (132, 97): |T| = 5 -/

def T132_97list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T132_97 : Fin 5 → Coordinate 1 := fun i => T132_97list.getD i.val (0,0,0,0,0)

theorem hfix132_97 : ∀ i, ((T132_97 i : Coordinate 1) : Coordinate 1 ⧸ reps rK132)
    ∈ fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132) :=
  repsFix_of_siftB rK132 ⟨97, by decide⟩ T132_97 (by decide)

theorem hinj132_97 : Function.Injective
    (fun i => ((T132_97 i : Coordinate 1) : Coordinate 1 ⧸ reps rK132)) :=
  repsInj_of_reduceAux rK132 T132_97 (by decide)

theorem hcardT132_97 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK132 ⟨97, by decide⟩ R132 hpxR132 hcardq132 (by decide)).symm

/-- **Cell (132, 97).** -/
theorem cell132_97 (e : List (ZMod 25)) (heK : charOK (basisAt rK132) e = true)
    (h : ↥(reps (⟨97, by decide⟩ : Fin 148))) :
    species (reps (⟨97, by decide⟩ : Fin 148)) h (basisElt (reps rK132) (charOfVec rK132 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK132 e (h : Coordinate 1) T132_97 i :=
  species_entry_eq_sum rK132 ⟨97, by decide⟩ e heK h T132_97 hfix132_97 hinj132_97 hcardT132_97
    (fun i => conj_mem_of_fixedPoints (reps ⟨97, by decide⟩) (reps rK132) (T132_97 i) (hfix132_97 i) h)

/-! ## Cell (132, 100): |T| = 5 -/

def T132_100list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T132_100 : Fin 5 → Coordinate 1 := fun i => T132_100list.getD i.val (0,0,0,0,0)

theorem hfix132_100 : ∀ i, ((T132_100 i : Coordinate 1) : Coordinate 1 ⧸ reps rK132)
    ∈ fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132) :=
  repsFix_of_siftB rK132 ⟨100, by decide⟩ T132_100 (by decide)

theorem hinj132_100 : Function.Injective
    (fun i => ((T132_100 i : Coordinate 1) : Coordinate 1 ⧸ reps rK132)) :=
  repsInj_of_reduceAux rK132 T132_100 (by decide)

theorem hcardT132_100 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK132 ⟨100, by decide⟩ R132 hpxR132 hcardq132 (by decide)).symm

/-- **Cell (132, 100).** -/
theorem cell132_100 (e : List (ZMod 25)) (heK : charOK (basisAt rK132) e = true)
    (h : ↥(reps (⟨100, by decide⟩ : Fin 148))) :
    species (reps (⟨100, by decide⟩ : Fin 148)) h (basisElt (reps rK132) (charOfVec rK132 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK132 e (h : Coordinate 1) T132_100 i :=
  species_entry_eq_sum rK132 ⟨100, by decide⟩ e heK h T132_100 hfix132_100 hinj132_100 hcardT132_100
    (fun i => conj_mem_of_fixedPoints (reps ⟨100, by decide⟩) (reps rK132) (T132_100 i) (hfix132_100 i) h)

/-! ## Cell (132, 109): |T| = 5 -/

def T132_109list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T132_109 : Fin 5 → Coordinate 1 := fun i => T132_109list.getD i.val (0,0,0,0,0)

theorem hfix132_109 : ∀ i, ((T132_109 i : Coordinate 1) : Coordinate 1 ⧸ reps rK132)
    ∈ fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132) :=
  repsFix_of_siftB rK132 ⟨109, by decide⟩ T132_109 (by decide)

theorem hinj132_109 : Function.Injective
    (fun i => ((T132_109 i : Coordinate 1) : Coordinate 1 ⧸ reps rK132)) :=
  repsInj_of_reduceAux rK132 T132_109 (by decide)

theorem hcardT132_109 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK132 ⟨109, by decide⟩ R132 hpxR132 hcardq132 (by decide)).symm

/-- **Cell (132, 109).** -/
theorem cell132_109 (e : List (ZMod 25)) (heK : charOK (basisAt rK132) e = true)
    (h : ↥(reps (⟨109, by decide⟩ : Fin 148))) :
    species (reps (⟨109, by decide⟩ : Fin 148)) h (basisElt (reps rK132) (charOfVec rK132 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK132 e (h : Coordinate 1) T132_109 i :=
  species_entry_eq_sum rK132 ⟨109, by decide⟩ e heK h T132_109 hfix132_109 hinj132_109 hcardT132_109
    (fun i => conj_mem_of_fixedPoints (reps ⟨109, by decide⟩) (reps rK132) (T132_109 i) (hfix132_109 i) h)

/-! ## Cell (132, 111): |T| = 5 -/

def T132_111list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T132_111 : Fin 5 → Coordinate 1 := fun i => T132_111list.getD i.val (0,0,0,0,0)

theorem hfix132_111 : ∀ i, ((T132_111 i : Coordinate 1) : Coordinate 1 ⧸ reps rK132)
    ∈ fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132) :=
  repsFix_of_siftB rK132 ⟨111, by decide⟩ T132_111 (by decide)

theorem hinj132_111 : Function.Injective
    (fun i => ((T132_111 i : Coordinate 1) : Coordinate 1 ⧸ reps rK132)) :=
  repsInj_of_reduceAux rK132 T132_111 (by decide)

theorem hcardT132_111 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK132 ⟨111, by decide⟩ R132 hpxR132 hcardq132 (by decide)).symm

/-- **Cell (132, 111).** -/
theorem cell132_111 (e : List (ZMod 25)) (heK : charOK (basisAt rK132) e = true)
    (h : ↥(reps (⟨111, by decide⟩ : Fin 148))) :
    species (reps (⟨111, by decide⟩ : Fin 148)) h (basisElt (reps rK132) (charOfVec rK132 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK132 e (h : Coordinate 1) T132_111 i :=
  species_entry_eq_sum rK132 ⟨111, by decide⟩ e heK h T132_111 hfix132_111 hinj132_111 hcardT132_111
    (fun i => conj_mem_of_fixedPoints (reps ⟨111, by decide⟩) (reps rK132) (T132_111 i) (hfix132_111 i) h)

/-! ## Cell (132, 132): |T| = 5 -/

def T132_132list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T132_132 : Fin 5 → Coordinate 1 := fun i => T132_132list.getD i.val (0,0,0,0,0)

theorem hfix132_132 : ∀ i, ((T132_132 i : Coordinate 1) : Coordinate 1 ⧸ reps rK132)
    ∈ fixedPoints (reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132) :=
  repsFix_of_siftB rK132 ⟨132, by decide⟩ T132_132 (by decide)

theorem hinj132_132 : Function.Injective
    (fun i => ((T132_132 i : Coordinate 1) : Coordinate 1 ⧸ reps rK132)) :=
  repsInj_of_reduceAux rK132 T132_132 (by decide)

theorem hcardT132_132 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK132 ⟨132, by decide⟩ R132 hpxR132 hcardq132 (by decide)).symm

/-- **Cell (132, 132).** -/
theorem cell132_132 (e : List (ZMod 25)) (heK : charOK (basisAt rK132) e = true)
    (h : ↥(reps (⟨132, by decide⟩ : Fin 148))) :
    species (reps (⟨132, by decide⟩ : Fin 148)) h (basisElt (reps rK132) (charOfVec rK132 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK132 e (h : Coordinate 1) T132_132 i :=
  species_entry_eq_sum rK132 ⟨132, by decide⟩ e heK h T132_132 hfix132_132 hinj132_132 hcardT132_132
    (fun i => conj_mem_of_fixedPoints (reps ⟨132, by decide⟩) (reps rK132) (T132_132 i) (hfix132_132 i) h)

namespace Q2

def R132_2 : Fin 5 → Coordinate 2 := fun i => R132list.getD i.val (0,0,0,0,0)
theorem hpxR132_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK132) (R132_2 i)) := by decide
theorem hcardq132_2 : Nat.card (Coordinate 2 ⧸ reps rK132) = 5 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (132, 0) twin -/

def T132_0_2 : Fin 5 → Coordinate 2 := fun i => T132_0list.getD i.val (0,0,0,0,0)

theorem hfix132_0_2 : ∀ i, ((T132_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK132)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK132) :=
  repsFix_of_siftB2 rK132 ⟨0, by decide⟩ T132_0_2 (by decide)

theorem hinj132_0_2 : Function.Injective
    (fun i => ((T132_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK132)) :=
  repsInj_of_reduceAux2 rK132 T132_0_2 (by decide)

theorem hcardT132_0_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK132)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK132 ⟨0, by decide⟩ R132_2 hpxR132_2 hcardq132_2 (by decide)).symm

/-- **Cell (132, 0) twin (q=2).** -/
theorem cell132_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK132) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK132) (charOfVec2 rK132 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK132 e (h : Coordinate 2) T132_0_2 i :=
  species_entry_eq_sum rK132 ⟨0, by decide⟩ e heK h T132_0_2 hfix132_0_2 hinj132_0_2 hcardT132_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK132) (T132_0_2 i) (hfix132_0_2 i) h)

/-! ### Cell (132, 4) twin -/

def T132_4_2 : Fin 5 → Coordinate 2 := fun i => T132_4list.getD i.val (0,0,0,0,0)

theorem hfix132_4_2 : ∀ i, ((T132_4_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK132)
    ∈ fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK132) :=
  repsFix_of_siftB2 rK132 ⟨4, by decide⟩ T132_4_2 (by decide)

theorem hinj132_4_2 : Function.Injective
    (fun i => ((T132_4_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK132)) :=
  repsInj_of_reduceAux2 rK132 T132_4_2 (by decide)

theorem hcardT132_4_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK132)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK132 ⟨4, by decide⟩ R132_2 hpxR132_2 hcardq132_2 (by decide)).symm

/-- **Cell (132, 4) twin (q=2).** -/
theorem cell132_4_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK132) e = true)
    (h : ↥(reps (⟨4, by decide⟩ : Fin 148))) :
    species (reps (⟨4, by decide⟩ : Fin 148)) h (basisElt (reps rK132) (charOfVec2 rK132 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK132 e (h : Coordinate 2) T132_4_2 i :=
  species_entry_eq_sum rK132 ⟨4, by decide⟩ e heK h T132_4_2 hfix132_4_2 hinj132_4_2 hcardT132_4_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨4, by decide⟩) (reps rK132) (T132_4_2 i) (hfix132_4_2 i) h)

/-! ### Cell (132, 10) twin -/

def T132_10_2 : Fin 5 → Coordinate 2 := fun i => T132_10list.getD i.val (0,0,0,0,0)

theorem hfix132_10_2 : ∀ i, ((T132_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK132)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK132) :=
  repsFix_of_siftB2 rK132 ⟨10, by decide⟩ T132_10_2 (by decide)

theorem hinj132_10_2 : Function.Injective
    (fun i => ((T132_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK132)) :=
  repsInj_of_reduceAux2 rK132 T132_10_2 (by decide)

theorem hcardT132_10_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK132)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK132 ⟨10, by decide⟩ R132_2 hpxR132_2 hcardq132_2 (by decide)).symm

/-- **Cell (132, 10) twin (q=2).** -/
theorem cell132_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK132) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK132) (charOfVec2 rK132 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK132 e (h : Coordinate 2) T132_10_2 i :=
  species_entry_eq_sum rK132 ⟨10, by decide⟩ e heK h T132_10_2 hfix132_10_2 hinj132_10_2 hcardT132_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK132) (T132_10_2 i) (hfix132_10_2 i) h)

/-! ### Cell (132, 12) twin -/

def T132_12_2 : Fin 5 → Coordinate 2 := fun i => T132_12list.getD i.val (0,0,0,0,0)

theorem hfix132_12_2 : ∀ i, ((T132_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK132)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK132) :=
  repsFix_of_siftB2 rK132 ⟨12, by decide⟩ T132_12_2 (by decide)

theorem hinj132_12_2 : Function.Injective
    (fun i => ((T132_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK132)) :=
  repsInj_of_reduceAux2 rK132 T132_12_2 (by decide)

theorem hcardT132_12_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK132)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK132 ⟨12, by decide⟩ R132_2 hpxR132_2 hcardq132_2 (by decide)).symm

/-- **Cell (132, 12) twin (q=2).** -/
theorem cell132_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK132) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK132) (charOfVec2 rK132 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK132 e (h : Coordinate 2) T132_12_2 i :=
  species_entry_eq_sum rK132 ⟨12, by decide⟩ e heK h T132_12_2 hfix132_12_2 hinj132_12_2 hcardT132_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK132) (T132_12_2 i) (hfix132_12_2 i) h)

/-! ### Cell (132, 22) twin -/

def T132_22_2 : Fin 5 → Coordinate 2 := fun i => T132_22list.getD i.val (0,0,0,0,0)

theorem hfix132_22_2 : ∀ i, ((T132_22_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK132)
    ∈ fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK132) :=
  repsFix_of_siftB2 rK132 ⟨22, by decide⟩ T132_22_2 (by decide)

theorem hinj132_22_2 : Function.Injective
    (fun i => ((T132_22_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK132)) :=
  repsInj_of_reduceAux2 rK132 T132_22_2 (by decide)

theorem hcardT132_22_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK132)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK132 ⟨22, by decide⟩ R132_2 hpxR132_2 hcardq132_2 (by decide)).symm

/-- **Cell (132, 22) twin (q=2).** -/
theorem cell132_22_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK132) e = true)
    (h : ↥(reps (⟨22, by decide⟩ : Fin 148))) :
    species (reps (⟨22, by decide⟩ : Fin 148)) h (basisElt (reps rK132) (charOfVec2 rK132 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK132 e (h : Coordinate 2) T132_22_2 i :=
  species_entry_eq_sum rK132 ⟨22, by decide⟩ e heK h T132_22_2 hfix132_22_2 hinj132_22_2 hcardT132_22_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨22, by decide⟩) (reps rK132) (T132_22_2 i) (hfix132_22_2 i) h)

/-! ### Cell (132, 31) twin -/

def T132_31_2 : Fin 5 → Coordinate 2 := fun i => T132_31list.getD i.val (0,0,0,0,0)

theorem hfix132_31_2 : ∀ i, ((T132_31_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK132)
    ∈ fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK132) :=
  repsFix_of_siftB2 rK132 ⟨31, by decide⟩ T132_31_2 (by decide)

theorem hinj132_31_2 : Function.Injective
    (fun i => ((T132_31_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK132)) :=
  repsInj_of_reduceAux2 rK132 T132_31_2 (by decide)

theorem hcardT132_31_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK132)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK132 ⟨31, by decide⟩ R132_2 hpxR132_2 hcardq132_2 (by decide)).symm

/-- **Cell (132, 31) twin (q=2).** -/
theorem cell132_31_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK132) e = true)
    (h : ↥(reps (⟨31, by decide⟩ : Fin 148))) :
    species (reps (⟨31, by decide⟩ : Fin 148)) h (basisElt (reps rK132) (charOfVec2 rK132 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK132 e (h : Coordinate 2) T132_31_2 i :=
  species_entry_eq_sum rK132 ⟨31, by decide⟩ e heK h T132_31_2 hfix132_31_2 hinj132_31_2 hcardT132_31_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨31, by decide⟩) (reps rK132) (T132_31_2 i) (hfix132_31_2 i) h)

/-! ### Cell (132, 35) twin -/

def T132_35_2 : Fin 5 → Coordinate 2 := fun i => T132_35list.getD i.val (0,0,0,0,0)

theorem hfix132_35_2 : ∀ i, ((T132_35_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK132)
    ∈ fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK132) :=
  repsFix_of_siftB2 rK132 ⟨35, by decide⟩ T132_35_2 (by decide)

theorem hinj132_35_2 : Function.Injective
    (fun i => ((T132_35_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK132)) :=
  repsInj_of_reduceAux2 rK132 T132_35_2 (by decide)

theorem hcardT132_35_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK132)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK132 ⟨35, by decide⟩ R132_2 hpxR132_2 hcardq132_2 (by decide)).symm

/-- **Cell (132, 35) twin (q=2).** -/
theorem cell132_35_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK132) e = true)
    (h : ↥(reps (⟨35, by decide⟩ : Fin 148))) :
    species (reps (⟨35, by decide⟩ : Fin 148)) h (basisElt (reps rK132) (charOfVec2 rK132 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK132 e (h : Coordinate 2) T132_35_2 i :=
  species_entry_eq_sum rK132 ⟨35, by decide⟩ e heK h T132_35_2 hfix132_35_2 hinj132_35_2 hcardT132_35_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨35, by decide⟩) (reps rK132) (T132_35_2 i) (hfix132_35_2 i) h)

/-! ### Cell (132, 38) twin -/

def T132_38_2 : Fin 5 → Coordinate 2 := fun i => T132_38list.getD i.val (0,0,0,0,0)

theorem hfix132_38_2 : ∀ i, ((T132_38_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK132)
    ∈ fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK132) :=
  repsFix_of_siftB2 rK132 ⟨38, by decide⟩ T132_38_2 (by decide)

theorem hinj132_38_2 : Function.Injective
    (fun i => ((T132_38_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK132)) :=
  repsInj_of_reduceAux2 rK132 T132_38_2 (by decide)

theorem hcardT132_38_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK132)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK132 ⟨38, by decide⟩ R132_2 hpxR132_2 hcardq132_2 (by decide)).symm

/-- **Cell (132, 38) twin (q=2).** -/
theorem cell132_38_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK132) e = true)
    (h : ↥(reps (⟨38, by decide⟩ : Fin 148))) :
    species (reps (⟨38, by decide⟩ : Fin 148)) h (basisElt (reps rK132) (charOfVec2 rK132 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK132 e (h : Coordinate 2) T132_38_2 i :=
  species_entry_eq_sum rK132 ⟨38, by decide⟩ e heK h T132_38_2 hfix132_38_2 hinj132_38_2 hcardT132_38_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨38, by decide⟩) (reps rK132) (T132_38_2 i) (hfix132_38_2 i) h)

/-! ### Cell (132, 47) twin -/

def T132_47_2 : Fin 5 → Coordinate 2 := fun i => T132_47list.getD i.val (0,0,0,0,0)

theorem hfix132_47_2 : ∀ i, ((T132_47_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK132)
    ∈ fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK132) :=
  repsFix_of_siftB2 rK132 ⟨47, by decide⟩ T132_47_2 (by decide)

theorem hinj132_47_2 : Function.Injective
    (fun i => ((T132_47_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK132)) :=
  repsInj_of_reduceAux2 rK132 T132_47_2 (by decide)

theorem hcardT132_47_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK132)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK132 ⟨47, by decide⟩ R132_2 hpxR132_2 hcardq132_2 (by decide)).symm

/-- **Cell (132, 47) twin (q=2).** -/
theorem cell132_47_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK132) e = true)
    (h : ↥(reps (⟨47, by decide⟩ : Fin 148))) :
    species (reps (⟨47, by decide⟩ : Fin 148)) h (basisElt (reps rK132) (charOfVec2 rK132 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK132 e (h : Coordinate 2) T132_47_2 i :=
  species_entry_eq_sum rK132 ⟨47, by decide⟩ e heK h T132_47_2 hfix132_47_2 hinj132_47_2 hcardT132_47_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨47, by decide⟩) (reps rK132) (T132_47_2 i) (hfix132_47_2 i) h)

/-! ### Cell (132, 49) twin -/

def T132_49_2 : Fin 5 → Coordinate 2 := fun i => T132_49list.getD i.val (0,0,0,0,0)

theorem hfix132_49_2 : ∀ i, ((T132_49_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK132)
    ∈ fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK132) :=
  repsFix_of_siftB2 rK132 ⟨49, by decide⟩ T132_49_2 (by decide)

theorem hinj132_49_2 : Function.Injective
    (fun i => ((T132_49_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK132)) :=
  repsInj_of_reduceAux2 rK132 T132_49_2 (by decide)

theorem hcardT132_49_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK132)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK132 ⟨49, by decide⟩ R132_2 hpxR132_2 hcardq132_2 (by decide)).symm

/-- **Cell (132, 49) twin (q=2).** -/
theorem cell132_49_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK132) e = true)
    (h : ↥(reps (⟨49, by decide⟩ : Fin 148))) :
    species (reps (⟨49, by decide⟩ : Fin 148)) h (basisElt (reps rK132) (charOfVec2 rK132 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK132 e (h : Coordinate 2) T132_49_2 i :=
  species_entry_eq_sum rK132 ⟨49, by decide⟩ e heK h T132_49_2 hfix132_49_2 hinj132_49_2 hcardT132_49_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨49, by decide⟩) (reps rK132) (T132_49_2 i) (hfix132_49_2 i) h)

/-! ### Cell (132, 53) twin -/

def T132_53_2 : Fin 5 → Coordinate 2 := fun i => T132_53list.getD i.val (0,0,0,0,0)

theorem hfix132_53_2 : ∀ i, ((T132_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK132)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK132) :=
  repsFix_of_siftB2 rK132 ⟨53, by decide⟩ T132_53_2 (by decide)

theorem hinj132_53_2 : Function.Injective
    (fun i => ((T132_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK132)) :=
  repsInj_of_reduceAux2 rK132 T132_53_2 (by decide)

theorem hcardT132_53_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK132)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK132 ⟨53, by decide⟩ R132_2 hpxR132_2 hcardq132_2 (by decide)).symm

/-- **Cell (132, 53) twin (q=2).** -/
theorem cell132_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK132) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK132) (charOfVec2 rK132 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK132 e (h : Coordinate 2) T132_53_2 i :=
  species_entry_eq_sum rK132 ⟨53, by decide⟩ e heK h T132_53_2 hfix132_53_2 hinj132_53_2 hcardT132_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK132) (T132_53_2 i) (hfix132_53_2 i) h)

/-! ### Cell (132, 83) twin -/

def T132_83_2 : Fin 5 → Coordinate 2 := fun i => T132_83list.getD i.val (0,0,0,0,0)

theorem hfix132_83_2 : ∀ i, ((T132_83_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK132)
    ∈ fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK132) :=
  repsFix_of_siftB2 rK132 ⟨83, by decide⟩ T132_83_2 (by decide)

theorem hinj132_83_2 : Function.Injective
    (fun i => ((T132_83_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK132)) :=
  repsInj_of_reduceAux2 rK132 T132_83_2 (by decide)

theorem hcardT132_83_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK132)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK132 ⟨83, by decide⟩ R132_2 hpxR132_2 hcardq132_2 (by decide)).symm

/-- **Cell (132, 83) twin (q=2).** -/
theorem cell132_83_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK132) e = true)
    (h : ↥(reps (⟨83, by decide⟩ : Fin 148))) :
    species (reps (⟨83, by decide⟩ : Fin 148)) h (basisElt (reps rK132) (charOfVec2 rK132 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK132 e (h : Coordinate 2) T132_83_2 i :=
  species_entry_eq_sum rK132 ⟨83, by decide⟩ e heK h T132_83_2 hfix132_83_2 hinj132_83_2 hcardT132_83_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨83, by decide⟩) (reps rK132) (T132_83_2 i) (hfix132_83_2 i) h)

/-! ### Cell (132, 93) twin -/

def T132_93_2 : Fin 5 → Coordinate 2 := fun i => T132_93list.getD i.val (0,0,0,0,0)

theorem hfix132_93_2 : ∀ i, ((T132_93_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK132)
    ∈ fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK132) :=
  repsFix_of_siftB2 rK132 ⟨93, by decide⟩ T132_93_2 (by decide)

theorem hinj132_93_2 : Function.Injective
    (fun i => ((T132_93_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK132)) :=
  repsInj_of_reduceAux2 rK132 T132_93_2 (by decide)

theorem hcardT132_93_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK132)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK132 ⟨93, by decide⟩ R132_2 hpxR132_2 hcardq132_2 (by decide)).symm

/-- **Cell (132, 93) twin (q=2).** -/
theorem cell132_93_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK132) e = true)
    (h : ↥(reps (⟨93, by decide⟩ : Fin 148))) :
    species (reps (⟨93, by decide⟩ : Fin 148)) h (basisElt (reps rK132) (charOfVec2 rK132 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK132 e (h : Coordinate 2) T132_93_2 i :=
  species_entry_eq_sum rK132 ⟨93, by decide⟩ e heK h T132_93_2 hfix132_93_2 hinj132_93_2 hcardT132_93_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨93, by decide⟩) (reps rK132) (T132_93_2 i) (hfix132_93_2 i) h)

/-! ### Cell (132, 97) twin -/

def T132_97_2 : Fin 5 → Coordinate 2 := fun i => T132_97list.getD i.val (0,0,0,0,0)

theorem hfix132_97_2 : ∀ i, ((T132_97_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK132)
    ∈ fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK132) :=
  repsFix_of_siftB2 rK132 ⟨97, by decide⟩ T132_97_2 (by decide)

theorem hinj132_97_2 : Function.Injective
    (fun i => ((T132_97_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK132)) :=
  repsInj_of_reduceAux2 rK132 T132_97_2 (by decide)

theorem hcardT132_97_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK132)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK132 ⟨97, by decide⟩ R132_2 hpxR132_2 hcardq132_2 (by decide)).symm

/-- **Cell (132, 97) twin (q=2).** -/
theorem cell132_97_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK132) e = true)
    (h : ↥(reps (⟨97, by decide⟩ : Fin 148))) :
    species (reps (⟨97, by decide⟩ : Fin 148)) h (basisElt (reps rK132) (charOfVec2 rK132 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK132 e (h : Coordinate 2) T132_97_2 i :=
  species_entry_eq_sum rK132 ⟨97, by decide⟩ e heK h T132_97_2 hfix132_97_2 hinj132_97_2 hcardT132_97_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨97, by decide⟩) (reps rK132) (T132_97_2 i) (hfix132_97_2 i) h)

/-! ### Cell (132, 100) twin -/

def T132_100_2 : Fin 5 → Coordinate 2 := fun i => T132_100list.getD i.val (0,0,0,0,0)

theorem hfix132_100_2 : ∀ i, ((T132_100_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK132)
    ∈ fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK132) :=
  repsFix_of_siftB2 rK132 ⟨100, by decide⟩ T132_100_2 (by decide)

theorem hinj132_100_2 : Function.Injective
    (fun i => ((T132_100_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK132)) :=
  repsInj_of_reduceAux2 rK132 T132_100_2 (by decide)

theorem hcardT132_100_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK132)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK132 ⟨100, by decide⟩ R132_2 hpxR132_2 hcardq132_2 (by decide)).symm

/-- **Cell (132, 100) twin (q=2).** -/
theorem cell132_100_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK132) e = true)
    (h : ↥(reps (⟨100, by decide⟩ : Fin 148))) :
    species (reps (⟨100, by decide⟩ : Fin 148)) h (basisElt (reps rK132) (charOfVec2 rK132 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK132 e (h : Coordinate 2) T132_100_2 i :=
  species_entry_eq_sum rK132 ⟨100, by decide⟩ e heK h T132_100_2 hfix132_100_2 hinj132_100_2 hcardT132_100_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨100, by decide⟩) (reps rK132) (T132_100_2 i) (hfix132_100_2 i) h)

/-! ### Cell (132, 109) twin -/

def T132_109_2 : Fin 5 → Coordinate 2 := fun i => T132_109list.getD i.val (0,0,0,0,0)

theorem hfix132_109_2 : ∀ i, ((T132_109_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK132)
    ∈ fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK132) :=
  repsFix_of_siftB2 rK132 ⟨109, by decide⟩ T132_109_2 (by decide)

theorem hinj132_109_2 : Function.Injective
    (fun i => ((T132_109_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK132)) :=
  repsInj_of_reduceAux2 rK132 T132_109_2 (by decide)

theorem hcardT132_109_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK132)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK132 ⟨109, by decide⟩ R132_2 hpxR132_2 hcardq132_2 (by decide)).symm

/-- **Cell (132, 109) twin (q=2).** -/
theorem cell132_109_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK132) e = true)
    (h : ↥(reps (⟨109, by decide⟩ : Fin 148))) :
    species (reps (⟨109, by decide⟩ : Fin 148)) h (basisElt (reps rK132) (charOfVec2 rK132 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK132 e (h : Coordinate 2) T132_109_2 i :=
  species_entry_eq_sum rK132 ⟨109, by decide⟩ e heK h T132_109_2 hfix132_109_2 hinj132_109_2 hcardT132_109_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨109, by decide⟩) (reps rK132) (T132_109_2 i) (hfix132_109_2 i) h)

/-! ### Cell (132, 111) twin -/

def T132_111_2 : Fin 5 → Coordinate 2 := fun i => T132_111list.getD i.val (0,0,0,0,0)

theorem hfix132_111_2 : ∀ i, ((T132_111_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK132)
    ∈ fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK132) :=
  repsFix_of_siftB2 rK132 ⟨111, by decide⟩ T132_111_2 (by decide)

theorem hinj132_111_2 : Function.Injective
    (fun i => ((T132_111_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK132)) :=
  repsInj_of_reduceAux2 rK132 T132_111_2 (by decide)

theorem hcardT132_111_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK132)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK132 ⟨111, by decide⟩ R132_2 hpxR132_2 hcardq132_2 (by decide)).symm

/-- **Cell (132, 111) twin (q=2).** -/
theorem cell132_111_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK132) e = true)
    (h : ↥(reps (⟨111, by decide⟩ : Fin 148))) :
    species (reps (⟨111, by decide⟩ : Fin 148)) h (basisElt (reps rK132) (charOfVec2 rK132 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK132 e (h : Coordinate 2) T132_111_2 i :=
  species_entry_eq_sum rK132 ⟨111, by decide⟩ e heK h T132_111_2 hfix132_111_2 hinj132_111_2 hcardT132_111_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨111, by decide⟩) (reps rK132) (T132_111_2 i) (hfix132_111_2 i) h)

/-! ### Cell (132, 132) twin -/

def T132_132_2 : Fin 5 → Coordinate 2 := fun i => T132_132list.getD i.val (0,0,0,0,0)

theorem hfix132_132_2 : ∀ i, ((T132_132_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK132)
    ∈ fixedPoints (reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK132) :=
  repsFix_of_siftB2 rK132 ⟨132, by decide⟩ T132_132_2 (by decide)

theorem hinj132_132_2 : Function.Injective
    (fun i => ((T132_132_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK132)) :=
  repsInj_of_reduceAux2 rK132 T132_132_2 (by decide)

theorem hcardT132_132_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK132)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK132 ⟨132, by decide⟩ R132_2 hpxR132_2 hcardq132_2 (by decide)).symm

/-- **Cell (132, 132) twin (q=2).** -/
theorem cell132_132_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK132) e = true)
    (h : ↥(reps (⟨132, by decide⟩ : Fin 148))) :
    species (reps (⟨132, by decide⟩ : Fin 148)) h (basisElt (reps rK132) (charOfVec2 rK132 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK132 e (h : Coordinate 2) T132_132_2 i :=
  species_entry_eq_sum rK132 ⟨132, by decide⟩ e heK h T132_132_2 hfix132_132_2 hinj132_132_2 hcardT132_132_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨132, by decide⟩) (reps rK132) (T132_132_2 i) (hfix132_132_2 i) h)

end Q2

/-! # K-class rK = 133  (|G/K| = 5) -/

def rK133 : Fin 148 := ⟨133, by decide⟩

def R133list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def R133 : Fin 5 → Coordinate 1 := fun i => R133list.getD i.val (0,0,0,0,0)

theorem hpxR133 : Function.Injective (fun i => reduceAux 1 (basisAt rK133) (R133 i)) := by decide
theorem hcardq133 : Nat.card (Coordinate 1 ⧸ reps rK133) = 5 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (133, 0): |T| = 5 -/

def T133_0list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T133_0 : Fin 5 → Coordinate 1 := fun i => T133_0list.getD i.val (0,0,0,0,0)

theorem hfix133_0 : ∀ i, ((T133_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK133)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133) :=
  repsFix_of_siftB rK133 ⟨0, by decide⟩ T133_0 (by decide)

theorem hinj133_0 : Function.Injective
    (fun i => ((T133_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK133)) :=
  repsInj_of_reduceAux rK133 T133_0 (by decide)

theorem hcardT133_0 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK133 ⟨0, by decide⟩ R133 hpxR133 hcardq133 (by decide)).symm

/-- **Cell (133, 0).** -/
theorem cell133_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK133) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK133) (charOfVec rK133 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK133 e (h : Coordinate 1) T133_0 i :=
  species_entry_eq_sum rK133 ⟨0, by decide⟩ e heK h T133_0 hfix133_0 hinj133_0 hcardT133_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK133) (T133_0 i) (hfix133_0 i) h)

/-! ## Cell (133, 4): |T| = 5 -/

def T133_4list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T133_4 : Fin 5 → Coordinate 1 := fun i => T133_4list.getD i.val (0,0,0,0,0)

theorem hfix133_4 : ∀ i, ((T133_4 i : Coordinate 1) : Coordinate 1 ⧸ reps rK133)
    ∈ fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133) :=
  repsFix_of_siftB rK133 ⟨4, by decide⟩ T133_4 (by decide)

theorem hinj133_4 : Function.Injective
    (fun i => ((T133_4 i : Coordinate 1) : Coordinate 1 ⧸ reps rK133)) :=
  repsInj_of_reduceAux rK133 T133_4 (by decide)

theorem hcardT133_4 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK133 ⟨4, by decide⟩ R133 hpxR133 hcardq133 (by decide)).symm

/-- **Cell (133, 4).** -/
theorem cell133_4 (e : List (ZMod 25)) (heK : charOK (basisAt rK133) e = true)
    (h : ↥(reps (⟨4, by decide⟩ : Fin 148))) :
    species (reps (⟨4, by decide⟩ : Fin 148)) h (basisElt (reps rK133) (charOfVec rK133 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK133 e (h : Coordinate 1) T133_4 i :=
  species_entry_eq_sum rK133 ⟨4, by decide⟩ e heK h T133_4 hfix133_4 hinj133_4 hcardT133_4
    (fun i => conj_mem_of_fixedPoints (reps ⟨4, by decide⟩) (reps rK133) (T133_4 i) (hfix133_4 i) h)

/-! ## Cell (133, 10): |T| = 5 -/

def T133_10list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T133_10 : Fin 5 → Coordinate 1 := fun i => T133_10list.getD i.val (0,0,0,0,0)

theorem hfix133_10 : ∀ i, ((T133_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK133)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133) :=
  repsFix_of_siftB rK133 ⟨10, by decide⟩ T133_10 (by decide)

theorem hinj133_10 : Function.Injective
    (fun i => ((T133_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK133)) :=
  repsInj_of_reduceAux rK133 T133_10 (by decide)

theorem hcardT133_10 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK133 ⟨10, by decide⟩ R133 hpxR133 hcardq133 (by decide)).symm

/-- **Cell (133, 10).** -/
theorem cell133_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK133) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK133) (charOfVec rK133 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK133 e (h : Coordinate 1) T133_10 i :=
  species_entry_eq_sum rK133 ⟨10, by decide⟩ e heK h T133_10 hfix133_10 hinj133_10 hcardT133_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK133) (T133_10 i) (hfix133_10 i) h)

/-! ## Cell (133, 12): |T| = 5 -/

def T133_12list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T133_12 : Fin 5 → Coordinate 1 := fun i => T133_12list.getD i.val (0,0,0,0,0)

theorem hfix133_12 : ∀ i, ((T133_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK133)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133) :=
  repsFix_of_siftB rK133 ⟨12, by decide⟩ T133_12 (by decide)

theorem hinj133_12 : Function.Injective
    (fun i => ((T133_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK133)) :=
  repsInj_of_reduceAux rK133 T133_12 (by decide)

theorem hcardT133_12 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK133 ⟨12, by decide⟩ R133 hpxR133 hcardq133 (by decide)).symm

/-- **Cell (133, 12).** -/
theorem cell133_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK133) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK133) (charOfVec rK133 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK133 e (h : Coordinate 1) T133_12 i :=
  species_entry_eq_sum rK133 ⟨12, by decide⟩ e heK h T133_12 hfix133_12 hinj133_12 hcardT133_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK133) (T133_12 i) (hfix133_12 i) h)

/-! ## Cell (133, 22): |T| = 5 -/

def T133_22list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T133_22 : Fin 5 → Coordinate 1 := fun i => T133_22list.getD i.val (0,0,0,0,0)

theorem hfix133_22 : ∀ i, ((T133_22 i : Coordinate 1) : Coordinate 1 ⧸ reps rK133)
    ∈ fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133) :=
  repsFix_of_siftB rK133 ⟨22, by decide⟩ T133_22 (by decide)

theorem hinj133_22 : Function.Injective
    (fun i => ((T133_22 i : Coordinate 1) : Coordinate 1 ⧸ reps rK133)) :=
  repsInj_of_reduceAux rK133 T133_22 (by decide)

theorem hcardT133_22 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK133 ⟨22, by decide⟩ R133 hpxR133 hcardq133 (by decide)).symm

/-- **Cell (133, 22).** -/
theorem cell133_22 (e : List (ZMod 25)) (heK : charOK (basisAt rK133) e = true)
    (h : ↥(reps (⟨22, by decide⟩ : Fin 148))) :
    species (reps (⟨22, by decide⟩ : Fin 148)) h (basisElt (reps rK133) (charOfVec rK133 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK133 e (h : Coordinate 1) T133_22 i :=
  species_entry_eq_sum rK133 ⟨22, by decide⟩ e heK h T133_22 hfix133_22 hinj133_22 hcardT133_22
    (fun i => conj_mem_of_fixedPoints (reps ⟨22, by decide⟩) (reps rK133) (T133_22 i) (hfix133_22 i) h)

/-! ## Cell (133, 32): |T| = 5 -/

def T133_32list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T133_32 : Fin 5 → Coordinate 1 := fun i => T133_32list.getD i.val (0,0,0,0,0)

theorem hfix133_32 : ∀ i, ((T133_32 i : Coordinate 1) : Coordinate 1 ⧸ reps rK133)
    ∈ fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133) :=
  repsFix_of_siftB rK133 ⟨32, by decide⟩ T133_32 (by decide)

theorem hinj133_32 : Function.Injective
    (fun i => ((T133_32 i : Coordinate 1) : Coordinate 1 ⧸ reps rK133)) :=
  repsInj_of_reduceAux rK133 T133_32 (by decide)

theorem hcardT133_32 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK133 ⟨32, by decide⟩ R133 hpxR133 hcardq133 (by decide)).symm

/-- **Cell (133, 32).** -/
theorem cell133_32 (e : List (ZMod 25)) (heK : charOK (basisAt rK133) e = true)
    (h : ↥(reps (⟨32, by decide⟩ : Fin 148))) :
    species (reps (⟨32, by decide⟩ : Fin 148)) h (basisElt (reps rK133) (charOfVec rK133 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK133 e (h : Coordinate 1) T133_32 i :=
  species_entry_eq_sum rK133 ⟨32, by decide⟩ e heK h T133_32 hfix133_32 hinj133_32 hcardT133_32
    (fun i => conj_mem_of_fixedPoints (reps ⟨32, by decide⟩) (reps rK133) (T133_32 i) (hfix133_32 i) h)

/-! ## Cell (133, 36): |T| = 5 -/

def T133_36list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T133_36 : Fin 5 → Coordinate 1 := fun i => T133_36list.getD i.val (0,0,0,0,0)

theorem hfix133_36 : ∀ i, ((T133_36 i : Coordinate 1) : Coordinate 1 ⧸ reps rK133)
    ∈ fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133) :=
  repsFix_of_siftB rK133 ⟨36, by decide⟩ T133_36 (by decide)

theorem hinj133_36 : Function.Injective
    (fun i => ((T133_36 i : Coordinate 1) : Coordinate 1 ⧸ reps rK133)) :=
  repsInj_of_reduceAux rK133 T133_36 (by decide)

theorem hcardT133_36 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK133 ⟨36, by decide⟩ R133 hpxR133 hcardq133 (by decide)).symm

/-- **Cell (133, 36).** -/
theorem cell133_36 (e : List (ZMod 25)) (heK : charOK (basisAt rK133) e = true)
    (h : ↥(reps (⟨36, by decide⟩ : Fin 148))) :
    species (reps (⟨36, by decide⟩ : Fin 148)) h (basisElt (reps rK133) (charOfVec rK133 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK133 e (h : Coordinate 1) T133_36 i :=
  species_entry_eq_sum rK133 ⟨36, by decide⟩ e heK h T133_36 hfix133_36 hinj133_36 hcardT133_36
    (fun i => conj_mem_of_fixedPoints (reps ⟨36, by decide⟩) (reps rK133) (T133_36 i) (hfix133_36 i) h)

/-! ## Cell (133, 39): |T| = 5 -/

def T133_39list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T133_39 : Fin 5 → Coordinate 1 := fun i => T133_39list.getD i.val (0,0,0,0,0)

theorem hfix133_39 : ∀ i, ((T133_39 i : Coordinate 1) : Coordinate 1 ⧸ reps rK133)
    ∈ fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133) :=
  repsFix_of_siftB rK133 ⟨39, by decide⟩ T133_39 (by decide)

theorem hinj133_39 : Function.Injective
    (fun i => ((T133_39 i : Coordinate 1) : Coordinate 1 ⧸ reps rK133)) :=
  repsInj_of_reduceAux rK133 T133_39 (by decide)

theorem hcardT133_39 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK133 ⟨39, by decide⟩ R133 hpxR133 hcardq133 (by decide)).symm

/-- **Cell (133, 39).** -/
theorem cell133_39 (e : List (ZMod 25)) (heK : charOK (basisAt rK133) e = true)
    (h : ↥(reps (⟨39, by decide⟩ : Fin 148))) :
    species (reps (⟨39, by decide⟩ : Fin 148)) h (basisElt (reps rK133) (charOfVec rK133 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK133 e (h : Coordinate 1) T133_39 i :=
  species_entry_eq_sum rK133 ⟨39, by decide⟩ e heK h T133_39 hfix133_39 hinj133_39 hcardT133_39
    (fun i => conj_mem_of_fixedPoints (reps ⟨39, by decide⟩) (reps rK133) (T133_39 i) (hfix133_39 i) h)

/-! ## Cell (133, 43): |T| = 5 -/

def T133_43list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T133_43 : Fin 5 → Coordinate 1 := fun i => T133_43list.getD i.val (0,0,0,0,0)

theorem hfix133_43 : ∀ i, ((T133_43 i : Coordinate 1) : Coordinate 1 ⧸ reps rK133)
    ∈ fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133) :=
  repsFix_of_siftB rK133 ⟨43, by decide⟩ T133_43 (by decide)

theorem hinj133_43 : Function.Injective
    (fun i => ((T133_43 i : Coordinate 1) : Coordinate 1 ⧸ reps rK133)) :=
  repsInj_of_reduceAux rK133 T133_43 (by decide)

theorem hcardT133_43 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK133 ⟨43, by decide⟩ R133 hpxR133 hcardq133 (by decide)).symm

/-- **Cell (133, 43).** -/
theorem cell133_43 (e : List (ZMod 25)) (heK : charOK (basisAt rK133) e = true)
    (h : ↥(reps (⟨43, by decide⟩ : Fin 148))) :
    species (reps (⟨43, by decide⟩ : Fin 148)) h (basisElt (reps rK133) (charOfVec rK133 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK133 e (h : Coordinate 1) T133_43 i :=
  species_entry_eq_sum rK133 ⟨43, by decide⟩ e heK h T133_43 hfix133_43 hinj133_43 hcardT133_43
    (fun i => conj_mem_of_fixedPoints (reps ⟨43, by decide⟩) (reps rK133) (T133_43 i) (hfix133_43 i) h)

/-! ## Cell (133, 50): |T| = 5 -/

def T133_50list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T133_50 : Fin 5 → Coordinate 1 := fun i => T133_50list.getD i.val (0,0,0,0,0)

theorem hfix133_50 : ∀ i, ((T133_50 i : Coordinate 1) : Coordinate 1 ⧸ reps rK133)
    ∈ fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133) :=
  repsFix_of_siftB rK133 ⟨50, by decide⟩ T133_50 (by decide)

theorem hinj133_50 : Function.Injective
    (fun i => ((T133_50 i : Coordinate 1) : Coordinate 1 ⧸ reps rK133)) :=
  repsInj_of_reduceAux rK133 T133_50 (by decide)

theorem hcardT133_50 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK133 ⟨50, by decide⟩ R133 hpxR133 hcardq133 (by decide)).symm

/-- **Cell (133, 50).** -/
theorem cell133_50 (e : List (ZMod 25)) (heK : charOK (basisAt rK133) e = true)
    (h : ↥(reps (⟨50, by decide⟩ : Fin 148))) :
    species (reps (⟨50, by decide⟩ : Fin 148)) h (basisElt (reps rK133) (charOfVec rK133 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK133 e (h : Coordinate 1) T133_50 i :=
  species_entry_eq_sum rK133 ⟨50, by decide⟩ e heK h T133_50 hfix133_50 hinj133_50 hcardT133_50
    (fun i => conj_mem_of_fixedPoints (reps ⟨50, by decide⟩) (reps rK133) (T133_50 i) (hfix133_50 i) h)

/-! ## Cell (133, 53): |T| = 5 -/

def T133_53list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T133_53 : Fin 5 → Coordinate 1 := fun i => T133_53list.getD i.val (0,0,0,0,0)

theorem hfix133_53 : ∀ i, ((T133_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK133)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133) :=
  repsFix_of_siftB rK133 ⟨53, by decide⟩ T133_53 (by decide)

theorem hinj133_53 : Function.Injective
    (fun i => ((T133_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK133)) :=
  repsInj_of_reduceAux rK133 T133_53 (by decide)

theorem hcardT133_53 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK133 ⟨53, by decide⟩ R133 hpxR133 hcardq133 (by decide)).symm

/-- **Cell (133, 53).** -/
theorem cell133_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK133) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK133) (charOfVec rK133 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK133 e (h : Coordinate 1) T133_53 i :=
  species_entry_eq_sum rK133 ⟨53, by decide⟩ e heK h T133_53 hfix133_53 hinj133_53 hcardT133_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK133) (T133_53 i) (hfix133_53 i) h)

/-! ## Cell (133, 83): |T| = 5 -/

def T133_83list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T133_83 : Fin 5 → Coordinate 1 := fun i => T133_83list.getD i.val (0,0,0,0,0)

theorem hfix133_83 : ∀ i, ((T133_83 i : Coordinate 1) : Coordinate 1 ⧸ reps rK133)
    ∈ fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133) :=
  repsFix_of_siftB rK133 ⟨83, by decide⟩ T133_83 (by decide)

theorem hinj133_83 : Function.Injective
    (fun i => ((T133_83 i : Coordinate 1) : Coordinate 1 ⧸ reps rK133)) :=
  repsInj_of_reduceAux rK133 T133_83 (by decide)

theorem hcardT133_83 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK133 ⟨83, by decide⟩ R133 hpxR133 hcardq133 (by decide)).symm

/-- **Cell (133, 83).** -/
theorem cell133_83 (e : List (ZMod 25)) (heK : charOK (basisAt rK133) e = true)
    (h : ↥(reps (⟨83, by decide⟩ : Fin 148))) :
    species (reps (⟨83, by decide⟩ : Fin 148)) h (basisElt (reps rK133) (charOfVec rK133 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK133 e (h : Coordinate 1) T133_83 i :=
  species_entry_eq_sum rK133 ⟨83, by decide⟩ e heK h T133_83 hfix133_83 hinj133_83 hcardT133_83
    (fun i => conj_mem_of_fixedPoints (reps ⟨83, by decide⟩) (reps rK133) (T133_83 i) (hfix133_83 i) h)

/-! ## Cell (133, 94): |T| = 5 -/

def T133_94list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T133_94 : Fin 5 → Coordinate 1 := fun i => T133_94list.getD i.val (0,0,0,0,0)

theorem hfix133_94 : ∀ i, ((T133_94 i : Coordinate 1) : Coordinate 1 ⧸ reps rK133)
    ∈ fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133) :=
  repsFix_of_siftB rK133 ⟨94, by decide⟩ T133_94 (by decide)

theorem hinj133_94 : Function.Injective
    (fun i => ((T133_94 i : Coordinate 1) : Coordinate 1 ⧸ reps rK133)) :=
  repsInj_of_reduceAux rK133 T133_94 (by decide)

theorem hcardT133_94 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK133 ⟨94, by decide⟩ R133 hpxR133 hcardq133 (by decide)).symm

/-- **Cell (133, 94).** -/
theorem cell133_94 (e : List (ZMod 25)) (heK : charOK (basisAt rK133) e = true)
    (h : ↥(reps (⟨94, by decide⟩ : Fin 148))) :
    species (reps (⟨94, by decide⟩ : Fin 148)) h (basisElt (reps rK133) (charOfVec rK133 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK133 e (h : Coordinate 1) T133_94 i :=
  species_entry_eq_sum rK133 ⟨94, by decide⟩ e heK h T133_94 hfix133_94 hinj133_94 hcardT133_94
    (fun i => conj_mem_of_fixedPoints (reps ⟨94, by decide⟩) (reps rK133) (T133_94 i) (hfix133_94 i) h)

/-! ## Cell (133, 98): |T| = 5 -/

def T133_98list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T133_98 : Fin 5 → Coordinate 1 := fun i => T133_98list.getD i.val (0,0,0,0,0)

theorem hfix133_98 : ∀ i, ((T133_98 i : Coordinate 1) : Coordinate 1 ⧸ reps rK133)
    ∈ fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133) :=
  repsFix_of_siftB rK133 ⟨98, by decide⟩ T133_98 (by decide)

theorem hinj133_98 : Function.Injective
    (fun i => ((T133_98 i : Coordinate 1) : Coordinate 1 ⧸ reps rK133)) :=
  repsInj_of_reduceAux rK133 T133_98 (by decide)

theorem hcardT133_98 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK133 ⟨98, by decide⟩ R133 hpxR133 hcardq133 (by decide)).symm

/-- **Cell (133, 98).** -/
theorem cell133_98 (e : List (ZMod 25)) (heK : charOK (basisAt rK133) e = true)
    (h : ↥(reps (⟨98, by decide⟩ : Fin 148))) :
    species (reps (⟨98, by decide⟩ : Fin 148)) h (basisElt (reps rK133) (charOfVec rK133 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK133 e (h : Coordinate 1) T133_98 i :=
  species_entry_eq_sum rK133 ⟨98, by decide⟩ e heK h T133_98 hfix133_98 hinj133_98 hcardT133_98
    (fun i => conj_mem_of_fixedPoints (reps ⟨98, by decide⟩) (reps rK133) (T133_98 i) (hfix133_98 i) h)

/-! ## Cell (133, 101): |T| = 5 -/

def T133_101list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T133_101 : Fin 5 → Coordinate 1 := fun i => T133_101list.getD i.val (0,0,0,0,0)

theorem hfix133_101 : ∀ i, ((T133_101 i : Coordinate 1) : Coordinate 1 ⧸ reps rK133)
    ∈ fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133) :=
  repsFix_of_siftB rK133 ⟨101, by decide⟩ T133_101 (by decide)

theorem hinj133_101 : Function.Injective
    (fun i => ((T133_101 i : Coordinate 1) : Coordinate 1 ⧸ reps rK133)) :=
  repsInj_of_reduceAux rK133 T133_101 (by decide)

theorem hcardT133_101 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK133 ⟨101, by decide⟩ R133 hpxR133 hcardq133 (by decide)).symm

/-- **Cell (133, 101).** -/
theorem cell133_101 (e : List (ZMod 25)) (heK : charOK (basisAt rK133) e = true)
    (h : ↥(reps (⟨101, by decide⟩ : Fin 148))) :
    species (reps (⟨101, by decide⟩ : Fin 148)) h (basisElt (reps rK133) (charOfVec rK133 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK133 e (h : Coordinate 1) T133_101 i :=
  species_entry_eq_sum rK133 ⟨101, by decide⟩ e heK h T133_101 hfix133_101 hinj133_101 hcardT133_101
    (fun i => conj_mem_of_fixedPoints (reps ⟨101, by decide⟩) (reps rK133) (T133_101 i) (hfix133_101 i) h)

/-! ## Cell (133, 105): |T| = 5 -/

def T133_105list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T133_105 : Fin 5 → Coordinate 1 := fun i => T133_105list.getD i.val (0,0,0,0,0)

theorem hfix133_105 : ∀ i, ((T133_105 i : Coordinate 1) : Coordinate 1 ⧸ reps rK133)
    ∈ fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133) :=
  repsFix_of_siftB rK133 ⟨105, by decide⟩ T133_105 (by decide)

theorem hinj133_105 : Function.Injective
    (fun i => ((T133_105 i : Coordinate 1) : Coordinate 1 ⧸ reps rK133)) :=
  repsInj_of_reduceAux rK133 T133_105 (by decide)

theorem hcardT133_105 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK133 ⟨105, by decide⟩ R133 hpxR133 hcardq133 (by decide)).symm

/-- **Cell (133, 105).** -/
theorem cell133_105 (e : List (ZMod 25)) (heK : charOK (basisAt rK133) e = true)
    (h : ↥(reps (⟨105, by decide⟩ : Fin 148))) :
    species (reps (⟨105, by decide⟩ : Fin 148)) h (basisElt (reps rK133) (charOfVec rK133 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK133 e (h : Coordinate 1) T133_105 i :=
  species_entry_eq_sum rK133 ⟨105, by decide⟩ e heK h T133_105 hfix133_105 hinj133_105 hcardT133_105
    (fun i => conj_mem_of_fixedPoints (reps ⟨105, by decide⟩) (reps rK133) (T133_105 i) (hfix133_105 i) h)

/-! ## Cell (133, 112): |T| = 5 -/

def T133_112list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T133_112 : Fin 5 → Coordinate 1 := fun i => T133_112list.getD i.val (0,0,0,0,0)

theorem hfix133_112 : ∀ i, ((T133_112 i : Coordinate 1) : Coordinate 1 ⧸ reps rK133)
    ∈ fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133) :=
  repsFix_of_siftB rK133 ⟨112, by decide⟩ T133_112 (by decide)

theorem hinj133_112 : Function.Injective
    (fun i => ((T133_112 i : Coordinate 1) : Coordinate 1 ⧸ reps rK133)) :=
  repsInj_of_reduceAux rK133 T133_112 (by decide)

theorem hcardT133_112 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK133 ⟨112, by decide⟩ R133 hpxR133 hcardq133 (by decide)).symm

/-- **Cell (133, 112).** -/
theorem cell133_112 (e : List (ZMod 25)) (heK : charOK (basisAt rK133) e = true)
    (h : ↥(reps (⟨112, by decide⟩ : Fin 148))) :
    species (reps (⟨112, by decide⟩ : Fin 148)) h (basisElt (reps rK133) (charOfVec rK133 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK133 e (h : Coordinate 1) T133_112 i :=
  species_entry_eq_sum rK133 ⟨112, by decide⟩ e heK h T133_112 hfix133_112 hinj133_112 hcardT133_112
    (fun i => conj_mem_of_fixedPoints (reps ⟨112, by decide⟩) (reps rK133) (T133_112 i) (hfix133_112 i) h)

/-! ## Cell (133, 133): |T| = 5 -/

def T133_133list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0)]
def T133_133 : Fin 5 → Coordinate 1 := fun i => T133_133list.getD i.val (0,0,0,0,0)

theorem hfix133_133 : ∀ i, ((T133_133 i : Coordinate 1) : Coordinate 1 ⧸ reps rK133)
    ∈ fixedPoints (reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133) :=
  repsFix_of_siftB rK133 ⟨133, by decide⟩ T133_133 (by decide)

theorem hinj133_133 : Function.Injective
    (fun i => ((T133_133 i : Coordinate 1) : Coordinate 1 ⧸ reps rK133)) :=
  repsInj_of_reduceAux rK133 T133_133 (by decide)

theorem hcardT133_133 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK133 ⟨133, by decide⟩ R133 hpxR133 hcardq133 (by decide)).symm

/-- **Cell (133, 133).** -/
theorem cell133_133 (e : List (ZMod 25)) (heK : charOK (basisAt rK133) e = true)
    (h : ↥(reps (⟨133, by decide⟩ : Fin 148))) :
    species (reps (⟨133, by decide⟩ : Fin 148)) h (basisElt (reps rK133) (charOfVec rK133 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK133 e (h : Coordinate 1) T133_133 i :=
  species_entry_eq_sum rK133 ⟨133, by decide⟩ e heK h T133_133 hfix133_133 hinj133_133 hcardT133_133
    (fun i => conj_mem_of_fixedPoints (reps ⟨133, by decide⟩) (reps rK133) (T133_133 i) (hfix133_133 i) h)

namespace Q2

def R133_2 : Fin 5 → Coordinate 2 := fun i => R133list.getD i.val (0,0,0,0,0)
theorem hpxR133_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK133) (R133_2 i)) := by decide
theorem hcardq133_2 : Nat.card (Coordinate 2 ⧸ reps rK133) = 5 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (133, 0) twin -/

def T133_0_2 : Fin 5 → Coordinate 2 := fun i => T133_0list.getD i.val (0,0,0,0,0)

theorem hfix133_0_2 : ∀ i, ((T133_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK133)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK133) :=
  repsFix_of_siftB2 rK133 ⟨0, by decide⟩ T133_0_2 (by decide)

theorem hinj133_0_2 : Function.Injective
    (fun i => ((T133_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK133)) :=
  repsInj_of_reduceAux2 rK133 T133_0_2 (by decide)

theorem hcardT133_0_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK133)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK133 ⟨0, by decide⟩ R133_2 hpxR133_2 hcardq133_2 (by decide)).symm

/-- **Cell (133, 0) twin (q=2).** -/
theorem cell133_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK133) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK133) (charOfVec2 rK133 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK133 e (h : Coordinate 2) T133_0_2 i :=
  species_entry_eq_sum rK133 ⟨0, by decide⟩ e heK h T133_0_2 hfix133_0_2 hinj133_0_2 hcardT133_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK133) (T133_0_2 i) (hfix133_0_2 i) h)

/-! ### Cell (133, 4) twin -/

def T133_4_2 : Fin 5 → Coordinate 2 := fun i => T133_4list.getD i.val (0,0,0,0,0)

theorem hfix133_4_2 : ∀ i, ((T133_4_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK133)
    ∈ fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK133) :=
  repsFix_of_siftB2 rK133 ⟨4, by decide⟩ T133_4_2 (by decide)

theorem hinj133_4_2 : Function.Injective
    (fun i => ((T133_4_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK133)) :=
  repsInj_of_reduceAux2 rK133 T133_4_2 (by decide)

theorem hcardT133_4_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK133)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK133 ⟨4, by decide⟩ R133_2 hpxR133_2 hcardq133_2 (by decide)).symm

/-- **Cell (133, 4) twin (q=2).** -/
theorem cell133_4_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK133) e = true)
    (h : ↥(reps (⟨4, by decide⟩ : Fin 148))) :
    species (reps (⟨4, by decide⟩ : Fin 148)) h (basisElt (reps rK133) (charOfVec2 rK133 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK133 e (h : Coordinate 2) T133_4_2 i :=
  species_entry_eq_sum rK133 ⟨4, by decide⟩ e heK h T133_4_2 hfix133_4_2 hinj133_4_2 hcardT133_4_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨4, by decide⟩) (reps rK133) (T133_4_2 i) (hfix133_4_2 i) h)

/-! ### Cell (133, 10) twin -/

def T133_10_2 : Fin 5 → Coordinate 2 := fun i => T133_10list.getD i.val (0,0,0,0,0)

theorem hfix133_10_2 : ∀ i, ((T133_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK133)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK133) :=
  repsFix_of_siftB2 rK133 ⟨10, by decide⟩ T133_10_2 (by decide)

theorem hinj133_10_2 : Function.Injective
    (fun i => ((T133_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK133)) :=
  repsInj_of_reduceAux2 rK133 T133_10_2 (by decide)

theorem hcardT133_10_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK133)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK133 ⟨10, by decide⟩ R133_2 hpxR133_2 hcardq133_2 (by decide)).symm

/-- **Cell (133, 10) twin (q=2).** -/
theorem cell133_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK133) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK133) (charOfVec2 rK133 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK133 e (h : Coordinate 2) T133_10_2 i :=
  species_entry_eq_sum rK133 ⟨10, by decide⟩ e heK h T133_10_2 hfix133_10_2 hinj133_10_2 hcardT133_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK133) (T133_10_2 i) (hfix133_10_2 i) h)

/-! ### Cell (133, 12) twin -/

def T133_12_2 : Fin 5 → Coordinate 2 := fun i => T133_12list.getD i.val (0,0,0,0,0)

theorem hfix133_12_2 : ∀ i, ((T133_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK133)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK133) :=
  repsFix_of_siftB2 rK133 ⟨12, by decide⟩ T133_12_2 (by decide)

theorem hinj133_12_2 : Function.Injective
    (fun i => ((T133_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK133)) :=
  repsInj_of_reduceAux2 rK133 T133_12_2 (by decide)

theorem hcardT133_12_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK133)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK133 ⟨12, by decide⟩ R133_2 hpxR133_2 hcardq133_2 (by decide)).symm

/-- **Cell (133, 12) twin (q=2).** -/
theorem cell133_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK133) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK133) (charOfVec2 rK133 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK133 e (h : Coordinate 2) T133_12_2 i :=
  species_entry_eq_sum rK133 ⟨12, by decide⟩ e heK h T133_12_2 hfix133_12_2 hinj133_12_2 hcardT133_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK133) (T133_12_2 i) (hfix133_12_2 i) h)

/-! ### Cell (133, 22) twin -/

def T133_22_2 : Fin 5 → Coordinate 2 := fun i => T133_22list.getD i.val (0,0,0,0,0)

theorem hfix133_22_2 : ∀ i, ((T133_22_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK133)
    ∈ fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK133) :=
  repsFix_of_siftB2 rK133 ⟨22, by decide⟩ T133_22_2 (by decide)

theorem hinj133_22_2 : Function.Injective
    (fun i => ((T133_22_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK133)) :=
  repsInj_of_reduceAux2 rK133 T133_22_2 (by decide)

theorem hcardT133_22_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK133)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK133 ⟨22, by decide⟩ R133_2 hpxR133_2 hcardq133_2 (by decide)).symm

/-- **Cell (133, 22) twin (q=2).** -/
theorem cell133_22_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK133) e = true)
    (h : ↥(reps (⟨22, by decide⟩ : Fin 148))) :
    species (reps (⟨22, by decide⟩ : Fin 148)) h (basisElt (reps rK133) (charOfVec2 rK133 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK133 e (h : Coordinate 2) T133_22_2 i :=
  species_entry_eq_sum rK133 ⟨22, by decide⟩ e heK h T133_22_2 hfix133_22_2 hinj133_22_2 hcardT133_22_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨22, by decide⟩) (reps rK133) (T133_22_2 i) (hfix133_22_2 i) h)

/-! ### Cell (133, 32) twin -/

def T133_32_2 : Fin 5 → Coordinate 2 := fun i => T133_32list.getD i.val (0,0,0,0,0)

theorem hfix133_32_2 : ∀ i, ((T133_32_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK133)
    ∈ fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK133) :=
  repsFix_of_siftB2 rK133 ⟨32, by decide⟩ T133_32_2 (by decide)

theorem hinj133_32_2 : Function.Injective
    (fun i => ((T133_32_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK133)) :=
  repsInj_of_reduceAux2 rK133 T133_32_2 (by decide)

theorem hcardT133_32_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK133)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK133 ⟨32, by decide⟩ R133_2 hpxR133_2 hcardq133_2 (by decide)).symm

/-- **Cell (133, 32) twin (q=2).** -/
theorem cell133_32_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK133) e = true)
    (h : ↥(reps (⟨32, by decide⟩ : Fin 148))) :
    species (reps (⟨32, by decide⟩ : Fin 148)) h (basisElt (reps rK133) (charOfVec2 rK133 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK133 e (h : Coordinate 2) T133_32_2 i :=
  species_entry_eq_sum rK133 ⟨32, by decide⟩ e heK h T133_32_2 hfix133_32_2 hinj133_32_2 hcardT133_32_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨32, by decide⟩) (reps rK133) (T133_32_2 i) (hfix133_32_2 i) h)

/-! ### Cell (133, 36) twin -/

def T133_36_2 : Fin 5 → Coordinate 2 := fun i => T133_36list.getD i.val (0,0,0,0,0)

theorem hfix133_36_2 : ∀ i, ((T133_36_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK133)
    ∈ fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK133) :=
  repsFix_of_siftB2 rK133 ⟨36, by decide⟩ T133_36_2 (by decide)

theorem hinj133_36_2 : Function.Injective
    (fun i => ((T133_36_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK133)) :=
  repsInj_of_reduceAux2 rK133 T133_36_2 (by decide)

theorem hcardT133_36_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK133)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK133 ⟨36, by decide⟩ R133_2 hpxR133_2 hcardq133_2 (by decide)).symm

/-- **Cell (133, 36) twin (q=2).** -/
theorem cell133_36_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK133) e = true)
    (h : ↥(reps (⟨36, by decide⟩ : Fin 148))) :
    species (reps (⟨36, by decide⟩ : Fin 148)) h (basisElt (reps rK133) (charOfVec2 rK133 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK133 e (h : Coordinate 2) T133_36_2 i :=
  species_entry_eq_sum rK133 ⟨36, by decide⟩ e heK h T133_36_2 hfix133_36_2 hinj133_36_2 hcardT133_36_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨36, by decide⟩) (reps rK133) (T133_36_2 i) (hfix133_36_2 i) h)

/-! ### Cell (133, 39) twin -/

def T133_39_2 : Fin 5 → Coordinate 2 := fun i => T133_39list.getD i.val (0,0,0,0,0)

theorem hfix133_39_2 : ∀ i, ((T133_39_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK133)
    ∈ fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK133) :=
  repsFix_of_siftB2 rK133 ⟨39, by decide⟩ T133_39_2 (by decide)

theorem hinj133_39_2 : Function.Injective
    (fun i => ((T133_39_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK133)) :=
  repsInj_of_reduceAux2 rK133 T133_39_2 (by decide)

theorem hcardT133_39_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK133)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK133 ⟨39, by decide⟩ R133_2 hpxR133_2 hcardq133_2 (by decide)).symm

/-- **Cell (133, 39) twin (q=2).** -/
theorem cell133_39_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK133) e = true)
    (h : ↥(reps (⟨39, by decide⟩ : Fin 148))) :
    species (reps (⟨39, by decide⟩ : Fin 148)) h (basisElt (reps rK133) (charOfVec2 rK133 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK133 e (h : Coordinate 2) T133_39_2 i :=
  species_entry_eq_sum rK133 ⟨39, by decide⟩ e heK h T133_39_2 hfix133_39_2 hinj133_39_2 hcardT133_39_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨39, by decide⟩) (reps rK133) (T133_39_2 i) (hfix133_39_2 i) h)

/-! ### Cell (133, 43) twin -/

def T133_43_2 : Fin 5 → Coordinate 2 := fun i => T133_43list.getD i.val (0,0,0,0,0)

theorem hfix133_43_2 : ∀ i, ((T133_43_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK133)
    ∈ fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK133) :=
  repsFix_of_siftB2 rK133 ⟨43, by decide⟩ T133_43_2 (by decide)

theorem hinj133_43_2 : Function.Injective
    (fun i => ((T133_43_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK133)) :=
  repsInj_of_reduceAux2 rK133 T133_43_2 (by decide)

theorem hcardT133_43_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK133)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK133 ⟨43, by decide⟩ R133_2 hpxR133_2 hcardq133_2 (by decide)).symm

/-- **Cell (133, 43) twin (q=2).** -/
theorem cell133_43_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK133) e = true)
    (h : ↥(reps (⟨43, by decide⟩ : Fin 148))) :
    species (reps (⟨43, by decide⟩ : Fin 148)) h (basisElt (reps rK133) (charOfVec2 rK133 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK133 e (h : Coordinate 2) T133_43_2 i :=
  species_entry_eq_sum rK133 ⟨43, by decide⟩ e heK h T133_43_2 hfix133_43_2 hinj133_43_2 hcardT133_43_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨43, by decide⟩) (reps rK133) (T133_43_2 i) (hfix133_43_2 i) h)

/-! ### Cell (133, 50) twin -/

def T133_50_2 : Fin 5 → Coordinate 2 := fun i => T133_50list.getD i.val (0,0,0,0,0)

theorem hfix133_50_2 : ∀ i, ((T133_50_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK133)
    ∈ fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK133) :=
  repsFix_of_siftB2 rK133 ⟨50, by decide⟩ T133_50_2 (by decide)

theorem hinj133_50_2 : Function.Injective
    (fun i => ((T133_50_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK133)) :=
  repsInj_of_reduceAux2 rK133 T133_50_2 (by decide)

theorem hcardT133_50_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK133)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK133 ⟨50, by decide⟩ R133_2 hpxR133_2 hcardq133_2 (by decide)).symm

/-- **Cell (133, 50) twin (q=2).** -/
theorem cell133_50_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK133) e = true)
    (h : ↥(reps (⟨50, by decide⟩ : Fin 148))) :
    species (reps (⟨50, by decide⟩ : Fin 148)) h (basisElt (reps rK133) (charOfVec2 rK133 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK133 e (h : Coordinate 2) T133_50_2 i :=
  species_entry_eq_sum rK133 ⟨50, by decide⟩ e heK h T133_50_2 hfix133_50_2 hinj133_50_2 hcardT133_50_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨50, by decide⟩) (reps rK133) (T133_50_2 i) (hfix133_50_2 i) h)

/-! ### Cell (133, 53) twin -/

def T133_53_2 : Fin 5 → Coordinate 2 := fun i => T133_53list.getD i.val (0,0,0,0,0)

theorem hfix133_53_2 : ∀ i, ((T133_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK133)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK133) :=
  repsFix_of_siftB2 rK133 ⟨53, by decide⟩ T133_53_2 (by decide)

theorem hinj133_53_2 : Function.Injective
    (fun i => ((T133_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK133)) :=
  repsInj_of_reduceAux2 rK133 T133_53_2 (by decide)

theorem hcardT133_53_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK133)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK133 ⟨53, by decide⟩ R133_2 hpxR133_2 hcardq133_2 (by decide)).symm

/-- **Cell (133, 53) twin (q=2).** -/
theorem cell133_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK133) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK133) (charOfVec2 rK133 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK133 e (h : Coordinate 2) T133_53_2 i :=
  species_entry_eq_sum rK133 ⟨53, by decide⟩ e heK h T133_53_2 hfix133_53_2 hinj133_53_2 hcardT133_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK133) (T133_53_2 i) (hfix133_53_2 i) h)

/-! ### Cell (133, 83) twin -/

def T133_83_2 : Fin 5 → Coordinate 2 := fun i => T133_83list.getD i.val (0,0,0,0,0)

theorem hfix133_83_2 : ∀ i, ((T133_83_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK133)
    ∈ fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK133) :=
  repsFix_of_siftB2 rK133 ⟨83, by decide⟩ T133_83_2 (by decide)

theorem hinj133_83_2 : Function.Injective
    (fun i => ((T133_83_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK133)) :=
  repsInj_of_reduceAux2 rK133 T133_83_2 (by decide)

theorem hcardT133_83_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK133)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK133 ⟨83, by decide⟩ R133_2 hpxR133_2 hcardq133_2 (by decide)).symm

/-- **Cell (133, 83) twin (q=2).** -/
theorem cell133_83_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK133) e = true)
    (h : ↥(reps (⟨83, by decide⟩ : Fin 148))) :
    species (reps (⟨83, by decide⟩ : Fin 148)) h (basisElt (reps rK133) (charOfVec2 rK133 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK133 e (h : Coordinate 2) T133_83_2 i :=
  species_entry_eq_sum rK133 ⟨83, by decide⟩ e heK h T133_83_2 hfix133_83_2 hinj133_83_2 hcardT133_83_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨83, by decide⟩) (reps rK133) (T133_83_2 i) (hfix133_83_2 i) h)

/-! ### Cell (133, 94) twin -/

def T133_94_2 : Fin 5 → Coordinate 2 := fun i => T133_94list.getD i.val (0,0,0,0,0)

theorem hfix133_94_2 : ∀ i, ((T133_94_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK133)
    ∈ fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK133) :=
  repsFix_of_siftB2 rK133 ⟨94, by decide⟩ T133_94_2 (by decide)

theorem hinj133_94_2 : Function.Injective
    (fun i => ((T133_94_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK133)) :=
  repsInj_of_reduceAux2 rK133 T133_94_2 (by decide)

theorem hcardT133_94_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK133)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK133 ⟨94, by decide⟩ R133_2 hpxR133_2 hcardq133_2 (by decide)).symm

/-- **Cell (133, 94) twin (q=2).** -/
theorem cell133_94_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK133) e = true)
    (h : ↥(reps (⟨94, by decide⟩ : Fin 148))) :
    species (reps (⟨94, by decide⟩ : Fin 148)) h (basisElt (reps rK133) (charOfVec2 rK133 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK133 e (h : Coordinate 2) T133_94_2 i :=
  species_entry_eq_sum rK133 ⟨94, by decide⟩ e heK h T133_94_2 hfix133_94_2 hinj133_94_2 hcardT133_94_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨94, by decide⟩) (reps rK133) (T133_94_2 i) (hfix133_94_2 i) h)

/-! ### Cell (133, 98) twin -/

def T133_98_2 : Fin 5 → Coordinate 2 := fun i => T133_98list.getD i.val (0,0,0,0,0)

theorem hfix133_98_2 : ∀ i, ((T133_98_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK133)
    ∈ fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK133) :=
  repsFix_of_siftB2 rK133 ⟨98, by decide⟩ T133_98_2 (by decide)

theorem hinj133_98_2 : Function.Injective
    (fun i => ((T133_98_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK133)) :=
  repsInj_of_reduceAux2 rK133 T133_98_2 (by decide)

theorem hcardT133_98_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK133)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK133 ⟨98, by decide⟩ R133_2 hpxR133_2 hcardq133_2 (by decide)).symm

/-- **Cell (133, 98) twin (q=2).** -/
theorem cell133_98_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK133) e = true)
    (h : ↥(reps (⟨98, by decide⟩ : Fin 148))) :
    species (reps (⟨98, by decide⟩ : Fin 148)) h (basisElt (reps rK133) (charOfVec2 rK133 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK133 e (h : Coordinate 2) T133_98_2 i :=
  species_entry_eq_sum rK133 ⟨98, by decide⟩ e heK h T133_98_2 hfix133_98_2 hinj133_98_2 hcardT133_98_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨98, by decide⟩) (reps rK133) (T133_98_2 i) (hfix133_98_2 i) h)

/-! ### Cell (133, 101) twin -/

def T133_101_2 : Fin 5 → Coordinate 2 := fun i => T133_101list.getD i.val (0,0,0,0,0)

theorem hfix133_101_2 : ∀ i, ((T133_101_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK133)
    ∈ fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK133) :=
  repsFix_of_siftB2 rK133 ⟨101, by decide⟩ T133_101_2 (by decide)

theorem hinj133_101_2 : Function.Injective
    (fun i => ((T133_101_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK133)) :=
  repsInj_of_reduceAux2 rK133 T133_101_2 (by decide)

theorem hcardT133_101_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK133)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK133 ⟨101, by decide⟩ R133_2 hpxR133_2 hcardq133_2 (by decide)).symm

/-- **Cell (133, 101) twin (q=2).** -/
theorem cell133_101_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK133) e = true)
    (h : ↥(reps (⟨101, by decide⟩ : Fin 148))) :
    species (reps (⟨101, by decide⟩ : Fin 148)) h (basisElt (reps rK133) (charOfVec2 rK133 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK133 e (h : Coordinate 2) T133_101_2 i :=
  species_entry_eq_sum rK133 ⟨101, by decide⟩ e heK h T133_101_2 hfix133_101_2 hinj133_101_2 hcardT133_101_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨101, by decide⟩) (reps rK133) (T133_101_2 i) (hfix133_101_2 i) h)

/-! ### Cell (133, 105) twin -/

def T133_105_2 : Fin 5 → Coordinate 2 := fun i => T133_105list.getD i.val (0,0,0,0,0)

theorem hfix133_105_2 : ∀ i, ((T133_105_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK133)
    ∈ fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK133) :=
  repsFix_of_siftB2 rK133 ⟨105, by decide⟩ T133_105_2 (by decide)

theorem hinj133_105_2 : Function.Injective
    (fun i => ((T133_105_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK133)) :=
  repsInj_of_reduceAux2 rK133 T133_105_2 (by decide)

theorem hcardT133_105_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK133)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK133 ⟨105, by decide⟩ R133_2 hpxR133_2 hcardq133_2 (by decide)).symm

/-- **Cell (133, 105) twin (q=2).** -/
theorem cell133_105_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK133) e = true)
    (h : ↥(reps (⟨105, by decide⟩ : Fin 148))) :
    species (reps (⟨105, by decide⟩ : Fin 148)) h (basisElt (reps rK133) (charOfVec2 rK133 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK133 e (h : Coordinate 2) T133_105_2 i :=
  species_entry_eq_sum rK133 ⟨105, by decide⟩ e heK h T133_105_2 hfix133_105_2 hinj133_105_2 hcardT133_105_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨105, by decide⟩) (reps rK133) (T133_105_2 i) (hfix133_105_2 i) h)

/-! ### Cell (133, 112) twin -/

def T133_112_2 : Fin 5 → Coordinate 2 := fun i => T133_112list.getD i.val (0,0,0,0,0)

theorem hfix133_112_2 : ∀ i, ((T133_112_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK133)
    ∈ fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK133) :=
  repsFix_of_siftB2 rK133 ⟨112, by decide⟩ T133_112_2 (by decide)

theorem hinj133_112_2 : Function.Injective
    (fun i => ((T133_112_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK133)) :=
  repsInj_of_reduceAux2 rK133 T133_112_2 (by decide)

theorem hcardT133_112_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK133)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK133 ⟨112, by decide⟩ R133_2 hpxR133_2 hcardq133_2 (by decide)).symm

/-- **Cell (133, 112) twin (q=2).** -/
theorem cell133_112_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK133) e = true)
    (h : ↥(reps (⟨112, by decide⟩ : Fin 148))) :
    species (reps (⟨112, by decide⟩ : Fin 148)) h (basisElt (reps rK133) (charOfVec2 rK133 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK133 e (h : Coordinate 2) T133_112_2 i :=
  species_entry_eq_sum rK133 ⟨112, by decide⟩ e heK h T133_112_2 hfix133_112_2 hinj133_112_2 hcardT133_112_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨112, by decide⟩) (reps rK133) (T133_112_2 i) (hfix133_112_2 i) h)

/-! ### Cell (133, 133) twin -/

def T133_133_2 : Fin 5 → Coordinate 2 := fun i => T133_133list.getD i.val (0,0,0,0,0)

theorem hfix133_133_2 : ∀ i, ((T133_133_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK133)
    ∈ fixedPoints (reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK133) :=
  repsFix_of_siftB2 rK133 ⟨133, by decide⟩ T133_133_2 (by decide)

theorem hinj133_133_2 : Function.Injective
    (fun i => ((T133_133_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK133)) :=
  repsInj_of_reduceAux2 rK133 T133_133_2 (by decide)

theorem hcardT133_133_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK133)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK133 ⟨133, by decide⟩ R133_2 hpxR133_2 hcardq133_2 (by decide)).symm

/-- **Cell (133, 133) twin (q=2).** -/
theorem cell133_133_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK133) e = true)
    (h : ↥(reps (⟨133, by decide⟩ : Fin 148))) :
    species (reps (⟨133, by decide⟩ : Fin 148)) h (basisElt (reps rK133) (charOfVec2 rK133 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK133 e (h : Coordinate 2) T133_133_2 i :=
  species_entry_eq_sum rK133 ⟨133, by decide⟩ e heK h T133_133_2 hfix133_133_2 hinj133_133_2 hcardT133_133_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨133, by decide⟩) (reps rK133) (T133_133_2 i) (hfix133_133_2 i) h)

end Q2

end LeanDring.P5Presentation
