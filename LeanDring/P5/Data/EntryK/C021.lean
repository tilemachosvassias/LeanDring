/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, K-strata data (5^3 stratum, rK 88-92): certified per-cell species-entry instantiations, both
twins.

Covers K-classes 88, 89, 90, 91, 92 (order-5^3 K, |R|=25).  For each nonzero `H`-column
(`(G/K)^H ≠ ∅`), the full coset transversal `R88..` and each `H`-fixed
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

/-! # K-class rK = 88  (|G/K| = 25) -/

def rK88 : Fin 148 := ⟨88, by decide⟩

def R88list : List Coordinates := [(0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0)]
def R88 : Fin 25 → Coordinate 1 := fun i => R88list.getD i.val (0,0,0,0,0)

theorem hpxR88 : Function.Injective (fun i => reduceAux 1 (basisAt rK88) (R88 i)) := by decide
theorem hcardq88 : Nat.card (Coordinate 1 ⧸ reps rK88) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (88, 0): |T| = 25 -/

def T88_0list : List Coordinates := [(0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0)]
def T88_0 : Fin 25 → Coordinate 1 := fun i => T88_0list.getD i.val (0,0,0,0,0)

theorem hfix88_0 : ∀ i, ((T88_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK88)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88) :=
  repsFix_of_siftB rK88 ⟨0, by decide⟩ T88_0 (by decide)

theorem hinj88_0 : Function.Injective
    (fun i => ((T88_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK88)) :=
  repsInj_of_reduceAux rK88 T88_0 (by decide)

theorem hcardT88_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK88 ⟨0, by decide⟩ R88 hpxR88 hcardq88 (by decide)).symm

/-- **Cell (88, 0).** -/
theorem cell88_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK88) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK88) (charOfVec rK88 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK88 e (h : Coordinate 1) T88_0 i :=
  species_entry_eq_sum rK88 ⟨0, by decide⟩ e heK h T88_0 hfix88_0 hinj88_0 hcardT88_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK88) (T88_0 i) (hfix88_0 i) h)

/-! ## Cell (88, 2): |T| = 5 -/

def T88_2list : List Coordinates := [(0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0)]
def T88_2 : Fin 5 → Coordinate 1 := fun i => T88_2list.getD i.val (0,0,0,0,0)

theorem hfix88_2 : ∀ i, ((T88_2 i : Coordinate 1) : Coordinate 1 ⧸ reps rK88)
    ∈ fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88) :=
  repsFix_of_siftB rK88 ⟨2, by decide⟩ T88_2 (by decide)

theorem hinj88_2 : Function.Injective
    (fun i => ((T88_2 i : Coordinate 1) : Coordinate 1 ⧸ reps rK88)) :=
  repsInj_of_reduceAux rK88 T88_2 (by decide)

theorem hcardT88_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK88 ⟨2, by decide⟩ R88 hpxR88 hcardq88 (by decide)).symm

/-- **Cell (88, 2).** -/
theorem cell88_2 (e : List (ZMod 25)) (heK : charOK (basisAt rK88) e = true)
    (h : ↥(reps (⟨2, by decide⟩ : Fin 148))) :
    species (reps (⟨2, by decide⟩ : Fin 148)) h (basisElt (reps rK88) (charOfVec rK88 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK88 e (h : Coordinate 1) T88_2 i :=
  species_entry_eq_sum rK88 ⟨2, by decide⟩ e heK h T88_2 hfix88_2 hinj88_2 hcardT88_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨2, by decide⟩) (reps rK88) (T88_2 i) (hfix88_2 i) h)

/-! ## Cell (88, 3): |T| = 5 -/

def T88_3list : List Coordinates := [(0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0)]
def T88_3 : Fin 5 → Coordinate 1 := fun i => T88_3list.getD i.val (0,0,0,0,0)

theorem hfix88_3 : ∀ i, ((T88_3 i : Coordinate 1) : Coordinate 1 ⧸ reps rK88)
    ∈ fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88) :=
  repsFix_of_siftB rK88 ⟨3, by decide⟩ T88_3 (by decide)

theorem hinj88_3 : Function.Injective
    (fun i => ((T88_3 i : Coordinate 1) : Coordinate 1 ⧸ reps rK88)) :=
  repsInj_of_reduceAux rK88 T88_3 (by decide)

theorem hcardT88_3 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK88 ⟨3, by decide⟩ R88 hpxR88 hcardq88 (by decide)).symm

/-- **Cell (88, 3).** -/
theorem cell88_3 (e : List (ZMod 25)) (heK : charOK (basisAt rK88) e = true)
    (h : ↥(reps (⟨3, by decide⟩ : Fin 148))) :
    species (reps (⟨3, by decide⟩ : Fin 148)) h (basisElt (reps rK88) (charOfVec rK88 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK88 e (h : Coordinate 1) T88_3 i :=
  species_entry_eq_sum rK88 ⟨3, by decide⟩ e heK h T88_3 hfix88_3 hinj88_3 hcardT88_3
    (fun i => conj_mem_of_fixedPoints (reps ⟨3, by decide⟩) (reps rK88) (T88_3 i) (hfix88_3 i) h)

/-! ## Cell (88, 4): |T| = 5 -/

def T88_4list : List Coordinates := [(0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0)]
def T88_4 : Fin 5 → Coordinate 1 := fun i => T88_4list.getD i.val (0,0,0,0,0)

theorem hfix88_4 : ∀ i, ((T88_4 i : Coordinate 1) : Coordinate 1 ⧸ reps rK88)
    ∈ fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88) :=
  repsFix_of_siftB rK88 ⟨4, by decide⟩ T88_4 (by decide)

theorem hinj88_4 : Function.Injective
    (fun i => ((T88_4 i : Coordinate 1) : Coordinate 1 ⧸ reps rK88)) :=
  repsInj_of_reduceAux rK88 T88_4 (by decide)

theorem hcardT88_4 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK88 ⟨4, by decide⟩ R88 hpxR88 hcardq88 (by decide)).symm

/-- **Cell (88, 4).** -/
theorem cell88_4 (e : List (ZMod 25)) (heK : charOK (basisAt rK88) e = true)
    (h : ↥(reps (⟨4, by decide⟩ : Fin 148))) :
    species (reps (⟨4, by decide⟩ : Fin 148)) h (basisElt (reps rK88) (charOfVec rK88 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK88 e (h : Coordinate 1) T88_4 i :=
  species_entry_eq_sum rK88 ⟨4, by decide⟩ e heK h T88_4 hfix88_4 hinj88_4 hcardT88_4
    (fun i => conj_mem_of_fixedPoints (reps ⟨4, by decide⟩) (reps rK88) (T88_4 i) (hfix88_4 i) h)

/-! ## Cell (88, 5): |T| = 5 -/

def T88_5list : List Coordinates := [(0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0)]
def T88_5 : Fin 5 → Coordinate 1 := fun i => T88_5list.getD i.val (0,0,0,0,0)

theorem hfix88_5 : ∀ i, ((T88_5 i : Coordinate 1) : Coordinate 1 ⧸ reps rK88)
    ∈ fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88) :=
  repsFix_of_siftB rK88 ⟨5, by decide⟩ T88_5 (by decide)

theorem hinj88_5 : Function.Injective
    (fun i => ((T88_5 i : Coordinate 1) : Coordinate 1 ⧸ reps rK88)) :=
  repsInj_of_reduceAux rK88 T88_5 (by decide)

theorem hcardT88_5 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK88 ⟨5, by decide⟩ R88 hpxR88 hcardq88 (by decide)).symm

/-- **Cell (88, 5).** -/
theorem cell88_5 (e : List (ZMod 25)) (heK : charOK (basisAt rK88) e = true)
    (h : ↥(reps (⟨5, by decide⟩ : Fin 148))) :
    species (reps (⟨5, by decide⟩ : Fin 148)) h (basisElt (reps rK88) (charOfVec rK88 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK88 e (h : Coordinate 1) T88_5 i :=
  species_entry_eq_sum rK88 ⟨5, by decide⟩ e heK h T88_5 hfix88_5 hinj88_5 hcardT88_5
    (fun i => conj_mem_of_fixedPoints (reps ⟨5, by decide⟩) (reps rK88) (T88_5 i) (hfix88_5 i) h)

/-! ## Cell (88, 6): |T| = 25 -/

def T88_6list : List Coordinates := [(0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0)]
def T88_6 : Fin 25 → Coordinate 1 := fun i => T88_6list.getD i.val (0,0,0,0,0)

theorem hfix88_6 : ∀ i, ((T88_6 i : Coordinate 1) : Coordinate 1 ⧸ reps rK88)
    ∈ fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88) :=
  repsFix_of_siftB rK88 ⟨6, by decide⟩ T88_6 (by decide)

theorem hinj88_6 : Function.Injective
    (fun i => ((T88_6 i : Coordinate 1) : Coordinate 1 ⧸ reps rK88)) :=
  repsInj_of_reduceAux rK88 T88_6 (by decide)

theorem hcardT88_6 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK88 ⟨6, by decide⟩ R88 hpxR88 hcardq88 (by decide)).symm

/-- **Cell (88, 6).** -/
theorem cell88_6 (e : List (ZMod 25)) (heK : charOK (basisAt rK88) e = true)
    (h : ↥(reps (⟨6, by decide⟩ : Fin 148))) :
    species (reps (⟨6, by decide⟩ : Fin 148)) h (basisElt (reps rK88) (charOfVec rK88 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK88 e (h : Coordinate 1) T88_6 i :=
  species_entry_eq_sum rK88 ⟨6, by decide⟩ e heK h T88_6 hfix88_6 hinj88_6 hcardT88_6
    (fun i => conj_mem_of_fixedPoints (reps ⟨6, by decide⟩) (reps rK88) (T88_6 i) (hfix88_6 i) h)

/-! ## Cell (88, 11): |T| = 5 -/

def T88_11list : List Coordinates := [(0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0)]
def T88_11 : Fin 5 → Coordinate 1 := fun i => T88_11list.getD i.val (0,0,0,0,0)

theorem hfix88_11 : ∀ i, ((T88_11 i : Coordinate 1) : Coordinate 1 ⧸ reps rK88)
    ∈ fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88) :=
  repsFix_of_siftB rK88 ⟨11, by decide⟩ T88_11 (by decide)

theorem hinj88_11 : Function.Injective
    (fun i => ((T88_11 i : Coordinate 1) : Coordinate 1 ⧸ reps rK88)) :=
  repsInj_of_reduceAux rK88 T88_11 (by decide)

theorem hcardT88_11 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK88 ⟨11, by decide⟩ R88 hpxR88 hcardq88 (by decide)).symm

/-- **Cell (88, 11).** -/
theorem cell88_11 (e : List (ZMod 25)) (heK : charOK (basisAt rK88) e = true)
    (h : ↥(reps (⟨11, by decide⟩ : Fin 148))) :
    species (reps (⟨11, by decide⟩ : Fin 148)) h (basisElt (reps rK88) (charOfVec rK88 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK88 e (h : Coordinate 1) T88_11 i :=
  species_entry_eq_sum rK88 ⟨11, by decide⟩ e heK h T88_11 hfix88_11 hinj88_11 hcardT88_11
    (fun i => conj_mem_of_fixedPoints (reps ⟨11, by decide⟩) (reps rK88) (T88_11 i) (hfix88_11 i) h)

/-! ## Cell (88, 12): |T| = 25 -/

def T88_12list : List Coordinates := [(0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0)]
def T88_12 : Fin 25 → Coordinate 1 := fun i => T88_12list.getD i.val (0,0,0,0,0)

theorem hfix88_12 : ∀ i, ((T88_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK88)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88) :=
  repsFix_of_siftB rK88 ⟨12, by decide⟩ T88_12 (by decide)

theorem hinj88_12 : Function.Injective
    (fun i => ((T88_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK88)) :=
  repsInj_of_reduceAux rK88 T88_12 (by decide)

theorem hcardT88_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK88 ⟨12, by decide⟩ R88 hpxR88 hcardq88 (by decide)).symm

/-- **Cell (88, 12).** -/
theorem cell88_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK88) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK88) (charOfVec rK88 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK88 e (h : Coordinate 1) T88_12 i :=
  species_entry_eq_sum rK88 ⟨12, by decide⟩ e heK h T88_12 hfix88_12 hinj88_12 hcardT88_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK88) (T88_12 i) (hfix88_12 i) h)

/-! ## Cell (88, 20): |T| = 5 -/

def T88_20list : List Coordinates := [(0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0)]
def T88_20 : Fin 5 → Coordinate 1 := fun i => T88_20list.getD i.val (0,0,0,0,0)

theorem hfix88_20 : ∀ i, ((T88_20 i : Coordinate 1) : Coordinate 1 ⧸ reps rK88)
    ∈ fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88) :=
  repsFix_of_siftB rK88 ⟨20, by decide⟩ T88_20 (by decide)

theorem hinj88_20 : Function.Injective
    (fun i => ((T88_20 i : Coordinate 1) : Coordinate 1 ⧸ reps rK88)) :=
  repsInj_of_reduceAux rK88 T88_20 (by decide)

theorem hcardT88_20 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK88 ⟨20, by decide⟩ R88 hpxR88 hcardq88 (by decide)).symm

/-- **Cell (88, 20).** -/
theorem cell88_20 (e : List (ZMod 25)) (heK : charOK (basisAt rK88) e = true)
    (h : ↥(reps (⟨20, by decide⟩ : Fin 148))) :
    species (reps (⟨20, by decide⟩ : Fin 148)) h (basisElt (reps rK88) (charOfVec rK88 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK88 e (h : Coordinate 1) T88_20 i :=
  species_entry_eq_sum rK88 ⟨20, by decide⟩ e heK h T88_20 hfix88_20 hinj88_20 hcardT88_20
    (fun i => conj_mem_of_fixedPoints (reps ⟨20, by decide⟩) (reps rK88) (T88_20 i) (hfix88_20 i) h)

/-! ## Cell (88, 21): |T| = 5 -/

def T88_21list : List Coordinates := [(0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0)]
def T88_21 : Fin 5 → Coordinate 1 := fun i => T88_21list.getD i.val (0,0,0,0,0)

theorem hfix88_21 : ∀ i, ((T88_21 i : Coordinate 1) : Coordinate 1 ⧸ reps rK88)
    ∈ fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88) :=
  repsFix_of_siftB rK88 ⟨21, by decide⟩ T88_21 (by decide)

theorem hinj88_21 : Function.Injective
    (fun i => ((T88_21 i : Coordinate 1) : Coordinate 1 ⧸ reps rK88)) :=
  repsInj_of_reduceAux rK88 T88_21 (by decide)

theorem hcardT88_21 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK88 ⟨21, by decide⟩ R88 hpxR88 hcardq88 (by decide)).symm

/-- **Cell (88, 21).** -/
theorem cell88_21 (e : List (ZMod 25)) (heK : charOK (basisAt rK88) e = true)
    (h : ↥(reps (⟨21, by decide⟩ : Fin 148))) :
    species (reps (⟨21, by decide⟩ : Fin 148)) h (basisElt (reps rK88) (charOfVec rK88 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK88 e (h : Coordinate 1) T88_21 i :=
  species_entry_eq_sum rK88 ⟨21, by decide⟩ e heK h T88_21 hfix88_21 hinj88_21 hcardT88_21
    (fun i => conj_mem_of_fixedPoints (reps ⟨21, by decide⟩) (reps rK88) (T88_21 i) (hfix88_21 i) h)

/-! ## Cell (88, 22): |T| = 5 -/

def T88_22list : List Coordinates := [(0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0)]
def T88_22 : Fin 5 → Coordinate 1 := fun i => T88_22list.getD i.val (0,0,0,0,0)

theorem hfix88_22 : ∀ i, ((T88_22 i : Coordinate 1) : Coordinate 1 ⧸ reps rK88)
    ∈ fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88) :=
  repsFix_of_siftB rK88 ⟨22, by decide⟩ T88_22 (by decide)

theorem hinj88_22 : Function.Injective
    (fun i => ((T88_22 i : Coordinate 1) : Coordinate 1 ⧸ reps rK88)) :=
  repsInj_of_reduceAux rK88 T88_22 (by decide)

theorem hcardT88_22 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK88 ⟨22, by decide⟩ R88 hpxR88 hcardq88 (by decide)).symm

/-- **Cell (88, 22).** -/
theorem cell88_22 (e : List (ZMod 25)) (heK : charOK (basisAt rK88) e = true)
    (h : ↥(reps (⟨22, by decide⟩ : Fin 148))) :
    species (reps (⟨22, by decide⟩ : Fin 148)) h (basisElt (reps rK88) (charOfVec rK88 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK88 e (h : Coordinate 1) T88_22 i :=
  species_entry_eq_sum rK88 ⟨22, by decide⟩ e heK h T88_22 hfix88_22 hinj88_22 hcardT88_22
    (fun i => conj_mem_of_fixedPoints (reps ⟨22, by decide⟩) (reps rK88) (T88_22 i) (hfix88_22 i) h)

/-! ## Cell (88, 23): |T| = 5 -/

def T88_23list : List Coordinates := [(0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0)]
def T88_23 : Fin 5 → Coordinate 1 := fun i => T88_23list.getD i.val (0,0,0,0,0)

theorem hfix88_23 : ∀ i, ((T88_23 i : Coordinate 1) : Coordinate 1 ⧸ reps rK88)
    ∈ fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88) :=
  repsFix_of_siftB rK88 ⟨23, by decide⟩ T88_23 (by decide)

theorem hinj88_23 : Function.Injective
    (fun i => ((T88_23 i : Coordinate 1) : Coordinate 1 ⧸ reps rK88)) :=
  repsInj_of_reduceAux rK88 T88_23 (by decide)

theorem hcardT88_23 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK88 ⟨23, by decide⟩ R88 hpxR88 hcardq88 (by decide)).symm

/-- **Cell (88, 23).** -/
theorem cell88_23 (e : List (ZMod 25)) (heK : charOK (basisAt rK88) e = true)
    (h : ↥(reps (⟨23, by decide⟩ : Fin 148))) :
    species (reps (⟨23, by decide⟩ : Fin 148)) h (basisElt (reps rK88) (charOfVec rK88 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK88 e (h : Coordinate 1) T88_23 i :=
  species_entry_eq_sum rK88 ⟨23, by decide⟩ e heK h T88_23 hfix88_23 hinj88_23 hcardT88_23
    (fun i => conj_mem_of_fixedPoints (reps ⟨23, by decide⟩) (reps rK88) (T88_23 i) (hfix88_23 i) h)

/-! ## Cell (88, 24): |T| = 25 -/

def T88_24list : List Coordinates := [(0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,1,0,1,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0)]
def T88_24 : Fin 25 → Coordinate 1 := fun i => T88_24list.getD i.val (0,0,0,0,0)

theorem hfix88_24 : ∀ i, ((T88_24 i : Coordinate 1) : Coordinate 1 ⧸ reps rK88)
    ∈ fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88) :=
  repsFix_of_siftB rK88 ⟨24, by decide⟩ T88_24 (by decide)

theorem hinj88_24 : Function.Injective
    (fun i => ((T88_24 i : Coordinate 1) : Coordinate 1 ⧸ reps rK88)) :=
  repsInj_of_reduceAux rK88 T88_24 (by decide)

theorem hcardT88_24 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK88 ⟨24, by decide⟩ R88 hpxR88 hcardq88 (by decide)).symm

/-- **Cell (88, 24).** -/
theorem cell88_24 (e : List (ZMod 25)) (heK : charOK (basisAt rK88) e = true)
    (h : ↥(reps (⟨24, by decide⟩ : Fin 148))) :
    species (reps (⟨24, by decide⟩ : Fin 148)) h (basisElt (reps rK88) (charOfVec rK88 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK88 e (h : Coordinate 1) T88_24 i :=
  species_entry_eq_sum rK88 ⟨24, by decide⟩ e heK h T88_24 hfix88_24 hinj88_24 hcardT88_24
    (fun i => conj_mem_of_fixedPoints (reps ⟨24, by decide⟩) (reps rK88) (T88_24 i) (hfix88_24 i) h)

/-! ## Cell (88, 54): |T| = 5 -/

def T88_54list : List Coordinates := [(0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0)]
def T88_54 : Fin 5 → Coordinate 1 := fun i => T88_54list.getD i.val (0,0,0,0,0)

theorem hfix88_54 : ∀ i, ((T88_54 i : Coordinate 1) : Coordinate 1 ⧸ reps rK88)
    ∈ fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88) :=
  repsFix_of_siftB rK88 ⟨54, by decide⟩ T88_54 (by decide)

theorem hinj88_54 : Function.Injective
    (fun i => ((T88_54 i : Coordinate 1) : Coordinate 1 ⧸ reps rK88)) :=
  repsInj_of_reduceAux rK88 T88_54 (by decide)

theorem hcardT88_54 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK88 ⟨54, by decide⟩ R88 hpxR88 hcardq88 (by decide)).symm

/-- **Cell (88, 54).** -/
theorem cell88_54 (e : List (ZMod 25)) (heK : charOK (basisAt rK88) e = true)
    (h : ↥(reps (⟨54, by decide⟩ : Fin 148))) :
    species (reps (⟨54, by decide⟩ : Fin 148)) h (basisElt (reps rK88) (charOfVec rK88 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK88 e (h : Coordinate 1) T88_54 i :=
  species_entry_eq_sum rK88 ⟨54, by decide⟩ e heK h T88_54 hfix88_54 hinj88_54 hcardT88_54
    (fun i => conj_mem_of_fixedPoints (reps ⟨54, by decide⟩) (reps rK88) (T88_54 i) (hfix88_54 i) h)

/-! ## Cell (88, 88): |T| = 5 -/

def T88_88list : List Coordinates := [(0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0)]
def T88_88 : Fin 5 → Coordinate 1 := fun i => T88_88list.getD i.val (0,0,0,0,0)

theorem hfix88_88 : ∀ i, ((T88_88 i : Coordinate 1) : Coordinate 1 ⧸ reps rK88)
    ∈ fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88) :=
  repsFix_of_siftB rK88 ⟨88, by decide⟩ T88_88 (by decide)

theorem hinj88_88 : Function.Injective
    (fun i => ((T88_88 i : Coordinate 1) : Coordinate 1 ⧸ reps rK88)) :=
  repsInj_of_reduceAux rK88 T88_88 (by decide)

theorem hcardT88_88 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK88 ⟨88, by decide⟩ R88 hpxR88 hcardq88 (by decide)).symm

/-- **Cell (88, 88).** -/
theorem cell88_88 (e : List (ZMod 25)) (heK : charOK (basisAt rK88) e = true)
    (h : ↥(reps (⟨88, by decide⟩ : Fin 148))) :
    species (reps (⟨88, by decide⟩ : Fin 148)) h (basisElt (reps rK88) (charOfVec rK88 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK88 e (h : Coordinate 1) T88_88 i :=
  species_entry_eq_sum rK88 ⟨88, by decide⟩ e heK h T88_88 hfix88_88 hinj88_88 hcardT88_88
    (fun i => conj_mem_of_fixedPoints (reps ⟨88, by decide⟩) (reps rK88) (T88_88 i) (hfix88_88 i) h)

namespace Q2

def R88_2 : Fin 25 → Coordinate 2 := fun i => R88list.getD i.val (0,0,0,0,0)
theorem hpxR88_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK88) (R88_2 i)) := by decide
theorem hcardq88_2 : Nat.card (Coordinate 2 ⧸ reps rK88) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (88, 0) twin -/

def T88_0_2 : Fin 25 → Coordinate 2 := fun i => T88_0list.getD i.val (0,0,0,0,0)

theorem hfix88_0_2 : ∀ i, ((T88_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK88)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK88) :=
  repsFix_of_siftB2 rK88 ⟨0, by decide⟩ T88_0_2 (by decide)

theorem hinj88_0_2 : Function.Injective
    (fun i => ((T88_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK88)) :=
  repsInj_of_reduceAux2 rK88 T88_0_2 (by decide)

theorem hcardT88_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK88)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK88 ⟨0, by decide⟩ R88_2 hpxR88_2 hcardq88_2 (by decide)).symm

/-- **Cell (88, 0) twin (q=2).** -/
theorem cell88_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK88) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK88) (charOfVec2 rK88 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK88 e (h : Coordinate 2) T88_0_2 i :=
  species_entry_eq_sum rK88 ⟨0, by decide⟩ e heK h T88_0_2 hfix88_0_2 hinj88_0_2 hcardT88_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK88) (T88_0_2 i) (hfix88_0_2 i) h)

/-! ### Cell (88, 2) twin -/

def T88_2_2 : Fin 5 → Coordinate 2 := fun i => T88_2list.getD i.val (0,0,0,0,0)

theorem hfix88_2_2 : ∀ i, ((T88_2_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK88)
    ∈ fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK88) :=
  repsFix_of_siftB2 rK88 ⟨2, by decide⟩ T88_2_2 (by decide)

theorem hinj88_2_2 : Function.Injective
    (fun i => ((T88_2_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK88)) :=
  repsInj_of_reduceAux2 rK88 T88_2_2 (by decide)

theorem hcardT88_2_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK88)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK88 ⟨2, by decide⟩ R88_2 hpxR88_2 hcardq88_2 (by decide)).symm

/-- **Cell (88, 2) twin (q=2).** -/
theorem cell88_2_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK88) e = true)
    (h : ↥(reps (⟨2, by decide⟩ : Fin 148))) :
    species (reps (⟨2, by decide⟩ : Fin 148)) h (basisElt (reps rK88) (charOfVec2 rK88 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK88 e (h : Coordinate 2) T88_2_2 i :=
  species_entry_eq_sum rK88 ⟨2, by decide⟩ e heK h T88_2_2 hfix88_2_2 hinj88_2_2 hcardT88_2_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨2, by decide⟩) (reps rK88) (T88_2_2 i) (hfix88_2_2 i) h)

/-! ### Cell (88, 3) twin -/

def T88_3_2 : Fin 5 → Coordinate 2 := fun i => T88_3list.getD i.val (0,0,0,0,0)

theorem hfix88_3_2 : ∀ i, ((T88_3_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK88)
    ∈ fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK88) :=
  repsFix_of_siftB2 rK88 ⟨3, by decide⟩ T88_3_2 (by decide)

theorem hinj88_3_2 : Function.Injective
    (fun i => ((T88_3_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK88)) :=
  repsInj_of_reduceAux2 rK88 T88_3_2 (by decide)

theorem hcardT88_3_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK88)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK88 ⟨3, by decide⟩ R88_2 hpxR88_2 hcardq88_2 (by decide)).symm

/-- **Cell (88, 3) twin (q=2).** -/
theorem cell88_3_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK88) e = true)
    (h : ↥(reps (⟨3, by decide⟩ : Fin 148))) :
    species (reps (⟨3, by decide⟩ : Fin 148)) h (basisElt (reps rK88) (charOfVec2 rK88 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK88 e (h : Coordinate 2) T88_3_2 i :=
  species_entry_eq_sum rK88 ⟨3, by decide⟩ e heK h T88_3_2 hfix88_3_2 hinj88_3_2 hcardT88_3_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨3, by decide⟩) (reps rK88) (T88_3_2 i) (hfix88_3_2 i) h)

/-! ### Cell (88, 4) twin -/

def T88_4_2 : Fin 5 → Coordinate 2 := fun i => T88_4list.getD i.val (0,0,0,0,0)

theorem hfix88_4_2 : ∀ i, ((T88_4_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK88)
    ∈ fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK88) :=
  repsFix_of_siftB2 rK88 ⟨4, by decide⟩ T88_4_2 (by decide)

theorem hinj88_4_2 : Function.Injective
    (fun i => ((T88_4_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK88)) :=
  repsInj_of_reduceAux2 rK88 T88_4_2 (by decide)

theorem hcardT88_4_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK88)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK88 ⟨4, by decide⟩ R88_2 hpxR88_2 hcardq88_2 (by decide)).symm

/-- **Cell (88, 4) twin (q=2).** -/
theorem cell88_4_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK88) e = true)
    (h : ↥(reps (⟨4, by decide⟩ : Fin 148))) :
    species (reps (⟨4, by decide⟩ : Fin 148)) h (basisElt (reps rK88) (charOfVec2 rK88 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK88 e (h : Coordinate 2) T88_4_2 i :=
  species_entry_eq_sum rK88 ⟨4, by decide⟩ e heK h T88_4_2 hfix88_4_2 hinj88_4_2 hcardT88_4_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨4, by decide⟩) (reps rK88) (T88_4_2 i) (hfix88_4_2 i) h)

/-! ### Cell (88, 5) twin -/

def T88_5_2 : Fin 5 → Coordinate 2 := fun i => T88_5list.getD i.val (0,0,0,0,0)

theorem hfix88_5_2 : ∀ i, ((T88_5_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK88)
    ∈ fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK88) :=
  repsFix_of_siftB2 rK88 ⟨5, by decide⟩ T88_5_2 (by decide)

theorem hinj88_5_2 : Function.Injective
    (fun i => ((T88_5_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK88)) :=
  repsInj_of_reduceAux2 rK88 T88_5_2 (by decide)

theorem hcardT88_5_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK88)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK88 ⟨5, by decide⟩ R88_2 hpxR88_2 hcardq88_2 (by decide)).symm

/-- **Cell (88, 5) twin (q=2).** -/
theorem cell88_5_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK88) e = true)
    (h : ↥(reps (⟨5, by decide⟩ : Fin 148))) :
    species (reps (⟨5, by decide⟩ : Fin 148)) h (basisElt (reps rK88) (charOfVec2 rK88 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK88 e (h : Coordinate 2) T88_5_2 i :=
  species_entry_eq_sum rK88 ⟨5, by decide⟩ e heK h T88_5_2 hfix88_5_2 hinj88_5_2 hcardT88_5_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨5, by decide⟩) (reps rK88) (T88_5_2 i) (hfix88_5_2 i) h)

/-! ### Cell (88, 6) twin -/

def T88_6_2 : Fin 25 → Coordinate 2 := fun i => T88_6list.getD i.val (0,0,0,0,0)

theorem hfix88_6_2 : ∀ i, ((T88_6_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK88)
    ∈ fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK88) :=
  repsFix_of_siftB2 rK88 ⟨6, by decide⟩ T88_6_2 (by decide)

theorem hinj88_6_2 : Function.Injective
    (fun i => ((T88_6_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK88)) :=
  repsInj_of_reduceAux2 rK88 T88_6_2 (by decide)

theorem hcardT88_6_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK88)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK88 ⟨6, by decide⟩ R88_2 hpxR88_2 hcardq88_2 (by decide)).symm

/-- **Cell (88, 6) twin (q=2).** -/
theorem cell88_6_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK88) e = true)
    (h : ↥(reps (⟨6, by decide⟩ : Fin 148))) :
    species (reps (⟨6, by decide⟩ : Fin 148)) h (basisElt (reps rK88) (charOfVec2 rK88 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK88 e (h : Coordinate 2) T88_6_2 i :=
  species_entry_eq_sum rK88 ⟨6, by decide⟩ e heK h T88_6_2 hfix88_6_2 hinj88_6_2 hcardT88_6_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨6, by decide⟩) (reps rK88) (T88_6_2 i) (hfix88_6_2 i) h)

/-! ### Cell (88, 11) twin -/

def T88_11_2 : Fin 5 → Coordinate 2 := fun i => T88_11list.getD i.val (0,0,0,0,0)

theorem hfix88_11_2 : ∀ i, ((T88_11_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK88)
    ∈ fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK88) :=
  repsFix_of_siftB2 rK88 ⟨11, by decide⟩ T88_11_2 (by decide)

theorem hinj88_11_2 : Function.Injective
    (fun i => ((T88_11_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK88)) :=
  repsInj_of_reduceAux2 rK88 T88_11_2 (by decide)

theorem hcardT88_11_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK88)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK88 ⟨11, by decide⟩ R88_2 hpxR88_2 hcardq88_2 (by decide)).symm

/-- **Cell (88, 11) twin (q=2).** -/
theorem cell88_11_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK88) e = true)
    (h : ↥(reps (⟨11, by decide⟩ : Fin 148))) :
    species (reps (⟨11, by decide⟩ : Fin 148)) h (basisElt (reps rK88) (charOfVec2 rK88 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK88 e (h : Coordinate 2) T88_11_2 i :=
  species_entry_eq_sum rK88 ⟨11, by decide⟩ e heK h T88_11_2 hfix88_11_2 hinj88_11_2 hcardT88_11_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨11, by decide⟩) (reps rK88) (T88_11_2 i) (hfix88_11_2 i) h)

/-! ### Cell (88, 12) twin -/

def T88_12_2 : Fin 25 → Coordinate 2 := fun i => T88_12list.getD i.val (0,0,0,0,0)

theorem hfix88_12_2 : ∀ i, ((T88_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK88)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK88) :=
  repsFix_of_siftB2 rK88 ⟨12, by decide⟩ T88_12_2 (by decide)

theorem hinj88_12_2 : Function.Injective
    (fun i => ((T88_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK88)) :=
  repsInj_of_reduceAux2 rK88 T88_12_2 (by decide)

theorem hcardT88_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK88)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK88 ⟨12, by decide⟩ R88_2 hpxR88_2 hcardq88_2 (by decide)).symm

/-- **Cell (88, 12) twin (q=2).** -/
theorem cell88_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK88) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK88) (charOfVec2 rK88 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK88 e (h : Coordinate 2) T88_12_2 i :=
  species_entry_eq_sum rK88 ⟨12, by decide⟩ e heK h T88_12_2 hfix88_12_2 hinj88_12_2 hcardT88_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK88) (T88_12_2 i) (hfix88_12_2 i) h)

/-! ### Cell (88, 20) twin -/

def T88_20_2 : Fin 5 → Coordinate 2 := fun i => T88_20list.getD i.val (0,0,0,0,0)

theorem hfix88_20_2 : ∀ i, ((T88_20_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK88)
    ∈ fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK88) :=
  repsFix_of_siftB2 rK88 ⟨20, by decide⟩ T88_20_2 (by decide)

theorem hinj88_20_2 : Function.Injective
    (fun i => ((T88_20_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK88)) :=
  repsInj_of_reduceAux2 rK88 T88_20_2 (by decide)

theorem hcardT88_20_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK88)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK88 ⟨20, by decide⟩ R88_2 hpxR88_2 hcardq88_2 (by decide)).symm

/-- **Cell (88, 20) twin (q=2).** -/
theorem cell88_20_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK88) e = true)
    (h : ↥(reps (⟨20, by decide⟩ : Fin 148))) :
    species (reps (⟨20, by decide⟩ : Fin 148)) h (basisElt (reps rK88) (charOfVec2 rK88 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK88 e (h : Coordinate 2) T88_20_2 i :=
  species_entry_eq_sum rK88 ⟨20, by decide⟩ e heK h T88_20_2 hfix88_20_2 hinj88_20_2 hcardT88_20_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨20, by decide⟩) (reps rK88) (T88_20_2 i) (hfix88_20_2 i) h)

/-! ### Cell (88, 21) twin -/

def T88_21_2 : Fin 5 → Coordinate 2 := fun i => T88_21list.getD i.val (0,0,0,0,0)

theorem hfix88_21_2 : ∀ i, ((T88_21_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK88)
    ∈ fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK88) :=
  repsFix_of_siftB2 rK88 ⟨21, by decide⟩ T88_21_2 (by decide)

theorem hinj88_21_2 : Function.Injective
    (fun i => ((T88_21_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK88)) :=
  repsInj_of_reduceAux2 rK88 T88_21_2 (by decide)

theorem hcardT88_21_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK88)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK88 ⟨21, by decide⟩ R88_2 hpxR88_2 hcardq88_2 (by decide)).symm

/-- **Cell (88, 21) twin (q=2).** -/
theorem cell88_21_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK88) e = true)
    (h : ↥(reps (⟨21, by decide⟩ : Fin 148))) :
    species (reps (⟨21, by decide⟩ : Fin 148)) h (basisElt (reps rK88) (charOfVec2 rK88 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK88 e (h : Coordinate 2) T88_21_2 i :=
  species_entry_eq_sum rK88 ⟨21, by decide⟩ e heK h T88_21_2 hfix88_21_2 hinj88_21_2 hcardT88_21_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨21, by decide⟩) (reps rK88) (T88_21_2 i) (hfix88_21_2 i) h)

/-! ### Cell (88, 22) twin -/

def T88_22_2 : Fin 5 → Coordinate 2 := fun i => T88_22list.getD i.val (0,0,0,0,0)

theorem hfix88_22_2 : ∀ i, ((T88_22_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK88)
    ∈ fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK88) :=
  repsFix_of_siftB2 rK88 ⟨22, by decide⟩ T88_22_2 (by decide)

theorem hinj88_22_2 : Function.Injective
    (fun i => ((T88_22_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK88)) :=
  repsInj_of_reduceAux2 rK88 T88_22_2 (by decide)

theorem hcardT88_22_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK88)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK88 ⟨22, by decide⟩ R88_2 hpxR88_2 hcardq88_2 (by decide)).symm

/-- **Cell (88, 22) twin (q=2).** -/
theorem cell88_22_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK88) e = true)
    (h : ↥(reps (⟨22, by decide⟩ : Fin 148))) :
    species (reps (⟨22, by decide⟩ : Fin 148)) h (basisElt (reps rK88) (charOfVec2 rK88 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK88 e (h : Coordinate 2) T88_22_2 i :=
  species_entry_eq_sum rK88 ⟨22, by decide⟩ e heK h T88_22_2 hfix88_22_2 hinj88_22_2 hcardT88_22_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨22, by decide⟩) (reps rK88) (T88_22_2 i) (hfix88_22_2 i) h)

/-! ### Cell (88, 23) twin -/

def T88_23_2 : Fin 5 → Coordinate 2 := fun i => T88_23list.getD i.val (0,0,0,0,0)

theorem hfix88_23_2 : ∀ i, ((T88_23_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK88)
    ∈ fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK88) :=
  repsFix_of_siftB2 rK88 ⟨23, by decide⟩ T88_23_2 (by decide)

theorem hinj88_23_2 : Function.Injective
    (fun i => ((T88_23_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK88)) :=
  repsInj_of_reduceAux2 rK88 T88_23_2 (by decide)

theorem hcardT88_23_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK88)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK88 ⟨23, by decide⟩ R88_2 hpxR88_2 hcardq88_2 (by decide)).symm

/-- **Cell (88, 23) twin (q=2).** -/
theorem cell88_23_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK88) e = true)
    (h : ↥(reps (⟨23, by decide⟩ : Fin 148))) :
    species (reps (⟨23, by decide⟩ : Fin 148)) h (basisElt (reps rK88) (charOfVec2 rK88 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK88 e (h : Coordinate 2) T88_23_2 i :=
  species_entry_eq_sum rK88 ⟨23, by decide⟩ e heK h T88_23_2 hfix88_23_2 hinj88_23_2 hcardT88_23_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨23, by decide⟩) (reps rK88) (T88_23_2 i) (hfix88_23_2 i) h)

/-! ### Cell (88, 24) twin -/

def T88_24_2 : Fin 25 → Coordinate 2 := fun i => T88_24list.getD i.val (0,0,0,0,0)

theorem hfix88_24_2 : ∀ i, ((T88_24_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK88)
    ∈ fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK88) :=
  repsFix_of_siftB2 rK88 ⟨24, by decide⟩ T88_24_2 (by decide)

theorem hinj88_24_2 : Function.Injective
    (fun i => ((T88_24_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK88)) :=
  repsInj_of_reduceAux2 rK88 T88_24_2 (by decide)

theorem hcardT88_24_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK88)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK88 ⟨24, by decide⟩ R88_2 hpxR88_2 hcardq88_2 (by decide)).symm

/-- **Cell (88, 24) twin (q=2).** -/
theorem cell88_24_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK88) e = true)
    (h : ↥(reps (⟨24, by decide⟩ : Fin 148))) :
    species (reps (⟨24, by decide⟩ : Fin 148)) h (basisElt (reps rK88) (charOfVec2 rK88 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK88 e (h : Coordinate 2) T88_24_2 i :=
  species_entry_eq_sum rK88 ⟨24, by decide⟩ e heK h T88_24_2 hfix88_24_2 hinj88_24_2 hcardT88_24_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨24, by decide⟩) (reps rK88) (T88_24_2 i) (hfix88_24_2 i) h)

/-! ### Cell (88, 54) twin -/

def T88_54_2 : Fin 5 → Coordinate 2 := fun i => T88_54list.getD i.val (0,0,0,0,0)

theorem hfix88_54_2 : ∀ i, ((T88_54_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK88)
    ∈ fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK88) :=
  repsFix_of_siftB2 rK88 ⟨54, by decide⟩ T88_54_2 (by decide)

theorem hinj88_54_2 : Function.Injective
    (fun i => ((T88_54_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK88)) :=
  repsInj_of_reduceAux2 rK88 T88_54_2 (by decide)

theorem hcardT88_54_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK88)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK88 ⟨54, by decide⟩ R88_2 hpxR88_2 hcardq88_2 (by decide)).symm

/-- **Cell (88, 54) twin (q=2).** -/
theorem cell88_54_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK88) e = true)
    (h : ↥(reps (⟨54, by decide⟩ : Fin 148))) :
    species (reps (⟨54, by decide⟩ : Fin 148)) h (basisElt (reps rK88) (charOfVec2 rK88 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK88 e (h : Coordinate 2) T88_54_2 i :=
  species_entry_eq_sum rK88 ⟨54, by decide⟩ e heK h T88_54_2 hfix88_54_2 hinj88_54_2 hcardT88_54_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨54, by decide⟩) (reps rK88) (T88_54_2 i) (hfix88_54_2 i) h)

/-! ### Cell (88, 88) twin -/

def T88_88_2 : Fin 5 → Coordinate 2 := fun i => T88_88list.getD i.val (0,0,0,0,0)

theorem hfix88_88_2 : ∀ i, ((T88_88_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK88)
    ∈ fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK88) :=
  repsFix_of_siftB2 rK88 ⟨88, by decide⟩ T88_88_2 (by decide)

theorem hinj88_88_2 : Function.Injective
    (fun i => ((T88_88_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK88)) :=
  repsInj_of_reduceAux2 rK88 T88_88_2 (by decide)

theorem hcardT88_88_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK88)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK88 ⟨88, by decide⟩ R88_2 hpxR88_2 hcardq88_2 (by decide)).symm

/-- **Cell (88, 88) twin (q=2).** -/
theorem cell88_88_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK88) e = true)
    (h : ↥(reps (⟨88, by decide⟩ : Fin 148))) :
    species (reps (⟨88, by decide⟩ : Fin 148)) h (basisElt (reps rK88) (charOfVec2 rK88 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK88 e (h : Coordinate 2) T88_88_2 i :=
  species_entry_eq_sum rK88 ⟨88, by decide⟩ e heK h T88_88_2 hfix88_88_2 hinj88_88_2 hcardT88_88_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨88, by decide⟩) (reps rK88) (T88_88_2 i) (hfix88_88_2 i) h)

end Q2

/-! # K-class rK = 89  (|G/K| = 25) -/

def rK89 : Fin 148 := ⟨89, by decide⟩

def R89list : List Coordinates := [(0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0)]
def R89 : Fin 25 → Coordinate 1 := fun i => R89list.getD i.val (0,0,0,0,0)

theorem hpxR89 : Function.Injective (fun i => reduceAux 1 (basisAt rK89) (R89 i)) := by decide
theorem hcardq89 : Nat.card (Coordinate 1 ⧸ reps rK89) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (89, 0): |T| = 25 -/

def T89_0list : List Coordinates := [(0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0)]
def T89_0 : Fin 25 → Coordinate 1 := fun i => T89_0list.getD i.val (0,0,0,0,0)

theorem hfix89_0 : ∀ i, ((T89_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK89)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89) :=
  repsFix_of_siftB rK89 ⟨0, by decide⟩ T89_0 (by decide)

theorem hinj89_0 : Function.Injective
    (fun i => ((T89_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK89)) :=
  repsInj_of_reduceAux rK89 T89_0 (by decide)

theorem hcardT89_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK89 ⟨0, by decide⟩ R89 hpxR89 hcardq89 (by decide)).symm

/-- **Cell (89, 0).** -/
theorem cell89_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK89) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK89) (charOfVec rK89 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK89 e (h : Coordinate 1) T89_0 i :=
  species_entry_eq_sum rK89 ⟨0, by decide⟩ e heK h T89_0 hfix89_0 hinj89_0 hcardT89_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK89) (T89_0 i) (hfix89_0 i) h)

/-! ## Cell (89, 2): |T| = 5 -/

def T89_2list : List Coordinates := [(0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0)]
def T89_2 : Fin 5 → Coordinate 1 := fun i => T89_2list.getD i.val (0,0,0,0,0)

theorem hfix89_2 : ∀ i, ((T89_2 i : Coordinate 1) : Coordinate 1 ⧸ reps rK89)
    ∈ fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89) :=
  repsFix_of_siftB rK89 ⟨2, by decide⟩ T89_2 (by decide)

theorem hinj89_2 : Function.Injective
    (fun i => ((T89_2 i : Coordinate 1) : Coordinate 1 ⧸ reps rK89)) :=
  repsInj_of_reduceAux rK89 T89_2 (by decide)

theorem hcardT89_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK89 ⟨2, by decide⟩ R89 hpxR89 hcardq89 (by decide)).symm

/-- **Cell (89, 2).** -/
theorem cell89_2 (e : List (ZMod 25)) (heK : charOK (basisAt rK89) e = true)
    (h : ↥(reps (⟨2, by decide⟩ : Fin 148))) :
    species (reps (⟨2, by decide⟩ : Fin 148)) h (basisElt (reps rK89) (charOfVec rK89 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK89 e (h : Coordinate 1) T89_2 i :=
  species_entry_eq_sum rK89 ⟨2, by decide⟩ e heK h T89_2 hfix89_2 hinj89_2 hcardT89_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨2, by decide⟩) (reps rK89) (T89_2 i) (hfix89_2 i) h)

/-! ## Cell (89, 3): |T| = 5 -/

def T89_3list : List Coordinates := [(0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0)]
def T89_3 : Fin 5 → Coordinate 1 := fun i => T89_3list.getD i.val (0,0,0,0,0)

theorem hfix89_3 : ∀ i, ((T89_3 i : Coordinate 1) : Coordinate 1 ⧸ reps rK89)
    ∈ fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89) :=
  repsFix_of_siftB rK89 ⟨3, by decide⟩ T89_3 (by decide)

theorem hinj89_3 : Function.Injective
    (fun i => ((T89_3 i : Coordinate 1) : Coordinate 1 ⧸ reps rK89)) :=
  repsInj_of_reduceAux rK89 T89_3 (by decide)

theorem hcardT89_3 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK89 ⟨3, by decide⟩ R89 hpxR89 hcardq89 (by decide)).symm

/-- **Cell (89, 3).** -/
theorem cell89_3 (e : List (ZMod 25)) (heK : charOK (basisAt rK89) e = true)
    (h : ↥(reps (⟨3, by decide⟩ : Fin 148))) :
    species (reps (⟨3, by decide⟩ : Fin 148)) h (basisElt (reps rK89) (charOfVec rK89 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK89 e (h : Coordinate 1) T89_3 i :=
  species_entry_eq_sum rK89 ⟨3, by decide⟩ e heK h T89_3 hfix89_3 hinj89_3 hcardT89_3
    (fun i => conj_mem_of_fixedPoints (reps ⟨3, by decide⟩) (reps rK89) (T89_3 i) (hfix89_3 i) h)

/-! ## Cell (89, 4): |T| = 5 -/

def T89_4list : List Coordinates := [(0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0)]
def T89_4 : Fin 5 → Coordinate 1 := fun i => T89_4list.getD i.val (0,0,0,0,0)

theorem hfix89_4 : ∀ i, ((T89_4 i : Coordinate 1) : Coordinate 1 ⧸ reps rK89)
    ∈ fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89) :=
  repsFix_of_siftB rK89 ⟨4, by decide⟩ T89_4 (by decide)

theorem hinj89_4 : Function.Injective
    (fun i => ((T89_4 i : Coordinate 1) : Coordinate 1 ⧸ reps rK89)) :=
  repsInj_of_reduceAux rK89 T89_4 (by decide)

theorem hcardT89_4 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK89 ⟨4, by decide⟩ R89 hpxR89 hcardq89 (by decide)).symm

/-- **Cell (89, 4).** -/
theorem cell89_4 (e : List (ZMod 25)) (heK : charOK (basisAt rK89) e = true)
    (h : ↥(reps (⟨4, by decide⟩ : Fin 148))) :
    species (reps (⟨4, by decide⟩ : Fin 148)) h (basisElt (reps rK89) (charOfVec rK89 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK89 e (h : Coordinate 1) T89_4 i :=
  species_entry_eq_sum rK89 ⟨4, by decide⟩ e heK h T89_4 hfix89_4 hinj89_4 hcardT89_4
    (fun i => conj_mem_of_fixedPoints (reps ⟨4, by decide⟩) (reps rK89) (T89_4 i) (hfix89_4 i) h)

/-! ## Cell (89, 5): |T| = 5 -/

def T89_5list : List Coordinates := [(0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0)]
def T89_5 : Fin 5 → Coordinate 1 := fun i => T89_5list.getD i.val (0,0,0,0,0)

theorem hfix89_5 : ∀ i, ((T89_5 i : Coordinate 1) : Coordinate 1 ⧸ reps rK89)
    ∈ fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89) :=
  repsFix_of_siftB rK89 ⟨5, by decide⟩ T89_5 (by decide)

theorem hinj89_5 : Function.Injective
    (fun i => ((T89_5 i : Coordinate 1) : Coordinate 1 ⧸ reps rK89)) :=
  repsInj_of_reduceAux rK89 T89_5 (by decide)

theorem hcardT89_5 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK89 ⟨5, by decide⟩ R89 hpxR89 hcardq89 (by decide)).symm

/-- **Cell (89, 5).** -/
theorem cell89_5 (e : List (ZMod 25)) (heK : charOK (basisAt rK89) e = true)
    (h : ↥(reps (⟨5, by decide⟩ : Fin 148))) :
    species (reps (⟨5, by decide⟩ : Fin 148)) h (basisElt (reps rK89) (charOfVec rK89 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK89 e (h : Coordinate 1) T89_5 i :=
  species_entry_eq_sum rK89 ⟨5, by decide⟩ e heK h T89_5 hfix89_5 hinj89_5 hcardT89_5
    (fun i => conj_mem_of_fixedPoints (reps ⟨5, by decide⟩) (reps rK89) (T89_5 i) (hfix89_5 i) h)

/-! ## Cell (89, 8): |T| = 25 -/

def T89_8list : List Coordinates := [(0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0)]
def T89_8 : Fin 25 → Coordinate 1 := fun i => T89_8list.getD i.val (0,0,0,0,0)

theorem hfix89_8 : ∀ i, ((T89_8 i : Coordinate 1) : Coordinate 1 ⧸ reps rK89)
    ∈ fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89) :=
  repsFix_of_siftB rK89 ⟨8, by decide⟩ T89_8 (by decide)

theorem hinj89_8 : Function.Injective
    (fun i => ((T89_8 i : Coordinate 1) : Coordinate 1 ⧸ reps rK89)) :=
  repsInj_of_reduceAux rK89 T89_8 (by decide)

theorem hcardT89_8 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK89 ⟨8, by decide⟩ R89 hpxR89 hcardq89 (by decide)).symm

/-- **Cell (89, 8).** -/
theorem cell89_8 (e : List (ZMod 25)) (heK : charOK (basisAt rK89) e = true)
    (h : ↥(reps (⟨8, by decide⟩ : Fin 148))) :
    species (reps (⟨8, by decide⟩ : Fin 148)) h (basisElt (reps rK89) (charOfVec rK89 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK89 e (h : Coordinate 1) T89_8 i :=
  species_entry_eq_sum rK89 ⟨8, by decide⟩ e heK h T89_8 hfix89_8 hinj89_8 hcardT89_8
    (fun i => conj_mem_of_fixedPoints (reps ⟨8, by decide⟩) (reps rK89) (T89_8 i) (hfix89_8 i) h)

/-! ## Cell (89, 11): |T| = 5 -/

def T89_11list : List Coordinates := [(0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0)]
def T89_11 : Fin 5 → Coordinate 1 := fun i => T89_11list.getD i.val (0,0,0,0,0)

theorem hfix89_11 : ∀ i, ((T89_11 i : Coordinate 1) : Coordinate 1 ⧸ reps rK89)
    ∈ fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89) :=
  repsFix_of_siftB rK89 ⟨11, by decide⟩ T89_11 (by decide)

theorem hinj89_11 : Function.Injective
    (fun i => ((T89_11 i : Coordinate 1) : Coordinate 1 ⧸ reps rK89)) :=
  repsInj_of_reduceAux rK89 T89_11 (by decide)

theorem hcardT89_11 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK89 ⟨11, by decide⟩ R89 hpxR89 hcardq89 (by decide)).symm

/-- **Cell (89, 11).** -/
theorem cell89_11 (e : List (ZMod 25)) (heK : charOK (basisAt rK89) e = true)
    (h : ↥(reps (⟨11, by decide⟩ : Fin 148))) :
    species (reps (⟨11, by decide⟩ : Fin 148)) h (basisElt (reps rK89) (charOfVec rK89 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK89 e (h : Coordinate 1) T89_11 i :=
  species_entry_eq_sum rK89 ⟨11, by decide⟩ e heK h T89_11 hfix89_11 hinj89_11 hcardT89_11
    (fun i => conj_mem_of_fixedPoints (reps ⟨11, by decide⟩) (reps rK89) (T89_11 i) (hfix89_11 i) h)

/-! ## Cell (89, 12): |T| = 25 -/

def T89_12list : List Coordinates := [(0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0)]
def T89_12 : Fin 25 → Coordinate 1 := fun i => T89_12list.getD i.val (0,0,0,0,0)

theorem hfix89_12 : ∀ i, ((T89_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK89)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89) :=
  repsFix_of_siftB rK89 ⟨12, by decide⟩ T89_12 (by decide)

theorem hinj89_12 : Function.Injective
    (fun i => ((T89_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK89)) :=
  repsInj_of_reduceAux rK89 T89_12 (by decide)

theorem hcardT89_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK89 ⟨12, by decide⟩ R89 hpxR89 hcardq89 (by decide)).symm

/-- **Cell (89, 12).** -/
theorem cell89_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK89) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK89) (charOfVec rK89 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK89 e (h : Coordinate 1) T89_12 i :=
  species_entry_eq_sum rK89 ⟨12, by decide⟩ e heK h T89_12 hfix89_12 hinj89_12 hcardT89_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK89) (T89_12 i) (hfix89_12 i) h)

/-! ## Cell (89, 20): |T| = 5 -/

def T89_20list : List Coordinates := [(0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0)]
def T89_20 : Fin 5 → Coordinate 1 := fun i => T89_20list.getD i.val (0,0,0,0,0)

theorem hfix89_20 : ∀ i, ((T89_20 i : Coordinate 1) : Coordinate 1 ⧸ reps rK89)
    ∈ fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89) :=
  repsFix_of_siftB rK89 ⟨20, by decide⟩ T89_20 (by decide)

theorem hinj89_20 : Function.Injective
    (fun i => ((T89_20 i : Coordinate 1) : Coordinate 1 ⧸ reps rK89)) :=
  repsInj_of_reduceAux rK89 T89_20 (by decide)

theorem hcardT89_20 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK89 ⟨20, by decide⟩ R89 hpxR89 hcardq89 (by decide)).symm

/-- **Cell (89, 20).** -/
theorem cell89_20 (e : List (ZMod 25)) (heK : charOK (basisAt rK89) e = true)
    (h : ↥(reps (⟨20, by decide⟩ : Fin 148))) :
    species (reps (⟨20, by decide⟩ : Fin 148)) h (basisElt (reps rK89) (charOfVec rK89 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK89 e (h : Coordinate 1) T89_20 i :=
  species_entry_eq_sum rK89 ⟨20, by decide⟩ e heK h T89_20 hfix89_20 hinj89_20 hcardT89_20
    (fun i => conj_mem_of_fixedPoints (reps ⟨20, by decide⟩) (reps rK89) (T89_20 i) (hfix89_20 i) h)

/-! ## Cell (89, 21): |T| = 5 -/

def T89_21list : List Coordinates := [(0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0)]
def T89_21 : Fin 5 → Coordinate 1 := fun i => T89_21list.getD i.val (0,0,0,0,0)

theorem hfix89_21 : ∀ i, ((T89_21 i : Coordinate 1) : Coordinate 1 ⧸ reps rK89)
    ∈ fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89) :=
  repsFix_of_siftB rK89 ⟨21, by decide⟩ T89_21 (by decide)

theorem hinj89_21 : Function.Injective
    (fun i => ((T89_21 i : Coordinate 1) : Coordinate 1 ⧸ reps rK89)) :=
  repsInj_of_reduceAux rK89 T89_21 (by decide)

theorem hcardT89_21 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK89 ⟨21, by decide⟩ R89 hpxR89 hcardq89 (by decide)).symm

/-- **Cell (89, 21).** -/
theorem cell89_21 (e : List (ZMod 25)) (heK : charOK (basisAt rK89) e = true)
    (h : ↥(reps (⟨21, by decide⟩ : Fin 148))) :
    species (reps (⟨21, by decide⟩ : Fin 148)) h (basisElt (reps rK89) (charOfVec rK89 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK89 e (h : Coordinate 1) T89_21 i :=
  species_entry_eq_sum rK89 ⟨21, by decide⟩ e heK h T89_21 hfix89_21 hinj89_21 hcardT89_21
    (fun i => conj_mem_of_fixedPoints (reps ⟨21, by decide⟩) (reps rK89) (T89_21 i) (hfix89_21 i) h)

/-! ## Cell (89, 22): |T| = 5 -/

def T89_22list : List Coordinates := [(0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0)]
def T89_22 : Fin 5 → Coordinate 1 := fun i => T89_22list.getD i.val (0,0,0,0,0)

theorem hfix89_22 : ∀ i, ((T89_22 i : Coordinate 1) : Coordinate 1 ⧸ reps rK89)
    ∈ fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89) :=
  repsFix_of_siftB rK89 ⟨22, by decide⟩ T89_22 (by decide)

theorem hinj89_22 : Function.Injective
    (fun i => ((T89_22 i : Coordinate 1) : Coordinate 1 ⧸ reps rK89)) :=
  repsInj_of_reduceAux rK89 T89_22 (by decide)

theorem hcardT89_22 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK89 ⟨22, by decide⟩ R89 hpxR89 hcardq89 (by decide)).symm

/-- **Cell (89, 22).** -/
theorem cell89_22 (e : List (ZMod 25)) (heK : charOK (basisAt rK89) e = true)
    (h : ↥(reps (⟨22, by decide⟩ : Fin 148))) :
    species (reps (⟨22, by decide⟩ : Fin 148)) h (basisElt (reps rK89) (charOfVec rK89 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK89 e (h : Coordinate 1) T89_22 i :=
  species_entry_eq_sum rK89 ⟨22, by decide⟩ e heK h T89_22 hfix89_22 hinj89_22 hcardT89_22
    (fun i => conj_mem_of_fixedPoints (reps ⟨22, by decide⟩) (reps rK89) (T89_22 i) (hfix89_22 i) h)

/-! ## Cell (89, 23): |T| = 5 -/

def T89_23list : List Coordinates := [(0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0)]
def T89_23 : Fin 5 → Coordinate 1 := fun i => T89_23list.getD i.val (0,0,0,0,0)

theorem hfix89_23 : ∀ i, ((T89_23 i : Coordinate 1) : Coordinate 1 ⧸ reps rK89)
    ∈ fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89) :=
  repsFix_of_siftB rK89 ⟨23, by decide⟩ T89_23 (by decide)

theorem hinj89_23 : Function.Injective
    (fun i => ((T89_23 i : Coordinate 1) : Coordinate 1 ⧸ reps rK89)) :=
  repsInj_of_reduceAux rK89 T89_23 (by decide)

theorem hcardT89_23 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK89 ⟨23, by decide⟩ R89 hpxR89 hcardq89 (by decide)).symm

/-- **Cell (89, 23).** -/
theorem cell89_23 (e : List (ZMod 25)) (heK : charOK (basisAt rK89) e = true)
    (h : ↥(reps (⟨23, by decide⟩ : Fin 148))) :
    species (reps (⟨23, by decide⟩ : Fin 148)) h (basisElt (reps rK89) (charOfVec rK89 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK89 e (h : Coordinate 1) T89_23 i :=
  species_entry_eq_sum rK89 ⟨23, by decide⟩ e heK h T89_23 hfix89_23 hinj89_23 hcardT89_23
    (fun i => conj_mem_of_fixedPoints (reps ⟨23, by decide⟩) (reps rK89) (T89_23 i) (hfix89_23 i) h)

/-! ## Cell (89, 26): |T| = 25 -/

def T89_26list : List Coordinates := [(0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,2,0,1,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,4,0,4,0), (0,4,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0)]
def T89_26 : Fin 25 → Coordinate 1 := fun i => T89_26list.getD i.val (0,0,0,0,0)

theorem hfix89_26 : ∀ i, ((T89_26 i : Coordinate 1) : Coordinate 1 ⧸ reps rK89)
    ∈ fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89) :=
  repsFix_of_siftB rK89 ⟨26, by decide⟩ T89_26 (by decide)

theorem hinj89_26 : Function.Injective
    (fun i => ((T89_26 i : Coordinate 1) : Coordinate 1 ⧸ reps rK89)) :=
  repsInj_of_reduceAux rK89 T89_26 (by decide)

theorem hcardT89_26 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK89 ⟨26, by decide⟩ R89 hpxR89 hcardq89 (by decide)).symm

/-- **Cell (89, 26).** -/
theorem cell89_26 (e : List (ZMod 25)) (heK : charOK (basisAt rK89) e = true)
    (h : ↥(reps (⟨26, by decide⟩ : Fin 148))) :
    species (reps (⟨26, by decide⟩ : Fin 148)) h (basisElt (reps rK89) (charOfVec rK89 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK89 e (h : Coordinate 1) T89_26 i :=
  species_entry_eq_sum rK89 ⟨26, by decide⟩ e heK h T89_26 hfix89_26 hinj89_26 hcardT89_26
    (fun i => conj_mem_of_fixedPoints (reps ⟨26, by decide⟩) (reps rK89) (T89_26 i) (hfix89_26 i) h)

/-! ## Cell (89, 54): |T| = 5 -/

def T89_54list : List Coordinates := [(0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0)]
def T89_54 : Fin 5 → Coordinate 1 := fun i => T89_54list.getD i.val (0,0,0,0,0)

theorem hfix89_54 : ∀ i, ((T89_54 i : Coordinate 1) : Coordinate 1 ⧸ reps rK89)
    ∈ fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89) :=
  repsFix_of_siftB rK89 ⟨54, by decide⟩ T89_54 (by decide)

theorem hinj89_54 : Function.Injective
    (fun i => ((T89_54 i : Coordinate 1) : Coordinate 1 ⧸ reps rK89)) :=
  repsInj_of_reduceAux rK89 T89_54 (by decide)

theorem hcardT89_54 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK89 ⟨54, by decide⟩ R89 hpxR89 hcardq89 (by decide)).symm

/-- **Cell (89, 54).** -/
theorem cell89_54 (e : List (ZMod 25)) (heK : charOK (basisAt rK89) e = true)
    (h : ↥(reps (⟨54, by decide⟩ : Fin 148))) :
    species (reps (⟨54, by decide⟩ : Fin 148)) h (basisElt (reps rK89) (charOfVec rK89 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK89 e (h : Coordinate 1) T89_54 i :=
  species_entry_eq_sum rK89 ⟨54, by decide⟩ e heK h T89_54 hfix89_54 hinj89_54 hcardT89_54
    (fun i => conj_mem_of_fixedPoints (reps ⟨54, by decide⟩) (reps rK89) (T89_54 i) (hfix89_54 i) h)

/-! ## Cell (89, 89): |T| = 5 -/

def T89_89list : List Coordinates := [(0,0,0,0,0), (0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0)]
def T89_89 : Fin 5 → Coordinate 1 := fun i => T89_89list.getD i.val (0,0,0,0,0)

theorem hfix89_89 : ∀ i, ((T89_89 i : Coordinate 1) : Coordinate 1 ⧸ reps rK89)
    ∈ fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89) :=
  repsFix_of_siftB rK89 ⟨89, by decide⟩ T89_89 (by decide)

theorem hinj89_89 : Function.Injective
    (fun i => ((T89_89 i : Coordinate 1) : Coordinate 1 ⧸ reps rK89)) :=
  repsInj_of_reduceAux rK89 T89_89 (by decide)

theorem hcardT89_89 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK89 ⟨89, by decide⟩ R89 hpxR89 hcardq89 (by decide)).symm

/-- **Cell (89, 89).** -/
theorem cell89_89 (e : List (ZMod 25)) (heK : charOK (basisAt rK89) e = true)
    (h : ↥(reps (⟨89, by decide⟩ : Fin 148))) :
    species (reps (⟨89, by decide⟩ : Fin 148)) h (basisElt (reps rK89) (charOfVec rK89 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK89 e (h : Coordinate 1) T89_89 i :=
  species_entry_eq_sum rK89 ⟨89, by decide⟩ e heK h T89_89 hfix89_89 hinj89_89 hcardT89_89
    (fun i => conj_mem_of_fixedPoints (reps ⟨89, by decide⟩) (reps rK89) (T89_89 i) (hfix89_89 i) h)

namespace Q2

def R89_2 : Fin 25 → Coordinate 2 := fun i => R89list.getD i.val (0,0,0,0,0)
theorem hpxR89_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK89) (R89_2 i)) := by decide
theorem hcardq89_2 : Nat.card (Coordinate 2 ⧸ reps rK89) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (89, 0) twin -/

def T89_0_2 : Fin 25 → Coordinate 2 := fun i => T89_0list.getD i.val (0,0,0,0,0)

theorem hfix89_0_2 : ∀ i, ((T89_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK89)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK89) :=
  repsFix_of_siftB2 rK89 ⟨0, by decide⟩ T89_0_2 (by decide)

theorem hinj89_0_2 : Function.Injective
    (fun i => ((T89_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK89)) :=
  repsInj_of_reduceAux2 rK89 T89_0_2 (by decide)

theorem hcardT89_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK89)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK89 ⟨0, by decide⟩ R89_2 hpxR89_2 hcardq89_2 (by decide)).symm

/-- **Cell (89, 0) twin (q=2).** -/
theorem cell89_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK89) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK89) (charOfVec2 rK89 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK89 e (h : Coordinate 2) T89_0_2 i :=
  species_entry_eq_sum rK89 ⟨0, by decide⟩ e heK h T89_0_2 hfix89_0_2 hinj89_0_2 hcardT89_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK89) (T89_0_2 i) (hfix89_0_2 i) h)

/-! ### Cell (89, 2) twin -/

def T89_2_2 : Fin 5 → Coordinate 2 := fun i => T89_2list.getD i.val (0,0,0,0,0)

theorem hfix89_2_2 : ∀ i, ((T89_2_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK89)
    ∈ fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK89) :=
  repsFix_of_siftB2 rK89 ⟨2, by decide⟩ T89_2_2 (by decide)

theorem hinj89_2_2 : Function.Injective
    (fun i => ((T89_2_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK89)) :=
  repsInj_of_reduceAux2 rK89 T89_2_2 (by decide)

theorem hcardT89_2_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK89)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK89 ⟨2, by decide⟩ R89_2 hpxR89_2 hcardq89_2 (by decide)).symm

/-- **Cell (89, 2) twin (q=2).** -/
theorem cell89_2_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK89) e = true)
    (h : ↥(reps (⟨2, by decide⟩ : Fin 148))) :
    species (reps (⟨2, by decide⟩ : Fin 148)) h (basisElt (reps rK89) (charOfVec2 rK89 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK89 e (h : Coordinate 2) T89_2_2 i :=
  species_entry_eq_sum rK89 ⟨2, by decide⟩ e heK h T89_2_2 hfix89_2_2 hinj89_2_2 hcardT89_2_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨2, by decide⟩) (reps rK89) (T89_2_2 i) (hfix89_2_2 i) h)

/-! ### Cell (89, 3) twin -/

def T89_3_2 : Fin 5 → Coordinate 2 := fun i => T89_3list.getD i.val (0,0,0,0,0)

theorem hfix89_3_2 : ∀ i, ((T89_3_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK89)
    ∈ fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK89) :=
  repsFix_of_siftB2 rK89 ⟨3, by decide⟩ T89_3_2 (by decide)

theorem hinj89_3_2 : Function.Injective
    (fun i => ((T89_3_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK89)) :=
  repsInj_of_reduceAux2 rK89 T89_3_2 (by decide)

theorem hcardT89_3_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK89)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK89 ⟨3, by decide⟩ R89_2 hpxR89_2 hcardq89_2 (by decide)).symm

/-- **Cell (89, 3) twin (q=2).** -/
theorem cell89_3_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK89) e = true)
    (h : ↥(reps (⟨3, by decide⟩ : Fin 148))) :
    species (reps (⟨3, by decide⟩ : Fin 148)) h (basisElt (reps rK89) (charOfVec2 rK89 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK89 e (h : Coordinate 2) T89_3_2 i :=
  species_entry_eq_sum rK89 ⟨3, by decide⟩ e heK h T89_3_2 hfix89_3_2 hinj89_3_2 hcardT89_3_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨3, by decide⟩) (reps rK89) (T89_3_2 i) (hfix89_3_2 i) h)

/-! ### Cell (89, 4) twin -/

def T89_4_2 : Fin 5 → Coordinate 2 := fun i => T89_4list.getD i.val (0,0,0,0,0)

theorem hfix89_4_2 : ∀ i, ((T89_4_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK89)
    ∈ fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK89) :=
  repsFix_of_siftB2 rK89 ⟨4, by decide⟩ T89_4_2 (by decide)

theorem hinj89_4_2 : Function.Injective
    (fun i => ((T89_4_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK89)) :=
  repsInj_of_reduceAux2 rK89 T89_4_2 (by decide)

theorem hcardT89_4_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK89)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK89 ⟨4, by decide⟩ R89_2 hpxR89_2 hcardq89_2 (by decide)).symm

/-- **Cell (89, 4) twin (q=2).** -/
theorem cell89_4_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK89) e = true)
    (h : ↥(reps (⟨4, by decide⟩ : Fin 148))) :
    species (reps (⟨4, by decide⟩ : Fin 148)) h (basisElt (reps rK89) (charOfVec2 rK89 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK89 e (h : Coordinate 2) T89_4_2 i :=
  species_entry_eq_sum rK89 ⟨4, by decide⟩ e heK h T89_4_2 hfix89_4_2 hinj89_4_2 hcardT89_4_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨4, by decide⟩) (reps rK89) (T89_4_2 i) (hfix89_4_2 i) h)

/-! ### Cell (89, 5) twin -/

def T89_5_2 : Fin 5 → Coordinate 2 := fun i => T89_5list.getD i.val (0,0,0,0,0)

theorem hfix89_5_2 : ∀ i, ((T89_5_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK89)
    ∈ fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK89) :=
  repsFix_of_siftB2 rK89 ⟨5, by decide⟩ T89_5_2 (by decide)

theorem hinj89_5_2 : Function.Injective
    (fun i => ((T89_5_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK89)) :=
  repsInj_of_reduceAux2 rK89 T89_5_2 (by decide)

theorem hcardT89_5_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK89)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK89 ⟨5, by decide⟩ R89_2 hpxR89_2 hcardq89_2 (by decide)).symm

/-- **Cell (89, 5) twin (q=2).** -/
theorem cell89_5_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK89) e = true)
    (h : ↥(reps (⟨5, by decide⟩ : Fin 148))) :
    species (reps (⟨5, by decide⟩ : Fin 148)) h (basisElt (reps rK89) (charOfVec2 rK89 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK89 e (h : Coordinate 2) T89_5_2 i :=
  species_entry_eq_sum rK89 ⟨5, by decide⟩ e heK h T89_5_2 hfix89_5_2 hinj89_5_2 hcardT89_5_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨5, by decide⟩) (reps rK89) (T89_5_2 i) (hfix89_5_2 i) h)

/-! ### Cell (89, 8) twin -/

def T89_8_2 : Fin 25 → Coordinate 2 := fun i => T89_8list.getD i.val (0,0,0,0,0)

theorem hfix89_8_2 : ∀ i, ((T89_8_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK89)
    ∈ fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK89) :=
  repsFix_of_siftB2 rK89 ⟨8, by decide⟩ T89_8_2 (by decide)

theorem hinj89_8_2 : Function.Injective
    (fun i => ((T89_8_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK89)) :=
  repsInj_of_reduceAux2 rK89 T89_8_2 (by decide)

theorem hcardT89_8_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK89)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK89 ⟨8, by decide⟩ R89_2 hpxR89_2 hcardq89_2 (by decide)).symm

/-- **Cell (89, 8) twin (q=2).** -/
theorem cell89_8_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK89) e = true)
    (h : ↥(reps (⟨8, by decide⟩ : Fin 148))) :
    species (reps (⟨8, by decide⟩ : Fin 148)) h (basisElt (reps rK89) (charOfVec2 rK89 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK89 e (h : Coordinate 2) T89_8_2 i :=
  species_entry_eq_sum rK89 ⟨8, by decide⟩ e heK h T89_8_2 hfix89_8_2 hinj89_8_2 hcardT89_8_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨8, by decide⟩) (reps rK89) (T89_8_2 i) (hfix89_8_2 i) h)

/-! ### Cell (89, 11) twin -/

def T89_11_2 : Fin 5 → Coordinate 2 := fun i => T89_11list.getD i.val (0,0,0,0,0)

theorem hfix89_11_2 : ∀ i, ((T89_11_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK89)
    ∈ fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK89) :=
  repsFix_of_siftB2 rK89 ⟨11, by decide⟩ T89_11_2 (by decide)

theorem hinj89_11_2 : Function.Injective
    (fun i => ((T89_11_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK89)) :=
  repsInj_of_reduceAux2 rK89 T89_11_2 (by decide)

theorem hcardT89_11_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK89)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK89 ⟨11, by decide⟩ R89_2 hpxR89_2 hcardq89_2 (by decide)).symm

/-- **Cell (89, 11) twin (q=2).** -/
theorem cell89_11_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK89) e = true)
    (h : ↥(reps (⟨11, by decide⟩ : Fin 148))) :
    species (reps (⟨11, by decide⟩ : Fin 148)) h (basisElt (reps rK89) (charOfVec2 rK89 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK89 e (h : Coordinate 2) T89_11_2 i :=
  species_entry_eq_sum rK89 ⟨11, by decide⟩ e heK h T89_11_2 hfix89_11_2 hinj89_11_2 hcardT89_11_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨11, by decide⟩) (reps rK89) (T89_11_2 i) (hfix89_11_2 i) h)

/-! ### Cell (89, 12) twin -/

def T89_12_2 : Fin 25 → Coordinate 2 := fun i => T89_12list.getD i.val (0,0,0,0,0)

theorem hfix89_12_2 : ∀ i, ((T89_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK89)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK89) :=
  repsFix_of_siftB2 rK89 ⟨12, by decide⟩ T89_12_2 (by decide)

theorem hinj89_12_2 : Function.Injective
    (fun i => ((T89_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK89)) :=
  repsInj_of_reduceAux2 rK89 T89_12_2 (by decide)

theorem hcardT89_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK89)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK89 ⟨12, by decide⟩ R89_2 hpxR89_2 hcardq89_2 (by decide)).symm

/-- **Cell (89, 12) twin (q=2).** -/
theorem cell89_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK89) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK89) (charOfVec2 rK89 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK89 e (h : Coordinate 2) T89_12_2 i :=
  species_entry_eq_sum rK89 ⟨12, by decide⟩ e heK h T89_12_2 hfix89_12_2 hinj89_12_2 hcardT89_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK89) (T89_12_2 i) (hfix89_12_2 i) h)

/-! ### Cell (89, 20) twin -/

def T89_20_2 : Fin 5 → Coordinate 2 := fun i => T89_20list.getD i.val (0,0,0,0,0)

theorem hfix89_20_2 : ∀ i, ((T89_20_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK89)
    ∈ fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK89) :=
  repsFix_of_siftB2 rK89 ⟨20, by decide⟩ T89_20_2 (by decide)

theorem hinj89_20_2 : Function.Injective
    (fun i => ((T89_20_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK89)) :=
  repsInj_of_reduceAux2 rK89 T89_20_2 (by decide)

theorem hcardT89_20_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK89)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK89 ⟨20, by decide⟩ R89_2 hpxR89_2 hcardq89_2 (by decide)).symm

/-- **Cell (89, 20) twin (q=2).** -/
theorem cell89_20_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK89) e = true)
    (h : ↥(reps (⟨20, by decide⟩ : Fin 148))) :
    species (reps (⟨20, by decide⟩ : Fin 148)) h (basisElt (reps rK89) (charOfVec2 rK89 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK89 e (h : Coordinate 2) T89_20_2 i :=
  species_entry_eq_sum rK89 ⟨20, by decide⟩ e heK h T89_20_2 hfix89_20_2 hinj89_20_2 hcardT89_20_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨20, by decide⟩) (reps rK89) (T89_20_2 i) (hfix89_20_2 i) h)

/-! ### Cell (89, 21) twin -/

def T89_21_2 : Fin 5 → Coordinate 2 := fun i => T89_21list.getD i.val (0,0,0,0,0)

theorem hfix89_21_2 : ∀ i, ((T89_21_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK89)
    ∈ fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK89) :=
  repsFix_of_siftB2 rK89 ⟨21, by decide⟩ T89_21_2 (by decide)

theorem hinj89_21_2 : Function.Injective
    (fun i => ((T89_21_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK89)) :=
  repsInj_of_reduceAux2 rK89 T89_21_2 (by decide)

theorem hcardT89_21_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK89)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK89 ⟨21, by decide⟩ R89_2 hpxR89_2 hcardq89_2 (by decide)).symm

/-- **Cell (89, 21) twin (q=2).** -/
theorem cell89_21_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK89) e = true)
    (h : ↥(reps (⟨21, by decide⟩ : Fin 148))) :
    species (reps (⟨21, by decide⟩ : Fin 148)) h (basisElt (reps rK89) (charOfVec2 rK89 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK89 e (h : Coordinate 2) T89_21_2 i :=
  species_entry_eq_sum rK89 ⟨21, by decide⟩ e heK h T89_21_2 hfix89_21_2 hinj89_21_2 hcardT89_21_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨21, by decide⟩) (reps rK89) (T89_21_2 i) (hfix89_21_2 i) h)

/-! ### Cell (89, 22) twin -/

def T89_22_2 : Fin 5 → Coordinate 2 := fun i => T89_22list.getD i.val (0,0,0,0,0)

theorem hfix89_22_2 : ∀ i, ((T89_22_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK89)
    ∈ fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK89) :=
  repsFix_of_siftB2 rK89 ⟨22, by decide⟩ T89_22_2 (by decide)

theorem hinj89_22_2 : Function.Injective
    (fun i => ((T89_22_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK89)) :=
  repsInj_of_reduceAux2 rK89 T89_22_2 (by decide)

theorem hcardT89_22_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK89)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK89 ⟨22, by decide⟩ R89_2 hpxR89_2 hcardq89_2 (by decide)).symm

/-- **Cell (89, 22) twin (q=2).** -/
theorem cell89_22_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK89) e = true)
    (h : ↥(reps (⟨22, by decide⟩ : Fin 148))) :
    species (reps (⟨22, by decide⟩ : Fin 148)) h (basisElt (reps rK89) (charOfVec2 rK89 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK89 e (h : Coordinate 2) T89_22_2 i :=
  species_entry_eq_sum rK89 ⟨22, by decide⟩ e heK h T89_22_2 hfix89_22_2 hinj89_22_2 hcardT89_22_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨22, by decide⟩) (reps rK89) (T89_22_2 i) (hfix89_22_2 i) h)

/-! ### Cell (89, 23) twin -/

def T89_23_2 : Fin 5 → Coordinate 2 := fun i => T89_23list.getD i.val (0,0,0,0,0)

theorem hfix89_23_2 : ∀ i, ((T89_23_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK89)
    ∈ fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK89) :=
  repsFix_of_siftB2 rK89 ⟨23, by decide⟩ T89_23_2 (by decide)

theorem hinj89_23_2 : Function.Injective
    (fun i => ((T89_23_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK89)) :=
  repsInj_of_reduceAux2 rK89 T89_23_2 (by decide)

theorem hcardT89_23_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK89)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK89 ⟨23, by decide⟩ R89_2 hpxR89_2 hcardq89_2 (by decide)).symm

/-- **Cell (89, 23) twin (q=2).** -/
theorem cell89_23_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK89) e = true)
    (h : ↥(reps (⟨23, by decide⟩ : Fin 148))) :
    species (reps (⟨23, by decide⟩ : Fin 148)) h (basisElt (reps rK89) (charOfVec2 rK89 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK89 e (h : Coordinate 2) T89_23_2 i :=
  species_entry_eq_sum rK89 ⟨23, by decide⟩ e heK h T89_23_2 hfix89_23_2 hinj89_23_2 hcardT89_23_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨23, by decide⟩) (reps rK89) (T89_23_2 i) (hfix89_23_2 i) h)

/-! ### Cell (89, 26) twin -/

def T89_26_2 : Fin 25 → Coordinate 2 := fun i => T89_26list.getD i.val (0,0,0,0,0)

theorem hfix89_26_2 : ∀ i, ((T89_26_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK89)
    ∈ fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK89) :=
  repsFix_of_siftB2 rK89 ⟨26, by decide⟩ T89_26_2 (by decide)

theorem hinj89_26_2 : Function.Injective
    (fun i => ((T89_26_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK89)) :=
  repsInj_of_reduceAux2 rK89 T89_26_2 (by decide)

theorem hcardT89_26_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK89)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK89 ⟨26, by decide⟩ R89_2 hpxR89_2 hcardq89_2 (by decide)).symm

/-- **Cell (89, 26) twin (q=2).** -/
theorem cell89_26_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK89) e = true)
    (h : ↥(reps (⟨26, by decide⟩ : Fin 148))) :
    species (reps (⟨26, by decide⟩ : Fin 148)) h (basisElt (reps rK89) (charOfVec2 rK89 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK89 e (h : Coordinate 2) T89_26_2 i :=
  species_entry_eq_sum rK89 ⟨26, by decide⟩ e heK h T89_26_2 hfix89_26_2 hinj89_26_2 hcardT89_26_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨26, by decide⟩) (reps rK89) (T89_26_2 i) (hfix89_26_2 i) h)

/-! ### Cell (89, 54) twin -/

def T89_54_2 : Fin 5 → Coordinate 2 := fun i => T89_54list.getD i.val (0,0,0,0,0)

theorem hfix89_54_2 : ∀ i, ((T89_54_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK89)
    ∈ fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK89) :=
  repsFix_of_siftB2 rK89 ⟨54, by decide⟩ T89_54_2 (by decide)

theorem hinj89_54_2 : Function.Injective
    (fun i => ((T89_54_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK89)) :=
  repsInj_of_reduceAux2 rK89 T89_54_2 (by decide)

theorem hcardT89_54_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK89)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK89 ⟨54, by decide⟩ R89_2 hpxR89_2 hcardq89_2 (by decide)).symm

/-- **Cell (89, 54) twin (q=2).** -/
theorem cell89_54_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK89) e = true)
    (h : ↥(reps (⟨54, by decide⟩ : Fin 148))) :
    species (reps (⟨54, by decide⟩ : Fin 148)) h (basisElt (reps rK89) (charOfVec2 rK89 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK89 e (h : Coordinate 2) T89_54_2 i :=
  species_entry_eq_sum rK89 ⟨54, by decide⟩ e heK h T89_54_2 hfix89_54_2 hinj89_54_2 hcardT89_54_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨54, by decide⟩) (reps rK89) (T89_54_2 i) (hfix89_54_2 i) h)

/-! ### Cell (89, 89) twin -/

def T89_89_2 : Fin 5 → Coordinate 2 := fun i => T89_89list.getD i.val (0,0,0,0,0)

theorem hfix89_89_2 : ∀ i, ((T89_89_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK89)
    ∈ fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK89) :=
  repsFix_of_siftB2 rK89 ⟨89, by decide⟩ T89_89_2 (by decide)

theorem hinj89_89_2 : Function.Injective
    (fun i => ((T89_89_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK89)) :=
  repsInj_of_reduceAux2 rK89 T89_89_2 (by decide)

theorem hcardT89_89_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK89)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK89 ⟨89, by decide⟩ R89_2 hpxR89_2 hcardq89_2 (by decide)).symm

/-- **Cell (89, 89) twin (q=2).** -/
theorem cell89_89_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK89) e = true)
    (h : ↥(reps (⟨89, by decide⟩ : Fin 148))) :
    species (reps (⟨89, by decide⟩ : Fin 148)) h (basisElt (reps rK89) (charOfVec2 rK89 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK89 e (h : Coordinate 2) T89_89_2 i :=
  species_entry_eq_sum rK89 ⟨89, by decide⟩ e heK h T89_89_2 hfix89_89_2 hinj89_89_2 hcardT89_89_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨89, by decide⟩) (reps rK89) (T89_89_2 i) (hfix89_89_2 i) h)

end Q2

/-! # K-class rK = 90  (|G/K| = 25) -/

def rK90 : Fin 148 := ⟨90, by decide⟩

def R90list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (1,0,4,0,0), (1,0,0,0,0), (1,0,1,0,0), (1,0,2,0,0), (1,0,3,0,0), (2,0,4,0,0), (2,0,0,0,0), (2,0,1,0,0), (2,0,2,0,0), (2,0,3,0,0), (3,0,4,0,0), (3,0,0,0,0), (3,0,1,0,0), (3,0,2,0,0), (3,0,3,0,0), (4,0,4,0,0), (4,0,0,0,0), (4,0,1,0,0), (4,0,2,0,0), (4,0,3,0,0)]
def R90 : Fin 25 → Coordinate 1 := fun i => R90list.getD i.val (0,0,0,0,0)

theorem hpxR90 : Function.Injective (fun i => reduceAux 1 (basisAt rK90) (R90 i)) := by decide
theorem hcardq90 : Nat.card (Coordinate 1 ⧸ reps rK90) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (90, 0): |T| = 25 -/

def T90_0list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (1,0,4,0,0), (1,0,0,0,0), (1,0,1,0,0), (1,0,2,0,0), (1,0,3,0,0), (2,0,4,0,0), (2,0,0,0,0), (2,0,1,0,0), (2,0,2,0,0), (2,0,3,0,0), (3,0,4,0,0), (3,0,0,0,0), (3,0,1,0,0), (3,0,2,0,0), (3,0,3,0,0), (4,0,4,0,0), (4,0,0,0,0), (4,0,1,0,0), (4,0,2,0,0), (4,0,3,0,0)]
def T90_0 : Fin 25 → Coordinate 1 := fun i => T90_0list.getD i.val (0,0,0,0,0)

theorem hfix90_0 : ∀ i, ((T90_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK90)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90) :=
  repsFix_of_siftB rK90 ⟨0, by decide⟩ T90_0 (by decide)

theorem hinj90_0 : Function.Injective
    (fun i => ((T90_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK90)) :=
  repsInj_of_reduceAux rK90 T90_0 (by decide)

theorem hcardT90_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK90 ⟨0, by decide⟩ R90 hpxR90 hcardq90 (by decide)).symm

/-- **Cell (90, 0).** -/
theorem cell90_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK90) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK90) (charOfVec rK90 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK90 e (h : Coordinate 1) T90_0 i :=
  species_entry_eq_sum rK90 ⟨0, by decide⟩ e heK h T90_0 hfix90_0 hinj90_0 hcardT90_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK90) (T90_0 i) (hfix90_0 i) h)

/-! ## Cell (90, 10): |T| = 25 -/

def T90_10list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (1,0,4,0,0), (1,0,0,0,0), (1,0,1,0,0), (1,0,2,0,0), (1,0,3,0,0), (2,0,4,0,0), (2,0,0,0,0), (2,0,1,0,0), (2,0,2,0,0), (2,0,3,0,0), (3,0,4,0,0), (3,0,0,0,0), (3,0,1,0,0), (3,0,2,0,0), (3,0,3,0,0), (4,0,4,0,0), (4,0,0,0,0), (4,0,1,0,0), (4,0,2,0,0), (4,0,3,0,0)]
def T90_10 : Fin 25 → Coordinate 1 := fun i => T90_10list.getD i.val (0,0,0,0,0)

theorem hfix90_10 : ∀ i, ((T90_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK90)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90) :=
  repsFix_of_siftB rK90 ⟨10, by decide⟩ T90_10 (by decide)

theorem hinj90_10 : Function.Injective
    (fun i => ((T90_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK90)) :=
  repsInj_of_reduceAux rK90 T90_10 (by decide)

theorem hcardT90_10 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK90 ⟨10, by decide⟩ R90 hpxR90 hcardq90 (by decide)).symm

/-- **Cell (90, 10).** -/
theorem cell90_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK90) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK90) (charOfVec rK90 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK90 e (h : Coordinate 1) T90_10 i :=
  species_entry_eq_sum rK90 ⟨10, by decide⟩ e heK h T90_10 hfix90_10 hinj90_10 hcardT90_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK90) (T90_10 i) (hfix90_10 i) h)

/-! ## Cell (90, 12): |T| = 25 -/

def T90_12list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (1,0,4,0,0), (1,0,0,0,0), (1,0,1,0,0), (1,0,2,0,0), (1,0,3,0,0), (2,0,4,0,0), (2,0,0,0,0), (2,0,1,0,0), (2,0,2,0,0), (2,0,3,0,0), (3,0,4,0,0), (3,0,0,0,0), (3,0,1,0,0), (3,0,2,0,0), (3,0,3,0,0), (4,0,4,0,0), (4,0,0,0,0), (4,0,1,0,0), (4,0,2,0,0), (4,0,3,0,0)]
def T90_12 : Fin 25 → Coordinate 1 := fun i => T90_12list.getD i.val (0,0,0,0,0)

theorem hfix90_12 : ∀ i, ((T90_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK90)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90) :=
  repsFix_of_siftB rK90 ⟨12, by decide⟩ T90_12 (by decide)

theorem hinj90_12 : Function.Injective
    (fun i => ((T90_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK90)) :=
  repsInj_of_reduceAux rK90 T90_12 (by decide)

theorem hcardT90_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK90 ⟨12, by decide⟩ R90 hpxR90 hcardq90 (by decide)).symm

/-- **Cell (90, 12).** -/
theorem cell90_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK90) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK90) (charOfVec rK90 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK90 e (h : Coordinate 1) T90_12 i :=
  species_entry_eq_sum rK90 ⟨12, by decide⟩ e heK h T90_12 hfix90_12 hinj90_12 hcardT90_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK90) (T90_12 i) (hfix90_12 i) h)

/-! ## Cell (90, 28): |T| = 25 -/

def T90_28list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (1,0,4,0,0), (1,0,0,0,0), (1,0,1,0,0), (1,0,2,0,0), (1,0,3,0,0), (2,0,4,0,0), (2,0,0,0,0), (2,0,1,0,0), (2,0,2,0,0), (2,0,3,0,0), (3,0,4,0,0), (3,0,0,0,0), (3,0,1,0,0), (3,0,2,0,0), (3,0,3,0,0), (4,0,4,0,0), (4,0,0,0,0), (4,0,1,0,0), (4,0,2,0,0), (4,0,3,0,0)]
def T90_28 : Fin 25 → Coordinate 1 := fun i => T90_28list.getD i.val (0,0,0,0,0)

theorem hfix90_28 : ∀ i, ((T90_28 i : Coordinate 1) : Coordinate 1 ⧸ reps rK90)
    ∈ fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90) :=
  repsFix_of_siftB rK90 ⟨28, by decide⟩ T90_28 (by decide)

theorem hinj90_28 : Function.Injective
    (fun i => ((T90_28 i : Coordinate 1) : Coordinate 1 ⧸ reps rK90)) :=
  repsInj_of_reduceAux rK90 T90_28 (by decide)

theorem hcardT90_28 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK90 ⟨28, by decide⟩ R90 hpxR90 hcardq90 (by decide)).symm

/-- **Cell (90, 28).** -/
theorem cell90_28 (e : List (ZMod 25)) (heK : charOK (basisAt rK90) e = true)
    (h : ↥(reps (⟨28, by decide⟩ : Fin 148))) :
    species (reps (⟨28, by decide⟩ : Fin 148)) h (basisElt (reps rK90) (charOfVec rK90 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK90 e (h : Coordinate 1) T90_28 i :=
  species_entry_eq_sum rK90 ⟨28, by decide⟩ e heK h T90_28 hfix90_28 hinj90_28 hcardT90_28
    (fun i => conj_mem_of_fixedPoints (reps ⟨28, by decide⟩) (reps rK90) (T90_28 i) (hfix90_28 i) h)

/-! ## Cell (90, 53): |T| = 25 -/

def T90_53list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (1,0,4,0,0), (1,0,0,0,0), (1,0,1,0,0), (1,0,2,0,0), (1,0,3,0,0), (2,0,4,0,0), (2,0,0,0,0), (2,0,1,0,0), (2,0,2,0,0), (2,0,3,0,0), (3,0,4,0,0), (3,0,0,0,0), (3,0,1,0,0), (3,0,2,0,0), (3,0,3,0,0), (4,0,4,0,0), (4,0,0,0,0), (4,0,1,0,0), (4,0,2,0,0), (4,0,3,0,0)]
def T90_53 : Fin 25 → Coordinate 1 := fun i => T90_53list.getD i.val (0,0,0,0,0)

theorem hfix90_53 : ∀ i, ((T90_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK90)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90) :=
  repsFix_of_siftB rK90 ⟨53, by decide⟩ T90_53 (by decide)

theorem hinj90_53 : Function.Injective
    (fun i => ((T90_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK90)) :=
  repsInj_of_reduceAux rK90 T90_53 (by decide)

theorem hcardT90_53 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK90 ⟨53, by decide⟩ R90 hpxR90 hcardq90 (by decide)).symm

/-- **Cell (90, 53).** -/
theorem cell90_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK90) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK90) (charOfVec rK90 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK90 e (h : Coordinate 1) T90_53 i :=
  species_entry_eq_sum rK90 ⟨53, by decide⟩ e heK h T90_53 hfix90_53 hinj90_53 hcardT90_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK90) (T90_53 i) (hfix90_53 i) h)

/-! ## Cell (90, 90): |T| = 25 -/

def T90_90list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (1,0,4,0,0), (1,0,0,0,0), (1,0,1,0,0), (1,0,2,0,0), (1,0,3,0,0), (2,0,4,0,0), (2,0,0,0,0), (2,0,1,0,0), (2,0,2,0,0), (2,0,3,0,0), (3,0,4,0,0), (3,0,0,0,0), (3,0,1,0,0), (3,0,2,0,0), (3,0,3,0,0), (4,0,4,0,0), (4,0,0,0,0), (4,0,1,0,0), (4,0,2,0,0), (4,0,3,0,0)]
def T90_90 : Fin 25 → Coordinate 1 := fun i => T90_90list.getD i.val (0,0,0,0,0)

theorem hfix90_90 : ∀ i, ((T90_90 i : Coordinate 1) : Coordinate 1 ⧸ reps rK90)
    ∈ fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90) :=
  repsFix_of_siftB rK90 ⟨90, by decide⟩ T90_90 (by decide)

theorem hinj90_90 : Function.Injective
    (fun i => ((T90_90 i : Coordinate 1) : Coordinate 1 ⧸ reps rK90)) :=
  repsInj_of_reduceAux rK90 T90_90 (by decide)

theorem hcardT90_90 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK90 ⟨90, by decide⟩ R90 hpxR90 hcardq90 (by decide)).symm

/-- **Cell (90, 90).** -/
theorem cell90_90 (e : List (ZMod 25)) (heK : charOK (basisAt rK90) e = true)
    (h : ↥(reps (⟨90, by decide⟩ : Fin 148))) :
    species (reps (⟨90, by decide⟩ : Fin 148)) h (basisElt (reps rK90) (charOfVec rK90 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK90 e (h : Coordinate 1) T90_90 i :=
  species_entry_eq_sum rK90 ⟨90, by decide⟩ e heK h T90_90 hfix90_90 hinj90_90 hcardT90_90
    (fun i => conj_mem_of_fixedPoints (reps ⟨90, by decide⟩) (reps rK90) (T90_90 i) (hfix90_90 i) h)

namespace Q2

def R90_2 : Fin 25 → Coordinate 2 := fun i => R90list.getD i.val (0,0,0,0,0)
theorem hpxR90_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK90) (R90_2 i)) := by decide
theorem hcardq90_2 : Nat.card (Coordinate 2 ⧸ reps rK90) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (90, 0) twin -/

def T90_0_2 : Fin 25 → Coordinate 2 := fun i => T90_0list.getD i.val (0,0,0,0,0)

theorem hfix90_0_2 : ∀ i, ((T90_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK90)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK90) :=
  repsFix_of_siftB2 rK90 ⟨0, by decide⟩ T90_0_2 (by decide)

theorem hinj90_0_2 : Function.Injective
    (fun i => ((T90_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK90)) :=
  repsInj_of_reduceAux2 rK90 T90_0_2 (by decide)

theorem hcardT90_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK90)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK90 ⟨0, by decide⟩ R90_2 hpxR90_2 hcardq90_2 (by decide)).symm

/-- **Cell (90, 0) twin (q=2).** -/
theorem cell90_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK90) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK90) (charOfVec2 rK90 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK90 e (h : Coordinate 2) T90_0_2 i :=
  species_entry_eq_sum rK90 ⟨0, by decide⟩ e heK h T90_0_2 hfix90_0_2 hinj90_0_2 hcardT90_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK90) (T90_0_2 i) (hfix90_0_2 i) h)

/-! ### Cell (90, 10) twin -/

def T90_10_2 : Fin 25 → Coordinate 2 := fun i => T90_10list.getD i.val (0,0,0,0,0)

theorem hfix90_10_2 : ∀ i, ((T90_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK90)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK90) :=
  repsFix_of_siftB2 rK90 ⟨10, by decide⟩ T90_10_2 (by decide)

theorem hinj90_10_2 : Function.Injective
    (fun i => ((T90_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK90)) :=
  repsInj_of_reduceAux2 rK90 T90_10_2 (by decide)

theorem hcardT90_10_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK90)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK90 ⟨10, by decide⟩ R90_2 hpxR90_2 hcardq90_2 (by decide)).symm

/-- **Cell (90, 10) twin (q=2).** -/
theorem cell90_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK90) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK90) (charOfVec2 rK90 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK90 e (h : Coordinate 2) T90_10_2 i :=
  species_entry_eq_sum rK90 ⟨10, by decide⟩ e heK h T90_10_2 hfix90_10_2 hinj90_10_2 hcardT90_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK90) (T90_10_2 i) (hfix90_10_2 i) h)

/-! ### Cell (90, 12) twin -/

def T90_12_2 : Fin 25 → Coordinate 2 := fun i => T90_12list.getD i.val (0,0,0,0,0)

theorem hfix90_12_2 : ∀ i, ((T90_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK90)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK90) :=
  repsFix_of_siftB2 rK90 ⟨12, by decide⟩ T90_12_2 (by decide)

theorem hinj90_12_2 : Function.Injective
    (fun i => ((T90_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK90)) :=
  repsInj_of_reduceAux2 rK90 T90_12_2 (by decide)

theorem hcardT90_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK90)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK90 ⟨12, by decide⟩ R90_2 hpxR90_2 hcardq90_2 (by decide)).symm

/-- **Cell (90, 12) twin (q=2).** -/
theorem cell90_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK90) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK90) (charOfVec2 rK90 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK90 e (h : Coordinate 2) T90_12_2 i :=
  species_entry_eq_sum rK90 ⟨12, by decide⟩ e heK h T90_12_2 hfix90_12_2 hinj90_12_2 hcardT90_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK90) (T90_12_2 i) (hfix90_12_2 i) h)

/-! ### Cell (90, 28) twin -/

def T90_28_2 : Fin 25 → Coordinate 2 := fun i => T90_28list.getD i.val (0,0,0,0,0)

theorem hfix90_28_2 : ∀ i, ((T90_28_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK90)
    ∈ fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK90) :=
  repsFix_of_siftB2 rK90 ⟨28, by decide⟩ T90_28_2 (by decide)

theorem hinj90_28_2 : Function.Injective
    (fun i => ((T90_28_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK90)) :=
  repsInj_of_reduceAux2 rK90 T90_28_2 (by decide)

theorem hcardT90_28_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK90)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK90 ⟨28, by decide⟩ R90_2 hpxR90_2 hcardq90_2 (by decide)).symm

/-- **Cell (90, 28) twin (q=2).** -/
theorem cell90_28_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK90) e = true)
    (h : ↥(reps (⟨28, by decide⟩ : Fin 148))) :
    species (reps (⟨28, by decide⟩ : Fin 148)) h (basisElt (reps rK90) (charOfVec2 rK90 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK90 e (h : Coordinate 2) T90_28_2 i :=
  species_entry_eq_sum rK90 ⟨28, by decide⟩ e heK h T90_28_2 hfix90_28_2 hinj90_28_2 hcardT90_28_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨28, by decide⟩) (reps rK90) (T90_28_2 i) (hfix90_28_2 i) h)

/-! ### Cell (90, 53) twin -/

def T90_53_2 : Fin 25 → Coordinate 2 := fun i => T90_53list.getD i.val (0,0,0,0,0)

theorem hfix90_53_2 : ∀ i, ((T90_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK90)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK90) :=
  repsFix_of_siftB2 rK90 ⟨53, by decide⟩ T90_53_2 (by decide)

theorem hinj90_53_2 : Function.Injective
    (fun i => ((T90_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK90)) :=
  repsInj_of_reduceAux2 rK90 T90_53_2 (by decide)

theorem hcardT90_53_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK90)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK90 ⟨53, by decide⟩ R90_2 hpxR90_2 hcardq90_2 (by decide)).symm

/-- **Cell (90, 53) twin (q=2).** -/
theorem cell90_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK90) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK90) (charOfVec2 rK90 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK90 e (h : Coordinate 2) T90_53_2 i :=
  species_entry_eq_sum rK90 ⟨53, by decide⟩ e heK h T90_53_2 hfix90_53_2 hinj90_53_2 hcardT90_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK90) (T90_53_2 i) (hfix90_53_2 i) h)

/-! ### Cell (90, 90) twin -/

def T90_90_2 : Fin 25 → Coordinate 2 := fun i => T90_90list.getD i.val (0,0,0,0,0)

theorem hfix90_90_2 : ∀ i, ((T90_90_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK90)
    ∈ fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK90) :=
  repsFix_of_siftB2 rK90 ⟨90, by decide⟩ T90_90_2 (by decide)

theorem hinj90_90_2 : Function.Injective
    (fun i => ((T90_90_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK90)) :=
  repsInj_of_reduceAux2 rK90 T90_90_2 (by decide)

theorem hcardT90_90_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK90)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK90 ⟨90, by decide⟩ R90_2 hpxR90_2 hcardq90_2 (by decide)).symm

/-- **Cell (90, 90) twin (q=2).** -/
theorem cell90_90_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK90) e = true)
    (h : ↥(reps (⟨90, by decide⟩ : Fin 148))) :
    species (reps (⟨90, by decide⟩ : Fin 148)) h (basisElt (reps rK90) (charOfVec2 rK90 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK90 e (h : Coordinate 2) T90_90_2 i :=
  species_entry_eq_sum rK90 ⟨90, by decide⟩ e heK h T90_90_2 hfix90_90_2 hinj90_90_2 hcardT90_90_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨90, by decide⟩) (reps rK90) (T90_90_2 i) (hfix90_90_2 i) h)

end Q2

/-! # K-class rK = 91  (|G/K| = 25) -/

def rK91 : Fin 148 := ⟨91, by decide⟩

def R91list : List Coordinates := [(0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0)]
def R91 : Fin 25 → Coordinate 1 := fun i => R91list.getD i.val (0,0,0,0,0)

theorem hpxR91 : Function.Injective (fun i => reduceAux 1 (basisAt rK91) (R91 i)) := by decide
theorem hcardq91 : Nat.card (Coordinate 1 ⧸ reps rK91) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (91, 0): |T| = 25 -/

def T91_0list : List Coordinates := [(0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0)]
def T91_0 : Fin 25 → Coordinate 1 := fun i => T91_0list.getD i.val (0,0,0,0,0)

theorem hfix91_0 : ∀ i, ((T91_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK91)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91) :=
  repsFix_of_siftB rK91 ⟨0, by decide⟩ T91_0 (by decide)

theorem hinj91_0 : Function.Injective
    (fun i => ((T91_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK91)) :=
  repsInj_of_reduceAux rK91 T91_0 (by decide)

theorem hcardT91_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK91 ⟨0, by decide⟩ R91 hpxR91 hcardq91 (by decide)).symm

/-- **Cell (91, 0).** -/
theorem cell91_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK91) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK91) (charOfVec rK91 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK91 e (h : Coordinate 1) T91_0 i :=
  species_entry_eq_sum rK91 ⟨0, by decide⟩ e heK h T91_0 hfix91_0 hinj91_0 hcardT91_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK91) (T91_0 i) (hfix91_0 i) h)

/-! ## Cell (91, 10): |T| = 25 -/

def T91_10list : List Coordinates := [(0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0)]
def T91_10 : Fin 25 → Coordinate 1 := fun i => T91_10list.getD i.val (0,0,0,0,0)

theorem hfix91_10 : ∀ i, ((T91_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK91)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91) :=
  repsFix_of_siftB rK91 ⟨10, by decide⟩ T91_10 (by decide)

theorem hinj91_10 : Function.Injective
    (fun i => ((T91_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK91)) :=
  repsInj_of_reduceAux rK91 T91_10 (by decide)

theorem hcardT91_10 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK91 ⟨10, by decide⟩ R91 hpxR91 hcardq91 (by decide)).symm

/-- **Cell (91, 10).** -/
theorem cell91_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK91) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK91) (charOfVec rK91 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK91 e (h : Coordinate 1) T91_10 i :=
  species_entry_eq_sum rK91 ⟨10, by decide⟩ e heK h T91_10 hfix91_10 hinj91_10 hcardT91_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK91) (T91_10 i) (hfix91_10 i) h)

/-! ## Cell (91, 12): |T| = 25 -/

def T91_12list : List Coordinates := [(0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0)]
def T91_12 : Fin 25 → Coordinate 1 := fun i => T91_12list.getD i.val (0,0,0,0,0)

theorem hfix91_12 : ∀ i, ((T91_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK91)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91) :=
  repsFix_of_siftB rK91 ⟨12, by decide⟩ T91_12 (by decide)

theorem hinj91_12 : Function.Injective
    (fun i => ((T91_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK91)) :=
  repsInj_of_reduceAux rK91 T91_12 (by decide)

theorem hcardT91_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK91 ⟨12, by decide⟩ R91 hpxR91 hcardq91 (by decide)).symm

/-- **Cell (91, 12).** -/
theorem cell91_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK91) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK91) (charOfVec rK91 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK91 e (h : Coordinate 1) T91_12 i :=
  species_entry_eq_sum rK91 ⟨12, by decide⟩ e heK h T91_12 hfix91_12 hinj91_12 hcardT91_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK91) (T91_12 i) (hfix91_12 i) h)

/-! ## Cell (91, 29): |T| = 25 -/

def T91_29list : List Coordinates := [(0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0)]
def T91_29 : Fin 25 → Coordinate 1 := fun i => T91_29list.getD i.val (0,0,0,0,0)

theorem hfix91_29 : ∀ i, ((T91_29 i : Coordinate 1) : Coordinate 1 ⧸ reps rK91)
    ∈ fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91) :=
  repsFix_of_siftB rK91 ⟨29, by decide⟩ T91_29 (by decide)

theorem hinj91_29 : Function.Injective
    (fun i => ((T91_29 i : Coordinate 1) : Coordinate 1 ⧸ reps rK91)) :=
  repsInj_of_reduceAux rK91 T91_29 (by decide)

theorem hcardT91_29 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK91 ⟨29, by decide⟩ R91 hpxR91 hcardq91 (by decide)).symm

/-- **Cell (91, 29).** -/
theorem cell91_29 (e : List (ZMod 25)) (heK : charOK (basisAt rK91) e = true)
    (h : ↥(reps (⟨29, by decide⟩ : Fin 148))) :
    species (reps (⟨29, by decide⟩ : Fin 148)) h (basisElt (reps rK91) (charOfVec rK91 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK91 e (h : Coordinate 1) T91_29 i :=
  species_entry_eq_sum rK91 ⟨29, by decide⟩ e heK h T91_29 hfix91_29 hinj91_29 hcardT91_29
    (fun i => conj_mem_of_fixedPoints (reps ⟨29, by decide⟩) (reps rK91) (T91_29 i) (hfix91_29 i) h)

/-! ## Cell (91, 53): |T| = 25 -/

def T91_53list : List Coordinates := [(0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0)]
def T91_53 : Fin 25 → Coordinate 1 := fun i => T91_53list.getD i.val (0,0,0,0,0)

theorem hfix91_53 : ∀ i, ((T91_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK91)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91) :=
  repsFix_of_siftB rK91 ⟨53, by decide⟩ T91_53 (by decide)

theorem hinj91_53 : Function.Injective
    (fun i => ((T91_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK91)) :=
  repsInj_of_reduceAux rK91 T91_53 (by decide)

theorem hcardT91_53 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK91 ⟨53, by decide⟩ R91 hpxR91 hcardq91 (by decide)).symm

/-- **Cell (91, 53).** -/
theorem cell91_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK91) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK91) (charOfVec rK91 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK91 e (h : Coordinate 1) T91_53 i :=
  species_entry_eq_sum rK91 ⟨53, by decide⟩ e heK h T91_53 hfix91_53 hinj91_53 hcardT91_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK91) (T91_53 i) (hfix91_53 i) h)

/-! ## Cell (91, 91): |T| = 25 -/

def T91_91list : List Coordinates := [(0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0)]
def T91_91 : Fin 25 → Coordinate 1 := fun i => T91_91list.getD i.val (0,0,0,0,0)

theorem hfix91_91 : ∀ i, ((T91_91 i : Coordinate 1) : Coordinate 1 ⧸ reps rK91)
    ∈ fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91) :=
  repsFix_of_siftB rK91 ⟨91, by decide⟩ T91_91 (by decide)

theorem hinj91_91 : Function.Injective
    (fun i => ((T91_91 i : Coordinate 1) : Coordinate 1 ⧸ reps rK91)) :=
  repsInj_of_reduceAux rK91 T91_91 (by decide)

theorem hcardT91_91 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK91 ⟨91, by decide⟩ R91 hpxR91 hcardq91 (by decide)).symm

/-- **Cell (91, 91).** -/
theorem cell91_91 (e : List (ZMod 25)) (heK : charOK (basisAt rK91) e = true)
    (h : ↥(reps (⟨91, by decide⟩ : Fin 148))) :
    species (reps (⟨91, by decide⟩ : Fin 148)) h (basisElt (reps rK91) (charOfVec rK91 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK91 e (h : Coordinate 1) T91_91 i :=
  species_entry_eq_sum rK91 ⟨91, by decide⟩ e heK h T91_91 hfix91_91 hinj91_91 hcardT91_91
    (fun i => conj_mem_of_fixedPoints (reps ⟨91, by decide⟩) (reps rK91) (T91_91 i) (hfix91_91 i) h)

namespace Q2

def R91_2 : Fin 25 → Coordinate 2 := fun i => R91list.getD i.val (0,0,0,0,0)
theorem hpxR91_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK91) (R91_2 i)) := by decide
theorem hcardq91_2 : Nat.card (Coordinate 2 ⧸ reps rK91) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (91, 0) twin -/

def T91_0_2 : Fin 25 → Coordinate 2 := fun i => T91_0list.getD i.val (0,0,0,0,0)

theorem hfix91_0_2 : ∀ i, ((T91_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK91)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK91) :=
  repsFix_of_siftB2 rK91 ⟨0, by decide⟩ T91_0_2 (by decide)

theorem hinj91_0_2 : Function.Injective
    (fun i => ((T91_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK91)) :=
  repsInj_of_reduceAux2 rK91 T91_0_2 (by decide)

theorem hcardT91_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK91)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK91 ⟨0, by decide⟩ R91_2 hpxR91_2 hcardq91_2 (by decide)).symm

/-- **Cell (91, 0) twin (q=2).** -/
theorem cell91_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK91) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK91) (charOfVec2 rK91 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK91 e (h : Coordinate 2) T91_0_2 i :=
  species_entry_eq_sum rK91 ⟨0, by decide⟩ e heK h T91_0_2 hfix91_0_2 hinj91_0_2 hcardT91_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK91) (T91_0_2 i) (hfix91_0_2 i) h)

/-! ### Cell (91, 10) twin -/

def T91_10_2 : Fin 25 → Coordinate 2 := fun i => T91_10list.getD i.val (0,0,0,0,0)

theorem hfix91_10_2 : ∀ i, ((T91_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK91)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK91) :=
  repsFix_of_siftB2 rK91 ⟨10, by decide⟩ T91_10_2 (by decide)

theorem hinj91_10_2 : Function.Injective
    (fun i => ((T91_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK91)) :=
  repsInj_of_reduceAux2 rK91 T91_10_2 (by decide)

theorem hcardT91_10_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK91)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK91 ⟨10, by decide⟩ R91_2 hpxR91_2 hcardq91_2 (by decide)).symm

/-- **Cell (91, 10) twin (q=2).** -/
theorem cell91_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK91) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK91) (charOfVec2 rK91 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK91 e (h : Coordinate 2) T91_10_2 i :=
  species_entry_eq_sum rK91 ⟨10, by decide⟩ e heK h T91_10_2 hfix91_10_2 hinj91_10_2 hcardT91_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK91) (T91_10_2 i) (hfix91_10_2 i) h)

/-! ### Cell (91, 12) twin -/

def T91_12_2 : Fin 25 → Coordinate 2 := fun i => T91_12list.getD i.val (0,0,0,0,0)

theorem hfix91_12_2 : ∀ i, ((T91_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK91)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK91) :=
  repsFix_of_siftB2 rK91 ⟨12, by decide⟩ T91_12_2 (by decide)

theorem hinj91_12_2 : Function.Injective
    (fun i => ((T91_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK91)) :=
  repsInj_of_reduceAux2 rK91 T91_12_2 (by decide)

theorem hcardT91_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK91)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK91 ⟨12, by decide⟩ R91_2 hpxR91_2 hcardq91_2 (by decide)).symm

/-- **Cell (91, 12) twin (q=2).** -/
theorem cell91_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK91) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK91) (charOfVec2 rK91 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK91 e (h : Coordinate 2) T91_12_2 i :=
  species_entry_eq_sum rK91 ⟨12, by decide⟩ e heK h T91_12_2 hfix91_12_2 hinj91_12_2 hcardT91_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK91) (T91_12_2 i) (hfix91_12_2 i) h)

/-! ### Cell (91, 29) twin -/

def T91_29_2 : Fin 25 → Coordinate 2 := fun i => T91_29list.getD i.val (0,0,0,0,0)

theorem hfix91_29_2 : ∀ i, ((T91_29_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK91)
    ∈ fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK91) :=
  repsFix_of_siftB2 rK91 ⟨29, by decide⟩ T91_29_2 (by decide)

theorem hinj91_29_2 : Function.Injective
    (fun i => ((T91_29_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK91)) :=
  repsInj_of_reduceAux2 rK91 T91_29_2 (by decide)

theorem hcardT91_29_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK91)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK91 ⟨29, by decide⟩ R91_2 hpxR91_2 hcardq91_2 (by decide)).symm

/-- **Cell (91, 29) twin (q=2).** -/
theorem cell91_29_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK91) e = true)
    (h : ↥(reps (⟨29, by decide⟩ : Fin 148))) :
    species (reps (⟨29, by decide⟩ : Fin 148)) h (basisElt (reps rK91) (charOfVec2 rK91 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK91 e (h : Coordinate 2) T91_29_2 i :=
  species_entry_eq_sum rK91 ⟨29, by decide⟩ e heK h T91_29_2 hfix91_29_2 hinj91_29_2 hcardT91_29_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨29, by decide⟩) (reps rK91) (T91_29_2 i) (hfix91_29_2 i) h)

/-! ### Cell (91, 53) twin -/

def T91_53_2 : Fin 25 → Coordinate 2 := fun i => T91_53list.getD i.val (0,0,0,0,0)

theorem hfix91_53_2 : ∀ i, ((T91_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK91)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK91) :=
  repsFix_of_siftB2 rK91 ⟨53, by decide⟩ T91_53_2 (by decide)

theorem hinj91_53_2 : Function.Injective
    (fun i => ((T91_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK91)) :=
  repsInj_of_reduceAux2 rK91 T91_53_2 (by decide)

theorem hcardT91_53_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK91)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK91 ⟨53, by decide⟩ R91_2 hpxR91_2 hcardq91_2 (by decide)).symm

/-- **Cell (91, 53) twin (q=2).** -/
theorem cell91_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK91) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK91) (charOfVec2 rK91 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK91 e (h : Coordinate 2) T91_53_2 i :=
  species_entry_eq_sum rK91 ⟨53, by decide⟩ e heK h T91_53_2 hfix91_53_2 hinj91_53_2 hcardT91_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK91) (T91_53_2 i) (hfix91_53_2 i) h)

/-! ### Cell (91, 91) twin -/

def T91_91_2 : Fin 25 → Coordinate 2 := fun i => T91_91list.getD i.val (0,0,0,0,0)

theorem hfix91_91_2 : ∀ i, ((T91_91_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK91)
    ∈ fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK91) :=
  repsFix_of_siftB2 rK91 ⟨91, by decide⟩ T91_91_2 (by decide)

theorem hinj91_91_2 : Function.Injective
    (fun i => ((T91_91_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK91)) :=
  repsInj_of_reduceAux2 rK91 T91_91_2 (by decide)

theorem hcardT91_91_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK91)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK91 ⟨91, by decide⟩ R91_2 hpxR91_2 hcardq91_2 (by decide)).symm

/-- **Cell (91, 91) twin (q=2).** -/
theorem cell91_91_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK91) e = true)
    (h : ↥(reps (⟨91, by decide⟩ : Fin 148))) :
    species (reps (⟨91, by decide⟩ : Fin 148)) h (basisElt (reps rK91) (charOfVec2 rK91 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK91 e (h : Coordinate 2) T91_91_2 i :=
  species_entry_eq_sum rK91 ⟨91, by decide⟩ e heK h T91_91_2 hfix91_91_2 hinj91_91_2 hcardT91_91_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨91, by decide⟩) (reps rK91) (T91_91_2 i) (hfix91_91_2 i) h)

end Q2

/-! # K-class rK = 92  (|G/K| = 25) -/

def rK92 : Fin 148 := ⟨92, by decide⟩

def R92list : List Coordinates := [(0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0)]
def R92 : Fin 25 → Coordinate 1 := fun i => R92list.getD i.val (0,0,0,0,0)

theorem hpxR92 : Function.Injective (fun i => reduceAux 1 (basisAt rK92) (R92 i)) := by decide
theorem hcardq92 : Nat.card (Coordinate 1 ⧸ reps rK92) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (92, 0): |T| = 25 -/

def T92_0list : List Coordinates := [(0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0)]
def T92_0 : Fin 25 → Coordinate 1 := fun i => T92_0list.getD i.val (0,0,0,0,0)

theorem hfix92_0 : ∀ i, ((T92_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK92)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92) :=
  repsFix_of_siftB rK92 ⟨0, by decide⟩ T92_0 (by decide)

theorem hinj92_0 : Function.Injective
    (fun i => ((T92_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK92)) :=
  repsInj_of_reduceAux rK92 T92_0 (by decide)

theorem hcardT92_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK92 ⟨0, by decide⟩ R92 hpxR92 hcardq92 (by decide)).symm

/-- **Cell (92, 0).** -/
theorem cell92_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK92) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK92) (charOfVec rK92 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK92 e (h : Coordinate 1) T92_0 i :=
  species_entry_eq_sum rK92 ⟨0, by decide⟩ e heK h T92_0 hfix92_0 hinj92_0 hcardT92_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK92) (T92_0 i) (hfix92_0 i) h)

/-! ## Cell (92, 10): |T| = 25 -/

def T92_10list : List Coordinates := [(0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0)]
def T92_10 : Fin 25 → Coordinate 1 := fun i => T92_10list.getD i.val (0,0,0,0,0)

theorem hfix92_10 : ∀ i, ((T92_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK92)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92) :=
  repsFix_of_siftB rK92 ⟨10, by decide⟩ T92_10 (by decide)

theorem hinj92_10 : Function.Injective
    (fun i => ((T92_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK92)) :=
  repsInj_of_reduceAux rK92 T92_10 (by decide)

theorem hcardT92_10 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK92 ⟨10, by decide⟩ R92 hpxR92 hcardq92 (by decide)).symm

/-- **Cell (92, 10).** -/
theorem cell92_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK92) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK92) (charOfVec rK92 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK92 e (h : Coordinate 1) T92_10 i :=
  species_entry_eq_sum rK92 ⟨10, by decide⟩ e heK h T92_10 hfix92_10 hinj92_10 hcardT92_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK92) (T92_10 i) (hfix92_10 i) h)

/-! ## Cell (92, 12): |T| = 25 -/

def T92_12list : List Coordinates := [(0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0)]
def T92_12 : Fin 25 → Coordinate 1 := fun i => T92_12list.getD i.val (0,0,0,0,0)

theorem hfix92_12 : ∀ i, ((T92_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK92)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92) :=
  repsFix_of_siftB rK92 ⟨12, by decide⟩ T92_12 (by decide)

theorem hinj92_12 : Function.Injective
    (fun i => ((T92_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK92)) :=
  repsInj_of_reduceAux rK92 T92_12 (by decide)

theorem hcardT92_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK92 ⟨12, by decide⟩ R92 hpxR92 hcardq92 (by decide)).symm

/-- **Cell (92, 12).** -/
theorem cell92_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK92) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK92) (charOfVec rK92 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK92 e (h : Coordinate 1) T92_12 i :=
  species_entry_eq_sum rK92 ⟨12, by decide⟩ e heK h T92_12 hfix92_12 hinj92_12 hcardT92_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK92) (T92_12 i) (hfix92_12 i) h)

/-! ## Cell (92, 30): |T| = 25 -/

def T92_30list : List Coordinates := [(0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0)]
def T92_30 : Fin 25 → Coordinate 1 := fun i => T92_30list.getD i.val (0,0,0,0,0)

theorem hfix92_30 : ∀ i, ((T92_30 i : Coordinate 1) : Coordinate 1 ⧸ reps rK92)
    ∈ fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92) :=
  repsFix_of_siftB rK92 ⟨30, by decide⟩ T92_30 (by decide)

theorem hinj92_30 : Function.Injective
    (fun i => ((T92_30 i : Coordinate 1) : Coordinate 1 ⧸ reps rK92)) :=
  repsInj_of_reduceAux rK92 T92_30 (by decide)

theorem hcardT92_30 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK92 ⟨30, by decide⟩ R92 hpxR92 hcardq92 (by decide)).symm

/-- **Cell (92, 30).** -/
theorem cell92_30 (e : List (ZMod 25)) (heK : charOK (basisAt rK92) e = true)
    (h : ↥(reps (⟨30, by decide⟩ : Fin 148))) :
    species (reps (⟨30, by decide⟩ : Fin 148)) h (basisElt (reps rK92) (charOfVec rK92 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK92 e (h : Coordinate 1) T92_30 i :=
  species_entry_eq_sum rK92 ⟨30, by decide⟩ e heK h T92_30 hfix92_30 hinj92_30 hcardT92_30
    (fun i => conj_mem_of_fixedPoints (reps ⟨30, by decide⟩) (reps rK92) (T92_30 i) (hfix92_30 i) h)

/-! ## Cell (92, 53): |T| = 25 -/

def T92_53list : List Coordinates := [(0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0)]
def T92_53 : Fin 25 → Coordinate 1 := fun i => T92_53list.getD i.val (0,0,0,0,0)

theorem hfix92_53 : ∀ i, ((T92_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK92)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92) :=
  repsFix_of_siftB rK92 ⟨53, by decide⟩ T92_53 (by decide)

theorem hinj92_53 : Function.Injective
    (fun i => ((T92_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK92)) :=
  repsInj_of_reduceAux rK92 T92_53 (by decide)

theorem hcardT92_53 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK92 ⟨53, by decide⟩ R92 hpxR92 hcardq92 (by decide)).symm

/-- **Cell (92, 53).** -/
theorem cell92_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK92) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK92) (charOfVec rK92 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK92 e (h : Coordinate 1) T92_53 i :=
  species_entry_eq_sum rK92 ⟨53, by decide⟩ e heK h T92_53 hfix92_53 hinj92_53 hcardT92_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK92) (T92_53 i) (hfix92_53 i) h)

/-! ## Cell (92, 92): |T| = 25 -/

def T92_92list : List Coordinates := [(0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0)]
def T92_92 : Fin 25 → Coordinate 1 := fun i => T92_92list.getD i.val (0,0,0,0,0)

theorem hfix92_92 : ∀ i, ((T92_92 i : Coordinate 1) : Coordinate 1 ⧸ reps rK92)
    ∈ fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92) :=
  repsFix_of_siftB rK92 ⟨92, by decide⟩ T92_92 (by decide)

theorem hinj92_92 : Function.Injective
    (fun i => ((T92_92 i : Coordinate 1) : Coordinate 1 ⧸ reps rK92)) :=
  repsInj_of_reduceAux rK92 T92_92 (by decide)

theorem hcardT92_92 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK92 ⟨92, by decide⟩ R92 hpxR92 hcardq92 (by decide)).symm

/-- **Cell (92, 92).** -/
theorem cell92_92 (e : List (ZMod 25)) (heK : charOK (basisAt rK92) e = true)
    (h : ↥(reps (⟨92, by decide⟩ : Fin 148))) :
    species (reps (⟨92, by decide⟩ : Fin 148)) h (basisElt (reps rK92) (charOfVec rK92 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK92 e (h : Coordinate 1) T92_92 i :=
  species_entry_eq_sum rK92 ⟨92, by decide⟩ e heK h T92_92 hfix92_92 hinj92_92 hcardT92_92
    (fun i => conj_mem_of_fixedPoints (reps ⟨92, by decide⟩) (reps rK92) (T92_92 i) (hfix92_92 i) h)

namespace Q2

def R92_2 : Fin 25 → Coordinate 2 := fun i => R92list.getD i.val (0,0,0,0,0)
theorem hpxR92_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK92) (R92_2 i)) := by decide
theorem hcardq92_2 : Nat.card (Coordinate 2 ⧸ reps rK92) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (92, 0) twin -/

def T92_0_2 : Fin 25 → Coordinate 2 := fun i => T92_0list.getD i.val (0,0,0,0,0)

theorem hfix92_0_2 : ∀ i, ((T92_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK92)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK92) :=
  repsFix_of_siftB2 rK92 ⟨0, by decide⟩ T92_0_2 (by decide)

theorem hinj92_0_2 : Function.Injective
    (fun i => ((T92_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK92)) :=
  repsInj_of_reduceAux2 rK92 T92_0_2 (by decide)

theorem hcardT92_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK92)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK92 ⟨0, by decide⟩ R92_2 hpxR92_2 hcardq92_2 (by decide)).symm

/-- **Cell (92, 0) twin (q=2).** -/
theorem cell92_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK92) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK92) (charOfVec2 rK92 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK92 e (h : Coordinate 2) T92_0_2 i :=
  species_entry_eq_sum rK92 ⟨0, by decide⟩ e heK h T92_0_2 hfix92_0_2 hinj92_0_2 hcardT92_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK92) (T92_0_2 i) (hfix92_0_2 i) h)

/-! ### Cell (92, 10) twin -/

def T92_10_2 : Fin 25 → Coordinate 2 := fun i => T92_10list.getD i.val (0,0,0,0,0)

theorem hfix92_10_2 : ∀ i, ((T92_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK92)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK92) :=
  repsFix_of_siftB2 rK92 ⟨10, by decide⟩ T92_10_2 (by decide)

theorem hinj92_10_2 : Function.Injective
    (fun i => ((T92_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK92)) :=
  repsInj_of_reduceAux2 rK92 T92_10_2 (by decide)

theorem hcardT92_10_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK92)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK92 ⟨10, by decide⟩ R92_2 hpxR92_2 hcardq92_2 (by decide)).symm

/-- **Cell (92, 10) twin (q=2).** -/
theorem cell92_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK92) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK92) (charOfVec2 rK92 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK92 e (h : Coordinate 2) T92_10_2 i :=
  species_entry_eq_sum rK92 ⟨10, by decide⟩ e heK h T92_10_2 hfix92_10_2 hinj92_10_2 hcardT92_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK92) (T92_10_2 i) (hfix92_10_2 i) h)

/-! ### Cell (92, 12) twin -/

def T92_12_2 : Fin 25 → Coordinate 2 := fun i => T92_12list.getD i.val (0,0,0,0,0)

theorem hfix92_12_2 : ∀ i, ((T92_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK92)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK92) :=
  repsFix_of_siftB2 rK92 ⟨12, by decide⟩ T92_12_2 (by decide)

theorem hinj92_12_2 : Function.Injective
    (fun i => ((T92_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK92)) :=
  repsInj_of_reduceAux2 rK92 T92_12_2 (by decide)

theorem hcardT92_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK92)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK92 ⟨12, by decide⟩ R92_2 hpxR92_2 hcardq92_2 (by decide)).symm

/-- **Cell (92, 12) twin (q=2).** -/
theorem cell92_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK92) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK92) (charOfVec2 rK92 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK92 e (h : Coordinate 2) T92_12_2 i :=
  species_entry_eq_sum rK92 ⟨12, by decide⟩ e heK h T92_12_2 hfix92_12_2 hinj92_12_2 hcardT92_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK92) (T92_12_2 i) (hfix92_12_2 i) h)

/-! ### Cell (92, 30) twin -/

def T92_30_2 : Fin 25 → Coordinate 2 := fun i => T92_30list.getD i.val (0,0,0,0,0)

theorem hfix92_30_2 : ∀ i, ((T92_30_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK92)
    ∈ fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK92) :=
  repsFix_of_siftB2 rK92 ⟨30, by decide⟩ T92_30_2 (by decide)

theorem hinj92_30_2 : Function.Injective
    (fun i => ((T92_30_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK92)) :=
  repsInj_of_reduceAux2 rK92 T92_30_2 (by decide)

theorem hcardT92_30_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK92)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK92 ⟨30, by decide⟩ R92_2 hpxR92_2 hcardq92_2 (by decide)).symm

/-- **Cell (92, 30) twin (q=2).** -/
theorem cell92_30_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK92) e = true)
    (h : ↥(reps (⟨30, by decide⟩ : Fin 148))) :
    species (reps (⟨30, by decide⟩ : Fin 148)) h (basisElt (reps rK92) (charOfVec2 rK92 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK92 e (h : Coordinate 2) T92_30_2 i :=
  species_entry_eq_sum rK92 ⟨30, by decide⟩ e heK h T92_30_2 hfix92_30_2 hinj92_30_2 hcardT92_30_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨30, by decide⟩) (reps rK92) (T92_30_2 i) (hfix92_30_2 i) h)

/-! ### Cell (92, 53) twin -/

def T92_53_2 : Fin 25 → Coordinate 2 := fun i => T92_53list.getD i.val (0,0,0,0,0)

theorem hfix92_53_2 : ∀ i, ((T92_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK92)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK92) :=
  repsFix_of_siftB2 rK92 ⟨53, by decide⟩ T92_53_2 (by decide)

theorem hinj92_53_2 : Function.Injective
    (fun i => ((T92_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK92)) :=
  repsInj_of_reduceAux2 rK92 T92_53_2 (by decide)

theorem hcardT92_53_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK92)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK92 ⟨53, by decide⟩ R92_2 hpxR92_2 hcardq92_2 (by decide)).symm

/-- **Cell (92, 53) twin (q=2).** -/
theorem cell92_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK92) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK92) (charOfVec2 rK92 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK92 e (h : Coordinate 2) T92_53_2 i :=
  species_entry_eq_sum rK92 ⟨53, by decide⟩ e heK h T92_53_2 hfix92_53_2 hinj92_53_2 hcardT92_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK92) (T92_53_2 i) (hfix92_53_2 i) h)

/-! ### Cell (92, 92) twin -/

def T92_92_2 : Fin 25 → Coordinate 2 := fun i => T92_92list.getD i.val (0,0,0,0,0)

theorem hfix92_92_2 : ∀ i, ((T92_92_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK92)
    ∈ fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK92) :=
  repsFix_of_siftB2 rK92 ⟨92, by decide⟩ T92_92_2 (by decide)

theorem hinj92_92_2 : Function.Injective
    (fun i => ((T92_92_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK92)) :=
  repsInj_of_reduceAux2 rK92 T92_92_2 (by decide)

theorem hcardT92_92_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK92)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK92 ⟨92, by decide⟩ R92_2 hpxR92_2 hcardq92_2 (by decide)).symm

/-- **Cell (92, 92) twin (q=2).** -/
theorem cell92_92_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK92) e = true)
    (h : ↥(reps (⟨92, by decide⟩ : Fin 148))) :
    species (reps (⟨92, by decide⟩ : Fin 148)) h (basisElt (reps rK92) (charOfVec2 rK92 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK92 e (h : Coordinate 2) T92_92_2 i :=
  species_entry_eq_sum rK92 ⟨92, by decide⟩ e heK h T92_92_2 hfix92_92_2 hinj92_92_2 hcardT92_92_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨92, by decide⟩) (reps rK92) (T92_92_2 i) (hfix92_92_2 i) h)

end Q2

end LeanDring.P5Presentation
