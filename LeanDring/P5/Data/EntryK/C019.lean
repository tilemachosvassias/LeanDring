/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, K-strata data (5^3 stratum, rK 80-84): certified per-cell species-entry instantiations, both
twins.

Covers K-classes 80, 81, 82, 83, 84 (order-5^3 K, |R|=25).  For each nonzero `H`-column
(`(G/K)^H ≠ ∅`), the full coset transversal `R80..` and each `H`-fixed
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

/-! # K-class rK = 80  (|G/K| = 25) -/

def rK80 : Fin 148 := ⟨80, by decide⟩

def R80list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (1,0,0,0,0), (1,1,0,0,0), (1,2,0,0,0), (1,3,0,0,0), (1,4,0,0,0), (2,0,0,0,0), (2,1,0,0,0), (2,2,0,0,0), (2,3,0,0,0), (2,4,0,0,0), (3,0,0,0,0), (3,1,0,0,0), (3,2,0,0,0), (3,3,0,0,0), (3,4,0,0,0), (4,0,0,0,0), (4,1,0,0,0), (4,2,0,0,0), (4,3,0,0,0), (4,4,0,0,0)]
def R80 : Fin 25 → Coordinate 1 := fun i => R80list.getD i.val (0,0,0,0,0)

theorem hpxR80 : Function.Injective (fun i => reduceAux 1 (basisAt rK80) (R80 i)) := by decide
theorem hcardq80 : Nat.card (Coordinate 1 ⧸ reps rK80) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (80, 0): |T| = 25 -/

def T80_0list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (1,0,0,0,0), (1,1,0,0,0), (1,2,0,0,0), (1,3,0,0,0), (1,4,0,0,0), (2,0,0,0,0), (2,1,0,0,0), (2,2,0,0,0), (2,3,0,0,0), (2,4,0,0,0), (3,0,0,0,0), (3,1,0,0,0), (3,2,0,0,0), (3,3,0,0,0), (3,4,0,0,0), (4,0,0,0,0), (4,1,0,0,0), (4,2,0,0,0), (4,3,0,0,0), (4,4,0,0,0)]
def T80_0 : Fin 25 → Coordinate 1 := fun i => T80_0list.getD i.val (0,0,0,0,0)

theorem hfix80_0 : ∀ i, ((T80_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK80)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80) :=
  repsFix_of_siftB rK80 ⟨0, by decide⟩ T80_0 (by decide)

theorem hinj80_0 : Function.Injective
    (fun i => ((T80_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK80)) :=
  repsInj_of_reduceAux rK80 T80_0 (by decide)

theorem hcardT80_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK80 ⟨0, by decide⟩ R80 hpxR80 hcardq80 (by decide)).symm

/-- **Cell (80, 0).** -/
theorem cell80_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK80) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK80) (charOfVec rK80 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK80 e (h : Coordinate 1) T80_0 i :=
  species_entry_eq_sum rK80 ⟨0, by decide⟩ e heK h T80_0 hfix80_0 hinj80_0 hcardT80_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK80) (T80_0 i) (hfix80_0 i) h)

/-! ## Cell (80, 1): |T| = 25 -/

def T80_1list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (1,0,0,0,0), (1,1,0,0,0), (1,2,0,0,0), (1,3,0,0,0), (1,4,0,0,0), (2,0,0,0,0), (2,1,0,0,0), (2,2,0,0,0), (2,3,0,0,0), (2,4,0,0,0), (3,0,0,0,0), (3,1,0,0,0), (3,2,0,0,0), (3,3,0,0,0), (3,4,0,0,0), (4,0,0,0,0), (4,1,0,0,0), (4,2,0,0,0), (4,3,0,0,0), (4,4,0,0,0)]
def T80_1 : Fin 25 → Coordinate 1 := fun i => T80_1list.getD i.val (0,0,0,0,0)

theorem hfix80_1 : ∀ i, ((T80_1 i : Coordinate 1) : Coordinate 1 ⧸ reps rK80)
    ∈ fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80) :=
  repsFix_of_siftB rK80 ⟨1, by decide⟩ T80_1 (by decide)

theorem hinj80_1 : Function.Injective
    (fun i => ((T80_1 i : Coordinate 1) : Coordinate 1 ⧸ reps rK80)) :=
  repsInj_of_reduceAux rK80 T80_1 (by decide)

theorem hcardT80_1 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK80 ⟨1, by decide⟩ R80 hpxR80 hcardq80 (by decide)).symm

/-- **Cell (80, 1).** -/
theorem cell80_1 (e : List (ZMod 25)) (heK : charOK (basisAt rK80) e = true)
    (h : ↥(reps (⟨1, by decide⟩ : Fin 148))) :
    species (reps (⟨1, by decide⟩ : Fin 148)) h (basisElt (reps rK80) (charOfVec rK80 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK80 e (h : Coordinate 1) T80_1 i :=
  species_entry_eq_sum rK80 ⟨1, by decide⟩ e heK h T80_1 hfix80_1 hinj80_1 hcardT80_1
    (fun i => conj_mem_of_fixedPoints (reps ⟨1, by decide⟩) (reps rK80) (T80_1 i) (hfix80_1 i) h)

/-! ## Cell (80, 6): |T| = 25 -/

def T80_6list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (1,0,0,0,0), (1,1,0,0,0), (1,2,0,0,0), (1,3,0,0,0), (1,4,0,0,0), (2,0,0,0,0), (2,1,0,0,0), (2,2,0,0,0), (2,3,0,0,0), (2,4,0,0,0), (3,0,0,0,0), (3,1,0,0,0), (3,2,0,0,0), (3,3,0,0,0), (3,4,0,0,0), (4,0,0,0,0), (4,1,0,0,0), (4,2,0,0,0), (4,3,0,0,0), (4,4,0,0,0)]
def T80_6 : Fin 25 → Coordinate 1 := fun i => T80_6list.getD i.val (0,0,0,0,0)

theorem hfix80_6 : ∀ i, ((T80_6 i : Coordinate 1) : Coordinate 1 ⧸ reps rK80)
    ∈ fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80) :=
  repsFix_of_siftB rK80 ⟨6, by decide⟩ T80_6 (by decide)

theorem hinj80_6 : Function.Injective
    (fun i => ((T80_6 i : Coordinate 1) : Coordinate 1 ⧸ reps rK80)) :=
  repsInj_of_reduceAux rK80 T80_6 (by decide)

theorem hcardT80_6 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK80 ⟨6, by decide⟩ R80 hpxR80 hcardq80 (by decide)).symm

/-- **Cell (80, 6).** -/
theorem cell80_6 (e : List (ZMod 25)) (heK : charOK (basisAt rK80) e = true)
    (h : ↥(reps (⟨6, by decide⟩ : Fin 148))) :
    species (reps (⟨6, by decide⟩ : Fin 148)) h (basisElt (reps rK80) (charOfVec rK80 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK80 e (h : Coordinate 1) T80_6 i :=
  species_entry_eq_sum rK80 ⟨6, by decide⟩ e heK h T80_6 hfix80_6 hinj80_6 hcardT80_6
    (fun i => conj_mem_of_fixedPoints (reps ⟨6, by decide⟩) (reps rK80) (T80_6 i) (hfix80_6 i) h)

/-! ## Cell (80, 7): |T| = 25 -/

def T80_7list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (1,0,0,0,0), (1,1,0,0,0), (1,2,0,0,0), (1,3,0,0,0), (1,4,0,0,0), (2,0,0,0,0), (2,1,0,0,0), (2,2,0,0,0), (2,3,0,0,0), (2,4,0,0,0), (3,0,0,0,0), (3,1,0,0,0), (3,2,0,0,0), (3,3,0,0,0), (3,4,0,0,0), (4,0,0,0,0), (4,1,0,0,0), (4,2,0,0,0), (4,3,0,0,0), (4,4,0,0,0)]
def T80_7 : Fin 25 → Coordinate 1 := fun i => T80_7list.getD i.val (0,0,0,0,0)

theorem hfix80_7 : ∀ i, ((T80_7 i : Coordinate 1) : Coordinate 1 ⧸ reps rK80)
    ∈ fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80) :=
  repsFix_of_siftB rK80 ⟨7, by decide⟩ T80_7 (by decide)

theorem hinj80_7 : Function.Injective
    (fun i => ((T80_7 i : Coordinate 1) : Coordinate 1 ⧸ reps rK80)) :=
  repsInj_of_reduceAux rK80 T80_7 (by decide)

theorem hcardT80_7 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK80 ⟨7, by decide⟩ R80 hpxR80 hcardq80 (by decide)).symm

/-- **Cell (80, 7).** -/
theorem cell80_7 (e : List (ZMod 25)) (heK : charOK (basisAt rK80) e = true)
    (h : ↥(reps (⟨7, by decide⟩ : Fin 148))) :
    species (reps (⟨7, by decide⟩ : Fin 148)) h (basisElt (reps rK80) (charOfVec rK80 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK80 e (h : Coordinate 1) T80_7 i :=
  species_entry_eq_sum rK80 ⟨7, by decide⟩ e heK h T80_7 hfix80_7 hinj80_7 hcardT80_7
    (fun i => conj_mem_of_fixedPoints (reps ⟨7, by decide⟩) (reps rK80) (T80_7 i) (hfix80_7 i) h)

/-! ## Cell (80, 8): |T| = 25 -/

def T80_8list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (1,0,0,0,0), (1,1,0,0,0), (1,2,0,0,0), (1,3,0,0,0), (1,4,0,0,0), (2,0,0,0,0), (2,1,0,0,0), (2,2,0,0,0), (2,3,0,0,0), (2,4,0,0,0), (3,0,0,0,0), (3,1,0,0,0), (3,2,0,0,0), (3,3,0,0,0), (3,4,0,0,0), (4,0,0,0,0), (4,1,0,0,0), (4,2,0,0,0), (4,3,0,0,0), (4,4,0,0,0)]
def T80_8 : Fin 25 → Coordinate 1 := fun i => T80_8list.getD i.val (0,0,0,0,0)

theorem hfix80_8 : ∀ i, ((T80_8 i : Coordinate 1) : Coordinate 1 ⧸ reps rK80)
    ∈ fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80) :=
  repsFix_of_siftB rK80 ⟨8, by decide⟩ T80_8 (by decide)

theorem hinj80_8 : Function.Injective
    (fun i => ((T80_8 i : Coordinate 1) : Coordinate 1 ⧸ reps rK80)) :=
  repsInj_of_reduceAux rK80 T80_8 (by decide)

theorem hcardT80_8 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK80 ⟨8, by decide⟩ R80 hpxR80 hcardq80 (by decide)).symm

/-- **Cell (80, 8).** -/
theorem cell80_8 (e : List (ZMod 25)) (heK : charOK (basisAt rK80) e = true)
    (h : ↥(reps (⟨8, by decide⟩ : Fin 148))) :
    species (reps (⟨8, by decide⟩ : Fin 148)) h (basisElt (reps rK80) (charOfVec rK80 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK80 e (h : Coordinate 1) T80_8 i :=
  species_entry_eq_sum rK80 ⟨8, by decide⟩ e heK h T80_8 hfix80_8 hinj80_8 hcardT80_8
    (fun i => conj_mem_of_fixedPoints (reps ⟨8, by decide⟩) (reps rK80) (T80_8 i) (hfix80_8 i) h)

/-! ## Cell (80, 9): |T| = 25 -/

def T80_9list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (1,0,0,0,0), (1,1,0,0,0), (1,2,0,0,0), (1,3,0,0,0), (1,4,0,0,0), (2,0,0,0,0), (2,1,0,0,0), (2,2,0,0,0), (2,3,0,0,0), (2,4,0,0,0), (3,0,0,0,0), (3,1,0,0,0), (3,2,0,0,0), (3,3,0,0,0), (3,4,0,0,0), (4,0,0,0,0), (4,1,0,0,0), (4,2,0,0,0), (4,3,0,0,0), (4,4,0,0,0)]
def T80_9 : Fin 25 → Coordinate 1 := fun i => T80_9list.getD i.val (0,0,0,0,0)

theorem hfix80_9 : ∀ i, ((T80_9 i : Coordinate 1) : Coordinate 1 ⧸ reps rK80)
    ∈ fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80) :=
  repsFix_of_siftB rK80 ⟨9, by decide⟩ T80_9 (by decide)

theorem hinj80_9 : Function.Injective
    (fun i => ((T80_9 i : Coordinate 1) : Coordinate 1 ⧸ reps rK80)) :=
  repsInj_of_reduceAux rK80 T80_9 (by decide)

theorem hcardT80_9 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK80 ⟨9, by decide⟩ R80 hpxR80 hcardq80 (by decide)).symm

/-- **Cell (80, 9).** -/
theorem cell80_9 (e : List (ZMod 25)) (heK : charOK (basisAt rK80) e = true)
    (h : ↥(reps (⟨9, by decide⟩ : Fin 148))) :
    species (reps (⟨9, by decide⟩ : Fin 148)) h (basisElt (reps rK80) (charOfVec rK80 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK80 e (h : Coordinate 1) T80_9 i :=
  species_entry_eq_sum rK80 ⟨9, by decide⟩ e heK h T80_9 hfix80_9 hinj80_9 hcardT80_9
    (fun i => conj_mem_of_fixedPoints (reps ⟨9, by decide⟩) (reps rK80) (T80_9 i) (hfix80_9 i) h)

/-! ## Cell (80, 10): |T| = 25 -/

def T80_10list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (1,0,0,0,0), (1,1,0,0,0), (1,2,0,0,0), (1,3,0,0,0), (1,4,0,0,0), (2,0,0,0,0), (2,1,0,0,0), (2,2,0,0,0), (2,3,0,0,0), (2,4,0,0,0), (3,0,0,0,0), (3,1,0,0,0), (3,2,0,0,0), (3,3,0,0,0), (3,4,0,0,0), (4,0,0,0,0), (4,1,0,0,0), (4,2,0,0,0), (4,3,0,0,0), (4,4,0,0,0)]
def T80_10 : Fin 25 → Coordinate 1 := fun i => T80_10list.getD i.val (0,0,0,0,0)

theorem hfix80_10 : ∀ i, ((T80_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK80)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80) :=
  repsFix_of_siftB rK80 ⟨10, by decide⟩ T80_10 (by decide)

theorem hinj80_10 : Function.Injective
    (fun i => ((T80_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK80)) :=
  repsInj_of_reduceAux rK80 T80_10 (by decide)

theorem hcardT80_10 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK80 ⟨10, by decide⟩ R80 hpxR80 hcardq80 (by decide)).symm

/-- **Cell (80, 10).** -/
theorem cell80_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK80) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK80) (charOfVec rK80 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK80 e (h : Coordinate 1) T80_10 i :=
  species_entry_eq_sum rK80 ⟨10, by decide⟩ e heK h T80_10 hfix80_10 hinj80_10 hcardT80_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK80) (T80_10 i) (hfix80_10 i) h)

/-! ## Cell (80, 12): |T| = 25 -/

def T80_12list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (1,0,0,0,0), (1,1,0,0,0), (1,2,0,0,0), (1,3,0,0,0), (1,4,0,0,0), (2,0,0,0,0), (2,1,0,0,0), (2,2,0,0,0), (2,3,0,0,0), (2,4,0,0,0), (3,0,0,0,0), (3,1,0,0,0), (3,2,0,0,0), (3,3,0,0,0), (3,4,0,0,0), (4,0,0,0,0), (4,1,0,0,0), (4,2,0,0,0), (4,3,0,0,0), (4,4,0,0,0)]
def T80_12 : Fin 25 → Coordinate 1 := fun i => T80_12list.getD i.val (0,0,0,0,0)

theorem hfix80_12 : ∀ i, ((T80_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK80)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80) :=
  repsFix_of_siftB rK80 ⟨12, by decide⟩ T80_12 (by decide)

theorem hinj80_12 : Function.Injective
    (fun i => ((T80_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK80)) :=
  repsInj_of_reduceAux rK80 T80_12 (by decide)

theorem hcardT80_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK80 ⟨12, by decide⟩ R80 hpxR80 hcardq80 (by decide)).symm

/-- **Cell (80, 12).** -/
theorem cell80_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK80) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK80) (charOfVec rK80 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK80 e (h : Coordinate 1) T80_12 i :=
  species_entry_eq_sum rK80 ⟨12, by decide⟩ e heK h T80_12 hfix80_12 hinj80_12 hcardT80_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK80) (T80_12 i) (hfix80_12 i) h)

/-! ## Cell (80, 13): |T| = 25 -/

def T80_13list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (1,0,0,0,0), (1,1,0,0,0), (1,2,0,0,0), (1,3,0,0,0), (1,4,0,0,0), (2,0,0,0,0), (2,1,0,0,0), (2,2,0,0,0), (2,3,0,0,0), (2,4,0,0,0), (3,0,0,0,0), (3,1,0,0,0), (3,2,0,0,0), (3,3,0,0,0), (3,4,0,0,0), (4,0,0,0,0), (4,1,0,0,0), (4,2,0,0,0), (4,3,0,0,0), (4,4,0,0,0)]
def T80_13 : Fin 25 → Coordinate 1 := fun i => T80_13list.getD i.val (0,0,0,0,0)

theorem hfix80_13 : ∀ i, ((T80_13 i : Coordinate 1) : Coordinate 1 ⧸ reps rK80)
    ∈ fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80) :=
  repsFix_of_siftB rK80 ⟨13, by decide⟩ T80_13 (by decide)

theorem hinj80_13 : Function.Injective
    (fun i => ((T80_13 i : Coordinate 1) : Coordinate 1 ⧸ reps rK80)) :=
  repsInj_of_reduceAux rK80 T80_13 (by decide)

theorem hcardT80_13 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK80 ⟨13, by decide⟩ R80 hpxR80 hcardq80 (by decide)).symm

/-- **Cell (80, 13).** -/
theorem cell80_13 (e : List (ZMod 25)) (heK : charOK (basisAt rK80) e = true)
    (h : ↥(reps (⟨13, by decide⟩ : Fin 148))) :
    species (reps (⟨13, by decide⟩ : Fin 148)) h (basisElt (reps rK80) (charOfVec rK80 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK80 e (h : Coordinate 1) T80_13 i :=
  species_entry_eq_sum rK80 ⟨13, by decide⟩ e heK h T80_13 hfix80_13 hinj80_13 hcardT80_13
    (fun i => conj_mem_of_fixedPoints (reps ⟨13, by decide⟩) (reps rK80) (T80_13 i) (hfix80_13 i) h)

/-! ## Cell (80, 19): |T| = 25 -/

def T80_19list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (1,0,0,0,0), (1,1,0,0,0), (1,2,0,0,0), (1,3,0,0,0), (1,4,0,0,0), (2,0,0,0,0), (2,1,0,0,0), (2,2,0,0,0), (2,3,0,0,0), (2,4,0,0,0), (3,0,0,0,0), (3,1,0,0,0), (3,2,0,0,0), (3,3,0,0,0), (3,4,0,0,0), (4,0,0,0,0), (4,1,0,0,0), (4,2,0,0,0), (4,3,0,0,0), (4,4,0,0,0)]
def T80_19 : Fin 25 → Coordinate 1 := fun i => T80_19list.getD i.val (0,0,0,0,0)

theorem hfix80_19 : ∀ i, ((T80_19 i : Coordinate 1) : Coordinate 1 ⧸ reps rK80)
    ∈ fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80) :=
  repsFix_of_siftB rK80 ⟨19, by decide⟩ T80_19 (by decide)

theorem hinj80_19 : Function.Injective
    (fun i => ((T80_19 i : Coordinate 1) : Coordinate 1 ⧸ reps rK80)) :=
  repsInj_of_reduceAux rK80 T80_19 (by decide)

theorem hcardT80_19 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK80 ⟨19, by decide⟩ R80 hpxR80 hcardq80 (by decide)).symm

/-- **Cell (80, 19).** -/
theorem cell80_19 (e : List (ZMod 25)) (heK : charOK (basisAt rK80) e = true)
    (h : ↥(reps (⟨19, by decide⟩ : Fin 148))) :
    species (reps (⟨19, by decide⟩ : Fin 148)) h (basisElt (reps rK80) (charOfVec rK80 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK80 e (h : Coordinate 1) T80_19 i :=
  species_entry_eq_sum rK80 ⟨19, by decide⟩ e heK h T80_19 hfix80_19 hinj80_19 hcardT80_19
    (fun i => conj_mem_of_fixedPoints (reps ⟨19, by decide⟩) (reps rK80) (T80_19 i) (hfix80_19 i) h)

/-! ## Cell (80, 24): |T| = 25 -/

def T80_24list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (1,0,0,0,0), (1,1,0,0,0), (1,2,0,0,0), (1,3,0,0,0), (1,4,0,0,0), (2,0,0,0,0), (2,1,0,0,0), (2,2,0,0,0), (2,3,0,0,0), (2,4,0,0,0), (3,0,0,0,0), (3,1,0,0,0), (3,2,0,0,0), (3,3,0,0,0), (3,4,0,0,0), (4,0,0,0,0), (4,1,0,0,0), (4,2,0,0,0), (4,3,0,0,0), (4,4,0,0,0)]
def T80_24 : Fin 25 → Coordinate 1 := fun i => T80_24list.getD i.val (0,0,0,0,0)

theorem hfix80_24 : ∀ i, ((T80_24 i : Coordinate 1) : Coordinate 1 ⧸ reps rK80)
    ∈ fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80) :=
  repsFix_of_siftB rK80 ⟨24, by decide⟩ T80_24 (by decide)

theorem hinj80_24 : Function.Injective
    (fun i => ((T80_24 i : Coordinate 1) : Coordinate 1 ⧸ reps rK80)) :=
  repsInj_of_reduceAux rK80 T80_24 (by decide)

theorem hcardT80_24 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK80 ⟨24, by decide⟩ R80 hpxR80 hcardq80 (by decide)).symm

/-- **Cell (80, 24).** -/
theorem cell80_24 (e : List (ZMod 25)) (heK : charOK (basisAt rK80) e = true)
    (h : ↥(reps (⟨24, by decide⟩ : Fin 148))) :
    species (reps (⟨24, by decide⟩ : Fin 148)) h (basisElt (reps rK80) (charOfVec rK80 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK80 e (h : Coordinate 1) T80_24 i :=
  species_entry_eq_sum rK80 ⟨24, by decide⟩ e heK h T80_24 hfix80_24 hinj80_24 hcardT80_24
    (fun i => conj_mem_of_fixedPoints (reps ⟨24, by decide⟩) (reps rK80) (T80_24 i) (hfix80_24 i) h)

/-! ## Cell (80, 25): |T| = 25 -/

def T80_25list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (1,0,0,0,0), (1,1,0,0,0), (1,2,0,0,0), (1,3,0,0,0), (1,4,0,0,0), (2,0,0,0,0), (2,1,0,0,0), (2,2,0,0,0), (2,3,0,0,0), (2,4,0,0,0), (3,0,0,0,0), (3,1,0,0,0), (3,2,0,0,0), (3,3,0,0,0), (3,4,0,0,0), (4,0,0,0,0), (4,1,0,0,0), (4,2,0,0,0), (4,3,0,0,0), (4,4,0,0,0)]
def T80_25 : Fin 25 → Coordinate 1 := fun i => T80_25list.getD i.val (0,0,0,0,0)

theorem hfix80_25 : ∀ i, ((T80_25 i : Coordinate 1) : Coordinate 1 ⧸ reps rK80)
    ∈ fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80) :=
  repsFix_of_siftB rK80 ⟨25, by decide⟩ T80_25 (by decide)

theorem hinj80_25 : Function.Injective
    (fun i => ((T80_25 i : Coordinate 1) : Coordinate 1 ⧸ reps rK80)) :=
  repsInj_of_reduceAux rK80 T80_25 (by decide)

theorem hcardT80_25 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK80 ⟨25, by decide⟩ R80 hpxR80 hcardq80 (by decide)).symm

/-- **Cell (80, 25).** -/
theorem cell80_25 (e : List (ZMod 25)) (heK : charOK (basisAt rK80) e = true)
    (h : ↥(reps (⟨25, by decide⟩ : Fin 148))) :
    species (reps (⟨25, by decide⟩ : Fin 148)) h (basisElt (reps rK80) (charOfVec rK80 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK80 e (h : Coordinate 1) T80_25 i :=
  species_entry_eq_sum rK80 ⟨25, by decide⟩ e heK h T80_25 hfix80_25 hinj80_25 hcardT80_25
    (fun i => conj_mem_of_fixedPoints (reps ⟨25, by decide⟩) (reps rK80) (T80_25 i) (hfix80_25 i) h)

/-! ## Cell (80, 26): |T| = 25 -/

def T80_26list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (1,0,0,0,0), (1,1,0,0,0), (1,2,0,0,0), (1,3,0,0,0), (1,4,0,0,0), (2,0,0,0,0), (2,1,0,0,0), (2,2,0,0,0), (2,3,0,0,0), (2,4,0,0,0), (3,0,0,0,0), (3,1,0,0,0), (3,2,0,0,0), (3,3,0,0,0), (3,4,0,0,0), (4,0,0,0,0), (4,1,0,0,0), (4,2,0,0,0), (4,3,0,0,0), (4,4,0,0,0)]
def T80_26 : Fin 25 → Coordinate 1 := fun i => T80_26list.getD i.val (0,0,0,0,0)

theorem hfix80_26 : ∀ i, ((T80_26 i : Coordinate 1) : Coordinate 1 ⧸ reps rK80)
    ∈ fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80) :=
  repsFix_of_siftB rK80 ⟨26, by decide⟩ T80_26 (by decide)

theorem hinj80_26 : Function.Injective
    (fun i => ((T80_26 i : Coordinate 1) : Coordinate 1 ⧸ reps rK80)) :=
  repsInj_of_reduceAux rK80 T80_26 (by decide)

theorem hcardT80_26 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK80 ⟨26, by decide⟩ R80 hpxR80 hcardq80 (by decide)).symm

/-- **Cell (80, 26).** -/
theorem cell80_26 (e : List (ZMod 25)) (heK : charOK (basisAt rK80) e = true)
    (h : ↥(reps (⟨26, by decide⟩ : Fin 148))) :
    species (reps (⟨26, by decide⟩ : Fin 148)) h (basisElt (reps rK80) (charOfVec rK80 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK80 e (h : Coordinate 1) T80_26 i :=
  species_entry_eq_sum rK80 ⟨26, by decide⟩ e heK h T80_26 hfix80_26 hinj80_26 hcardT80_26
    (fun i => conj_mem_of_fixedPoints (reps ⟨26, by decide⟩) (reps rK80) (T80_26 i) (hfix80_26 i) h)

/-! ## Cell (80, 27): |T| = 25 -/

def T80_27list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (1,0,0,0,0), (1,1,0,0,0), (1,2,0,0,0), (1,3,0,0,0), (1,4,0,0,0), (2,0,0,0,0), (2,1,0,0,0), (2,2,0,0,0), (2,3,0,0,0), (2,4,0,0,0), (3,0,0,0,0), (3,1,0,0,0), (3,2,0,0,0), (3,3,0,0,0), (3,4,0,0,0), (4,0,0,0,0), (4,1,0,0,0), (4,2,0,0,0), (4,3,0,0,0), (4,4,0,0,0)]
def T80_27 : Fin 25 → Coordinate 1 := fun i => T80_27list.getD i.val (0,0,0,0,0)

theorem hfix80_27 : ∀ i, ((T80_27 i : Coordinate 1) : Coordinate 1 ⧸ reps rK80)
    ∈ fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80) :=
  repsFix_of_siftB rK80 ⟨27, by decide⟩ T80_27 (by decide)

theorem hinj80_27 : Function.Injective
    (fun i => ((T80_27 i : Coordinate 1) : Coordinate 1 ⧸ reps rK80)) :=
  repsInj_of_reduceAux rK80 T80_27 (by decide)

theorem hcardT80_27 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK80 ⟨27, by decide⟩ R80 hpxR80 hcardq80 (by decide)).symm

/-- **Cell (80, 27).** -/
theorem cell80_27 (e : List (ZMod 25)) (heK : charOK (basisAt rK80) e = true)
    (h : ↥(reps (⟨27, by decide⟩ : Fin 148))) :
    species (reps (⟨27, by decide⟩ : Fin 148)) h (basisElt (reps rK80) (charOfVec rK80 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK80 e (h : Coordinate 1) T80_27 i :=
  species_entry_eq_sum rK80 ⟨27, by decide⟩ e heK h T80_27 hfix80_27 hinj80_27 hcardT80_27
    (fun i => conj_mem_of_fixedPoints (reps ⟨27, by decide⟩) (reps rK80) (T80_27 i) (hfix80_27 i) h)

/-! ## Cell (80, 53): |T| = 25 -/

def T80_53list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (1,0,0,0,0), (1,1,0,0,0), (1,2,0,0,0), (1,3,0,0,0), (1,4,0,0,0), (2,0,0,0,0), (2,1,0,0,0), (2,2,0,0,0), (2,3,0,0,0), (2,4,0,0,0), (3,0,0,0,0), (3,1,0,0,0), (3,2,0,0,0), (3,3,0,0,0), (3,4,0,0,0), (4,0,0,0,0), (4,1,0,0,0), (4,2,0,0,0), (4,3,0,0,0), (4,4,0,0,0)]
def T80_53 : Fin 25 → Coordinate 1 := fun i => T80_53list.getD i.val (0,0,0,0,0)

theorem hfix80_53 : ∀ i, ((T80_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK80)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80) :=
  repsFix_of_siftB rK80 ⟨53, by decide⟩ T80_53 (by decide)

theorem hinj80_53 : Function.Injective
    (fun i => ((T80_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK80)) :=
  repsInj_of_reduceAux rK80 T80_53 (by decide)

theorem hcardT80_53 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK80 ⟨53, by decide⟩ R80 hpxR80 hcardq80 (by decide)).symm

/-- **Cell (80, 53).** -/
theorem cell80_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK80) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK80) (charOfVec rK80 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK80 e (h : Coordinate 1) T80_53 i :=
  species_entry_eq_sum rK80 ⟨53, by decide⟩ e heK h T80_53 hfix80_53 hinj80_53 hcardT80_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK80) (T80_53 i) (hfix80_53 i) h)

/-! ## Cell (80, 80): |T| = 25 -/

def T80_80list : List Coordinates := [(0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0), (0,3,0,0,0), (0,4,0,0,0), (1,0,0,0,0), (1,1,0,0,0), (1,2,0,0,0), (1,3,0,0,0), (1,4,0,0,0), (2,0,0,0,0), (2,1,0,0,0), (2,2,0,0,0), (2,3,0,0,0), (2,4,0,0,0), (3,0,0,0,0), (3,1,0,0,0), (3,2,0,0,0), (3,3,0,0,0), (3,4,0,0,0), (4,0,0,0,0), (4,1,0,0,0), (4,2,0,0,0), (4,3,0,0,0), (4,4,0,0,0)]
def T80_80 : Fin 25 → Coordinate 1 := fun i => T80_80list.getD i.val (0,0,0,0,0)

theorem hfix80_80 : ∀ i, ((T80_80 i : Coordinate 1) : Coordinate 1 ⧸ reps rK80)
    ∈ fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80) :=
  repsFix_of_siftB rK80 ⟨80, by decide⟩ T80_80 (by decide)

theorem hinj80_80 : Function.Injective
    (fun i => ((T80_80 i : Coordinate 1) : Coordinate 1 ⧸ reps rK80)) :=
  repsInj_of_reduceAux rK80 T80_80 (by decide)

theorem hcardT80_80 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK80 ⟨80, by decide⟩ R80 hpxR80 hcardq80 (by decide)).symm

/-- **Cell (80, 80).** -/
theorem cell80_80 (e : List (ZMod 25)) (heK : charOK (basisAt rK80) e = true)
    (h : ↥(reps (⟨80, by decide⟩ : Fin 148))) :
    species (reps (⟨80, by decide⟩ : Fin 148)) h (basisElt (reps rK80) (charOfVec rK80 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK80 e (h : Coordinate 1) T80_80 i :=
  species_entry_eq_sum rK80 ⟨80, by decide⟩ e heK h T80_80 hfix80_80 hinj80_80 hcardT80_80
    (fun i => conj_mem_of_fixedPoints (reps ⟨80, by decide⟩) (reps rK80) (T80_80 i) (hfix80_80 i) h)

namespace Q2

def R80_2 : Fin 25 → Coordinate 2 := fun i => R80list.getD i.val (0,0,0,0,0)
theorem hpxR80_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK80) (R80_2 i)) := by decide
theorem hcardq80_2 : Nat.card (Coordinate 2 ⧸ reps rK80) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (80, 0) twin -/

def T80_0_2 : Fin 25 → Coordinate 2 := fun i => T80_0list.getD i.val (0,0,0,0,0)

theorem hfix80_0_2 : ∀ i, ((T80_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK80)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK80) :=
  repsFix_of_siftB2 rK80 ⟨0, by decide⟩ T80_0_2 (by decide)

theorem hinj80_0_2 : Function.Injective
    (fun i => ((T80_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK80)) :=
  repsInj_of_reduceAux2 rK80 T80_0_2 (by decide)

theorem hcardT80_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK80)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK80 ⟨0, by decide⟩ R80_2 hpxR80_2 hcardq80_2 (by decide)).symm

/-- **Cell (80, 0) twin (q=2).** -/
theorem cell80_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK80) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK80) (charOfVec2 rK80 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK80 e (h : Coordinate 2) T80_0_2 i :=
  species_entry_eq_sum rK80 ⟨0, by decide⟩ e heK h T80_0_2 hfix80_0_2 hinj80_0_2 hcardT80_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK80) (T80_0_2 i) (hfix80_0_2 i) h)

/-! ### Cell (80, 1) twin -/

def T80_1_2 : Fin 25 → Coordinate 2 := fun i => T80_1list.getD i.val (0,0,0,0,0)

theorem hfix80_1_2 : ∀ i, ((T80_1_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK80)
    ∈ fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK80) :=
  repsFix_of_siftB2 rK80 ⟨1, by decide⟩ T80_1_2 (by decide)

theorem hinj80_1_2 : Function.Injective
    (fun i => ((T80_1_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK80)) :=
  repsInj_of_reduceAux2 rK80 T80_1_2 (by decide)

theorem hcardT80_1_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK80)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK80 ⟨1, by decide⟩ R80_2 hpxR80_2 hcardq80_2 (by decide)).symm

/-- **Cell (80, 1) twin (q=2).** -/
theorem cell80_1_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK80) e = true)
    (h : ↥(reps (⟨1, by decide⟩ : Fin 148))) :
    species (reps (⟨1, by decide⟩ : Fin 148)) h (basisElt (reps rK80) (charOfVec2 rK80 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK80 e (h : Coordinate 2) T80_1_2 i :=
  species_entry_eq_sum rK80 ⟨1, by decide⟩ e heK h T80_1_2 hfix80_1_2 hinj80_1_2 hcardT80_1_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨1, by decide⟩) (reps rK80) (T80_1_2 i) (hfix80_1_2 i) h)

/-! ### Cell (80, 6) twin -/

def T80_6_2 : Fin 25 → Coordinate 2 := fun i => T80_6list.getD i.val (0,0,0,0,0)

theorem hfix80_6_2 : ∀ i, ((T80_6_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK80)
    ∈ fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK80) :=
  repsFix_of_siftB2 rK80 ⟨6, by decide⟩ T80_6_2 (by decide)

theorem hinj80_6_2 : Function.Injective
    (fun i => ((T80_6_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK80)) :=
  repsInj_of_reduceAux2 rK80 T80_6_2 (by decide)

theorem hcardT80_6_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK80)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK80 ⟨6, by decide⟩ R80_2 hpxR80_2 hcardq80_2 (by decide)).symm

/-- **Cell (80, 6) twin (q=2).** -/
theorem cell80_6_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK80) e = true)
    (h : ↥(reps (⟨6, by decide⟩ : Fin 148))) :
    species (reps (⟨6, by decide⟩ : Fin 148)) h (basisElt (reps rK80) (charOfVec2 rK80 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK80 e (h : Coordinate 2) T80_6_2 i :=
  species_entry_eq_sum rK80 ⟨6, by decide⟩ e heK h T80_6_2 hfix80_6_2 hinj80_6_2 hcardT80_6_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨6, by decide⟩) (reps rK80) (T80_6_2 i) (hfix80_6_2 i) h)

/-! ### Cell (80, 7) twin -/

def T80_7_2 : Fin 25 → Coordinate 2 := fun i => T80_7list.getD i.val (0,0,0,0,0)

theorem hfix80_7_2 : ∀ i, ((T80_7_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK80)
    ∈ fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK80) :=
  repsFix_of_siftB2 rK80 ⟨7, by decide⟩ T80_7_2 (by decide)

theorem hinj80_7_2 : Function.Injective
    (fun i => ((T80_7_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK80)) :=
  repsInj_of_reduceAux2 rK80 T80_7_2 (by decide)

theorem hcardT80_7_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK80)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK80 ⟨7, by decide⟩ R80_2 hpxR80_2 hcardq80_2 (by decide)).symm

/-- **Cell (80, 7) twin (q=2).** -/
theorem cell80_7_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK80) e = true)
    (h : ↥(reps (⟨7, by decide⟩ : Fin 148))) :
    species (reps (⟨7, by decide⟩ : Fin 148)) h (basisElt (reps rK80) (charOfVec2 rK80 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK80 e (h : Coordinate 2) T80_7_2 i :=
  species_entry_eq_sum rK80 ⟨7, by decide⟩ e heK h T80_7_2 hfix80_7_2 hinj80_7_2 hcardT80_7_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨7, by decide⟩) (reps rK80) (T80_7_2 i) (hfix80_7_2 i) h)

/-! ### Cell (80, 8) twin -/

def T80_8_2 : Fin 25 → Coordinate 2 := fun i => T80_8list.getD i.val (0,0,0,0,0)

theorem hfix80_8_2 : ∀ i, ((T80_8_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK80)
    ∈ fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK80) :=
  repsFix_of_siftB2 rK80 ⟨8, by decide⟩ T80_8_2 (by decide)

theorem hinj80_8_2 : Function.Injective
    (fun i => ((T80_8_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK80)) :=
  repsInj_of_reduceAux2 rK80 T80_8_2 (by decide)

theorem hcardT80_8_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK80)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK80 ⟨8, by decide⟩ R80_2 hpxR80_2 hcardq80_2 (by decide)).symm

/-- **Cell (80, 8) twin (q=2).** -/
theorem cell80_8_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK80) e = true)
    (h : ↥(reps (⟨8, by decide⟩ : Fin 148))) :
    species (reps (⟨8, by decide⟩ : Fin 148)) h (basisElt (reps rK80) (charOfVec2 rK80 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK80 e (h : Coordinate 2) T80_8_2 i :=
  species_entry_eq_sum rK80 ⟨8, by decide⟩ e heK h T80_8_2 hfix80_8_2 hinj80_8_2 hcardT80_8_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨8, by decide⟩) (reps rK80) (T80_8_2 i) (hfix80_8_2 i) h)

/-! ### Cell (80, 9) twin -/

def T80_9_2 : Fin 25 → Coordinate 2 := fun i => T80_9list.getD i.val (0,0,0,0,0)

theorem hfix80_9_2 : ∀ i, ((T80_9_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK80)
    ∈ fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK80) :=
  repsFix_of_siftB2 rK80 ⟨9, by decide⟩ T80_9_2 (by decide)

theorem hinj80_9_2 : Function.Injective
    (fun i => ((T80_9_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK80)) :=
  repsInj_of_reduceAux2 rK80 T80_9_2 (by decide)

theorem hcardT80_9_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK80)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK80 ⟨9, by decide⟩ R80_2 hpxR80_2 hcardq80_2 (by decide)).symm

/-- **Cell (80, 9) twin (q=2).** -/
theorem cell80_9_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK80) e = true)
    (h : ↥(reps (⟨9, by decide⟩ : Fin 148))) :
    species (reps (⟨9, by decide⟩ : Fin 148)) h (basisElt (reps rK80) (charOfVec2 rK80 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK80 e (h : Coordinate 2) T80_9_2 i :=
  species_entry_eq_sum rK80 ⟨9, by decide⟩ e heK h T80_9_2 hfix80_9_2 hinj80_9_2 hcardT80_9_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨9, by decide⟩) (reps rK80) (T80_9_2 i) (hfix80_9_2 i) h)

/-! ### Cell (80, 10) twin -/

def T80_10_2 : Fin 25 → Coordinate 2 := fun i => T80_10list.getD i.val (0,0,0,0,0)

theorem hfix80_10_2 : ∀ i, ((T80_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK80)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK80) :=
  repsFix_of_siftB2 rK80 ⟨10, by decide⟩ T80_10_2 (by decide)

theorem hinj80_10_2 : Function.Injective
    (fun i => ((T80_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK80)) :=
  repsInj_of_reduceAux2 rK80 T80_10_2 (by decide)

theorem hcardT80_10_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK80)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK80 ⟨10, by decide⟩ R80_2 hpxR80_2 hcardq80_2 (by decide)).symm

/-- **Cell (80, 10) twin (q=2).** -/
theorem cell80_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK80) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK80) (charOfVec2 rK80 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK80 e (h : Coordinate 2) T80_10_2 i :=
  species_entry_eq_sum rK80 ⟨10, by decide⟩ e heK h T80_10_2 hfix80_10_2 hinj80_10_2 hcardT80_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK80) (T80_10_2 i) (hfix80_10_2 i) h)

/-! ### Cell (80, 12) twin -/

def T80_12_2 : Fin 25 → Coordinate 2 := fun i => T80_12list.getD i.val (0,0,0,0,0)

theorem hfix80_12_2 : ∀ i, ((T80_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK80)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK80) :=
  repsFix_of_siftB2 rK80 ⟨12, by decide⟩ T80_12_2 (by decide)

theorem hinj80_12_2 : Function.Injective
    (fun i => ((T80_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK80)) :=
  repsInj_of_reduceAux2 rK80 T80_12_2 (by decide)

theorem hcardT80_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK80)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK80 ⟨12, by decide⟩ R80_2 hpxR80_2 hcardq80_2 (by decide)).symm

/-- **Cell (80, 12) twin (q=2).** -/
theorem cell80_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK80) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK80) (charOfVec2 rK80 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK80 e (h : Coordinate 2) T80_12_2 i :=
  species_entry_eq_sum rK80 ⟨12, by decide⟩ e heK h T80_12_2 hfix80_12_2 hinj80_12_2 hcardT80_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK80) (T80_12_2 i) (hfix80_12_2 i) h)

/-! ### Cell (80, 13) twin -/

def T80_13_2 : Fin 25 → Coordinate 2 := fun i => T80_13list.getD i.val (0,0,0,0,0)

theorem hfix80_13_2 : ∀ i, ((T80_13_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK80)
    ∈ fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK80) :=
  repsFix_of_siftB2 rK80 ⟨13, by decide⟩ T80_13_2 (by decide)

theorem hinj80_13_2 : Function.Injective
    (fun i => ((T80_13_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK80)) :=
  repsInj_of_reduceAux2 rK80 T80_13_2 (by decide)

theorem hcardT80_13_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK80)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK80 ⟨13, by decide⟩ R80_2 hpxR80_2 hcardq80_2 (by decide)).symm

/-- **Cell (80, 13) twin (q=2).** -/
theorem cell80_13_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK80) e = true)
    (h : ↥(reps (⟨13, by decide⟩ : Fin 148))) :
    species (reps (⟨13, by decide⟩ : Fin 148)) h (basisElt (reps rK80) (charOfVec2 rK80 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK80 e (h : Coordinate 2) T80_13_2 i :=
  species_entry_eq_sum rK80 ⟨13, by decide⟩ e heK h T80_13_2 hfix80_13_2 hinj80_13_2 hcardT80_13_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨13, by decide⟩) (reps rK80) (T80_13_2 i) (hfix80_13_2 i) h)

/-! ### Cell (80, 19) twin -/

def T80_19_2 : Fin 25 → Coordinate 2 := fun i => T80_19list.getD i.val (0,0,0,0,0)

theorem hfix80_19_2 : ∀ i, ((T80_19_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK80)
    ∈ fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK80) :=
  repsFix_of_siftB2 rK80 ⟨19, by decide⟩ T80_19_2 (by decide)

theorem hinj80_19_2 : Function.Injective
    (fun i => ((T80_19_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK80)) :=
  repsInj_of_reduceAux2 rK80 T80_19_2 (by decide)

theorem hcardT80_19_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK80)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK80 ⟨19, by decide⟩ R80_2 hpxR80_2 hcardq80_2 (by decide)).symm

/-- **Cell (80, 19) twin (q=2).** -/
theorem cell80_19_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK80) e = true)
    (h : ↥(reps (⟨19, by decide⟩ : Fin 148))) :
    species (reps (⟨19, by decide⟩ : Fin 148)) h (basisElt (reps rK80) (charOfVec2 rK80 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK80 e (h : Coordinate 2) T80_19_2 i :=
  species_entry_eq_sum rK80 ⟨19, by decide⟩ e heK h T80_19_2 hfix80_19_2 hinj80_19_2 hcardT80_19_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨19, by decide⟩) (reps rK80) (T80_19_2 i) (hfix80_19_2 i) h)

/-! ### Cell (80, 24) twin -/

def T80_24_2 : Fin 25 → Coordinate 2 := fun i => T80_24list.getD i.val (0,0,0,0,0)

theorem hfix80_24_2 : ∀ i, ((T80_24_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK80)
    ∈ fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK80) :=
  repsFix_of_siftB2 rK80 ⟨24, by decide⟩ T80_24_2 (by decide)

theorem hinj80_24_2 : Function.Injective
    (fun i => ((T80_24_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK80)) :=
  repsInj_of_reduceAux2 rK80 T80_24_2 (by decide)

theorem hcardT80_24_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK80)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK80 ⟨24, by decide⟩ R80_2 hpxR80_2 hcardq80_2 (by decide)).symm

/-- **Cell (80, 24) twin (q=2).** -/
theorem cell80_24_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK80) e = true)
    (h : ↥(reps (⟨24, by decide⟩ : Fin 148))) :
    species (reps (⟨24, by decide⟩ : Fin 148)) h (basisElt (reps rK80) (charOfVec2 rK80 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK80 e (h : Coordinate 2) T80_24_2 i :=
  species_entry_eq_sum rK80 ⟨24, by decide⟩ e heK h T80_24_2 hfix80_24_2 hinj80_24_2 hcardT80_24_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨24, by decide⟩) (reps rK80) (T80_24_2 i) (hfix80_24_2 i) h)

/-! ### Cell (80, 25) twin -/

def T80_25_2 : Fin 25 → Coordinate 2 := fun i => T80_25list.getD i.val (0,0,0,0,0)

theorem hfix80_25_2 : ∀ i, ((T80_25_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK80)
    ∈ fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK80) :=
  repsFix_of_siftB2 rK80 ⟨25, by decide⟩ T80_25_2 (by decide)

theorem hinj80_25_2 : Function.Injective
    (fun i => ((T80_25_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK80)) :=
  repsInj_of_reduceAux2 rK80 T80_25_2 (by decide)

theorem hcardT80_25_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK80)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK80 ⟨25, by decide⟩ R80_2 hpxR80_2 hcardq80_2 (by decide)).symm

/-- **Cell (80, 25) twin (q=2).** -/
theorem cell80_25_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK80) e = true)
    (h : ↥(reps (⟨25, by decide⟩ : Fin 148))) :
    species (reps (⟨25, by decide⟩ : Fin 148)) h (basisElt (reps rK80) (charOfVec2 rK80 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK80 e (h : Coordinate 2) T80_25_2 i :=
  species_entry_eq_sum rK80 ⟨25, by decide⟩ e heK h T80_25_2 hfix80_25_2 hinj80_25_2 hcardT80_25_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨25, by decide⟩) (reps rK80) (T80_25_2 i) (hfix80_25_2 i) h)

/-! ### Cell (80, 26) twin -/

def T80_26_2 : Fin 25 → Coordinate 2 := fun i => T80_26list.getD i.val (0,0,0,0,0)

theorem hfix80_26_2 : ∀ i, ((T80_26_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK80)
    ∈ fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK80) :=
  repsFix_of_siftB2 rK80 ⟨26, by decide⟩ T80_26_2 (by decide)

theorem hinj80_26_2 : Function.Injective
    (fun i => ((T80_26_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK80)) :=
  repsInj_of_reduceAux2 rK80 T80_26_2 (by decide)

theorem hcardT80_26_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK80)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK80 ⟨26, by decide⟩ R80_2 hpxR80_2 hcardq80_2 (by decide)).symm

/-- **Cell (80, 26) twin (q=2).** -/
theorem cell80_26_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK80) e = true)
    (h : ↥(reps (⟨26, by decide⟩ : Fin 148))) :
    species (reps (⟨26, by decide⟩ : Fin 148)) h (basisElt (reps rK80) (charOfVec2 rK80 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK80 e (h : Coordinate 2) T80_26_2 i :=
  species_entry_eq_sum rK80 ⟨26, by decide⟩ e heK h T80_26_2 hfix80_26_2 hinj80_26_2 hcardT80_26_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨26, by decide⟩) (reps rK80) (T80_26_2 i) (hfix80_26_2 i) h)

/-! ### Cell (80, 27) twin -/

def T80_27_2 : Fin 25 → Coordinate 2 := fun i => T80_27list.getD i.val (0,0,0,0,0)

theorem hfix80_27_2 : ∀ i, ((T80_27_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK80)
    ∈ fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK80) :=
  repsFix_of_siftB2 rK80 ⟨27, by decide⟩ T80_27_2 (by decide)

theorem hinj80_27_2 : Function.Injective
    (fun i => ((T80_27_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK80)) :=
  repsInj_of_reduceAux2 rK80 T80_27_2 (by decide)

theorem hcardT80_27_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK80)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK80 ⟨27, by decide⟩ R80_2 hpxR80_2 hcardq80_2 (by decide)).symm

/-- **Cell (80, 27) twin (q=2).** -/
theorem cell80_27_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK80) e = true)
    (h : ↥(reps (⟨27, by decide⟩ : Fin 148))) :
    species (reps (⟨27, by decide⟩ : Fin 148)) h (basisElt (reps rK80) (charOfVec2 rK80 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK80 e (h : Coordinate 2) T80_27_2 i :=
  species_entry_eq_sum rK80 ⟨27, by decide⟩ e heK h T80_27_2 hfix80_27_2 hinj80_27_2 hcardT80_27_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨27, by decide⟩) (reps rK80) (T80_27_2 i) (hfix80_27_2 i) h)

/-! ### Cell (80, 53) twin -/

def T80_53_2 : Fin 25 → Coordinate 2 := fun i => T80_53list.getD i.val (0,0,0,0,0)

theorem hfix80_53_2 : ∀ i, ((T80_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK80)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK80) :=
  repsFix_of_siftB2 rK80 ⟨53, by decide⟩ T80_53_2 (by decide)

theorem hinj80_53_2 : Function.Injective
    (fun i => ((T80_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK80)) :=
  repsInj_of_reduceAux2 rK80 T80_53_2 (by decide)

theorem hcardT80_53_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK80)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK80 ⟨53, by decide⟩ R80_2 hpxR80_2 hcardq80_2 (by decide)).symm

/-- **Cell (80, 53) twin (q=2).** -/
theorem cell80_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK80) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK80) (charOfVec2 rK80 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK80 e (h : Coordinate 2) T80_53_2 i :=
  species_entry_eq_sum rK80 ⟨53, by decide⟩ e heK h T80_53_2 hfix80_53_2 hinj80_53_2 hcardT80_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK80) (T80_53_2 i) (hfix80_53_2 i) h)

/-! ### Cell (80, 80) twin -/

def T80_80_2 : Fin 25 → Coordinate 2 := fun i => T80_80list.getD i.val (0,0,0,0,0)

theorem hfix80_80_2 : ∀ i, ((T80_80_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK80)
    ∈ fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK80) :=
  repsFix_of_siftB2 rK80 ⟨80, by decide⟩ T80_80_2 (by decide)

theorem hinj80_80_2 : Function.Injective
    (fun i => ((T80_80_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK80)) :=
  repsInj_of_reduceAux2 rK80 T80_80_2 (by decide)

theorem hcardT80_80_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK80)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK80 ⟨80, by decide⟩ R80_2 hpxR80_2 hcardq80_2 (by decide)).symm

/-- **Cell (80, 80) twin (q=2).** -/
theorem cell80_80_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK80) e = true)
    (h : ↥(reps (⟨80, by decide⟩ : Fin 148))) :
    species (reps (⟨80, by decide⟩ : Fin 148)) h (basisElt (reps rK80) (charOfVec2 rK80 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK80 e (h : Coordinate 2) T80_80_2 i :=
  species_entry_eq_sum rK80 ⟨80, by decide⟩ e heK h T80_80_2 hfix80_80_2 hinj80_80_2 hcardT80_80_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨80, by decide⟩) (reps rK80) (T80_80_2 i) (hfix80_80_2 i) h)

end Q2

/-! # K-class rK = 81  (|G/K| = 25) -/

def rK81 : Fin 148 := ⟨81, by decide⟩

def R81list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0)]
def R81 : Fin 25 → Coordinate 1 := fun i => R81list.getD i.val (0,0,0,0,0)

theorem hpxR81 : Function.Injective (fun i => reduceAux 1 (basisAt rK81) (R81 i)) := by decide
theorem hcardq81 : Nat.card (Coordinate 1 ⧸ reps rK81) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (81, 0): |T| = 25 -/

def T81_0list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0)]
def T81_0 : Fin 25 → Coordinate 1 := fun i => T81_0list.getD i.val (0,0,0,0,0)

theorem hfix81_0 : ∀ i, ((T81_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK81)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81) :=
  repsFix_of_siftB rK81 ⟨0, by decide⟩ T81_0 (by decide)

theorem hinj81_0 : Function.Injective
    (fun i => ((T81_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK81)) :=
  repsInj_of_reduceAux rK81 T81_0 (by decide)

theorem hcardT81_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK81 ⟨0, by decide⟩ R81 hpxR81 hcardq81 (by decide)).symm

/-- **Cell (81, 0).** -/
theorem cell81_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK81) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK81) (charOfVec rK81 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK81 e (h : Coordinate 1) T81_0 i :=
  species_entry_eq_sum rK81 ⟨0, by decide⟩ e heK h T81_0 hfix81_0 hinj81_0 hcardT81_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK81) (T81_0 i) (hfix81_0 i) h)

/-! ## Cell (81, 2): |T| = 25 -/

def T81_2list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0)]
def T81_2 : Fin 25 → Coordinate 1 := fun i => T81_2list.getD i.val (0,0,0,0,0)

theorem hfix81_2 : ∀ i, ((T81_2 i : Coordinate 1) : Coordinate 1 ⧸ reps rK81)
    ∈ fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81) :=
  repsFix_of_siftB rK81 ⟨2, by decide⟩ T81_2 (by decide)

theorem hinj81_2 : Function.Injective
    (fun i => ((T81_2 i : Coordinate 1) : Coordinate 1 ⧸ reps rK81)) :=
  repsInj_of_reduceAux rK81 T81_2 (by decide)

theorem hcardT81_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK81 ⟨2, by decide⟩ R81 hpxR81 hcardq81 (by decide)).symm

/-- **Cell (81, 2).** -/
theorem cell81_2 (e : List (ZMod 25)) (heK : charOK (basisAt rK81) e = true)
    (h : ↥(reps (⟨2, by decide⟩ : Fin 148))) :
    species (reps (⟨2, by decide⟩ : Fin 148)) h (basisElt (reps rK81) (charOfVec rK81 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK81 e (h : Coordinate 1) T81_2 i :=
  species_entry_eq_sum rK81 ⟨2, by decide⟩ e heK h T81_2 hfix81_2 hinj81_2 hcardT81_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨2, by decide⟩) (reps rK81) (T81_2 i) (hfix81_2 i) h)

/-! ## Cell (81, 10): |T| = 25 -/

def T81_10list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0)]
def T81_10 : Fin 25 → Coordinate 1 := fun i => T81_10list.getD i.val (0,0,0,0,0)

theorem hfix81_10 : ∀ i, ((T81_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK81)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81) :=
  repsFix_of_siftB rK81 ⟨10, by decide⟩ T81_10 (by decide)

theorem hinj81_10 : Function.Injective
    (fun i => ((T81_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK81)) :=
  repsInj_of_reduceAux rK81 T81_10 (by decide)

theorem hcardT81_10 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK81 ⟨10, by decide⟩ R81 hpxR81 hcardq81 (by decide)).symm

/-- **Cell (81, 10).** -/
theorem cell81_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK81) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK81) (charOfVec rK81 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK81 e (h : Coordinate 1) T81_10 i :=
  species_entry_eq_sum rK81 ⟨10, by decide⟩ e heK h T81_10 hfix81_10 hinj81_10 hcardT81_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK81) (T81_10 i) (hfix81_10 i) h)

/-! ## Cell (81, 12): |T| = 25 -/

def T81_12list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0)]
def T81_12 : Fin 25 → Coordinate 1 := fun i => T81_12list.getD i.val (0,0,0,0,0)

theorem hfix81_12 : ∀ i, ((T81_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK81)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81) :=
  repsFix_of_siftB rK81 ⟨12, by decide⟩ T81_12 (by decide)

theorem hinj81_12 : Function.Injective
    (fun i => ((T81_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK81)) :=
  repsInj_of_reduceAux rK81 T81_12 (by decide)

theorem hcardT81_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK81 ⟨12, by decide⟩ R81 hpxR81 hcardq81 (by decide)).symm

/-- **Cell (81, 12).** -/
theorem cell81_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK81) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK81) (charOfVec rK81 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK81 e (h : Coordinate 1) T81_12 i :=
  species_entry_eq_sum rK81 ⟨12, by decide⟩ e heK h T81_12 hfix81_12 hinj81_12 hcardT81_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK81) (T81_12 i) (hfix81_12 i) h)

/-! ## Cell (81, 20): |T| = 25 -/

def T81_20list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0)]
def T81_20 : Fin 25 → Coordinate 1 := fun i => T81_20list.getD i.val (0,0,0,0,0)

theorem hfix81_20 : ∀ i, ((T81_20 i : Coordinate 1) : Coordinate 1 ⧸ reps rK81)
    ∈ fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81) :=
  repsFix_of_siftB rK81 ⟨20, by decide⟩ T81_20 (by decide)

theorem hinj81_20 : Function.Injective
    (fun i => ((T81_20 i : Coordinate 1) : Coordinate 1 ⧸ reps rK81)) :=
  repsInj_of_reduceAux rK81 T81_20 (by decide)

theorem hcardT81_20 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK81 ⟨20, by decide⟩ R81 hpxR81 hcardq81 (by decide)).symm

/-- **Cell (81, 20).** -/
theorem cell81_20 (e : List (ZMod 25)) (heK : charOK (basisAt rK81) e = true)
    (h : ↥(reps (⟨20, by decide⟩ : Fin 148))) :
    species (reps (⟨20, by decide⟩ : Fin 148)) h (basisElt (reps rK81) (charOfVec rK81 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK81 e (h : Coordinate 1) T81_20 i :=
  species_entry_eq_sum rK81 ⟨20, by decide⟩ e heK h T81_20 hfix81_20 hinj81_20 hcardT81_20
    (fun i => conj_mem_of_fixedPoints (reps ⟨20, by decide⟩) (reps rK81) (T81_20 i) (hfix81_20 i) h)

/-! ## Cell (81, 53): |T| = 25 -/

def T81_53list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0)]
def T81_53 : Fin 25 → Coordinate 1 := fun i => T81_53list.getD i.val (0,0,0,0,0)

theorem hfix81_53 : ∀ i, ((T81_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK81)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81) :=
  repsFix_of_siftB rK81 ⟨53, by decide⟩ T81_53 (by decide)

theorem hinj81_53 : Function.Injective
    (fun i => ((T81_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK81)) :=
  repsInj_of_reduceAux rK81 T81_53 (by decide)

theorem hcardT81_53 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK81 ⟨53, by decide⟩ R81 hpxR81 hcardq81 (by decide)).symm

/-- **Cell (81, 53).** -/
theorem cell81_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK81) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK81) (charOfVec rK81 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK81 e (h : Coordinate 1) T81_53 i :=
  species_entry_eq_sum rK81 ⟨53, by decide⟩ e heK h T81_53 hfix81_53 hinj81_53 hcardT81_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK81) (T81_53 i) (hfix81_53 i) h)

/-! ## Cell (81, 81): |T| = 25 -/

def T81_81list : List Coordinates := [(0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0)]
def T81_81 : Fin 25 → Coordinate 1 := fun i => T81_81list.getD i.val (0,0,0,0,0)

theorem hfix81_81 : ∀ i, ((T81_81 i : Coordinate 1) : Coordinate 1 ⧸ reps rK81)
    ∈ fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81) :=
  repsFix_of_siftB rK81 ⟨81, by decide⟩ T81_81 (by decide)

theorem hinj81_81 : Function.Injective
    (fun i => ((T81_81 i : Coordinate 1) : Coordinate 1 ⧸ reps rK81)) :=
  repsInj_of_reduceAux rK81 T81_81 (by decide)

theorem hcardT81_81 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK81 ⟨81, by decide⟩ R81 hpxR81 hcardq81 (by decide)).symm

/-- **Cell (81, 81).** -/
theorem cell81_81 (e : List (ZMod 25)) (heK : charOK (basisAt rK81) e = true)
    (h : ↥(reps (⟨81, by decide⟩ : Fin 148))) :
    species (reps (⟨81, by decide⟩ : Fin 148)) h (basisElt (reps rK81) (charOfVec rK81 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK81 e (h : Coordinate 1) T81_81 i :=
  species_entry_eq_sum rK81 ⟨81, by decide⟩ e heK h T81_81 hfix81_81 hinj81_81 hcardT81_81
    (fun i => conj_mem_of_fixedPoints (reps ⟨81, by decide⟩) (reps rK81) (T81_81 i) (hfix81_81 i) h)

namespace Q2

def R81_2 : Fin 25 → Coordinate 2 := fun i => R81list.getD i.val (0,0,0,0,0)
theorem hpxR81_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK81) (R81_2 i)) := by decide
theorem hcardq81_2 : Nat.card (Coordinate 2 ⧸ reps rK81) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (81, 0) twin -/

def T81_0_2 : Fin 25 → Coordinate 2 := fun i => T81_0list.getD i.val (0,0,0,0,0)

theorem hfix81_0_2 : ∀ i, ((T81_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK81)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK81) :=
  repsFix_of_siftB2 rK81 ⟨0, by decide⟩ T81_0_2 (by decide)

theorem hinj81_0_2 : Function.Injective
    (fun i => ((T81_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK81)) :=
  repsInj_of_reduceAux2 rK81 T81_0_2 (by decide)

theorem hcardT81_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK81)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK81 ⟨0, by decide⟩ R81_2 hpxR81_2 hcardq81_2 (by decide)).symm

/-- **Cell (81, 0) twin (q=2).** -/
theorem cell81_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK81) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK81) (charOfVec2 rK81 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK81 e (h : Coordinate 2) T81_0_2 i :=
  species_entry_eq_sum rK81 ⟨0, by decide⟩ e heK h T81_0_2 hfix81_0_2 hinj81_0_2 hcardT81_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK81) (T81_0_2 i) (hfix81_0_2 i) h)

/-! ### Cell (81, 2) twin -/

def T81_2_2 : Fin 25 → Coordinate 2 := fun i => T81_2list.getD i.val (0,0,0,0,0)

theorem hfix81_2_2 : ∀ i, ((T81_2_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK81)
    ∈ fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK81) :=
  repsFix_of_siftB2 rK81 ⟨2, by decide⟩ T81_2_2 (by decide)

theorem hinj81_2_2 : Function.Injective
    (fun i => ((T81_2_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK81)) :=
  repsInj_of_reduceAux2 rK81 T81_2_2 (by decide)

theorem hcardT81_2_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK81)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK81 ⟨2, by decide⟩ R81_2 hpxR81_2 hcardq81_2 (by decide)).symm

/-- **Cell (81, 2) twin (q=2).** -/
theorem cell81_2_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK81) e = true)
    (h : ↥(reps (⟨2, by decide⟩ : Fin 148))) :
    species (reps (⟨2, by decide⟩ : Fin 148)) h (basisElt (reps rK81) (charOfVec2 rK81 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK81 e (h : Coordinate 2) T81_2_2 i :=
  species_entry_eq_sum rK81 ⟨2, by decide⟩ e heK h T81_2_2 hfix81_2_2 hinj81_2_2 hcardT81_2_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨2, by decide⟩) (reps rK81) (T81_2_2 i) (hfix81_2_2 i) h)

/-! ### Cell (81, 10) twin -/

def T81_10_2 : Fin 25 → Coordinate 2 := fun i => T81_10list.getD i.val (0,0,0,0,0)

theorem hfix81_10_2 : ∀ i, ((T81_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK81)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK81) :=
  repsFix_of_siftB2 rK81 ⟨10, by decide⟩ T81_10_2 (by decide)

theorem hinj81_10_2 : Function.Injective
    (fun i => ((T81_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK81)) :=
  repsInj_of_reduceAux2 rK81 T81_10_2 (by decide)

theorem hcardT81_10_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK81)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK81 ⟨10, by decide⟩ R81_2 hpxR81_2 hcardq81_2 (by decide)).symm

/-- **Cell (81, 10) twin (q=2).** -/
theorem cell81_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK81) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK81) (charOfVec2 rK81 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK81 e (h : Coordinate 2) T81_10_2 i :=
  species_entry_eq_sum rK81 ⟨10, by decide⟩ e heK h T81_10_2 hfix81_10_2 hinj81_10_2 hcardT81_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK81) (T81_10_2 i) (hfix81_10_2 i) h)

/-! ### Cell (81, 12) twin -/

def T81_12_2 : Fin 25 → Coordinate 2 := fun i => T81_12list.getD i.val (0,0,0,0,0)

theorem hfix81_12_2 : ∀ i, ((T81_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK81)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK81) :=
  repsFix_of_siftB2 rK81 ⟨12, by decide⟩ T81_12_2 (by decide)

theorem hinj81_12_2 : Function.Injective
    (fun i => ((T81_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK81)) :=
  repsInj_of_reduceAux2 rK81 T81_12_2 (by decide)

theorem hcardT81_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK81)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK81 ⟨12, by decide⟩ R81_2 hpxR81_2 hcardq81_2 (by decide)).symm

/-- **Cell (81, 12) twin (q=2).** -/
theorem cell81_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK81) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK81) (charOfVec2 rK81 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK81 e (h : Coordinate 2) T81_12_2 i :=
  species_entry_eq_sum rK81 ⟨12, by decide⟩ e heK h T81_12_2 hfix81_12_2 hinj81_12_2 hcardT81_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK81) (T81_12_2 i) (hfix81_12_2 i) h)

/-! ### Cell (81, 20) twin -/

def T81_20_2 : Fin 25 → Coordinate 2 := fun i => T81_20list.getD i.val (0,0,0,0,0)

theorem hfix81_20_2 : ∀ i, ((T81_20_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK81)
    ∈ fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK81) :=
  repsFix_of_siftB2 rK81 ⟨20, by decide⟩ T81_20_2 (by decide)

theorem hinj81_20_2 : Function.Injective
    (fun i => ((T81_20_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK81)) :=
  repsInj_of_reduceAux2 rK81 T81_20_2 (by decide)

theorem hcardT81_20_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK81)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK81 ⟨20, by decide⟩ R81_2 hpxR81_2 hcardq81_2 (by decide)).symm

/-- **Cell (81, 20) twin (q=2).** -/
theorem cell81_20_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK81) e = true)
    (h : ↥(reps (⟨20, by decide⟩ : Fin 148))) :
    species (reps (⟨20, by decide⟩ : Fin 148)) h (basisElt (reps rK81) (charOfVec2 rK81 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK81 e (h : Coordinate 2) T81_20_2 i :=
  species_entry_eq_sum rK81 ⟨20, by decide⟩ e heK h T81_20_2 hfix81_20_2 hinj81_20_2 hcardT81_20_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨20, by decide⟩) (reps rK81) (T81_20_2 i) (hfix81_20_2 i) h)

/-! ### Cell (81, 53) twin -/

def T81_53_2 : Fin 25 → Coordinate 2 := fun i => T81_53list.getD i.val (0,0,0,0,0)

theorem hfix81_53_2 : ∀ i, ((T81_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK81)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK81) :=
  repsFix_of_siftB2 rK81 ⟨53, by decide⟩ T81_53_2 (by decide)

theorem hinj81_53_2 : Function.Injective
    (fun i => ((T81_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK81)) :=
  repsInj_of_reduceAux2 rK81 T81_53_2 (by decide)

theorem hcardT81_53_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK81)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK81 ⟨53, by decide⟩ R81_2 hpxR81_2 hcardq81_2 (by decide)).symm

/-- **Cell (81, 53) twin (q=2).** -/
theorem cell81_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK81) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK81) (charOfVec2 rK81 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK81 e (h : Coordinate 2) T81_53_2 i :=
  species_entry_eq_sum rK81 ⟨53, by decide⟩ e heK h T81_53_2 hfix81_53_2 hinj81_53_2 hcardT81_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK81) (T81_53_2 i) (hfix81_53_2 i) h)

/-! ### Cell (81, 81) twin -/

def T81_81_2 : Fin 25 → Coordinate 2 := fun i => T81_81list.getD i.val (0,0,0,0,0)

theorem hfix81_81_2 : ∀ i, ((T81_81_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK81)
    ∈ fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK81) :=
  repsFix_of_siftB2 rK81 ⟨81, by decide⟩ T81_81_2 (by decide)

theorem hinj81_81_2 : Function.Injective
    (fun i => ((T81_81_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK81)) :=
  repsInj_of_reduceAux2 rK81 T81_81_2 (by decide)

theorem hcardT81_81_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK81)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK81 ⟨81, by decide⟩ R81_2 hpxR81_2 hcardq81_2 (by decide)).symm

/-- **Cell (81, 81) twin (q=2).** -/
theorem cell81_81_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK81) e = true)
    (h : ↥(reps (⟨81, by decide⟩ : Fin 148))) :
    species (reps (⟨81, by decide⟩ : Fin 148)) h (basisElt (reps rK81) (charOfVec2 rK81 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK81 e (h : Coordinate 2) T81_81_2 i :=
  species_entry_eq_sum rK81 ⟨81, by decide⟩ e heK h T81_81_2 hfix81_81_2 hinj81_81_2 hcardT81_81_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨81, by decide⟩) (reps rK81) (T81_81_2 i) (hfix81_81_2 i) h)

end Q2

/-! # K-class rK = 82  (|G/K| = 25) -/

def rK82 : Fin 148 := ⟨82, by decide⟩

def R82list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0)]
def R82 : Fin 25 → Coordinate 1 := fun i => R82list.getD i.val (0,0,0,0,0)

theorem hpxR82 : Function.Injective (fun i => reduceAux 1 (basisAt rK82) (R82 i)) := by decide
theorem hcardq82 : Nat.card (Coordinate 1 ⧸ reps rK82) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (82, 0): |T| = 25 -/

def T82_0list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0)]
def T82_0 : Fin 25 → Coordinate 1 := fun i => T82_0list.getD i.val (0,0,0,0,0)

theorem hfix82_0 : ∀ i, ((T82_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK82)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82) :=
  repsFix_of_siftB rK82 ⟨0, by decide⟩ T82_0 (by decide)

theorem hinj82_0 : Function.Injective
    (fun i => ((T82_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK82)) :=
  repsInj_of_reduceAux rK82 T82_0 (by decide)

theorem hcardT82_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK82 ⟨0, by decide⟩ R82 hpxR82 hcardq82 (by decide)).symm

/-- **Cell (82, 0).** -/
theorem cell82_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK82) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK82) (charOfVec rK82 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK82 e (h : Coordinate 1) T82_0 i :=
  species_entry_eq_sum rK82 ⟨0, by decide⟩ e heK h T82_0 hfix82_0 hinj82_0 hcardT82_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK82) (T82_0 i) (hfix82_0 i) h)

/-! ## Cell (82, 3): |T| = 25 -/

def T82_3list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0)]
def T82_3 : Fin 25 → Coordinate 1 := fun i => T82_3list.getD i.val (0,0,0,0,0)

theorem hfix82_3 : ∀ i, ((T82_3 i : Coordinate 1) : Coordinate 1 ⧸ reps rK82)
    ∈ fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82) :=
  repsFix_of_siftB rK82 ⟨3, by decide⟩ T82_3 (by decide)

theorem hinj82_3 : Function.Injective
    (fun i => ((T82_3 i : Coordinate 1) : Coordinate 1 ⧸ reps rK82)) :=
  repsInj_of_reduceAux rK82 T82_3 (by decide)

theorem hcardT82_3 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK82 ⟨3, by decide⟩ R82 hpxR82 hcardq82 (by decide)).symm

/-- **Cell (82, 3).** -/
theorem cell82_3 (e : List (ZMod 25)) (heK : charOK (basisAt rK82) e = true)
    (h : ↥(reps (⟨3, by decide⟩ : Fin 148))) :
    species (reps (⟨3, by decide⟩ : Fin 148)) h (basisElt (reps rK82) (charOfVec rK82 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK82 e (h : Coordinate 1) T82_3 i :=
  species_entry_eq_sum rK82 ⟨3, by decide⟩ e heK h T82_3 hfix82_3 hinj82_3 hcardT82_3
    (fun i => conj_mem_of_fixedPoints (reps ⟨3, by decide⟩) (reps rK82) (T82_3 i) (hfix82_3 i) h)

/-! ## Cell (82, 10): |T| = 25 -/

def T82_10list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0)]
def T82_10 : Fin 25 → Coordinate 1 := fun i => T82_10list.getD i.val (0,0,0,0,0)

theorem hfix82_10 : ∀ i, ((T82_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK82)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82) :=
  repsFix_of_siftB rK82 ⟨10, by decide⟩ T82_10 (by decide)

theorem hinj82_10 : Function.Injective
    (fun i => ((T82_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK82)) :=
  repsInj_of_reduceAux rK82 T82_10 (by decide)

theorem hcardT82_10 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK82 ⟨10, by decide⟩ R82 hpxR82 hcardq82 (by decide)).symm

/-- **Cell (82, 10).** -/
theorem cell82_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK82) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK82) (charOfVec rK82 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK82 e (h : Coordinate 1) T82_10 i :=
  species_entry_eq_sum rK82 ⟨10, by decide⟩ e heK h T82_10 hfix82_10 hinj82_10 hcardT82_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK82) (T82_10 i) (hfix82_10 i) h)

/-! ## Cell (82, 12): |T| = 25 -/

def T82_12list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0)]
def T82_12 : Fin 25 → Coordinate 1 := fun i => T82_12list.getD i.val (0,0,0,0,0)

theorem hfix82_12 : ∀ i, ((T82_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK82)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82) :=
  repsFix_of_siftB rK82 ⟨12, by decide⟩ T82_12 (by decide)

theorem hinj82_12 : Function.Injective
    (fun i => ((T82_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK82)) :=
  repsInj_of_reduceAux rK82 T82_12 (by decide)

theorem hcardT82_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK82 ⟨12, by decide⟩ R82 hpxR82 hcardq82 (by decide)).symm

/-- **Cell (82, 12).** -/
theorem cell82_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK82) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK82) (charOfVec rK82 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK82 e (h : Coordinate 1) T82_12 i :=
  species_entry_eq_sum rK82 ⟨12, by decide⟩ e heK h T82_12 hfix82_12 hinj82_12 hcardT82_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK82) (T82_12 i) (hfix82_12 i) h)

/-! ## Cell (82, 21): |T| = 25 -/

def T82_21list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0)]
def T82_21 : Fin 25 → Coordinate 1 := fun i => T82_21list.getD i.val (0,0,0,0,0)

theorem hfix82_21 : ∀ i, ((T82_21 i : Coordinate 1) : Coordinate 1 ⧸ reps rK82)
    ∈ fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82) :=
  repsFix_of_siftB rK82 ⟨21, by decide⟩ T82_21 (by decide)

theorem hinj82_21 : Function.Injective
    (fun i => ((T82_21 i : Coordinate 1) : Coordinate 1 ⧸ reps rK82)) :=
  repsInj_of_reduceAux rK82 T82_21 (by decide)

theorem hcardT82_21 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK82 ⟨21, by decide⟩ R82 hpxR82 hcardq82 (by decide)).symm

/-- **Cell (82, 21).** -/
theorem cell82_21 (e : List (ZMod 25)) (heK : charOK (basisAt rK82) e = true)
    (h : ↥(reps (⟨21, by decide⟩ : Fin 148))) :
    species (reps (⟨21, by decide⟩ : Fin 148)) h (basisElt (reps rK82) (charOfVec rK82 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK82 e (h : Coordinate 1) T82_21 i :=
  species_entry_eq_sum rK82 ⟨21, by decide⟩ e heK h T82_21 hfix82_21 hinj82_21 hcardT82_21
    (fun i => conj_mem_of_fixedPoints (reps ⟨21, by decide⟩) (reps rK82) (T82_21 i) (hfix82_21 i) h)

/-! ## Cell (82, 53): |T| = 25 -/

def T82_53list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0)]
def T82_53 : Fin 25 → Coordinate 1 := fun i => T82_53list.getD i.val (0,0,0,0,0)

theorem hfix82_53 : ∀ i, ((T82_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK82)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82) :=
  repsFix_of_siftB rK82 ⟨53, by decide⟩ T82_53 (by decide)

theorem hinj82_53 : Function.Injective
    (fun i => ((T82_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK82)) :=
  repsInj_of_reduceAux rK82 T82_53 (by decide)

theorem hcardT82_53 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK82 ⟨53, by decide⟩ R82 hpxR82 hcardq82 (by decide)).symm

/-- **Cell (82, 53).** -/
theorem cell82_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK82) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK82) (charOfVec rK82 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK82 e (h : Coordinate 1) T82_53 i :=
  species_entry_eq_sum rK82 ⟨53, by decide⟩ e heK h T82_53 hfix82_53 hinj82_53 hcardT82_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK82) (T82_53 i) (hfix82_53 i) h)

/-! ## Cell (82, 82): |T| = 25 -/

def T82_82list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0)]
def T82_82 : Fin 25 → Coordinate 1 := fun i => T82_82list.getD i.val (0,0,0,0,0)

theorem hfix82_82 : ∀ i, ((T82_82 i : Coordinate 1) : Coordinate 1 ⧸ reps rK82)
    ∈ fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82) :=
  repsFix_of_siftB rK82 ⟨82, by decide⟩ T82_82 (by decide)

theorem hinj82_82 : Function.Injective
    (fun i => ((T82_82 i : Coordinate 1) : Coordinate 1 ⧸ reps rK82)) :=
  repsInj_of_reduceAux rK82 T82_82 (by decide)

theorem hcardT82_82 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK82 ⟨82, by decide⟩ R82 hpxR82 hcardq82 (by decide)).symm

/-- **Cell (82, 82).** -/
theorem cell82_82 (e : List (ZMod 25)) (heK : charOK (basisAt rK82) e = true)
    (h : ↥(reps (⟨82, by decide⟩ : Fin 148))) :
    species (reps (⟨82, by decide⟩ : Fin 148)) h (basisElt (reps rK82) (charOfVec rK82 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK82 e (h : Coordinate 1) T82_82 i :=
  species_entry_eq_sum rK82 ⟨82, by decide⟩ e heK h T82_82 hfix82_82 hinj82_82 hcardT82_82
    (fun i => conj_mem_of_fixedPoints (reps ⟨82, by decide⟩) (reps rK82) (T82_82 i) (hfix82_82 i) h)

namespace Q2

def R82_2 : Fin 25 → Coordinate 2 := fun i => R82list.getD i.val (0,0,0,0,0)
theorem hpxR82_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK82) (R82_2 i)) := by decide
theorem hcardq82_2 : Nat.card (Coordinate 2 ⧸ reps rK82) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (82, 0) twin -/

def T82_0_2 : Fin 25 → Coordinate 2 := fun i => T82_0list.getD i.val (0,0,0,0,0)

theorem hfix82_0_2 : ∀ i, ((T82_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK82)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK82) :=
  repsFix_of_siftB2 rK82 ⟨0, by decide⟩ T82_0_2 (by decide)

theorem hinj82_0_2 : Function.Injective
    (fun i => ((T82_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK82)) :=
  repsInj_of_reduceAux2 rK82 T82_0_2 (by decide)

theorem hcardT82_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK82)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK82 ⟨0, by decide⟩ R82_2 hpxR82_2 hcardq82_2 (by decide)).symm

/-- **Cell (82, 0) twin (q=2).** -/
theorem cell82_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK82) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK82) (charOfVec2 rK82 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK82 e (h : Coordinate 2) T82_0_2 i :=
  species_entry_eq_sum rK82 ⟨0, by decide⟩ e heK h T82_0_2 hfix82_0_2 hinj82_0_2 hcardT82_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK82) (T82_0_2 i) (hfix82_0_2 i) h)

/-! ### Cell (82, 3) twin -/

def T82_3_2 : Fin 25 → Coordinate 2 := fun i => T82_3list.getD i.val (0,0,0,0,0)

theorem hfix82_3_2 : ∀ i, ((T82_3_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK82)
    ∈ fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK82) :=
  repsFix_of_siftB2 rK82 ⟨3, by decide⟩ T82_3_2 (by decide)

theorem hinj82_3_2 : Function.Injective
    (fun i => ((T82_3_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK82)) :=
  repsInj_of_reduceAux2 rK82 T82_3_2 (by decide)

theorem hcardT82_3_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK82)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK82 ⟨3, by decide⟩ R82_2 hpxR82_2 hcardq82_2 (by decide)).symm

/-- **Cell (82, 3) twin (q=2).** -/
theorem cell82_3_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK82) e = true)
    (h : ↥(reps (⟨3, by decide⟩ : Fin 148))) :
    species (reps (⟨3, by decide⟩ : Fin 148)) h (basisElt (reps rK82) (charOfVec2 rK82 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK82 e (h : Coordinate 2) T82_3_2 i :=
  species_entry_eq_sum rK82 ⟨3, by decide⟩ e heK h T82_3_2 hfix82_3_2 hinj82_3_2 hcardT82_3_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨3, by decide⟩) (reps rK82) (T82_3_2 i) (hfix82_3_2 i) h)

/-! ### Cell (82, 10) twin -/

def T82_10_2 : Fin 25 → Coordinate 2 := fun i => T82_10list.getD i.val (0,0,0,0,0)

theorem hfix82_10_2 : ∀ i, ((T82_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK82)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK82) :=
  repsFix_of_siftB2 rK82 ⟨10, by decide⟩ T82_10_2 (by decide)

theorem hinj82_10_2 : Function.Injective
    (fun i => ((T82_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK82)) :=
  repsInj_of_reduceAux2 rK82 T82_10_2 (by decide)

theorem hcardT82_10_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK82)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK82 ⟨10, by decide⟩ R82_2 hpxR82_2 hcardq82_2 (by decide)).symm

/-- **Cell (82, 10) twin (q=2).** -/
theorem cell82_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK82) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK82) (charOfVec2 rK82 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK82 e (h : Coordinate 2) T82_10_2 i :=
  species_entry_eq_sum rK82 ⟨10, by decide⟩ e heK h T82_10_2 hfix82_10_2 hinj82_10_2 hcardT82_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK82) (T82_10_2 i) (hfix82_10_2 i) h)

/-! ### Cell (82, 12) twin -/

def T82_12_2 : Fin 25 → Coordinate 2 := fun i => T82_12list.getD i.val (0,0,0,0,0)

theorem hfix82_12_2 : ∀ i, ((T82_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK82)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK82) :=
  repsFix_of_siftB2 rK82 ⟨12, by decide⟩ T82_12_2 (by decide)

theorem hinj82_12_2 : Function.Injective
    (fun i => ((T82_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK82)) :=
  repsInj_of_reduceAux2 rK82 T82_12_2 (by decide)

theorem hcardT82_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK82)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK82 ⟨12, by decide⟩ R82_2 hpxR82_2 hcardq82_2 (by decide)).symm

/-- **Cell (82, 12) twin (q=2).** -/
theorem cell82_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK82) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK82) (charOfVec2 rK82 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK82 e (h : Coordinate 2) T82_12_2 i :=
  species_entry_eq_sum rK82 ⟨12, by decide⟩ e heK h T82_12_2 hfix82_12_2 hinj82_12_2 hcardT82_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK82) (T82_12_2 i) (hfix82_12_2 i) h)

/-! ### Cell (82, 21) twin -/

def T82_21_2 : Fin 25 → Coordinate 2 := fun i => T82_21list.getD i.val (0,0,0,0,0)

theorem hfix82_21_2 : ∀ i, ((T82_21_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK82)
    ∈ fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK82) :=
  repsFix_of_siftB2 rK82 ⟨21, by decide⟩ T82_21_2 (by decide)

theorem hinj82_21_2 : Function.Injective
    (fun i => ((T82_21_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK82)) :=
  repsInj_of_reduceAux2 rK82 T82_21_2 (by decide)

theorem hcardT82_21_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK82)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK82 ⟨21, by decide⟩ R82_2 hpxR82_2 hcardq82_2 (by decide)).symm

/-- **Cell (82, 21) twin (q=2).** -/
theorem cell82_21_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK82) e = true)
    (h : ↥(reps (⟨21, by decide⟩ : Fin 148))) :
    species (reps (⟨21, by decide⟩ : Fin 148)) h (basisElt (reps rK82) (charOfVec2 rK82 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK82 e (h : Coordinate 2) T82_21_2 i :=
  species_entry_eq_sum rK82 ⟨21, by decide⟩ e heK h T82_21_2 hfix82_21_2 hinj82_21_2 hcardT82_21_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨21, by decide⟩) (reps rK82) (T82_21_2 i) (hfix82_21_2 i) h)

/-! ### Cell (82, 53) twin -/

def T82_53_2 : Fin 25 → Coordinate 2 := fun i => T82_53list.getD i.val (0,0,0,0,0)

theorem hfix82_53_2 : ∀ i, ((T82_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK82)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK82) :=
  repsFix_of_siftB2 rK82 ⟨53, by decide⟩ T82_53_2 (by decide)

theorem hinj82_53_2 : Function.Injective
    (fun i => ((T82_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK82)) :=
  repsInj_of_reduceAux2 rK82 T82_53_2 (by decide)

theorem hcardT82_53_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK82)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK82 ⟨53, by decide⟩ R82_2 hpxR82_2 hcardq82_2 (by decide)).symm

/-- **Cell (82, 53) twin (q=2).** -/
theorem cell82_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK82) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK82) (charOfVec2 rK82 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK82 e (h : Coordinate 2) T82_53_2 i :=
  species_entry_eq_sum rK82 ⟨53, by decide⟩ e heK h T82_53_2 hfix82_53_2 hinj82_53_2 hcardT82_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK82) (T82_53_2 i) (hfix82_53_2 i) h)

/-! ### Cell (82, 82) twin -/

def T82_82_2 : Fin 25 → Coordinate 2 := fun i => T82_82list.getD i.val (0,0,0,0,0)

theorem hfix82_82_2 : ∀ i, ((T82_82_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK82)
    ∈ fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK82) :=
  repsFix_of_siftB2 rK82 ⟨82, by decide⟩ T82_82_2 (by decide)

theorem hinj82_82_2 : Function.Injective
    (fun i => ((T82_82_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK82)) :=
  repsInj_of_reduceAux2 rK82 T82_82_2 (by decide)

theorem hcardT82_82_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK82)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK82 ⟨82, by decide⟩ R82_2 hpxR82_2 hcardq82_2 (by decide)).symm

/-- **Cell (82, 82) twin (q=2).** -/
theorem cell82_82_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK82) e = true)
    (h : ↥(reps (⟨82, by decide⟩ : Fin 148))) :
    species (reps (⟨82, by decide⟩ : Fin 148)) h (basisElt (reps rK82) (charOfVec2 rK82 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK82 e (h : Coordinate 2) T82_82_2 i :=
  species_entry_eq_sum rK82 ⟨82, by decide⟩ e heK h T82_82_2 hfix82_82_2 hinj82_82_2 hcardT82_82_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨82, by decide⟩) (reps rK82) (T82_82_2 i) (hfix82_82_2 i) h)

end Q2

/-! # K-class rK = 83  (|G/K| = 25) -/

def rK83 : Fin 148 := ⟨83, by decide⟩

def R83list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0)]
def R83 : Fin 25 → Coordinate 1 := fun i => R83list.getD i.val (0,0,0,0,0)

theorem hpxR83 : Function.Injective (fun i => reduceAux 1 (basisAt rK83) (R83 i)) := by decide
theorem hcardq83 : Nat.card (Coordinate 1 ⧸ reps rK83) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (83, 0): |T| = 25 -/

def T83_0list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0)]
def T83_0 : Fin 25 → Coordinate 1 := fun i => T83_0list.getD i.val (0,0,0,0,0)

theorem hfix83_0 : ∀ i, ((T83_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK83)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83) :=
  repsFix_of_siftB rK83 ⟨0, by decide⟩ T83_0 (by decide)

theorem hinj83_0 : Function.Injective
    (fun i => ((T83_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK83)) :=
  repsInj_of_reduceAux rK83 T83_0 (by decide)

theorem hcardT83_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK83 ⟨0, by decide⟩ R83 hpxR83 hcardq83 (by decide)).symm

/-- **Cell (83, 0).** -/
theorem cell83_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK83) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK83) (charOfVec rK83 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK83 e (h : Coordinate 1) T83_0 i :=
  species_entry_eq_sum rK83 ⟨0, by decide⟩ e heK h T83_0 hfix83_0 hinj83_0 hcardT83_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK83) (T83_0 i) (hfix83_0 i) h)

/-! ## Cell (83, 4): |T| = 25 -/

def T83_4list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0)]
def T83_4 : Fin 25 → Coordinate 1 := fun i => T83_4list.getD i.val (0,0,0,0,0)

theorem hfix83_4 : ∀ i, ((T83_4 i : Coordinate 1) : Coordinate 1 ⧸ reps rK83)
    ∈ fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83) :=
  repsFix_of_siftB rK83 ⟨4, by decide⟩ T83_4 (by decide)

theorem hinj83_4 : Function.Injective
    (fun i => ((T83_4 i : Coordinate 1) : Coordinate 1 ⧸ reps rK83)) :=
  repsInj_of_reduceAux rK83 T83_4 (by decide)

theorem hcardT83_4 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK83 ⟨4, by decide⟩ R83 hpxR83 hcardq83 (by decide)).symm

/-- **Cell (83, 4).** -/
theorem cell83_4 (e : List (ZMod 25)) (heK : charOK (basisAt rK83) e = true)
    (h : ↥(reps (⟨4, by decide⟩ : Fin 148))) :
    species (reps (⟨4, by decide⟩ : Fin 148)) h (basisElt (reps rK83) (charOfVec rK83 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK83 e (h : Coordinate 1) T83_4 i :=
  species_entry_eq_sum rK83 ⟨4, by decide⟩ e heK h T83_4 hfix83_4 hinj83_4 hcardT83_4
    (fun i => conj_mem_of_fixedPoints (reps ⟨4, by decide⟩) (reps rK83) (T83_4 i) (hfix83_4 i) h)

/-! ## Cell (83, 10): |T| = 25 -/

def T83_10list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0)]
def T83_10 : Fin 25 → Coordinate 1 := fun i => T83_10list.getD i.val (0,0,0,0,0)

theorem hfix83_10 : ∀ i, ((T83_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK83)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83) :=
  repsFix_of_siftB rK83 ⟨10, by decide⟩ T83_10 (by decide)

theorem hinj83_10 : Function.Injective
    (fun i => ((T83_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK83)) :=
  repsInj_of_reduceAux rK83 T83_10 (by decide)

theorem hcardT83_10 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK83 ⟨10, by decide⟩ R83 hpxR83 hcardq83 (by decide)).symm

/-- **Cell (83, 10).** -/
theorem cell83_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK83) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK83) (charOfVec rK83 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK83 e (h : Coordinate 1) T83_10 i :=
  species_entry_eq_sum rK83 ⟨10, by decide⟩ e heK h T83_10 hfix83_10 hinj83_10 hcardT83_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK83) (T83_10 i) (hfix83_10 i) h)

/-! ## Cell (83, 12): |T| = 25 -/

def T83_12list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0)]
def T83_12 : Fin 25 → Coordinate 1 := fun i => T83_12list.getD i.val (0,0,0,0,0)

theorem hfix83_12 : ∀ i, ((T83_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK83)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83) :=
  repsFix_of_siftB rK83 ⟨12, by decide⟩ T83_12 (by decide)

theorem hinj83_12 : Function.Injective
    (fun i => ((T83_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK83)) :=
  repsInj_of_reduceAux rK83 T83_12 (by decide)

theorem hcardT83_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK83 ⟨12, by decide⟩ R83 hpxR83 hcardq83 (by decide)).symm

/-- **Cell (83, 12).** -/
theorem cell83_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK83) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK83) (charOfVec rK83 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK83 e (h : Coordinate 1) T83_12 i :=
  species_entry_eq_sum rK83 ⟨12, by decide⟩ e heK h T83_12 hfix83_12 hinj83_12 hcardT83_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK83) (T83_12 i) (hfix83_12 i) h)

/-! ## Cell (83, 22): |T| = 25 -/

def T83_22list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0)]
def T83_22 : Fin 25 → Coordinate 1 := fun i => T83_22list.getD i.val (0,0,0,0,0)

theorem hfix83_22 : ∀ i, ((T83_22 i : Coordinate 1) : Coordinate 1 ⧸ reps rK83)
    ∈ fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83) :=
  repsFix_of_siftB rK83 ⟨22, by decide⟩ T83_22 (by decide)

theorem hinj83_22 : Function.Injective
    (fun i => ((T83_22 i : Coordinate 1) : Coordinate 1 ⧸ reps rK83)) :=
  repsInj_of_reduceAux rK83 T83_22 (by decide)

theorem hcardT83_22 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK83 ⟨22, by decide⟩ R83 hpxR83 hcardq83 (by decide)).symm

/-- **Cell (83, 22).** -/
theorem cell83_22 (e : List (ZMod 25)) (heK : charOK (basisAt rK83) e = true)
    (h : ↥(reps (⟨22, by decide⟩ : Fin 148))) :
    species (reps (⟨22, by decide⟩ : Fin 148)) h (basisElt (reps rK83) (charOfVec rK83 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK83 e (h : Coordinate 1) T83_22 i :=
  species_entry_eq_sum rK83 ⟨22, by decide⟩ e heK h T83_22 hfix83_22 hinj83_22 hcardT83_22
    (fun i => conj_mem_of_fixedPoints (reps ⟨22, by decide⟩) (reps rK83) (T83_22 i) (hfix83_22 i) h)

/-! ## Cell (83, 53): |T| = 25 -/

def T83_53list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0)]
def T83_53 : Fin 25 → Coordinate 1 := fun i => T83_53list.getD i.val (0,0,0,0,0)

theorem hfix83_53 : ∀ i, ((T83_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK83)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83) :=
  repsFix_of_siftB rK83 ⟨53, by decide⟩ T83_53 (by decide)

theorem hinj83_53 : Function.Injective
    (fun i => ((T83_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK83)) :=
  repsInj_of_reduceAux rK83 T83_53 (by decide)

theorem hcardT83_53 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK83 ⟨53, by decide⟩ R83 hpxR83 hcardq83 (by decide)).symm

/-- **Cell (83, 53).** -/
theorem cell83_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK83) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK83) (charOfVec rK83 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK83 e (h : Coordinate 1) T83_53 i :=
  species_entry_eq_sum rK83 ⟨53, by decide⟩ e heK h T83_53 hfix83_53 hinj83_53 hcardT83_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK83) (T83_53 i) (hfix83_53 i) h)

/-! ## Cell (83, 83): |T| = 25 -/

def T83_83list : List Coordinates := [(0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0), (0,4,1,0,0), (0,4,2,0,0)]
def T83_83 : Fin 25 → Coordinate 1 := fun i => T83_83list.getD i.val (0,0,0,0,0)

theorem hfix83_83 : ∀ i, ((T83_83 i : Coordinate 1) : Coordinate 1 ⧸ reps rK83)
    ∈ fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83) :=
  repsFix_of_siftB rK83 ⟨83, by decide⟩ T83_83 (by decide)

theorem hinj83_83 : Function.Injective
    (fun i => ((T83_83 i : Coordinate 1) : Coordinate 1 ⧸ reps rK83)) :=
  repsInj_of_reduceAux rK83 T83_83 (by decide)

theorem hcardT83_83 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK83 ⟨83, by decide⟩ R83 hpxR83 hcardq83 (by decide)).symm

/-- **Cell (83, 83).** -/
theorem cell83_83 (e : List (ZMod 25)) (heK : charOK (basisAt rK83) e = true)
    (h : ↥(reps (⟨83, by decide⟩ : Fin 148))) :
    species (reps (⟨83, by decide⟩ : Fin 148)) h (basisElt (reps rK83) (charOfVec rK83 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK83 e (h : Coordinate 1) T83_83 i :=
  species_entry_eq_sum rK83 ⟨83, by decide⟩ e heK h T83_83 hfix83_83 hinj83_83 hcardT83_83
    (fun i => conj_mem_of_fixedPoints (reps ⟨83, by decide⟩) (reps rK83) (T83_83 i) (hfix83_83 i) h)

namespace Q2

def R83_2 : Fin 25 → Coordinate 2 := fun i => R83list.getD i.val (0,0,0,0,0)
theorem hpxR83_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK83) (R83_2 i)) := by decide
theorem hcardq83_2 : Nat.card (Coordinate 2 ⧸ reps rK83) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (83, 0) twin -/

def T83_0_2 : Fin 25 → Coordinate 2 := fun i => T83_0list.getD i.val (0,0,0,0,0)

theorem hfix83_0_2 : ∀ i, ((T83_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK83)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK83) :=
  repsFix_of_siftB2 rK83 ⟨0, by decide⟩ T83_0_2 (by decide)

theorem hinj83_0_2 : Function.Injective
    (fun i => ((T83_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK83)) :=
  repsInj_of_reduceAux2 rK83 T83_0_2 (by decide)

theorem hcardT83_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK83)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK83 ⟨0, by decide⟩ R83_2 hpxR83_2 hcardq83_2 (by decide)).symm

/-- **Cell (83, 0) twin (q=2).** -/
theorem cell83_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK83) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK83) (charOfVec2 rK83 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK83 e (h : Coordinate 2) T83_0_2 i :=
  species_entry_eq_sum rK83 ⟨0, by decide⟩ e heK h T83_0_2 hfix83_0_2 hinj83_0_2 hcardT83_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK83) (T83_0_2 i) (hfix83_0_2 i) h)

/-! ### Cell (83, 4) twin -/

def T83_4_2 : Fin 25 → Coordinate 2 := fun i => T83_4list.getD i.val (0,0,0,0,0)

theorem hfix83_4_2 : ∀ i, ((T83_4_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK83)
    ∈ fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK83) :=
  repsFix_of_siftB2 rK83 ⟨4, by decide⟩ T83_4_2 (by decide)

theorem hinj83_4_2 : Function.Injective
    (fun i => ((T83_4_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK83)) :=
  repsInj_of_reduceAux2 rK83 T83_4_2 (by decide)

theorem hcardT83_4_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK83)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK83 ⟨4, by decide⟩ R83_2 hpxR83_2 hcardq83_2 (by decide)).symm

/-- **Cell (83, 4) twin (q=2).** -/
theorem cell83_4_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK83) e = true)
    (h : ↥(reps (⟨4, by decide⟩ : Fin 148))) :
    species (reps (⟨4, by decide⟩ : Fin 148)) h (basisElt (reps rK83) (charOfVec2 rK83 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK83 e (h : Coordinate 2) T83_4_2 i :=
  species_entry_eq_sum rK83 ⟨4, by decide⟩ e heK h T83_4_2 hfix83_4_2 hinj83_4_2 hcardT83_4_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨4, by decide⟩) (reps rK83) (T83_4_2 i) (hfix83_4_2 i) h)

/-! ### Cell (83, 10) twin -/

def T83_10_2 : Fin 25 → Coordinate 2 := fun i => T83_10list.getD i.val (0,0,0,0,0)

theorem hfix83_10_2 : ∀ i, ((T83_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK83)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK83) :=
  repsFix_of_siftB2 rK83 ⟨10, by decide⟩ T83_10_2 (by decide)

theorem hinj83_10_2 : Function.Injective
    (fun i => ((T83_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK83)) :=
  repsInj_of_reduceAux2 rK83 T83_10_2 (by decide)

theorem hcardT83_10_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK83)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK83 ⟨10, by decide⟩ R83_2 hpxR83_2 hcardq83_2 (by decide)).symm

/-- **Cell (83, 10) twin (q=2).** -/
theorem cell83_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK83) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK83) (charOfVec2 rK83 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK83 e (h : Coordinate 2) T83_10_2 i :=
  species_entry_eq_sum rK83 ⟨10, by decide⟩ e heK h T83_10_2 hfix83_10_2 hinj83_10_2 hcardT83_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK83) (T83_10_2 i) (hfix83_10_2 i) h)

/-! ### Cell (83, 12) twin -/

def T83_12_2 : Fin 25 → Coordinate 2 := fun i => T83_12list.getD i.val (0,0,0,0,0)

theorem hfix83_12_2 : ∀ i, ((T83_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK83)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK83) :=
  repsFix_of_siftB2 rK83 ⟨12, by decide⟩ T83_12_2 (by decide)

theorem hinj83_12_2 : Function.Injective
    (fun i => ((T83_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK83)) :=
  repsInj_of_reduceAux2 rK83 T83_12_2 (by decide)

theorem hcardT83_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK83)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK83 ⟨12, by decide⟩ R83_2 hpxR83_2 hcardq83_2 (by decide)).symm

/-- **Cell (83, 12) twin (q=2).** -/
theorem cell83_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK83) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK83) (charOfVec2 rK83 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK83 e (h : Coordinate 2) T83_12_2 i :=
  species_entry_eq_sum rK83 ⟨12, by decide⟩ e heK h T83_12_2 hfix83_12_2 hinj83_12_2 hcardT83_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK83) (T83_12_2 i) (hfix83_12_2 i) h)

/-! ### Cell (83, 22) twin -/

def T83_22_2 : Fin 25 → Coordinate 2 := fun i => T83_22list.getD i.val (0,0,0,0,0)

theorem hfix83_22_2 : ∀ i, ((T83_22_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK83)
    ∈ fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK83) :=
  repsFix_of_siftB2 rK83 ⟨22, by decide⟩ T83_22_2 (by decide)

theorem hinj83_22_2 : Function.Injective
    (fun i => ((T83_22_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK83)) :=
  repsInj_of_reduceAux2 rK83 T83_22_2 (by decide)

theorem hcardT83_22_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK83)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK83 ⟨22, by decide⟩ R83_2 hpxR83_2 hcardq83_2 (by decide)).symm

/-- **Cell (83, 22) twin (q=2).** -/
theorem cell83_22_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK83) e = true)
    (h : ↥(reps (⟨22, by decide⟩ : Fin 148))) :
    species (reps (⟨22, by decide⟩ : Fin 148)) h (basisElt (reps rK83) (charOfVec2 rK83 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK83 e (h : Coordinate 2) T83_22_2 i :=
  species_entry_eq_sum rK83 ⟨22, by decide⟩ e heK h T83_22_2 hfix83_22_2 hinj83_22_2 hcardT83_22_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨22, by decide⟩) (reps rK83) (T83_22_2 i) (hfix83_22_2 i) h)

/-! ### Cell (83, 53) twin -/

def T83_53_2 : Fin 25 → Coordinate 2 := fun i => T83_53list.getD i.val (0,0,0,0,0)

theorem hfix83_53_2 : ∀ i, ((T83_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK83)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK83) :=
  repsFix_of_siftB2 rK83 ⟨53, by decide⟩ T83_53_2 (by decide)

theorem hinj83_53_2 : Function.Injective
    (fun i => ((T83_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK83)) :=
  repsInj_of_reduceAux2 rK83 T83_53_2 (by decide)

theorem hcardT83_53_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK83)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK83 ⟨53, by decide⟩ R83_2 hpxR83_2 hcardq83_2 (by decide)).symm

/-- **Cell (83, 53) twin (q=2).** -/
theorem cell83_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK83) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK83) (charOfVec2 rK83 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK83 e (h : Coordinate 2) T83_53_2 i :=
  species_entry_eq_sum rK83 ⟨53, by decide⟩ e heK h T83_53_2 hfix83_53_2 hinj83_53_2 hcardT83_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK83) (T83_53_2 i) (hfix83_53_2 i) h)

/-! ### Cell (83, 83) twin -/

def T83_83_2 : Fin 25 → Coordinate 2 := fun i => T83_83list.getD i.val (0,0,0,0,0)

theorem hfix83_83_2 : ∀ i, ((T83_83_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK83)
    ∈ fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK83) :=
  repsFix_of_siftB2 rK83 ⟨83, by decide⟩ T83_83_2 (by decide)

theorem hinj83_83_2 : Function.Injective
    (fun i => ((T83_83_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK83)) :=
  repsInj_of_reduceAux2 rK83 T83_83_2 (by decide)

theorem hcardT83_83_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK83)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK83 ⟨83, by decide⟩ R83_2 hpxR83_2 hcardq83_2 (by decide)).symm

/-- **Cell (83, 83) twin (q=2).** -/
theorem cell83_83_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK83) e = true)
    (h : ↥(reps (⟨83, by decide⟩ : Fin 148))) :
    species (reps (⟨83, by decide⟩ : Fin 148)) h (basisElt (reps rK83) (charOfVec2 rK83 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK83 e (h : Coordinate 2) T83_83_2 i :=
  species_entry_eq_sum rK83 ⟨83, by decide⟩ e heK h T83_83_2 hfix83_83_2 hinj83_83_2 hcardT83_83_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨83, by decide⟩) (reps rK83) (T83_83_2 i) (hfix83_83_2 i) h)

end Q2

/-! # K-class rK = 84  (|G/K| = 25) -/

def rK84 : Fin 148 := ⟨84, by decide⟩

def R84list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0)]
def R84 : Fin 25 → Coordinate 1 := fun i => R84list.getD i.val (0,0,0,0,0)

theorem hpxR84 : Function.Injective (fun i => reduceAux 1 (basisAt rK84) (R84 i)) := by decide
theorem hcardq84 : Nat.card (Coordinate 1 ⧸ reps rK84) = 25 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (84, 0): |T| = 25 -/

def T84_0list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0)]
def T84_0 : Fin 25 → Coordinate 1 := fun i => T84_0list.getD i.val (0,0,0,0,0)

theorem hfix84_0 : ∀ i, ((T84_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK84)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84) :=
  repsFix_of_siftB rK84 ⟨0, by decide⟩ T84_0 (by decide)

theorem hinj84_0 : Function.Injective
    (fun i => ((T84_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK84)) :=
  repsInj_of_reduceAux rK84 T84_0 (by decide)

theorem hcardT84_0 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK84 ⟨0, by decide⟩ R84 hpxR84 hcardq84 (by decide)).symm

/-- **Cell (84, 0).** -/
theorem cell84_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK84) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK84) (charOfVec rK84 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK84 e (h : Coordinate 1) T84_0 i :=
  species_entry_eq_sum rK84 ⟨0, by decide⟩ e heK h T84_0 hfix84_0 hinj84_0 hcardT84_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK84) (T84_0 i) (hfix84_0 i) h)

/-! ## Cell (84, 5): |T| = 25 -/

def T84_5list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0)]
def T84_5 : Fin 25 → Coordinate 1 := fun i => T84_5list.getD i.val (0,0,0,0,0)

theorem hfix84_5 : ∀ i, ((T84_5 i : Coordinate 1) : Coordinate 1 ⧸ reps rK84)
    ∈ fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84) :=
  repsFix_of_siftB rK84 ⟨5, by decide⟩ T84_5 (by decide)

theorem hinj84_5 : Function.Injective
    (fun i => ((T84_5 i : Coordinate 1) : Coordinate 1 ⧸ reps rK84)) :=
  repsInj_of_reduceAux rK84 T84_5 (by decide)

theorem hcardT84_5 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK84 ⟨5, by decide⟩ R84 hpxR84 hcardq84 (by decide)).symm

/-- **Cell (84, 5).** -/
theorem cell84_5 (e : List (ZMod 25)) (heK : charOK (basisAt rK84) e = true)
    (h : ↥(reps (⟨5, by decide⟩ : Fin 148))) :
    species (reps (⟨5, by decide⟩ : Fin 148)) h (basisElt (reps rK84) (charOfVec rK84 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK84 e (h : Coordinate 1) T84_5 i :=
  species_entry_eq_sum rK84 ⟨5, by decide⟩ e heK h T84_5 hfix84_5 hinj84_5 hcardT84_5
    (fun i => conj_mem_of_fixedPoints (reps ⟨5, by decide⟩) (reps rK84) (T84_5 i) (hfix84_5 i) h)

/-! ## Cell (84, 10): |T| = 25 -/

def T84_10list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0)]
def T84_10 : Fin 25 → Coordinate 1 := fun i => T84_10list.getD i.val (0,0,0,0,0)

theorem hfix84_10 : ∀ i, ((T84_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK84)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84) :=
  repsFix_of_siftB rK84 ⟨10, by decide⟩ T84_10 (by decide)

theorem hinj84_10 : Function.Injective
    (fun i => ((T84_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK84)) :=
  repsInj_of_reduceAux rK84 T84_10 (by decide)

theorem hcardT84_10 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK84 ⟨10, by decide⟩ R84 hpxR84 hcardq84 (by decide)).symm

/-- **Cell (84, 10).** -/
theorem cell84_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK84) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK84) (charOfVec rK84 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK84 e (h : Coordinate 1) T84_10 i :=
  species_entry_eq_sum rK84 ⟨10, by decide⟩ e heK h T84_10 hfix84_10 hinj84_10 hcardT84_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK84) (T84_10 i) (hfix84_10 i) h)

/-! ## Cell (84, 12): |T| = 25 -/

def T84_12list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0)]
def T84_12 : Fin 25 → Coordinate 1 := fun i => T84_12list.getD i.val (0,0,0,0,0)

theorem hfix84_12 : ∀ i, ((T84_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK84)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84) :=
  repsFix_of_siftB rK84 ⟨12, by decide⟩ T84_12 (by decide)

theorem hinj84_12 : Function.Injective
    (fun i => ((T84_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK84)) :=
  repsInj_of_reduceAux rK84 T84_12 (by decide)

theorem hcardT84_12 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK84 ⟨12, by decide⟩ R84 hpxR84 hcardq84 (by decide)).symm

/-- **Cell (84, 12).** -/
theorem cell84_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK84) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK84) (charOfVec rK84 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK84 e (h : Coordinate 1) T84_12 i :=
  species_entry_eq_sum rK84 ⟨12, by decide⟩ e heK h T84_12 hfix84_12 hinj84_12 hcardT84_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK84) (T84_12 i) (hfix84_12 i) h)

/-! ## Cell (84, 23): |T| = 25 -/

def T84_23list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0)]
def T84_23 : Fin 25 → Coordinate 1 := fun i => T84_23list.getD i.val (0,0,0,0,0)

theorem hfix84_23 : ∀ i, ((T84_23 i : Coordinate 1) : Coordinate 1 ⧸ reps rK84)
    ∈ fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84) :=
  repsFix_of_siftB rK84 ⟨23, by decide⟩ T84_23 (by decide)

theorem hinj84_23 : Function.Injective
    (fun i => ((T84_23 i : Coordinate 1) : Coordinate 1 ⧸ reps rK84)) :=
  repsInj_of_reduceAux rK84 T84_23 (by decide)

theorem hcardT84_23 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK84 ⟨23, by decide⟩ R84 hpxR84 hcardq84 (by decide)).symm

/-- **Cell (84, 23).** -/
theorem cell84_23 (e : List (ZMod 25)) (heK : charOK (basisAt rK84) e = true)
    (h : ↥(reps (⟨23, by decide⟩ : Fin 148))) :
    species (reps (⟨23, by decide⟩ : Fin 148)) h (basisElt (reps rK84) (charOfVec rK84 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK84 e (h : Coordinate 1) T84_23 i :=
  species_entry_eq_sum rK84 ⟨23, by decide⟩ e heK h T84_23 hfix84_23 hinj84_23 hcardT84_23
    (fun i => conj_mem_of_fixedPoints (reps ⟨23, by decide⟩) (reps rK84) (T84_23 i) (hfix84_23 i) h)

/-! ## Cell (84, 53): |T| = 25 -/

def T84_53list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0)]
def T84_53 : Fin 25 → Coordinate 1 := fun i => T84_53list.getD i.val (0,0,0,0,0)

theorem hfix84_53 : ∀ i, ((T84_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK84)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84) :=
  repsFix_of_siftB rK84 ⟨53, by decide⟩ T84_53 (by decide)

theorem hinj84_53 : Function.Injective
    (fun i => ((T84_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK84)) :=
  repsInj_of_reduceAux rK84 T84_53 (by decide)

theorem hcardT84_53 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK84 ⟨53, by decide⟩ R84 hpxR84 hcardq84 (by decide)).symm

/-- **Cell (84, 53).** -/
theorem cell84_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK84) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK84) (charOfVec rK84 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK84 e (h : Coordinate 1) T84_53 i :=
  species_entry_eq_sum rK84 ⟨53, by decide⟩ e heK h T84_53 hfix84_53 hinj84_53 hcardT84_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK84) (T84_53 i) (hfix84_53 i) h)

/-! ## Cell (84, 84): |T| = 25 -/

def T84_84list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,1,1,0,0), (0,1,2,0,0), (0,1,3,0,0), (0,1,4,0,0), (0,1,0,0,0), (0,2,1,0,0), (0,2,2,0,0), (0,2,3,0,0), (0,2,4,0,0), (0,2,0,0,0), (0,3,1,0,0), (0,3,2,0,0), (0,3,3,0,0), (0,3,4,0,0), (0,3,0,0,0), (0,4,1,0,0), (0,4,2,0,0), (0,4,3,0,0), (0,4,4,0,0), (0,4,0,0,0)]
def T84_84 : Fin 25 → Coordinate 1 := fun i => T84_84list.getD i.val (0,0,0,0,0)

theorem hfix84_84 : ∀ i, ((T84_84 i : Coordinate 1) : Coordinate 1 ⧸ reps rK84)
    ∈ fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84) :=
  repsFix_of_siftB rK84 ⟨84, by decide⟩ T84_84 (by decide)

theorem hinj84_84 : Function.Injective
    (fun i => ((T84_84 i : Coordinate 1) : Coordinate 1 ⧸ reps rK84)) :=
  repsInj_of_reduceAux rK84 T84_84 (by decide)

theorem hcardT84_84 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK84 ⟨84, by decide⟩ R84 hpxR84 hcardq84 (by decide)).symm

/-- **Cell (84, 84).** -/
theorem cell84_84 (e : List (ZMod 25)) (heK : charOK (basisAt rK84) e = true)
    (h : ↥(reps (⟨84, by decide⟩ : Fin 148))) :
    species (reps (⟨84, by decide⟩ : Fin 148)) h (basisElt (reps rK84) (charOfVec rK84 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK84 e (h : Coordinate 1) T84_84 i :=
  species_entry_eq_sum rK84 ⟨84, by decide⟩ e heK h T84_84 hfix84_84 hinj84_84 hcardT84_84
    (fun i => conj_mem_of_fixedPoints (reps ⟨84, by decide⟩) (reps rK84) (T84_84 i) (hfix84_84 i) h)

namespace Q2

def R84_2 : Fin 25 → Coordinate 2 := fun i => R84list.getD i.val (0,0,0,0,0)
theorem hpxR84_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK84) (R84_2 i)) := by decide
theorem hcardq84_2 : Nat.card (Coordinate 2 ⧸ reps rK84) = 25 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (84, 0) twin -/

def T84_0_2 : Fin 25 → Coordinate 2 := fun i => T84_0list.getD i.val (0,0,0,0,0)

theorem hfix84_0_2 : ∀ i, ((T84_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK84)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK84) :=
  repsFix_of_siftB2 rK84 ⟨0, by decide⟩ T84_0_2 (by decide)

theorem hinj84_0_2 : Function.Injective
    (fun i => ((T84_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK84)) :=
  repsInj_of_reduceAux2 rK84 T84_0_2 (by decide)

theorem hcardT84_0_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK84)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK84 ⟨0, by decide⟩ R84_2 hpxR84_2 hcardq84_2 (by decide)).symm

/-- **Cell (84, 0) twin (q=2).** -/
theorem cell84_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK84) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK84) (charOfVec2 rK84 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK84 e (h : Coordinate 2) T84_0_2 i :=
  species_entry_eq_sum rK84 ⟨0, by decide⟩ e heK h T84_0_2 hfix84_0_2 hinj84_0_2 hcardT84_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK84) (T84_0_2 i) (hfix84_0_2 i) h)

/-! ### Cell (84, 5) twin -/

def T84_5_2 : Fin 25 → Coordinate 2 := fun i => T84_5list.getD i.val (0,0,0,0,0)

theorem hfix84_5_2 : ∀ i, ((T84_5_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK84)
    ∈ fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK84) :=
  repsFix_of_siftB2 rK84 ⟨5, by decide⟩ T84_5_2 (by decide)

theorem hinj84_5_2 : Function.Injective
    (fun i => ((T84_5_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK84)) :=
  repsInj_of_reduceAux2 rK84 T84_5_2 (by decide)

theorem hcardT84_5_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK84)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK84 ⟨5, by decide⟩ R84_2 hpxR84_2 hcardq84_2 (by decide)).symm

/-- **Cell (84, 5) twin (q=2).** -/
theorem cell84_5_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK84) e = true)
    (h : ↥(reps (⟨5, by decide⟩ : Fin 148))) :
    species (reps (⟨5, by decide⟩ : Fin 148)) h (basisElt (reps rK84) (charOfVec2 rK84 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK84 e (h : Coordinate 2) T84_5_2 i :=
  species_entry_eq_sum rK84 ⟨5, by decide⟩ e heK h T84_5_2 hfix84_5_2 hinj84_5_2 hcardT84_5_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨5, by decide⟩) (reps rK84) (T84_5_2 i) (hfix84_5_2 i) h)

/-! ### Cell (84, 10) twin -/

def T84_10_2 : Fin 25 → Coordinate 2 := fun i => T84_10list.getD i.val (0,0,0,0,0)

theorem hfix84_10_2 : ∀ i, ((T84_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK84)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK84) :=
  repsFix_of_siftB2 rK84 ⟨10, by decide⟩ T84_10_2 (by decide)

theorem hinj84_10_2 : Function.Injective
    (fun i => ((T84_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK84)) :=
  repsInj_of_reduceAux2 rK84 T84_10_2 (by decide)

theorem hcardT84_10_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK84)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK84 ⟨10, by decide⟩ R84_2 hpxR84_2 hcardq84_2 (by decide)).symm

/-- **Cell (84, 10) twin (q=2).** -/
theorem cell84_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK84) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK84) (charOfVec2 rK84 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK84 e (h : Coordinate 2) T84_10_2 i :=
  species_entry_eq_sum rK84 ⟨10, by decide⟩ e heK h T84_10_2 hfix84_10_2 hinj84_10_2 hcardT84_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK84) (T84_10_2 i) (hfix84_10_2 i) h)

/-! ### Cell (84, 12) twin -/

def T84_12_2 : Fin 25 → Coordinate 2 := fun i => T84_12list.getD i.val (0,0,0,0,0)

theorem hfix84_12_2 : ∀ i, ((T84_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK84)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK84) :=
  repsFix_of_siftB2 rK84 ⟨12, by decide⟩ T84_12_2 (by decide)

theorem hinj84_12_2 : Function.Injective
    (fun i => ((T84_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK84)) :=
  repsInj_of_reduceAux2 rK84 T84_12_2 (by decide)

theorem hcardT84_12_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK84)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK84 ⟨12, by decide⟩ R84_2 hpxR84_2 hcardq84_2 (by decide)).symm

/-- **Cell (84, 12) twin (q=2).** -/
theorem cell84_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK84) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK84) (charOfVec2 rK84 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK84 e (h : Coordinate 2) T84_12_2 i :=
  species_entry_eq_sum rK84 ⟨12, by decide⟩ e heK h T84_12_2 hfix84_12_2 hinj84_12_2 hcardT84_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK84) (T84_12_2 i) (hfix84_12_2 i) h)

/-! ### Cell (84, 23) twin -/

def T84_23_2 : Fin 25 → Coordinate 2 := fun i => T84_23list.getD i.val (0,0,0,0,0)

theorem hfix84_23_2 : ∀ i, ((T84_23_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK84)
    ∈ fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK84) :=
  repsFix_of_siftB2 rK84 ⟨23, by decide⟩ T84_23_2 (by decide)

theorem hinj84_23_2 : Function.Injective
    (fun i => ((T84_23_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK84)) :=
  repsInj_of_reduceAux2 rK84 T84_23_2 (by decide)

theorem hcardT84_23_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK84)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK84 ⟨23, by decide⟩ R84_2 hpxR84_2 hcardq84_2 (by decide)).symm

/-- **Cell (84, 23) twin (q=2).** -/
theorem cell84_23_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK84) e = true)
    (h : ↥(reps (⟨23, by decide⟩ : Fin 148))) :
    species (reps (⟨23, by decide⟩ : Fin 148)) h (basisElt (reps rK84) (charOfVec2 rK84 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK84 e (h : Coordinate 2) T84_23_2 i :=
  species_entry_eq_sum rK84 ⟨23, by decide⟩ e heK h T84_23_2 hfix84_23_2 hinj84_23_2 hcardT84_23_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨23, by decide⟩) (reps rK84) (T84_23_2 i) (hfix84_23_2 i) h)

/-! ### Cell (84, 53) twin -/

def T84_53_2 : Fin 25 → Coordinate 2 := fun i => T84_53list.getD i.val (0,0,0,0,0)

theorem hfix84_53_2 : ∀ i, ((T84_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK84)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK84) :=
  repsFix_of_siftB2 rK84 ⟨53, by decide⟩ T84_53_2 (by decide)

theorem hinj84_53_2 : Function.Injective
    (fun i => ((T84_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK84)) :=
  repsInj_of_reduceAux2 rK84 T84_53_2 (by decide)

theorem hcardT84_53_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK84)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK84 ⟨53, by decide⟩ R84_2 hpxR84_2 hcardq84_2 (by decide)).symm

/-- **Cell (84, 53) twin (q=2).** -/
theorem cell84_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK84) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK84) (charOfVec2 rK84 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK84 e (h : Coordinate 2) T84_53_2 i :=
  species_entry_eq_sum rK84 ⟨53, by decide⟩ e heK h T84_53_2 hfix84_53_2 hinj84_53_2 hcardT84_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK84) (T84_53_2 i) (hfix84_53_2 i) h)

/-! ### Cell (84, 84) twin -/

def T84_84_2 : Fin 25 → Coordinate 2 := fun i => T84_84list.getD i.val (0,0,0,0,0)

theorem hfix84_84_2 : ∀ i, ((T84_84_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK84)
    ∈ fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK84) :=
  repsFix_of_siftB2 rK84 ⟨84, by decide⟩ T84_84_2 (by decide)

theorem hinj84_84_2 : Function.Injective
    (fun i => ((T84_84_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK84)) :=
  repsInj_of_reduceAux2 rK84 T84_84_2 (by decide)

theorem hcardT84_84_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK84)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK84 ⟨84, by decide⟩ R84_2 hpxR84_2 hcardq84_2 (by decide)).symm

/-- **Cell (84, 84) twin (q=2).** -/
theorem cell84_84_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK84) e = true)
    (h : ↥(reps (⟨84, by decide⟩ : Fin 148))) :
    species (reps (⟨84, by decide⟩ : Fin 148)) h (basisElt (reps rK84) (charOfVec2 rK84 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK84 e (h : Coordinate 2) T84_84_2 i :=
  species_entry_eq_sum rK84 ⟨84, by decide⟩ e heK h T84_84_2 hfix84_84_2 hinj84_84_2 hcardT84_84_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨84, by decide⟩) (reps rK84) (T84_84_2 i) (hfix84_84_2 i) h)

end Q2

end LeanDring.P5Presentation
