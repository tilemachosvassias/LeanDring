/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, K-strata data (5^4 stratum, rK 119-119): certified per-cell species-entry instantiations, both
twins.

Covers K-classes 119 (order-5^4 K, |R|=5).  For each nonzero `H`-column
(`(G/K)^H ≠ ∅`), the full coset transversal `R119..` and each `H`-fixed
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

/-! # K-class rK = 119  (|G/K| = 5) -/

def rK119 : Fin 148 := ⟨119, by decide⟩

def R119list : List Coordinates := [(0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0)]
def R119 : Fin 5 → Coordinate 1 := fun i => R119list.getD i.val (0,0,0,0,0)

theorem hpxR119 : Function.Injective (fun i => reduceAux 1 (basisAt rK119) (R119 i)) := by decide
theorem hcardq119 : Nat.card (Coordinate 1 ⧸ reps rK119) = 5 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (119, 0): |T| = 5 -/

def T119_0list : List Coordinates := [(0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0)]
def T119_0 : Fin 5 → Coordinate 1 := fun i => T119_0list.getD i.val (0,0,0,0,0)

theorem hfix119_0 : ∀ i, ((T119_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119) :=
  repsFix_of_siftB rK119 ⟨0, by decide⟩ T119_0 (by decide)

theorem hinj119_0 : Function.Injective
    (fun i => ((T119_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)) :=
  repsInj_of_reduceAux rK119 T119_0 (by decide)

theorem hcardT119_0 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK119 ⟨0, by decide⟩ R119 hpxR119 hcardq119 (by decide)).symm

/-- **Cell (119, 0).** -/
theorem cell119_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK119) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK119 e (h : Coordinate 1) T119_0 i :=
  species_entry_eq_sum rK119 ⟨0, by decide⟩ e heK h T119_0 hfix119_0 hinj119_0 hcardT119_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK119) (T119_0 i) (hfix119_0 i) h)

/-! ## Cell (119, 1): |T| = 5 -/

def T119_1list : List Coordinates := [(0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0)]
def T119_1 : Fin 5 → Coordinate 1 := fun i => T119_1list.getD i.val (0,0,0,0,0)

theorem hfix119_1 : ∀ i, ((T119_1 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119) :=
  repsFix_of_siftB rK119 ⟨1, by decide⟩ T119_1 (by decide)

theorem hinj119_1 : Function.Injective
    (fun i => ((T119_1 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)) :=
  repsInj_of_reduceAux rK119 T119_1 (by decide)

theorem hcardT119_1 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK119 ⟨1, by decide⟩ R119 hpxR119 hcardq119 (by decide)).symm

/-- **Cell (119, 1).** -/
theorem cell119_1 (e : List (ZMod 25)) (heK : charOK (basisAt rK119) e = true)
    (h : ↥(reps (⟨1, by decide⟩ : Fin 148))) :
    species (reps (⟨1, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK119 e (h : Coordinate 1) T119_1 i :=
  species_entry_eq_sum rK119 ⟨1, by decide⟩ e heK h T119_1 hfix119_1 hinj119_1 hcardT119_1
    (fun i => conj_mem_of_fixedPoints (reps ⟨1, by decide⟩) (reps rK119) (T119_1 i) (hfix119_1 i) h)

/-! ## Cell (119, 6): |T| = 5 -/

def T119_6list : List Coordinates := [(0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0)]
def T119_6 : Fin 5 → Coordinate 1 := fun i => T119_6list.getD i.val (0,0,0,0,0)

theorem hfix119_6 : ∀ i, ((T119_6 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119) :=
  repsFix_of_siftB rK119 ⟨6, by decide⟩ T119_6 (by decide)

theorem hinj119_6 : Function.Injective
    (fun i => ((T119_6 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)) :=
  repsInj_of_reduceAux rK119 T119_6 (by decide)

theorem hcardT119_6 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK119 ⟨6, by decide⟩ R119 hpxR119 hcardq119 (by decide)).symm

/-- **Cell (119, 6).** -/
theorem cell119_6 (e : List (ZMod 25)) (heK : charOK (basisAt rK119) e = true)
    (h : ↥(reps (⟨6, by decide⟩ : Fin 148))) :
    species (reps (⟨6, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK119 e (h : Coordinate 1) T119_6 i :=
  species_entry_eq_sum rK119 ⟨6, by decide⟩ e heK h T119_6 hfix119_6 hinj119_6 hcardT119_6
    (fun i => conj_mem_of_fixedPoints (reps ⟨6, by decide⟩) (reps rK119) (T119_6 i) (hfix119_6 i) h)

/-! ## Cell (119, 7): |T| = 5 -/

def T119_7list : List Coordinates := [(0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0)]
def T119_7 : Fin 5 → Coordinate 1 := fun i => T119_7list.getD i.val (0,0,0,0,0)

theorem hfix119_7 : ∀ i, ((T119_7 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119) :=
  repsFix_of_siftB rK119 ⟨7, by decide⟩ T119_7 (by decide)

theorem hinj119_7 : Function.Injective
    (fun i => ((T119_7 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)) :=
  repsInj_of_reduceAux rK119 T119_7 (by decide)

theorem hcardT119_7 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK119 ⟨7, by decide⟩ R119 hpxR119 hcardq119 (by decide)).symm

/-- **Cell (119, 7).** -/
theorem cell119_7 (e : List (ZMod 25)) (heK : charOK (basisAt rK119) e = true)
    (h : ↥(reps (⟨7, by decide⟩ : Fin 148))) :
    species (reps (⟨7, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK119 e (h : Coordinate 1) T119_7 i :=
  species_entry_eq_sum rK119 ⟨7, by decide⟩ e heK h T119_7 hfix119_7 hinj119_7 hcardT119_7
    (fun i => conj_mem_of_fixedPoints (reps ⟨7, by decide⟩) (reps rK119) (T119_7 i) (hfix119_7 i) h)

/-! ## Cell (119, 8): |T| = 5 -/

def T119_8list : List Coordinates := [(0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0)]
def T119_8 : Fin 5 → Coordinate 1 := fun i => T119_8list.getD i.val (0,0,0,0,0)

theorem hfix119_8 : ∀ i, ((T119_8 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119) :=
  repsFix_of_siftB rK119 ⟨8, by decide⟩ T119_8 (by decide)

theorem hinj119_8 : Function.Injective
    (fun i => ((T119_8 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)) :=
  repsInj_of_reduceAux rK119 T119_8 (by decide)

theorem hcardT119_8 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK119 ⟨8, by decide⟩ R119 hpxR119 hcardq119 (by decide)).symm

/-- **Cell (119, 8).** -/
theorem cell119_8 (e : List (ZMod 25)) (heK : charOK (basisAt rK119) e = true)
    (h : ↥(reps (⟨8, by decide⟩ : Fin 148))) :
    species (reps (⟨8, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK119 e (h : Coordinate 1) T119_8 i :=
  species_entry_eq_sum rK119 ⟨8, by decide⟩ e heK h T119_8 hfix119_8 hinj119_8 hcardT119_8
    (fun i => conj_mem_of_fixedPoints (reps ⟨8, by decide⟩) (reps rK119) (T119_8 i) (hfix119_8 i) h)

/-! ## Cell (119, 9): |T| = 5 -/

def T119_9list : List Coordinates := [(0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0)]
def T119_9 : Fin 5 → Coordinate 1 := fun i => T119_9list.getD i.val (0,0,0,0,0)

theorem hfix119_9 : ∀ i, ((T119_9 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119) :=
  repsFix_of_siftB rK119 ⟨9, by decide⟩ T119_9 (by decide)

theorem hinj119_9 : Function.Injective
    (fun i => ((T119_9 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)) :=
  repsInj_of_reduceAux rK119 T119_9 (by decide)

theorem hcardT119_9 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK119 ⟨9, by decide⟩ R119 hpxR119 hcardq119 (by decide)).symm

/-- **Cell (119, 9).** -/
theorem cell119_9 (e : List (ZMod 25)) (heK : charOK (basisAt rK119) e = true)
    (h : ↥(reps (⟨9, by decide⟩ : Fin 148))) :
    species (reps (⟨9, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK119 e (h : Coordinate 1) T119_9 i :=
  species_entry_eq_sum rK119 ⟨9, by decide⟩ e heK h T119_9 hfix119_9 hinj119_9 hcardT119_9
    (fun i => conj_mem_of_fixedPoints (reps ⟨9, by decide⟩) (reps rK119) (T119_9 i) (hfix119_9 i) h)

/-! ## Cell (119, 10): |T| = 5 -/

def T119_10list : List Coordinates := [(0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0)]
def T119_10 : Fin 5 → Coordinate 1 := fun i => T119_10list.getD i.val (0,0,0,0,0)

theorem hfix119_10 : ∀ i, ((T119_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119) :=
  repsFix_of_siftB rK119 ⟨10, by decide⟩ T119_10 (by decide)

theorem hinj119_10 : Function.Injective
    (fun i => ((T119_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)) :=
  repsInj_of_reduceAux rK119 T119_10 (by decide)

theorem hcardT119_10 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK119 ⟨10, by decide⟩ R119 hpxR119 hcardq119 (by decide)).symm

/-- **Cell (119, 10).** -/
theorem cell119_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK119) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK119 e (h : Coordinate 1) T119_10 i :=
  species_entry_eq_sum rK119 ⟨10, by decide⟩ e heK h T119_10 hfix119_10 hinj119_10 hcardT119_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK119) (T119_10 i) (hfix119_10 i) h)

/-! ## Cell (119, 12): |T| = 5 -/

def T119_12list : List Coordinates := [(0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0)]
def T119_12 : Fin 5 → Coordinate 1 := fun i => T119_12list.getD i.val (0,0,0,0,0)

theorem hfix119_12 : ∀ i, ((T119_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119) :=
  repsFix_of_siftB rK119 ⟨12, by decide⟩ T119_12 (by decide)

theorem hinj119_12 : Function.Injective
    (fun i => ((T119_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)) :=
  repsInj_of_reduceAux rK119 T119_12 (by decide)

theorem hcardT119_12 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK119 ⟨12, by decide⟩ R119 hpxR119 hcardq119 (by decide)).symm

/-- **Cell (119, 12).** -/
theorem cell119_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK119) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK119 e (h : Coordinate 1) T119_12 i :=
  species_entry_eq_sum rK119 ⟨12, by decide⟩ e heK h T119_12 hfix119_12 hinj119_12 hcardT119_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK119) (T119_12 i) (hfix119_12 i) h)

/-! ## Cell (119, 13): |T| = 5 -/

def T119_13list : List Coordinates := [(0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0)]
def T119_13 : Fin 5 → Coordinate 1 := fun i => T119_13list.getD i.val (0,0,0,0,0)

theorem hfix119_13 : ∀ i, ((T119_13 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119) :=
  repsFix_of_siftB rK119 ⟨13, by decide⟩ T119_13 (by decide)

theorem hinj119_13 : Function.Injective
    (fun i => ((T119_13 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)) :=
  repsInj_of_reduceAux rK119 T119_13 (by decide)

theorem hcardT119_13 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK119 ⟨13, by decide⟩ R119 hpxR119 hcardq119 (by decide)).symm

/-- **Cell (119, 13).** -/
theorem cell119_13 (e : List (ZMod 25)) (heK : charOK (basisAt rK119) e = true)
    (h : ↥(reps (⟨13, by decide⟩ : Fin 148))) :
    species (reps (⟨13, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK119 e (h : Coordinate 1) T119_13 i :=
  species_entry_eq_sum rK119 ⟨13, by decide⟩ e heK h T119_13 hfix119_13 hinj119_13 hcardT119_13
    (fun i => conj_mem_of_fixedPoints (reps ⟨13, by decide⟩) (reps rK119) (T119_13 i) (hfix119_13 i) h)

/-! ## Cell (119, 19): |T| = 5 -/

def T119_19list : List Coordinates := [(0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0)]
def T119_19 : Fin 5 → Coordinate 1 := fun i => T119_19list.getD i.val (0,0,0,0,0)

theorem hfix119_19 : ∀ i, ((T119_19 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119) :=
  repsFix_of_siftB rK119 ⟨19, by decide⟩ T119_19 (by decide)

theorem hinj119_19 : Function.Injective
    (fun i => ((T119_19 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)) :=
  repsInj_of_reduceAux rK119 T119_19 (by decide)

theorem hcardT119_19 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK119 ⟨19, by decide⟩ R119 hpxR119 hcardq119 (by decide)).symm

/-- **Cell (119, 19).** -/
theorem cell119_19 (e : List (ZMod 25)) (heK : charOK (basisAt rK119) e = true)
    (h : ↥(reps (⟨19, by decide⟩ : Fin 148))) :
    species (reps (⟨19, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK119 e (h : Coordinate 1) T119_19 i :=
  species_entry_eq_sum rK119 ⟨19, by decide⟩ e heK h T119_19 hfix119_19 hinj119_19 hcardT119_19
    (fun i => conj_mem_of_fixedPoints (reps ⟨19, by decide⟩) (reps rK119) (T119_19 i) (hfix119_19 i) h)

/-! ## Cell (119, 24): |T| = 5 -/

def T119_24list : List Coordinates := [(0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0)]
def T119_24 : Fin 5 → Coordinate 1 := fun i => T119_24list.getD i.val (0,0,0,0,0)

theorem hfix119_24 : ∀ i, ((T119_24 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119) :=
  repsFix_of_siftB rK119 ⟨24, by decide⟩ T119_24 (by decide)

theorem hinj119_24 : Function.Injective
    (fun i => ((T119_24 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)) :=
  repsInj_of_reduceAux rK119 T119_24 (by decide)

theorem hcardT119_24 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK119 ⟨24, by decide⟩ R119 hpxR119 hcardq119 (by decide)).symm

/-- **Cell (119, 24).** -/
theorem cell119_24 (e : List (ZMod 25)) (heK : charOK (basisAt rK119) e = true)
    (h : ↥(reps (⟨24, by decide⟩ : Fin 148))) :
    species (reps (⟨24, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK119 e (h : Coordinate 1) T119_24 i :=
  species_entry_eq_sum rK119 ⟨24, by decide⟩ e heK h T119_24 hfix119_24 hinj119_24 hcardT119_24
    (fun i => conj_mem_of_fixedPoints (reps ⟨24, by decide⟩) (reps rK119) (T119_24 i) (hfix119_24 i) h)

/-! ## Cell (119, 25): |T| = 5 -/

def T119_25list : List Coordinates := [(0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0)]
def T119_25 : Fin 5 → Coordinate 1 := fun i => T119_25list.getD i.val (0,0,0,0,0)

theorem hfix119_25 : ∀ i, ((T119_25 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119) :=
  repsFix_of_siftB rK119 ⟨25, by decide⟩ T119_25 (by decide)

theorem hinj119_25 : Function.Injective
    (fun i => ((T119_25 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)) :=
  repsInj_of_reduceAux rK119 T119_25 (by decide)

theorem hcardT119_25 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK119 ⟨25, by decide⟩ R119 hpxR119 hcardq119 (by decide)).symm

/-- **Cell (119, 25).** -/
theorem cell119_25 (e : List (ZMod 25)) (heK : charOK (basisAt rK119) e = true)
    (h : ↥(reps (⟨25, by decide⟩ : Fin 148))) :
    species (reps (⟨25, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK119 e (h : Coordinate 1) T119_25 i :=
  species_entry_eq_sum rK119 ⟨25, by decide⟩ e heK h T119_25 hfix119_25 hinj119_25 hcardT119_25
    (fun i => conj_mem_of_fixedPoints (reps ⟨25, by decide⟩) (reps rK119) (T119_25 i) (hfix119_25 i) h)

/-! ## Cell (119, 26): |T| = 5 -/

def T119_26list : List Coordinates := [(0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0)]
def T119_26 : Fin 5 → Coordinate 1 := fun i => T119_26list.getD i.val (0,0,0,0,0)

theorem hfix119_26 : ∀ i, ((T119_26 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119) :=
  repsFix_of_siftB rK119 ⟨26, by decide⟩ T119_26 (by decide)

theorem hinj119_26 : Function.Injective
    (fun i => ((T119_26 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)) :=
  repsInj_of_reduceAux rK119 T119_26 (by decide)

theorem hcardT119_26 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK119 ⟨26, by decide⟩ R119 hpxR119 hcardq119 (by decide)).symm

/-- **Cell (119, 26).** -/
theorem cell119_26 (e : List (ZMod 25)) (heK : charOK (basisAt rK119) e = true)
    (h : ↥(reps (⟨26, by decide⟩ : Fin 148))) :
    species (reps (⟨26, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK119 e (h : Coordinate 1) T119_26 i :=
  species_entry_eq_sum rK119 ⟨26, by decide⟩ e heK h T119_26 hfix119_26 hinj119_26 hcardT119_26
    (fun i => conj_mem_of_fixedPoints (reps ⟨26, by decide⟩) (reps rK119) (T119_26 i) (hfix119_26 i) h)

/-! ## Cell (119, 27): |T| = 5 -/

def T119_27list : List Coordinates := [(0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0)]
def T119_27 : Fin 5 → Coordinate 1 := fun i => T119_27list.getD i.val (0,0,0,0,0)

theorem hfix119_27 : ∀ i, ((T119_27 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119) :=
  repsFix_of_siftB rK119 ⟨27, by decide⟩ T119_27 (by decide)

theorem hinj119_27 : Function.Injective
    (fun i => ((T119_27 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)) :=
  repsInj_of_reduceAux rK119 T119_27 (by decide)

theorem hcardT119_27 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK119 ⟨27, by decide⟩ R119 hpxR119 hcardq119 (by decide)).symm

/-- **Cell (119, 27).** -/
theorem cell119_27 (e : List (ZMod 25)) (heK : charOK (basisAt rK119) e = true)
    (h : ↥(reps (⟨27, by decide⟩ : Fin 148))) :
    species (reps (⟨27, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK119 e (h : Coordinate 1) T119_27 i :=
  species_entry_eq_sum rK119 ⟨27, by decide⟩ e heK h T119_27 hfix119_27 hinj119_27 hcardT119_27
    (fun i => conj_mem_of_fixedPoints (reps ⟨27, by decide⟩) (reps rK119) (T119_27 i) (hfix119_27 i) h)

/-! ## Cell (119, 31): |T| = 5 -/

def T119_31list : List Coordinates := [(0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0)]
def T119_31 : Fin 5 → Coordinate 1 := fun i => T119_31list.getD i.val (0,0,0,0,0)

theorem hfix119_31 : ∀ i, ((T119_31 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119) :=
  repsFix_of_siftB rK119 ⟨31, by decide⟩ T119_31 (by decide)

theorem hinj119_31 : Function.Injective
    (fun i => ((T119_31 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)) :=
  repsInj_of_reduceAux rK119 T119_31 (by decide)

theorem hcardT119_31 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK119 ⟨31, by decide⟩ R119 hpxR119 hcardq119 (by decide)).symm

/-- **Cell (119, 31).** -/
theorem cell119_31 (e : List (ZMod 25)) (heK : charOK (basisAt rK119) e = true)
    (h : ↥(reps (⟨31, by decide⟩ : Fin 148))) :
    species (reps (⟨31, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK119 e (h : Coordinate 1) T119_31 i :=
  species_entry_eq_sum rK119 ⟨31, by decide⟩ e heK h T119_31 hfix119_31 hinj119_31 hcardT119_31
    (fun i => conj_mem_of_fixedPoints (reps ⟨31, by decide⟩) (reps rK119) (T119_31 i) (hfix119_31 i) h)

/-! ## Cell (119, 36): |T| = 5 -/

def T119_36list : List Coordinates := [(0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0)]
def T119_36 : Fin 5 → Coordinate 1 := fun i => T119_36list.getD i.val (0,0,0,0,0)

theorem hfix119_36 : ∀ i, ((T119_36 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119) :=
  repsFix_of_siftB rK119 ⟨36, by decide⟩ T119_36 (by decide)

theorem hinj119_36 : Function.Injective
    (fun i => ((T119_36 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)) :=
  repsInj_of_reduceAux rK119 T119_36 (by decide)

theorem hcardT119_36 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK119 ⟨36, by decide⟩ R119 hpxR119 hcardq119 (by decide)).symm

/-- **Cell (119, 36).** -/
theorem cell119_36 (e : List (ZMod 25)) (heK : charOK (basisAt rK119) e = true)
    (h : ↥(reps (⟨36, by decide⟩ : Fin 148))) :
    species (reps (⟨36, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK119 e (h : Coordinate 1) T119_36 i :=
  species_entry_eq_sum rK119 ⟨36, by decide⟩ e heK h T119_36 hfix119_36 hinj119_36 hcardT119_36
    (fun i => conj_mem_of_fixedPoints (reps ⟨36, by decide⟩) (reps rK119) (T119_36 i) (hfix119_36 i) h)

/-! ## Cell (119, 41): |T| = 5 -/

def T119_41list : List Coordinates := [(0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0)]
def T119_41 : Fin 5 → Coordinate 1 := fun i => T119_41list.getD i.val (0,0,0,0,0)

theorem hfix119_41 : ∀ i, ((T119_41 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119) :=
  repsFix_of_siftB rK119 ⟨41, by decide⟩ T119_41 (by decide)

theorem hinj119_41 : Function.Injective
    (fun i => ((T119_41 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)) :=
  repsInj_of_reduceAux rK119 T119_41 (by decide)

theorem hcardT119_41 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK119 ⟨41, by decide⟩ R119 hpxR119 hcardq119 (by decide)).symm

/-- **Cell (119, 41).** -/
theorem cell119_41 (e : List (ZMod 25)) (heK : charOK (basisAt rK119) e = true)
    (h : ↥(reps (⟨41, by decide⟩ : Fin 148))) :
    species (reps (⟨41, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK119 e (h : Coordinate 1) T119_41 i :=
  species_entry_eq_sum rK119 ⟨41, by decide⟩ e heK h T119_41 hfix119_41 hinj119_41 hcardT119_41
    (fun i => conj_mem_of_fixedPoints (reps ⟨41, by decide⟩) (reps rK119) (T119_41 i) (hfix119_41 i) h)

/-! ## Cell (119, 46): |T| = 5 -/

def T119_46list : List Coordinates := [(0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0)]
def T119_46 : Fin 5 → Coordinate 1 := fun i => T119_46list.getD i.val (0,0,0,0,0)

theorem hfix119_46 : ∀ i, ((T119_46 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119) :=
  repsFix_of_siftB rK119 ⟨46, by decide⟩ T119_46 (by decide)

theorem hinj119_46 : Function.Injective
    (fun i => ((T119_46 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)) :=
  repsInj_of_reduceAux rK119 T119_46 (by decide)

theorem hcardT119_46 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK119 ⟨46, by decide⟩ R119 hpxR119 hcardq119 (by decide)).symm

/-- **Cell (119, 46).** -/
theorem cell119_46 (e : List (ZMod 25)) (heK : charOK (basisAt rK119) e = true)
    (h : ↥(reps (⟨46, by decide⟩ : Fin 148))) :
    species (reps (⟨46, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK119 e (h : Coordinate 1) T119_46 i :=
  species_entry_eq_sum rK119 ⟨46, by decide⟩ e heK h T119_46 hfix119_46 hinj119_46 hcardT119_46
    (fun i => conj_mem_of_fixedPoints (reps ⟨46, by decide⟩) (reps rK119) (T119_46 i) (hfix119_46 i) h)

/-! ## Cell (119, 51): |T| = 5 -/

def T119_51list : List Coordinates := [(0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0)]
def T119_51 : Fin 5 → Coordinate 1 := fun i => T119_51list.getD i.val (0,0,0,0,0)

theorem hfix119_51 : ∀ i, ((T119_51 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119) :=
  repsFix_of_siftB rK119 ⟨51, by decide⟩ T119_51 (by decide)

theorem hinj119_51 : Function.Injective
    (fun i => ((T119_51 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)) :=
  repsInj_of_reduceAux rK119 T119_51 (by decide)

theorem hcardT119_51 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK119 ⟨51, by decide⟩ R119 hpxR119 hcardq119 (by decide)).symm

/-- **Cell (119, 51).** -/
theorem cell119_51 (e : List (ZMod 25)) (heK : charOK (basisAt rK119) e = true)
    (h : ↥(reps (⟨51, by decide⟩ : Fin 148))) :
    species (reps (⟨51, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK119 e (h : Coordinate 1) T119_51 i :=
  species_entry_eq_sum rK119 ⟨51, by decide⟩ e heK h T119_51 hfix119_51 hinj119_51 hcardT119_51
    (fun i => conj_mem_of_fixedPoints (reps ⟨51, by decide⟩) (reps rK119) (T119_51 i) (hfix119_51 i) h)

/-! ## Cell (119, 53): |T| = 5 -/

def T119_53list : List Coordinates := [(0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0)]
def T119_53 : Fin 5 → Coordinate 1 := fun i => T119_53list.getD i.val (0,0,0,0,0)

theorem hfix119_53 : ∀ i, ((T119_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119) :=
  repsFix_of_siftB rK119 ⟨53, by decide⟩ T119_53 (by decide)

theorem hinj119_53 : Function.Injective
    (fun i => ((T119_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)) :=
  repsInj_of_reduceAux rK119 T119_53 (by decide)

theorem hcardT119_53 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK119 ⟨53, by decide⟩ R119 hpxR119 hcardq119 (by decide)).symm

/-- **Cell (119, 53).** -/
theorem cell119_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK119) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK119 e (h : Coordinate 1) T119_53 i :=
  species_entry_eq_sum rK119 ⟨53, by decide⟩ e heK h T119_53 hfix119_53 hinj119_53 hcardT119_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK119) (T119_53 i) (hfix119_53 i) h)

/-! ## Cell (119, 70): |T| = 5 -/

def T119_70list : List Coordinates := [(0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0)]
def T119_70 : Fin 5 → Coordinate 1 := fun i => T119_70list.getD i.val (0,0,0,0,0)

theorem hfix119_70 : ∀ i, ((T119_70 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119) :=
  repsFix_of_siftB rK119 ⟨70, by decide⟩ T119_70 (by decide)

theorem hinj119_70 : Function.Injective
    (fun i => ((T119_70 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)) :=
  repsInj_of_reduceAux rK119 T119_70 (by decide)

theorem hcardT119_70 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK119 ⟨70, by decide⟩ R119 hpxR119 hcardq119 (by decide)).symm

/-- **Cell (119, 70).** -/
theorem cell119_70 (e : List (ZMod 25)) (heK : charOK (basisAt rK119) e = true)
    (h : ↥(reps (⟨70, by decide⟩ : Fin 148))) :
    species (reps (⟨70, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK119 e (h : Coordinate 1) T119_70 i :=
  species_entry_eq_sum rK119 ⟨70, by decide⟩ e heK h T119_70 hfix119_70 hinj119_70 hcardT119_70
    (fun i => conj_mem_of_fixedPoints (reps ⟨70, by decide⟩) (reps rK119) (T119_70 i) (hfix119_70 i) h)

/-! ## Cell (119, 71): |T| = 5 -/

def T119_71list : List Coordinates := [(0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0)]
def T119_71 : Fin 5 → Coordinate 1 := fun i => T119_71list.getD i.val (0,0,0,0,0)

theorem hfix119_71 : ∀ i, ((T119_71 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119) :=
  repsFix_of_siftB rK119 ⟨71, by decide⟩ T119_71 (by decide)

theorem hinj119_71 : Function.Injective
    (fun i => ((T119_71 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)) :=
  repsInj_of_reduceAux rK119 T119_71 (by decide)

theorem hcardT119_71 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK119 ⟨71, by decide⟩ R119 hpxR119 hcardq119 (by decide)).symm

/-- **Cell (119, 71).** -/
theorem cell119_71 (e : List (ZMod 25)) (heK : charOK (basisAt rK119) e = true)
    (h : ↥(reps (⟨71, by decide⟩ : Fin 148))) :
    species (reps (⟨71, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK119 e (h : Coordinate 1) T119_71 i :=
  species_entry_eq_sum rK119 ⟨71, by decide⟩ e heK h T119_71 hfix119_71 hinj119_71 hcardT119_71
    (fun i => conj_mem_of_fixedPoints (reps ⟨71, by decide⟩) (reps rK119) (T119_71 i) (hfix119_71 i) h)

/-! ## Cell (119, 72): |T| = 5 -/

def T119_72list : List Coordinates := [(0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0)]
def T119_72 : Fin 5 → Coordinate 1 := fun i => T119_72list.getD i.val (0,0,0,0,0)

theorem hfix119_72 : ∀ i, ((T119_72 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119) :=
  repsFix_of_siftB rK119 ⟨72, by decide⟩ T119_72 (by decide)

theorem hinj119_72 : Function.Injective
    (fun i => ((T119_72 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)) :=
  repsInj_of_reduceAux rK119 T119_72 (by decide)

theorem hcardT119_72 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK119 ⟨72, by decide⟩ R119 hpxR119 hcardq119 (by decide)).symm

/-- **Cell (119, 72).** -/
theorem cell119_72 (e : List (ZMod 25)) (heK : charOK (basisAt rK119) e = true)
    (h : ↥(reps (⟨72, by decide⟩ : Fin 148))) :
    species (reps (⟨72, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK119 e (h : Coordinate 1) T119_72 i :=
  species_entry_eq_sum rK119 ⟨72, by decide⟩ e heK h T119_72 hfix119_72 hinj119_72 hcardT119_72
    (fun i => conj_mem_of_fixedPoints (reps ⟨72, by decide⟩) (reps rK119) (T119_72 i) (hfix119_72 i) h)

/-! ## Cell (119, 73): |T| = 5 -/

def T119_73list : List Coordinates := [(0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0)]
def T119_73 : Fin 5 → Coordinate 1 := fun i => T119_73list.getD i.val (0,0,0,0,0)

theorem hfix119_73 : ∀ i, ((T119_73 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119) :=
  repsFix_of_siftB rK119 ⟨73, by decide⟩ T119_73 (by decide)

theorem hinj119_73 : Function.Injective
    (fun i => ((T119_73 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)) :=
  repsInj_of_reduceAux rK119 T119_73 (by decide)

theorem hcardT119_73 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK119 ⟨73, by decide⟩ R119 hpxR119 hcardq119 (by decide)).symm

/-- **Cell (119, 73).** -/
theorem cell119_73 (e : List (ZMod 25)) (heK : charOK (basisAt rK119) e = true)
    (h : ↥(reps (⟨73, by decide⟩ : Fin 148))) :
    species (reps (⟨73, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK119 e (h : Coordinate 1) T119_73 i :=
  species_entry_eq_sum rK119 ⟨73, by decide⟩ e heK h T119_73 hfix119_73 hinj119_73 hcardT119_73
    (fun i => conj_mem_of_fixedPoints (reps ⟨73, by decide⟩) (reps rK119) (T119_73 i) (hfix119_73 i) h)

/-! ## Cell (119, 74): |T| = 5 -/

def T119_74list : List Coordinates := [(0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0)]
def T119_74 : Fin 5 → Coordinate 1 := fun i => T119_74list.getD i.val (0,0,0,0,0)

theorem hfix119_74 : ∀ i, ((T119_74 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119) :=
  repsFix_of_siftB rK119 ⟨74, by decide⟩ T119_74 (by decide)

theorem hinj119_74 : Function.Injective
    (fun i => ((T119_74 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)) :=
  repsInj_of_reduceAux rK119 T119_74 (by decide)

theorem hcardT119_74 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK119 ⟨74, by decide⟩ R119 hpxR119 hcardq119 (by decide)).symm

/-- **Cell (119, 74).** -/
theorem cell119_74 (e : List (ZMod 25)) (heK : charOK (basisAt rK119) e = true)
    (h : ↥(reps (⟨74, by decide⟩ : Fin 148))) :
    species (reps (⟨74, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK119 e (h : Coordinate 1) T119_74 i :=
  species_entry_eq_sum rK119 ⟨74, by decide⟩ e heK h T119_74 hfix119_74 hinj119_74 hcardT119_74
    (fun i => conj_mem_of_fixedPoints (reps ⟨74, by decide⟩) (reps rK119) (T119_74 i) (hfix119_74 i) h)

/-! ## Cell (119, 80): |T| = 5 -/

def T119_80list : List Coordinates := [(0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0)]
def T119_80 : Fin 5 → Coordinate 1 := fun i => T119_80list.getD i.val (0,0,0,0,0)

theorem hfix119_80 : ∀ i, ((T119_80 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119) :=
  repsFix_of_siftB rK119 ⟨80, by decide⟩ T119_80 (by decide)

theorem hinj119_80 : Function.Injective
    (fun i => ((T119_80 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)) :=
  repsInj_of_reduceAux rK119 T119_80 (by decide)

theorem hcardT119_80 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK119 ⟨80, by decide⟩ R119 hpxR119 hcardq119 (by decide)).symm

/-- **Cell (119, 80).** -/
theorem cell119_80 (e : List (ZMod 25)) (heK : charOK (basisAt rK119) e = true)
    (h : ↥(reps (⟨80, by decide⟩ : Fin 148))) :
    species (reps (⟨80, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK119 e (h : Coordinate 1) T119_80 i :=
  species_entry_eq_sum rK119 ⟨80, by decide⟩ e heK h T119_80 hfix119_80 hinj119_80 hcardT119_80
    (fun i => conj_mem_of_fixedPoints (reps ⟨80, by decide⟩) (reps rK119) (T119_80 i) (hfix119_80 i) h)

/-! ## Cell (119, 93): |T| = 5 -/

def T119_93list : List Coordinates := [(0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0)]
def T119_93 : Fin 5 → Coordinate 1 := fun i => T119_93list.getD i.val (0,0,0,0,0)

theorem hfix119_93 : ∀ i, ((T119_93 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119) :=
  repsFix_of_siftB rK119 ⟨93, by decide⟩ T119_93 (by decide)

theorem hinj119_93 : Function.Injective
    (fun i => ((T119_93 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)) :=
  repsInj_of_reduceAux rK119 T119_93 (by decide)

theorem hcardT119_93 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK119 ⟨93, by decide⟩ R119 hpxR119 hcardq119 (by decide)).symm

/-- **Cell (119, 93).** -/
theorem cell119_93 (e : List (ZMod 25)) (heK : charOK (basisAt rK119) e = true)
    (h : ↥(reps (⟨93, by decide⟩ : Fin 148))) :
    species (reps (⟨93, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK119 e (h : Coordinate 1) T119_93 i :=
  species_entry_eq_sum rK119 ⟨93, by decide⟩ e heK h T119_93 hfix119_93 hinj119_93 hcardT119_93
    (fun i => conj_mem_of_fixedPoints (reps ⟨93, by decide⟩) (reps rK119) (T119_93 i) (hfix119_93 i) h)

/-! ## Cell (119, 98): |T| = 5 -/

def T119_98list : List Coordinates := [(0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0)]
def T119_98 : Fin 5 → Coordinate 1 := fun i => T119_98list.getD i.val (0,0,0,0,0)

theorem hfix119_98 : ∀ i, ((T119_98 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119) :=
  repsFix_of_siftB rK119 ⟨98, by decide⟩ T119_98 (by decide)

theorem hinj119_98 : Function.Injective
    (fun i => ((T119_98 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)) :=
  repsInj_of_reduceAux rK119 T119_98 (by decide)

theorem hcardT119_98 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK119 ⟨98, by decide⟩ R119 hpxR119 hcardq119 (by decide)).symm

/-- **Cell (119, 98).** -/
theorem cell119_98 (e : List (ZMod 25)) (heK : charOK (basisAt rK119) e = true)
    (h : ↥(reps (⟨98, by decide⟩ : Fin 148))) :
    species (reps (⟨98, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK119 e (h : Coordinate 1) T119_98 i :=
  species_entry_eq_sum rK119 ⟨98, by decide⟩ e heK h T119_98 hfix119_98 hinj119_98 hcardT119_98
    (fun i => conj_mem_of_fixedPoints (reps ⟨98, by decide⟩) (reps rK119) (T119_98 i) (hfix119_98 i) h)

/-! ## Cell (119, 103): |T| = 5 -/

def T119_103list : List Coordinates := [(0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0)]
def T119_103 : Fin 5 → Coordinate 1 := fun i => T119_103list.getD i.val (0,0,0,0,0)

theorem hfix119_103 : ∀ i, ((T119_103 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119) :=
  repsFix_of_siftB rK119 ⟨103, by decide⟩ T119_103 (by decide)

theorem hinj119_103 : Function.Injective
    (fun i => ((T119_103 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)) :=
  repsInj_of_reduceAux rK119 T119_103 (by decide)

theorem hcardT119_103 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK119 ⟨103, by decide⟩ R119 hpxR119 hcardq119 (by decide)).symm

/-- **Cell (119, 103).** -/
theorem cell119_103 (e : List (ZMod 25)) (heK : charOK (basisAt rK119) e = true)
    (h : ↥(reps (⟨103, by decide⟩ : Fin 148))) :
    species (reps (⟨103, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK119 e (h : Coordinate 1) T119_103 i :=
  species_entry_eq_sum rK119 ⟨103, by decide⟩ e heK h T119_103 hfix119_103 hinj119_103 hcardT119_103
    (fun i => conj_mem_of_fixedPoints (reps ⟨103, by decide⟩) (reps rK119) (T119_103 i) (hfix119_103 i) h)

/-! ## Cell (119, 108): |T| = 5 -/

def T119_108list : List Coordinates := [(0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0)]
def T119_108 : Fin 5 → Coordinate 1 := fun i => T119_108list.getD i.val (0,0,0,0,0)

theorem hfix119_108 : ∀ i, ((T119_108 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119) :=
  repsFix_of_siftB rK119 ⟨108, by decide⟩ T119_108 (by decide)

theorem hinj119_108 : Function.Injective
    (fun i => ((T119_108 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)) :=
  repsInj_of_reduceAux rK119 T119_108 (by decide)

theorem hcardT119_108 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK119 ⟨108, by decide⟩ R119 hpxR119 hcardq119 (by decide)).symm

/-- **Cell (119, 108).** -/
theorem cell119_108 (e : List (ZMod 25)) (heK : charOK (basisAt rK119) e = true)
    (h : ↥(reps (⟨108, by decide⟩ : Fin 148))) :
    species (reps (⟨108, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK119 e (h : Coordinate 1) T119_108 i :=
  species_entry_eq_sum rK119 ⟨108, by decide⟩ e heK h T119_108 hfix119_108 hinj119_108 hcardT119_108
    (fun i => conj_mem_of_fixedPoints (reps ⟨108, by decide⟩) (reps rK119) (T119_108 i) (hfix119_108 i) h)

/-! ## Cell (119, 113): |T| = 5 -/

def T119_113list : List Coordinates := [(0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0)]
def T119_113 : Fin 5 → Coordinate 1 := fun i => T119_113list.getD i.val (0,0,0,0,0)

theorem hfix119_113 : ∀ i, ((T119_113 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119) :=
  repsFix_of_siftB rK119 ⟨113, by decide⟩ T119_113 (by decide)

theorem hinj119_113 : Function.Injective
    (fun i => ((T119_113 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)) :=
  repsInj_of_reduceAux rK119 T119_113 (by decide)

theorem hcardT119_113 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK119 ⟨113, by decide⟩ R119 hpxR119 hcardq119 (by decide)).symm

/-- **Cell (119, 113).** -/
theorem cell119_113 (e : List (ZMod 25)) (heK : charOK (basisAt rK119) e = true)
    (h : ↥(reps (⟨113, by decide⟩ : Fin 148))) :
    species (reps (⟨113, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK119 e (h : Coordinate 1) T119_113 i :=
  species_entry_eq_sum rK119 ⟨113, by decide⟩ e heK h T119_113 hfix119_113 hinj119_113 hcardT119_113
    (fun i => conj_mem_of_fixedPoints (reps ⟨113, by decide⟩) (reps rK119) (T119_113 i) (hfix119_113 i) h)

/-! ## Cell (119, 119): |T| = 5 -/

def T119_119list : List Coordinates := [(0,3,0,0,0), (0,4,0,0,0), (0,0,0,0,0), (0,1,0,0,0), (0,2,0,0,0)]
def T119_119 : Fin 5 → Coordinate 1 := fun i => T119_119list.getD i.val (0,0,0,0,0)

theorem hfix119_119 : ∀ i, ((T119_119 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119) :=
  repsFix_of_siftB rK119 ⟨119, by decide⟩ T119_119 (by decide)

theorem hinj119_119 : Function.Injective
    (fun i => ((T119_119 i : Coordinate 1) : Coordinate 1 ⧸ reps rK119)) :=
  repsInj_of_reduceAux rK119 T119_119 (by decide)

theorem hcardT119_119 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK119 ⟨119, by decide⟩ R119 hpxR119 hcardq119 (by decide)).symm

/-- **Cell (119, 119).** -/
theorem cell119_119 (e : List (ZMod 25)) (heK : charOK (basisAt rK119) e = true)
    (h : ↥(reps (⟨119, by decide⟩ : Fin 148))) :
    species (reps (⟨119, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK119 e (h : Coordinate 1) T119_119 i :=
  species_entry_eq_sum rK119 ⟨119, by decide⟩ e heK h T119_119 hfix119_119 hinj119_119 hcardT119_119
    (fun i => conj_mem_of_fixedPoints (reps ⟨119, by decide⟩) (reps rK119) (T119_119 i) (hfix119_119 i) h)

namespace Q2

def R119_2 : Fin 5 → Coordinate 2 := fun i => R119list.getD i.val (0,0,0,0,0)
theorem hpxR119_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK119) (R119_2 i)) := by decide
theorem hcardq119_2 : Nat.card (Coordinate 2 ⧸ reps rK119) = 5 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (119, 0) twin -/

def T119_0_2 : Fin 5 → Coordinate 2 := fun i => T119_0list.getD i.val (0,0,0,0,0)

theorem hfix119_0_2 : ∀ i, ((T119_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119) :=
  repsFix_of_siftB2 rK119 ⟨0, by decide⟩ T119_0_2 (by decide)

theorem hinj119_0_2 : Function.Injective
    (fun i => ((T119_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)) :=
  repsInj_of_reduceAux2 rK119 T119_0_2 (by decide)

theorem hcardT119_0_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK119 ⟨0, by decide⟩ R119_2 hpxR119_2 hcardq119_2 (by decide)).symm

/-- **Cell (119, 0) twin (q=2).** -/
theorem cell119_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK119) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec2 rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK119 e (h : Coordinate 2) T119_0_2 i :=
  species_entry_eq_sum rK119 ⟨0, by decide⟩ e heK h T119_0_2 hfix119_0_2 hinj119_0_2 hcardT119_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK119) (T119_0_2 i) (hfix119_0_2 i) h)

/-! ### Cell (119, 1) twin -/

def T119_1_2 : Fin 5 → Coordinate 2 := fun i => T119_1list.getD i.val (0,0,0,0,0)

theorem hfix119_1_2 : ∀ i, ((T119_1_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119) :=
  repsFix_of_siftB2 rK119 ⟨1, by decide⟩ T119_1_2 (by decide)

theorem hinj119_1_2 : Function.Injective
    (fun i => ((T119_1_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)) :=
  repsInj_of_reduceAux2 rK119 T119_1_2 (by decide)

theorem hcardT119_1_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK119 ⟨1, by decide⟩ R119_2 hpxR119_2 hcardq119_2 (by decide)).symm

/-- **Cell (119, 1) twin (q=2).** -/
theorem cell119_1_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK119) e = true)
    (h : ↥(reps (⟨1, by decide⟩ : Fin 148))) :
    species (reps (⟨1, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec2 rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK119 e (h : Coordinate 2) T119_1_2 i :=
  species_entry_eq_sum rK119 ⟨1, by decide⟩ e heK h T119_1_2 hfix119_1_2 hinj119_1_2 hcardT119_1_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨1, by decide⟩) (reps rK119) (T119_1_2 i) (hfix119_1_2 i) h)

/-! ### Cell (119, 6) twin -/

def T119_6_2 : Fin 5 → Coordinate 2 := fun i => T119_6list.getD i.val (0,0,0,0,0)

theorem hfix119_6_2 : ∀ i, ((T119_6_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119) :=
  repsFix_of_siftB2 rK119 ⟨6, by decide⟩ T119_6_2 (by decide)

theorem hinj119_6_2 : Function.Injective
    (fun i => ((T119_6_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)) :=
  repsInj_of_reduceAux2 rK119 T119_6_2 (by decide)

theorem hcardT119_6_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK119 ⟨6, by decide⟩ R119_2 hpxR119_2 hcardq119_2 (by decide)).symm

/-- **Cell (119, 6) twin (q=2).** -/
theorem cell119_6_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK119) e = true)
    (h : ↥(reps (⟨6, by decide⟩ : Fin 148))) :
    species (reps (⟨6, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec2 rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK119 e (h : Coordinate 2) T119_6_2 i :=
  species_entry_eq_sum rK119 ⟨6, by decide⟩ e heK h T119_6_2 hfix119_6_2 hinj119_6_2 hcardT119_6_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨6, by decide⟩) (reps rK119) (T119_6_2 i) (hfix119_6_2 i) h)

/-! ### Cell (119, 7) twin -/

def T119_7_2 : Fin 5 → Coordinate 2 := fun i => T119_7list.getD i.val (0,0,0,0,0)

theorem hfix119_7_2 : ∀ i, ((T119_7_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119) :=
  repsFix_of_siftB2 rK119 ⟨7, by decide⟩ T119_7_2 (by decide)

theorem hinj119_7_2 : Function.Injective
    (fun i => ((T119_7_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)) :=
  repsInj_of_reduceAux2 rK119 T119_7_2 (by decide)

theorem hcardT119_7_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK119 ⟨7, by decide⟩ R119_2 hpxR119_2 hcardq119_2 (by decide)).symm

/-- **Cell (119, 7) twin (q=2).** -/
theorem cell119_7_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK119) e = true)
    (h : ↥(reps (⟨7, by decide⟩ : Fin 148))) :
    species (reps (⟨7, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec2 rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK119 e (h : Coordinate 2) T119_7_2 i :=
  species_entry_eq_sum rK119 ⟨7, by decide⟩ e heK h T119_7_2 hfix119_7_2 hinj119_7_2 hcardT119_7_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨7, by decide⟩) (reps rK119) (T119_7_2 i) (hfix119_7_2 i) h)

/-! ### Cell (119, 8) twin -/

def T119_8_2 : Fin 5 → Coordinate 2 := fun i => T119_8list.getD i.val (0,0,0,0,0)

theorem hfix119_8_2 : ∀ i, ((T119_8_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119) :=
  repsFix_of_siftB2 rK119 ⟨8, by decide⟩ T119_8_2 (by decide)

theorem hinj119_8_2 : Function.Injective
    (fun i => ((T119_8_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)) :=
  repsInj_of_reduceAux2 rK119 T119_8_2 (by decide)

theorem hcardT119_8_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK119 ⟨8, by decide⟩ R119_2 hpxR119_2 hcardq119_2 (by decide)).symm

/-- **Cell (119, 8) twin (q=2).** -/
theorem cell119_8_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK119) e = true)
    (h : ↥(reps (⟨8, by decide⟩ : Fin 148))) :
    species (reps (⟨8, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec2 rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK119 e (h : Coordinate 2) T119_8_2 i :=
  species_entry_eq_sum rK119 ⟨8, by decide⟩ e heK h T119_8_2 hfix119_8_2 hinj119_8_2 hcardT119_8_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨8, by decide⟩) (reps rK119) (T119_8_2 i) (hfix119_8_2 i) h)

/-! ### Cell (119, 9) twin -/

def T119_9_2 : Fin 5 → Coordinate 2 := fun i => T119_9list.getD i.val (0,0,0,0,0)

theorem hfix119_9_2 : ∀ i, ((T119_9_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119) :=
  repsFix_of_siftB2 rK119 ⟨9, by decide⟩ T119_9_2 (by decide)

theorem hinj119_9_2 : Function.Injective
    (fun i => ((T119_9_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)) :=
  repsInj_of_reduceAux2 rK119 T119_9_2 (by decide)

theorem hcardT119_9_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK119 ⟨9, by decide⟩ R119_2 hpxR119_2 hcardq119_2 (by decide)).symm

/-- **Cell (119, 9) twin (q=2).** -/
theorem cell119_9_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK119) e = true)
    (h : ↥(reps (⟨9, by decide⟩ : Fin 148))) :
    species (reps (⟨9, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec2 rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK119 e (h : Coordinate 2) T119_9_2 i :=
  species_entry_eq_sum rK119 ⟨9, by decide⟩ e heK h T119_9_2 hfix119_9_2 hinj119_9_2 hcardT119_9_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨9, by decide⟩) (reps rK119) (T119_9_2 i) (hfix119_9_2 i) h)

/-! ### Cell (119, 10) twin -/

def T119_10_2 : Fin 5 → Coordinate 2 := fun i => T119_10list.getD i.val (0,0,0,0,0)

theorem hfix119_10_2 : ∀ i, ((T119_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119) :=
  repsFix_of_siftB2 rK119 ⟨10, by decide⟩ T119_10_2 (by decide)

theorem hinj119_10_2 : Function.Injective
    (fun i => ((T119_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)) :=
  repsInj_of_reduceAux2 rK119 T119_10_2 (by decide)

theorem hcardT119_10_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK119 ⟨10, by decide⟩ R119_2 hpxR119_2 hcardq119_2 (by decide)).symm

/-- **Cell (119, 10) twin (q=2).** -/
theorem cell119_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK119) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec2 rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK119 e (h : Coordinate 2) T119_10_2 i :=
  species_entry_eq_sum rK119 ⟨10, by decide⟩ e heK h T119_10_2 hfix119_10_2 hinj119_10_2 hcardT119_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK119) (T119_10_2 i) (hfix119_10_2 i) h)

/-! ### Cell (119, 12) twin -/

def T119_12_2 : Fin 5 → Coordinate 2 := fun i => T119_12list.getD i.val (0,0,0,0,0)

theorem hfix119_12_2 : ∀ i, ((T119_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119) :=
  repsFix_of_siftB2 rK119 ⟨12, by decide⟩ T119_12_2 (by decide)

theorem hinj119_12_2 : Function.Injective
    (fun i => ((T119_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)) :=
  repsInj_of_reduceAux2 rK119 T119_12_2 (by decide)

theorem hcardT119_12_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK119 ⟨12, by decide⟩ R119_2 hpxR119_2 hcardq119_2 (by decide)).symm

/-- **Cell (119, 12) twin (q=2).** -/
theorem cell119_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK119) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec2 rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK119 e (h : Coordinate 2) T119_12_2 i :=
  species_entry_eq_sum rK119 ⟨12, by decide⟩ e heK h T119_12_2 hfix119_12_2 hinj119_12_2 hcardT119_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK119) (T119_12_2 i) (hfix119_12_2 i) h)

/-! ### Cell (119, 13) twin -/

def T119_13_2 : Fin 5 → Coordinate 2 := fun i => T119_13list.getD i.val (0,0,0,0,0)

theorem hfix119_13_2 : ∀ i, ((T119_13_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119) :=
  repsFix_of_siftB2 rK119 ⟨13, by decide⟩ T119_13_2 (by decide)

theorem hinj119_13_2 : Function.Injective
    (fun i => ((T119_13_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)) :=
  repsInj_of_reduceAux2 rK119 T119_13_2 (by decide)

theorem hcardT119_13_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK119 ⟨13, by decide⟩ R119_2 hpxR119_2 hcardq119_2 (by decide)).symm

/-- **Cell (119, 13) twin (q=2).** -/
theorem cell119_13_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK119) e = true)
    (h : ↥(reps (⟨13, by decide⟩ : Fin 148))) :
    species (reps (⟨13, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec2 rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK119 e (h : Coordinate 2) T119_13_2 i :=
  species_entry_eq_sum rK119 ⟨13, by decide⟩ e heK h T119_13_2 hfix119_13_2 hinj119_13_2 hcardT119_13_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨13, by decide⟩) (reps rK119) (T119_13_2 i) (hfix119_13_2 i) h)

/-! ### Cell (119, 19) twin -/

def T119_19_2 : Fin 5 → Coordinate 2 := fun i => T119_19list.getD i.val (0,0,0,0,0)

theorem hfix119_19_2 : ∀ i, ((T119_19_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119) :=
  repsFix_of_siftB2 rK119 ⟨19, by decide⟩ T119_19_2 (by decide)

theorem hinj119_19_2 : Function.Injective
    (fun i => ((T119_19_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)) :=
  repsInj_of_reduceAux2 rK119 T119_19_2 (by decide)

theorem hcardT119_19_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK119 ⟨19, by decide⟩ R119_2 hpxR119_2 hcardq119_2 (by decide)).symm

/-- **Cell (119, 19) twin (q=2).** -/
theorem cell119_19_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK119) e = true)
    (h : ↥(reps (⟨19, by decide⟩ : Fin 148))) :
    species (reps (⟨19, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec2 rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK119 e (h : Coordinate 2) T119_19_2 i :=
  species_entry_eq_sum rK119 ⟨19, by decide⟩ e heK h T119_19_2 hfix119_19_2 hinj119_19_2 hcardT119_19_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨19, by decide⟩) (reps rK119) (T119_19_2 i) (hfix119_19_2 i) h)

/-! ### Cell (119, 24) twin -/

def T119_24_2 : Fin 5 → Coordinate 2 := fun i => T119_24list.getD i.val (0,0,0,0,0)

theorem hfix119_24_2 : ∀ i, ((T119_24_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119) :=
  repsFix_of_siftB2 rK119 ⟨24, by decide⟩ T119_24_2 (by decide)

theorem hinj119_24_2 : Function.Injective
    (fun i => ((T119_24_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)) :=
  repsInj_of_reduceAux2 rK119 T119_24_2 (by decide)

theorem hcardT119_24_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK119 ⟨24, by decide⟩ R119_2 hpxR119_2 hcardq119_2 (by decide)).symm

/-- **Cell (119, 24) twin (q=2).** -/
theorem cell119_24_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK119) e = true)
    (h : ↥(reps (⟨24, by decide⟩ : Fin 148))) :
    species (reps (⟨24, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec2 rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK119 e (h : Coordinate 2) T119_24_2 i :=
  species_entry_eq_sum rK119 ⟨24, by decide⟩ e heK h T119_24_2 hfix119_24_2 hinj119_24_2 hcardT119_24_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨24, by decide⟩) (reps rK119) (T119_24_2 i) (hfix119_24_2 i) h)

/-! ### Cell (119, 25) twin -/

def T119_25_2 : Fin 5 → Coordinate 2 := fun i => T119_25list.getD i.val (0,0,0,0,0)

theorem hfix119_25_2 : ∀ i, ((T119_25_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119) :=
  repsFix_of_siftB2 rK119 ⟨25, by decide⟩ T119_25_2 (by decide)

theorem hinj119_25_2 : Function.Injective
    (fun i => ((T119_25_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)) :=
  repsInj_of_reduceAux2 rK119 T119_25_2 (by decide)

theorem hcardT119_25_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK119 ⟨25, by decide⟩ R119_2 hpxR119_2 hcardq119_2 (by decide)).symm

/-- **Cell (119, 25) twin (q=2).** -/
theorem cell119_25_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK119) e = true)
    (h : ↥(reps (⟨25, by decide⟩ : Fin 148))) :
    species (reps (⟨25, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec2 rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK119 e (h : Coordinate 2) T119_25_2 i :=
  species_entry_eq_sum rK119 ⟨25, by decide⟩ e heK h T119_25_2 hfix119_25_2 hinj119_25_2 hcardT119_25_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨25, by decide⟩) (reps rK119) (T119_25_2 i) (hfix119_25_2 i) h)

/-! ### Cell (119, 26) twin -/

def T119_26_2 : Fin 5 → Coordinate 2 := fun i => T119_26list.getD i.val (0,0,0,0,0)

theorem hfix119_26_2 : ∀ i, ((T119_26_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119) :=
  repsFix_of_siftB2 rK119 ⟨26, by decide⟩ T119_26_2 (by decide)

theorem hinj119_26_2 : Function.Injective
    (fun i => ((T119_26_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)) :=
  repsInj_of_reduceAux2 rK119 T119_26_2 (by decide)

theorem hcardT119_26_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK119 ⟨26, by decide⟩ R119_2 hpxR119_2 hcardq119_2 (by decide)).symm

/-- **Cell (119, 26) twin (q=2).** -/
theorem cell119_26_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK119) e = true)
    (h : ↥(reps (⟨26, by decide⟩ : Fin 148))) :
    species (reps (⟨26, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec2 rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK119 e (h : Coordinate 2) T119_26_2 i :=
  species_entry_eq_sum rK119 ⟨26, by decide⟩ e heK h T119_26_2 hfix119_26_2 hinj119_26_2 hcardT119_26_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨26, by decide⟩) (reps rK119) (T119_26_2 i) (hfix119_26_2 i) h)

/-! ### Cell (119, 27) twin -/

def T119_27_2 : Fin 5 → Coordinate 2 := fun i => T119_27list.getD i.val (0,0,0,0,0)

theorem hfix119_27_2 : ∀ i, ((T119_27_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119) :=
  repsFix_of_siftB2 rK119 ⟨27, by decide⟩ T119_27_2 (by decide)

theorem hinj119_27_2 : Function.Injective
    (fun i => ((T119_27_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)) :=
  repsInj_of_reduceAux2 rK119 T119_27_2 (by decide)

theorem hcardT119_27_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK119 ⟨27, by decide⟩ R119_2 hpxR119_2 hcardq119_2 (by decide)).symm

/-- **Cell (119, 27) twin (q=2).** -/
theorem cell119_27_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK119) e = true)
    (h : ↥(reps (⟨27, by decide⟩ : Fin 148))) :
    species (reps (⟨27, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec2 rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK119 e (h : Coordinate 2) T119_27_2 i :=
  species_entry_eq_sum rK119 ⟨27, by decide⟩ e heK h T119_27_2 hfix119_27_2 hinj119_27_2 hcardT119_27_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨27, by decide⟩) (reps rK119) (T119_27_2 i) (hfix119_27_2 i) h)

/-! ### Cell (119, 31) twin -/

def T119_31_2 : Fin 5 → Coordinate 2 := fun i => T119_31list.getD i.val (0,0,0,0,0)

theorem hfix119_31_2 : ∀ i, ((T119_31_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119) :=
  repsFix_of_siftB2 rK119 ⟨31, by decide⟩ T119_31_2 (by decide)

theorem hinj119_31_2 : Function.Injective
    (fun i => ((T119_31_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)) :=
  repsInj_of_reduceAux2 rK119 T119_31_2 (by decide)

theorem hcardT119_31_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK119 ⟨31, by decide⟩ R119_2 hpxR119_2 hcardq119_2 (by decide)).symm

/-- **Cell (119, 31) twin (q=2).** -/
theorem cell119_31_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK119) e = true)
    (h : ↥(reps (⟨31, by decide⟩ : Fin 148))) :
    species (reps (⟨31, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec2 rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK119 e (h : Coordinate 2) T119_31_2 i :=
  species_entry_eq_sum rK119 ⟨31, by decide⟩ e heK h T119_31_2 hfix119_31_2 hinj119_31_2 hcardT119_31_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨31, by decide⟩) (reps rK119) (T119_31_2 i) (hfix119_31_2 i) h)

/-! ### Cell (119, 36) twin -/

def T119_36_2 : Fin 5 → Coordinate 2 := fun i => T119_36list.getD i.val (0,0,0,0,0)

theorem hfix119_36_2 : ∀ i, ((T119_36_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119) :=
  repsFix_of_siftB2 rK119 ⟨36, by decide⟩ T119_36_2 (by decide)

theorem hinj119_36_2 : Function.Injective
    (fun i => ((T119_36_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)) :=
  repsInj_of_reduceAux2 rK119 T119_36_2 (by decide)

theorem hcardT119_36_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK119 ⟨36, by decide⟩ R119_2 hpxR119_2 hcardq119_2 (by decide)).symm

/-- **Cell (119, 36) twin (q=2).** -/
theorem cell119_36_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK119) e = true)
    (h : ↥(reps (⟨36, by decide⟩ : Fin 148))) :
    species (reps (⟨36, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec2 rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK119 e (h : Coordinate 2) T119_36_2 i :=
  species_entry_eq_sum rK119 ⟨36, by decide⟩ e heK h T119_36_2 hfix119_36_2 hinj119_36_2 hcardT119_36_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨36, by decide⟩) (reps rK119) (T119_36_2 i) (hfix119_36_2 i) h)

/-! ### Cell (119, 41) twin -/

def T119_41_2 : Fin 5 → Coordinate 2 := fun i => T119_41list.getD i.val (0,0,0,0,0)

theorem hfix119_41_2 : ∀ i, ((T119_41_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119) :=
  repsFix_of_siftB2 rK119 ⟨41, by decide⟩ T119_41_2 (by decide)

theorem hinj119_41_2 : Function.Injective
    (fun i => ((T119_41_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)) :=
  repsInj_of_reduceAux2 rK119 T119_41_2 (by decide)

theorem hcardT119_41_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK119 ⟨41, by decide⟩ R119_2 hpxR119_2 hcardq119_2 (by decide)).symm

/-- **Cell (119, 41) twin (q=2).** -/
theorem cell119_41_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK119) e = true)
    (h : ↥(reps (⟨41, by decide⟩ : Fin 148))) :
    species (reps (⟨41, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec2 rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK119 e (h : Coordinate 2) T119_41_2 i :=
  species_entry_eq_sum rK119 ⟨41, by decide⟩ e heK h T119_41_2 hfix119_41_2 hinj119_41_2 hcardT119_41_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨41, by decide⟩) (reps rK119) (T119_41_2 i) (hfix119_41_2 i) h)

/-! ### Cell (119, 46) twin -/

def T119_46_2 : Fin 5 → Coordinate 2 := fun i => T119_46list.getD i.val (0,0,0,0,0)

theorem hfix119_46_2 : ∀ i, ((T119_46_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119) :=
  repsFix_of_siftB2 rK119 ⟨46, by decide⟩ T119_46_2 (by decide)

theorem hinj119_46_2 : Function.Injective
    (fun i => ((T119_46_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)) :=
  repsInj_of_reduceAux2 rK119 T119_46_2 (by decide)

theorem hcardT119_46_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK119 ⟨46, by decide⟩ R119_2 hpxR119_2 hcardq119_2 (by decide)).symm

/-- **Cell (119, 46) twin (q=2).** -/
theorem cell119_46_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK119) e = true)
    (h : ↥(reps (⟨46, by decide⟩ : Fin 148))) :
    species (reps (⟨46, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec2 rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK119 e (h : Coordinate 2) T119_46_2 i :=
  species_entry_eq_sum rK119 ⟨46, by decide⟩ e heK h T119_46_2 hfix119_46_2 hinj119_46_2 hcardT119_46_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨46, by decide⟩) (reps rK119) (T119_46_2 i) (hfix119_46_2 i) h)

/-! ### Cell (119, 51) twin -/

def T119_51_2 : Fin 5 → Coordinate 2 := fun i => T119_51list.getD i.val (0,0,0,0,0)

theorem hfix119_51_2 : ∀ i, ((T119_51_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119) :=
  repsFix_of_siftB2 rK119 ⟨51, by decide⟩ T119_51_2 (by decide)

theorem hinj119_51_2 : Function.Injective
    (fun i => ((T119_51_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)) :=
  repsInj_of_reduceAux2 rK119 T119_51_2 (by decide)

theorem hcardT119_51_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK119 ⟨51, by decide⟩ R119_2 hpxR119_2 hcardq119_2 (by decide)).symm

/-- **Cell (119, 51) twin (q=2).** -/
theorem cell119_51_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK119) e = true)
    (h : ↥(reps (⟨51, by decide⟩ : Fin 148))) :
    species (reps (⟨51, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec2 rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK119 e (h : Coordinate 2) T119_51_2 i :=
  species_entry_eq_sum rK119 ⟨51, by decide⟩ e heK h T119_51_2 hfix119_51_2 hinj119_51_2 hcardT119_51_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨51, by decide⟩) (reps rK119) (T119_51_2 i) (hfix119_51_2 i) h)

/-! ### Cell (119, 53) twin -/

def T119_53_2 : Fin 5 → Coordinate 2 := fun i => T119_53list.getD i.val (0,0,0,0,0)

theorem hfix119_53_2 : ∀ i, ((T119_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119) :=
  repsFix_of_siftB2 rK119 ⟨53, by decide⟩ T119_53_2 (by decide)

theorem hinj119_53_2 : Function.Injective
    (fun i => ((T119_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)) :=
  repsInj_of_reduceAux2 rK119 T119_53_2 (by decide)

theorem hcardT119_53_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK119 ⟨53, by decide⟩ R119_2 hpxR119_2 hcardq119_2 (by decide)).symm

/-- **Cell (119, 53) twin (q=2).** -/
theorem cell119_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK119) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec2 rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK119 e (h : Coordinate 2) T119_53_2 i :=
  species_entry_eq_sum rK119 ⟨53, by decide⟩ e heK h T119_53_2 hfix119_53_2 hinj119_53_2 hcardT119_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK119) (T119_53_2 i) (hfix119_53_2 i) h)

/-! ### Cell (119, 70) twin -/

def T119_70_2 : Fin 5 → Coordinate 2 := fun i => T119_70list.getD i.val (0,0,0,0,0)

theorem hfix119_70_2 : ∀ i, ((T119_70_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119) :=
  repsFix_of_siftB2 rK119 ⟨70, by decide⟩ T119_70_2 (by decide)

theorem hinj119_70_2 : Function.Injective
    (fun i => ((T119_70_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)) :=
  repsInj_of_reduceAux2 rK119 T119_70_2 (by decide)

theorem hcardT119_70_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK119 ⟨70, by decide⟩ R119_2 hpxR119_2 hcardq119_2 (by decide)).symm

/-- **Cell (119, 70) twin (q=2).** -/
theorem cell119_70_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK119) e = true)
    (h : ↥(reps (⟨70, by decide⟩ : Fin 148))) :
    species (reps (⟨70, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec2 rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK119 e (h : Coordinate 2) T119_70_2 i :=
  species_entry_eq_sum rK119 ⟨70, by decide⟩ e heK h T119_70_2 hfix119_70_2 hinj119_70_2 hcardT119_70_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨70, by decide⟩) (reps rK119) (T119_70_2 i) (hfix119_70_2 i) h)

/-! ### Cell (119, 71) twin -/

def T119_71_2 : Fin 5 → Coordinate 2 := fun i => T119_71list.getD i.val (0,0,0,0,0)

theorem hfix119_71_2 : ∀ i, ((T119_71_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119) :=
  repsFix_of_siftB2 rK119 ⟨71, by decide⟩ T119_71_2 (by decide)

theorem hinj119_71_2 : Function.Injective
    (fun i => ((T119_71_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)) :=
  repsInj_of_reduceAux2 rK119 T119_71_2 (by decide)

theorem hcardT119_71_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK119 ⟨71, by decide⟩ R119_2 hpxR119_2 hcardq119_2 (by decide)).symm

/-- **Cell (119, 71) twin (q=2).** -/
theorem cell119_71_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK119) e = true)
    (h : ↥(reps (⟨71, by decide⟩ : Fin 148))) :
    species (reps (⟨71, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec2 rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK119 e (h : Coordinate 2) T119_71_2 i :=
  species_entry_eq_sum rK119 ⟨71, by decide⟩ e heK h T119_71_2 hfix119_71_2 hinj119_71_2 hcardT119_71_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨71, by decide⟩) (reps rK119) (T119_71_2 i) (hfix119_71_2 i) h)

/-! ### Cell (119, 72) twin -/

def T119_72_2 : Fin 5 → Coordinate 2 := fun i => T119_72list.getD i.val (0,0,0,0,0)

theorem hfix119_72_2 : ∀ i, ((T119_72_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119) :=
  repsFix_of_siftB2 rK119 ⟨72, by decide⟩ T119_72_2 (by decide)

theorem hinj119_72_2 : Function.Injective
    (fun i => ((T119_72_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)) :=
  repsInj_of_reduceAux2 rK119 T119_72_2 (by decide)

theorem hcardT119_72_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK119 ⟨72, by decide⟩ R119_2 hpxR119_2 hcardq119_2 (by decide)).symm

/-- **Cell (119, 72) twin (q=2).** -/
theorem cell119_72_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK119) e = true)
    (h : ↥(reps (⟨72, by decide⟩ : Fin 148))) :
    species (reps (⟨72, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec2 rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK119 e (h : Coordinate 2) T119_72_2 i :=
  species_entry_eq_sum rK119 ⟨72, by decide⟩ e heK h T119_72_2 hfix119_72_2 hinj119_72_2 hcardT119_72_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨72, by decide⟩) (reps rK119) (T119_72_2 i) (hfix119_72_2 i) h)

/-! ### Cell (119, 73) twin -/

def T119_73_2 : Fin 5 → Coordinate 2 := fun i => T119_73list.getD i.val (0,0,0,0,0)

theorem hfix119_73_2 : ∀ i, ((T119_73_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119) :=
  repsFix_of_siftB2 rK119 ⟨73, by decide⟩ T119_73_2 (by decide)

theorem hinj119_73_2 : Function.Injective
    (fun i => ((T119_73_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)) :=
  repsInj_of_reduceAux2 rK119 T119_73_2 (by decide)

theorem hcardT119_73_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK119 ⟨73, by decide⟩ R119_2 hpxR119_2 hcardq119_2 (by decide)).symm

/-- **Cell (119, 73) twin (q=2).** -/
theorem cell119_73_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK119) e = true)
    (h : ↥(reps (⟨73, by decide⟩ : Fin 148))) :
    species (reps (⟨73, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec2 rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK119 e (h : Coordinate 2) T119_73_2 i :=
  species_entry_eq_sum rK119 ⟨73, by decide⟩ e heK h T119_73_2 hfix119_73_2 hinj119_73_2 hcardT119_73_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨73, by decide⟩) (reps rK119) (T119_73_2 i) (hfix119_73_2 i) h)

/-! ### Cell (119, 74) twin -/

def T119_74_2 : Fin 5 → Coordinate 2 := fun i => T119_74list.getD i.val (0,0,0,0,0)

theorem hfix119_74_2 : ∀ i, ((T119_74_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119) :=
  repsFix_of_siftB2 rK119 ⟨74, by decide⟩ T119_74_2 (by decide)

theorem hinj119_74_2 : Function.Injective
    (fun i => ((T119_74_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)) :=
  repsInj_of_reduceAux2 rK119 T119_74_2 (by decide)

theorem hcardT119_74_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK119 ⟨74, by decide⟩ R119_2 hpxR119_2 hcardq119_2 (by decide)).symm

/-- **Cell (119, 74) twin (q=2).** -/
theorem cell119_74_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK119) e = true)
    (h : ↥(reps (⟨74, by decide⟩ : Fin 148))) :
    species (reps (⟨74, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec2 rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK119 e (h : Coordinate 2) T119_74_2 i :=
  species_entry_eq_sum rK119 ⟨74, by decide⟩ e heK h T119_74_2 hfix119_74_2 hinj119_74_2 hcardT119_74_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨74, by decide⟩) (reps rK119) (T119_74_2 i) (hfix119_74_2 i) h)

/-! ### Cell (119, 80) twin -/

def T119_80_2 : Fin 5 → Coordinate 2 := fun i => T119_80list.getD i.val (0,0,0,0,0)

theorem hfix119_80_2 : ∀ i, ((T119_80_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119) :=
  repsFix_of_siftB2 rK119 ⟨80, by decide⟩ T119_80_2 (by decide)

theorem hinj119_80_2 : Function.Injective
    (fun i => ((T119_80_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)) :=
  repsInj_of_reduceAux2 rK119 T119_80_2 (by decide)

theorem hcardT119_80_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK119 ⟨80, by decide⟩ R119_2 hpxR119_2 hcardq119_2 (by decide)).symm

/-- **Cell (119, 80) twin (q=2).** -/
theorem cell119_80_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK119) e = true)
    (h : ↥(reps (⟨80, by decide⟩ : Fin 148))) :
    species (reps (⟨80, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec2 rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK119 e (h : Coordinate 2) T119_80_2 i :=
  species_entry_eq_sum rK119 ⟨80, by decide⟩ e heK h T119_80_2 hfix119_80_2 hinj119_80_2 hcardT119_80_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨80, by decide⟩) (reps rK119) (T119_80_2 i) (hfix119_80_2 i) h)

/-! ### Cell (119, 93) twin -/

def T119_93_2 : Fin 5 → Coordinate 2 := fun i => T119_93list.getD i.val (0,0,0,0,0)

theorem hfix119_93_2 : ∀ i, ((T119_93_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119) :=
  repsFix_of_siftB2 rK119 ⟨93, by decide⟩ T119_93_2 (by decide)

theorem hinj119_93_2 : Function.Injective
    (fun i => ((T119_93_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)) :=
  repsInj_of_reduceAux2 rK119 T119_93_2 (by decide)

theorem hcardT119_93_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK119 ⟨93, by decide⟩ R119_2 hpxR119_2 hcardq119_2 (by decide)).symm

/-- **Cell (119, 93) twin (q=2).** -/
theorem cell119_93_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK119) e = true)
    (h : ↥(reps (⟨93, by decide⟩ : Fin 148))) :
    species (reps (⟨93, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec2 rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK119 e (h : Coordinate 2) T119_93_2 i :=
  species_entry_eq_sum rK119 ⟨93, by decide⟩ e heK h T119_93_2 hfix119_93_2 hinj119_93_2 hcardT119_93_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨93, by decide⟩) (reps rK119) (T119_93_2 i) (hfix119_93_2 i) h)

/-! ### Cell (119, 98) twin -/

def T119_98_2 : Fin 5 → Coordinate 2 := fun i => T119_98list.getD i.val (0,0,0,0,0)

theorem hfix119_98_2 : ∀ i, ((T119_98_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119) :=
  repsFix_of_siftB2 rK119 ⟨98, by decide⟩ T119_98_2 (by decide)

theorem hinj119_98_2 : Function.Injective
    (fun i => ((T119_98_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)) :=
  repsInj_of_reduceAux2 rK119 T119_98_2 (by decide)

theorem hcardT119_98_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK119 ⟨98, by decide⟩ R119_2 hpxR119_2 hcardq119_2 (by decide)).symm

/-- **Cell (119, 98) twin (q=2).** -/
theorem cell119_98_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK119) e = true)
    (h : ↥(reps (⟨98, by decide⟩ : Fin 148))) :
    species (reps (⟨98, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec2 rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK119 e (h : Coordinate 2) T119_98_2 i :=
  species_entry_eq_sum rK119 ⟨98, by decide⟩ e heK h T119_98_2 hfix119_98_2 hinj119_98_2 hcardT119_98_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨98, by decide⟩) (reps rK119) (T119_98_2 i) (hfix119_98_2 i) h)

/-! ### Cell (119, 103) twin -/

def T119_103_2 : Fin 5 → Coordinate 2 := fun i => T119_103list.getD i.val (0,0,0,0,0)

theorem hfix119_103_2 : ∀ i, ((T119_103_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119) :=
  repsFix_of_siftB2 rK119 ⟨103, by decide⟩ T119_103_2 (by decide)

theorem hinj119_103_2 : Function.Injective
    (fun i => ((T119_103_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)) :=
  repsInj_of_reduceAux2 rK119 T119_103_2 (by decide)

theorem hcardT119_103_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK119 ⟨103, by decide⟩ R119_2 hpxR119_2 hcardq119_2 (by decide)).symm

/-- **Cell (119, 103) twin (q=2).** -/
theorem cell119_103_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK119) e = true)
    (h : ↥(reps (⟨103, by decide⟩ : Fin 148))) :
    species (reps (⟨103, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec2 rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK119 e (h : Coordinate 2) T119_103_2 i :=
  species_entry_eq_sum rK119 ⟨103, by decide⟩ e heK h T119_103_2 hfix119_103_2 hinj119_103_2 hcardT119_103_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨103, by decide⟩) (reps rK119) (T119_103_2 i) (hfix119_103_2 i) h)

/-! ### Cell (119, 108) twin -/

def T119_108_2 : Fin 5 → Coordinate 2 := fun i => T119_108list.getD i.val (0,0,0,0,0)

theorem hfix119_108_2 : ∀ i, ((T119_108_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119) :=
  repsFix_of_siftB2 rK119 ⟨108, by decide⟩ T119_108_2 (by decide)

theorem hinj119_108_2 : Function.Injective
    (fun i => ((T119_108_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)) :=
  repsInj_of_reduceAux2 rK119 T119_108_2 (by decide)

theorem hcardT119_108_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK119 ⟨108, by decide⟩ R119_2 hpxR119_2 hcardq119_2 (by decide)).symm

/-- **Cell (119, 108) twin (q=2).** -/
theorem cell119_108_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK119) e = true)
    (h : ↥(reps (⟨108, by decide⟩ : Fin 148))) :
    species (reps (⟨108, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec2 rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK119 e (h : Coordinate 2) T119_108_2 i :=
  species_entry_eq_sum rK119 ⟨108, by decide⟩ e heK h T119_108_2 hfix119_108_2 hinj119_108_2 hcardT119_108_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨108, by decide⟩) (reps rK119) (T119_108_2 i) (hfix119_108_2 i) h)

/-! ### Cell (119, 113) twin -/

def T119_113_2 : Fin 5 → Coordinate 2 := fun i => T119_113list.getD i.val (0,0,0,0,0)

theorem hfix119_113_2 : ∀ i, ((T119_113_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119) :=
  repsFix_of_siftB2 rK119 ⟨113, by decide⟩ T119_113_2 (by decide)

theorem hinj119_113_2 : Function.Injective
    (fun i => ((T119_113_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)) :=
  repsInj_of_reduceAux2 rK119 T119_113_2 (by decide)

theorem hcardT119_113_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK119 ⟨113, by decide⟩ R119_2 hpxR119_2 hcardq119_2 (by decide)).symm

/-- **Cell (119, 113) twin (q=2).** -/
theorem cell119_113_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK119) e = true)
    (h : ↥(reps (⟨113, by decide⟩ : Fin 148))) :
    species (reps (⟨113, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec2 rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK119 e (h : Coordinate 2) T119_113_2 i :=
  species_entry_eq_sum rK119 ⟨113, by decide⟩ e heK h T119_113_2 hfix119_113_2 hinj119_113_2 hcardT119_113_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨113, by decide⟩) (reps rK119) (T119_113_2 i) (hfix119_113_2 i) h)

/-! ### Cell (119, 119) twin -/

def T119_119_2 : Fin 5 → Coordinate 2 := fun i => T119_119list.getD i.val (0,0,0,0,0)

theorem hfix119_119_2 : ∀ i, ((T119_119_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)
    ∈ fixedPoints (reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119) :=
  repsFix_of_siftB2 rK119 ⟨119, by decide⟩ T119_119_2 (by decide)

theorem hinj119_119_2 : Function.Injective
    (fun i => ((T119_119_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK119)) :=
  repsInj_of_reduceAux2 rK119 T119_119_2 (by decide)

theorem hcardT119_119_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK119)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK119 ⟨119, by decide⟩ R119_2 hpxR119_2 hcardq119_2 (by decide)).symm

/-- **Cell (119, 119) twin (q=2).** -/
theorem cell119_119_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK119) e = true)
    (h : ↥(reps (⟨119, by decide⟩ : Fin 148))) :
    species (reps (⟨119, by decide⟩ : Fin 148)) h (basisElt (reps rK119) (charOfVec2 rK119 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK119 e (h : Coordinate 2) T119_119_2 i :=
  species_entry_eq_sum rK119 ⟨119, by decide⟩ e heK h T119_119_2 hfix119_119_2 hinj119_119_2 hcardT119_119_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨119, by decide⟩) (reps rK119) (T119_119_2 i) (hfix119_119_2 i) h)

end Q2

end LeanDring.P5Presentation
