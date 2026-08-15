/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, K-strata data (5^4 stratum, rK 116-116): certified per-cell species-entry instantiations, both
twins.

Covers K-classes 116 (order-5^4 K, |R|=5).  For each nonzero `H`-column
(`(G/K)^H ≠ ∅`), the full coset transversal `R116..` and each `H`-fixed
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

/-! # K-class rK = 116  (|G/K| = 5) -/

def rK116 : Fin 148 := ⟨116, by decide⟩

def R116list : List Coordinates := [(0,0,0,0,0), (1,0,0,0,0), (2,0,0,0,0), (3,0,0,0,0), (4,0,0,0,0)]
def R116 : Fin 5 → Coordinate 1 := fun i => R116list.getD i.val (0,0,0,0,0)

theorem hpxR116 : Function.Injective (fun i => reduceAux 1 (basisAt rK116) (R116 i)) := by decide
theorem hcardq116 : Nat.card (Coordinate 1 ⧸ reps rK116) = 5 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (116, 0): |T| = 5 -/

def T116_0list : List Coordinates := [(0,0,0,0,0), (1,0,0,0,0), (2,0,0,0,0), (3,0,0,0,0), (4,0,0,0,0)]
def T116_0 : Fin 5 → Coordinate 1 := fun i => T116_0list.getD i.val (0,0,0,0,0)

theorem hfix116_0 : ∀ i, ((T116_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116) :=
  repsFix_of_siftB rK116 ⟨0, by decide⟩ T116_0 (by decide)

theorem hinj116_0 : Function.Injective
    (fun i => ((T116_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)) :=
  repsInj_of_reduceAux rK116 T116_0 (by decide)

theorem hcardT116_0 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK116 ⟨0, by decide⟩ R116 hpxR116 hcardq116 (by decide)).symm

/-- **Cell (116, 0).** -/
theorem cell116_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK116) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK116 e (h : Coordinate 1) T116_0 i :=
  species_entry_eq_sum rK116 ⟨0, by decide⟩ e heK h T116_0 hfix116_0 hinj116_0 hcardT116_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK116) (T116_0 i) (hfix116_0 i) h)

/-! ## Cell (116, 1): |T| = 5 -/

def T116_1list : List Coordinates := [(0,0,0,0,0), (1,0,0,0,0), (2,0,0,0,0), (3,0,0,0,0), (4,0,0,0,0)]
def T116_1 : Fin 5 → Coordinate 1 := fun i => T116_1list.getD i.val (0,0,0,0,0)

theorem hfix116_1 : ∀ i, ((T116_1 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116) :=
  repsFix_of_siftB rK116 ⟨1, by decide⟩ T116_1 (by decide)

theorem hinj116_1 : Function.Injective
    (fun i => ((T116_1 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)) :=
  repsInj_of_reduceAux rK116 T116_1 (by decide)

theorem hcardT116_1 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK116 ⟨1, by decide⟩ R116 hpxR116 hcardq116 (by decide)).symm

/-- **Cell (116, 1).** -/
theorem cell116_1 (e : List (ZMod 25)) (heK : charOK (basisAt rK116) e = true)
    (h : ↥(reps (⟨1, by decide⟩ : Fin 148))) :
    species (reps (⟨1, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK116 e (h : Coordinate 1) T116_1 i :=
  species_entry_eq_sum rK116 ⟨1, by decide⟩ e heK h T116_1 hfix116_1 hinj116_1 hcardT116_1
    (fun i => conj_mem_of_fixedPoints (reps ⟨1, by decide⟩) (reps rK116) (T116_1 i) (hfix116_1 i) h)

/-! ## Cell (116, 6): |T| = 5 -/

def T116_6list : List Coordinates := [(0,0,0,0,0), (1,0,0,0,0), (2,0,0,0,0), (3,0,0,0,0), (4,0,0,0,0)]
def T116_6 : Fin 5 → Coordinate 1 := fun i => T116_6list.getD i.val (0,0,0,0,0)

theorem hfix116_6 : ∀ i, ((T116_6 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116) :=
  repsFix_of_siftB rK116 ⟨6, by decide⟩ T116_6 (by decide)

theorem hinj116_6 : Function.Injective
    (fun i => ((T116_6 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)) :=
  repsInj_of_reduceAux rK116 T116_6 (by decide)

theorem hcardT116_6 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK116 ⟨6, by decide⟩ R116 hpxR116 hcardq116 (by decide)).symm

/-- **Cell (116, 6).** -/
theorem cell116_6 (e : List (ZMod 25)) (heK : charOK (basisAt rK116) e = true)
    (h : ↥(reps (⟨6, by decide⟩ : Fin 148))) :
    species (reps (⟨6, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK116 e (h : Coordinate 1) T116_6 i :=
  species_entry_eq_sum rK116 ⟨6, by decide⟩ e heK h T116_6 hfix116_6 hinj116_6 hcardT116_6
    (fun i => conj_mem_of_fixedPoints (reps ⟨6, by decide⟩) (reps rK116) (T116_6 i) (hfix116_6 i) h)

/-! ## Cell (116, 7): |T| = 5 -/

def T116_7list : List Coordinates := [(0,0,0,0,0), (1,0,0,0,0), (2,0,0,0,0), (3,0,0,0,0), (4,0,0,0,0)]
def T116_7 : Fin 5 → Coordinate 1 := fun i => T116_7list.getD i.val (0,0,0,0,0)

theorem hfix116_7 : ∀ i, ((T116_7 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116) :=
  repsFix_of_siftB rK116 ⟨7, by decide⟩ T116_7 (by decide)

theorem hinj116_7 : Function.Injective
    (fun i => ((T116_7 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)) :=
  repsInj_of_reduceAux rK116 T116_7 (by decide)

theorem hcardT116_7 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK116 ⟨7, by decide⟩ R116 hpxR116 hcardq116 (by decide)).symm

/-- **Cell (116, 7).** -/
theorem cell116_7 (e : List (ZMod 25)) (heK : charOK (basisAt rK116) e = true)
    (h : ↥(reps (⟨7, by decide⟩ : Fin 148))) :
    species (reps (⟨7, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK116 e (h : Coordinate 1) T116_7 i :=
  species_entry_eq_sum rK116 ⟨7, by decide⟩ e heK h T116_7 hfix116_7 hinj116_7 hcardT116_7
    (fun i => conj_mem_of_fixedPoints (reps ⟨7, by decide⟩) (reps rK116) (T116_7 i) (hfix116_7 i) h)

/-! ## Cell (116, 8): |T| = 5 -/

def T116_8list : List Coordinates := [(0,0,0,0,0), (1,0,0,0,0), (2,0,0,0,0), (3,0,0,0,0), (4,0,0,0,0)]
def T116_8 : Fin 5 → Coordinate 1 := fun i => T116_8list.getD i.val (0,0,0,0,0)

theorem hfix116_8 : ∀ i, ((T116_8 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116) :=
  repsFix_of_siftB rK116 ⟨8, by decide⟩ T116_8 (by decide)

theorem hinj116_8 : Function.Injective
    (fun i => ((T116_8 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)) :=
  repsInj_of_reduceAux rK116 T116_8 (by decide)

theorem hcardT116_8 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK116 ⟨8, by decide⟩ R116 hpxR116 hcardq116 (by decide)).symm

/-- **Cell (116, 8).** -/
theorem cell116_8 (e : List (ZMod 25)) (heK : charOK (basisAt rK116) e = true)
    (h : ↥(reps (⟨8, by decide⟩ : Fin 148))) :
    species (reps (⟨8, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK116 e (h : Coordinate 1) T116_8 i :=
  species_entry_eq_sum rK116 ⟨8, by decide⟩ e heK h T116_8 hfix116_8 hinj116_8 hcardT116_8
    (fun i => conj_mem_of_fixedPoints (reps ⟨8, by decide⟩) (reps rK116) (T116_8 i) (hfix116_8 i) h)

/-! ## Cell (116, 9): |T| = 5 -/

def T116_9list : List Coordinates := [(0,0,0,0,0), (1,0,0,0,0), (2,0,0,0,0), (3,0,0,0,0), (4,0,0,0,0)]
def T116_9 : Fin 5 → Coordinate 1 := fun i => T116_9list.getD i.val (0,0,0,0,0)

theorem hfix116_9 : ∀ i, ((T116_9 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116) :=
  repsFix_of_siftB rK116 ⟨9, by decide⟩ T116_9 (by decide)

theorem hinj116_9 : Function.Injective
    (fun i => ((T116_9 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)) :=
  repsInj_of_reduceAux rK116 T116_9 (by decide)

theorem hcardT116_9 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK116 ⟨9, by decide⟩ R116 hpxR116 hcardq116 (by decide)).symm

/-- **Cell (116, 9).** -/
theorem cell116_9 (e : List (ZMod 25)) (heK : charOK (basisAt rK116) e = true)
    (h : ↥(reps (⟨9, by decide⟩ : Fin 148))) :
    species (reps (⟨9, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK116 e (h : Coordinate 1) T116_9 i :=
  species_entry_eq_sum rK116 ⟨9, by decide⟩ e heK h T116_9 hfix116_9 hinj116_9 hcardT116_9
    (fun i => conj_mem_of_fixedPoints (reps ⟨9, by decide⟩) (reps rK116) (T116_9 i) (hfix116_9 i) h)

/-! ## Cell (116, 10): |T| = 5 -/

def T116_10list : List Coordinates := [(0,0,0,0,0), (1,0,0,0,0), (2,0,0,0,0), (3,0,0,0,0), (4,0,0,0,0)]
def T116_10 : Fin 5 → Coordinate 1 := fun i => T116_10list.getD i.val (0,0,0,0,0)

theorem hfix116_10 : ∀ i, ((T116_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116) :=
  repsFix_of_siftB rK116 ⟨10, by decide⟩ T116_10 (by decide)

theorem hinj116_10 : Function.Injective
    (fun i => ((T116_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)) :=
  repsInj_of_reduceAux rK116 T116_10 (by decide)

theorem hcardT116_10 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK116 ⟨10, by decide⟩ R116 hpxR116 hcardq116 (by decide)).symm

/-- **Cell (116, 10).** -/
theorem cell116_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK116) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK116 e (h : Coordinate 1) T116_10 i :=
  species_entry_eq_sum rK116 ⟨10, by decide⟩ e heK h T116_10 hfix116_10 hinj116_10 hcardT116_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK116) (T116_10 i) (hfix116_10 i) h)

/-! ## Cell (116, 12): |T| = 5 -/

def T116_12list : List Coordinates := [(0,0,0,0,0), (1,0,0,0,0), (2,0,0,0,0), (3,0,0,0,0), (4,0,0,0,0)]
def T116_12 : Fin 5 → Coordinate 1 := fun i => T116_12list.getD i.val (0,0,0,0,0)

theorem hfix116_12 : ∀ i, ((T116_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116) :=
  repsFix_of_siftB rK116 ⟨12, by decide⟩ T116_12 (by decide)

theorem hinj116_12 : Function.Injective
    (fun i => ((T116_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)) :=
  repsInj_of_reduceAux rK116 T116_12 (by decide)

theorem hcardT116_12 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK116 ⟨12, by decide⟩ R116 hpxR116 hcardq116 (by decide)).symm

/-- **Cell (116, 12).** -/
theorem cell116_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK116) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK116 e (h : Coordinate 1) T116_12 i :=
  species_entry_eq_sum rK116 ⟨12, by decide⟩ e heK h T116_12 hfix116_12 hinj116_12 hcardT116_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK116) (T116_12 i) (hfix116_12 i) h)

/-! ## Cell (116, 13): |T| = 5 -/

def T116_13list : List Coordinates := [(0,0,0,0,0), (1,0,0,0,0), (2,0,0,0,0), (3,0,0,0,0), (4,0,0,0,0)]
def T116_13 : Fin 5 → Coordinate 1 := fun i => T116_13list.getD i.val (0,0,0,0,0)

theorem hfix116_13 : ∀ i, ((T116_13 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116) :=
  repsFix_of_siftB rK116 ⟨13, by decide⟩ T116_13 (by decide)

theorem hinj116_13 : Function.Injective
    (fun i => ((T116_13 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)) :=
  repsInj_of_reduceAux rK116 T116_13 (by decide)

theorem hcardT116_13 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK116 ⟨13, by decide⟩ R116 hpxR116 hcardq116 (by decide)).symm

/-- **Cell (116, 13).** -/
theorem cell116_13 (e : List (ZMod 25)) (heK : charOK (basisAt rK116) e = true)
    (h : ↥(reps (⟨13, by decide⟩ : Fin 148))) :
    species (reps (⟨13, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK116 e (h : Coordinate 1) T116_13 i :=
  species_entry_eq_sum rK116 ⟨13, by decide⟩ e heK h T116_13 hfix116_13 hinj116_13 hcardT116_13
    (fun i => conj_mem_of_fixedPoints (reps ⟨13, by decide⟩) (reps rK116) (T116_13 i) (hfix116_13 i) h)

/-! ## Cell (116, 19): |T| = 5 -/

def T116_19list : List Coordinates := [(0,0,0,0,0), (1,0,0,0,0), (2,0,0,0,0), (3,0,0,0,0), (4,0,0,0,0)]
def T116_19 : Fin 5 → Coordinate 1 := fun i => T116_19list.getD i.val (0,0,0,0,0)

theorem hfix116_19 : ∀ i, ((T116_19 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116) :=
  repsFix_of_siftB rK116 ⟨19, by decide⟩ T116_19 (by decide)

theorem hinj116_19 : Function.Injective
    (fun i => ((T116_19 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)) :=
  repsInj_of_reduceAux rK116 T116_19 (by decide)

theorem hcardT116_19 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK116 ⟨19, by decide⟩ R116 hpxR116 hcardq116 (by decide)).symm

/-- **Cell (116, 19).** -/
theorem cell116_19 (e : List (ZMod 25)) (heK : charOK (basisAt rK116) e = true)
    (h : ↥(reps (⟨19, by decide⟩ : Fin 148))) :
    species (reps (⟨19, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK116 e (h : Coordinate 1) T116_19 i :=
  species_entry_eq_sum rK116 ⟨19, by decide⟩ e heK h T116_19 hfix116_19 hinj116_19 hcardT116_19
    (fun i => conj_mem_of_fixedPoints (reps ⟨19, by decide⟩) (reps rK116) (T116_19 i) (hfix116_19 i) h)

/-! ## Cell (116, 24): |T| = 5 -/

def T116_24list : List Coordinates := [(0,0,0,0,0), (1,0,0,0,0), (2,0,0,0,0), (3,0,0,0,0), (4,0,0,0,0)]
def T116_24 : Fin 5 → Coordinate 1 := fun i => T116_24list.getD i.val (0,0,0,0,0)

theorem hfix116_24 : ∀ i, ((T116_24 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116) :=
  repsFix_of_siftB rK116 ⟨24, by decide⟩ T116_24 (by decide)

theorem hinj116_24 : Function.Injective
    (fun i => ((T116_24 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)) :=
  repsInj_of_reduceAux rK116 T116_24 (by decide)

theorem hcardT116_24 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK116 ⟨24, by decide⟩ R116 hpxR116 hcardq116 (by decide)).symm

/-- **Cell (116, 24).** -/
theorem cell116_24 (e : List (ZMod 25)) (heK : charOK (basisAt rK116) e = true)
    (h : ↥(reps (⟨24, by decide⟩ : Fin 148))) :
    species (reps (⟨24, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK116 e (h : Coordinate 1) T116_24 i :=
  species_entry_eq_sum rK116 ⟨24, by decide⟩ e heK h T116_24 hfix116_24 hinj116_24 hcardT116_24
    (fun i => conj_mem_of_fixedPoints (reps ⟨24, by decide⟩) (reps rK116) (T116_24 i) (hfix116_24 i) h)

/-! ## Cell (116, 25): |T| = 5 -/

def T116_25list : List Coordinates := [(0,0,0,0,0), (1,0,0,0,0), (2,0,0,0,0), (3,0,0,0,0), (4,0,0,0,0)]
def T116_25 : Fin 5 → Coordinate 1 := fun i => T116_25list.getD i.val (0,0,0,0,0)

theorem hfix116_25 : ∀ i, ((T116_25 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116) :=
  repsFix_of_siftB rK116 ⟨25, by decide⟩ T116_25 (by decide)

theorem hinj116_25 : Function.Injective
    (fun i => ((T116_25 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)) :=
  repsInj_of_reduceAux rK116 T116_25 (by decide)

theorem hcardT116_25 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK116 ⟨25, by decide⟩ R116 hpxR116 hcardq116 (by decide)).symm

/-- **Cell (116, 25).** -/
theorem cell116_25 (e : List (ZMod 25)) (heK : charOK (basisAt rK116) e = true)
    (h : ↥(reps (⟨25, by decide⟩ : Fin 148))) :
    species (reps (⟨25, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK116 e (h : Coordinate 1) T116_25 i :=
  species_entry_eq_sum rK116 ⟨25, by decide⟩ e heK h T116_25 hfix116_25 hinj116_25 hcardT116_25
    (fun i => conj_mem_of_fixedPoints (reps ⟨25, by decide⟩) (reps rK116) (T116_25 i) (hfix116_25 i) h)

/-! ## Cell (116, 26): |T| = 5 -/

def T116_26list : List Coordinates := [(0,0,0,0,0), (1,0,0,0,0), (2,0,0,0,0), (3,0,0,0,0), (4,0,0,0,0)]
def T116_26 : Fin 5 → Coordinate 1 := fun i => T116_26list.getD i.val (0,0,0,0,0)

theorem hfix116_26 : ∀ i, ((T116_26 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116) :=
  repsFix_of_siftB rK116 ⟨26, by decide⟩ T116_26 (by decide)

theorem hinj116_26 : Function.Injective
    (fun i => ((T116_26 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)) :=
  repsInj_of_reduceAux rK116 T116_26 (by decide)

theorem hcardT116_26 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK116 ⟨26, by decide⟩ R116 hpxR116 hcardq116 (by decide)).symm

/-- **Cell (116, 26).** -/
theorem cell116_26 (e : List (ZMod 25)) (heK : charOK (basisAt rK116) e = true)
    (h : ↥(reps (⟨26, by decide⟩ : Fin 148))) :
    species (reps (⟨26, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK116 e (h : Coordinate 1) T116_26 i :=
  species_entry_eq_sum rK116 ⟨26, by decide⟩ e heK h T116_26 hfix116_26 hinj116_26 hcardT116_26
    (fun i => conj_mem_of_fixedPoints (reps ⟨26, by decide⟩) (reps rK116) (T116_26 i) (hfix116_26 i) h)

/-! ## Cell (116, 27): |T| = 5 -/

def T116_27list : List Coordinates := [(0,0,0,0,0), (1,0,0,0,0), (2,0,0,0,0), (3,0,0,0,0), (4,0,0,0,0)]
def T116_27 : Fin 5 → Coordinate 1 := fun i => T116_27list.getD i.val (0,0,0,0,0)

theorem hfix116_27 : ∀ i, ((T116_27 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116) :=
  repsFix_of_siftB rK116 ⟨27, by decide⟩ T116_27 (by decide)

theorem hinj116_27 : Function.Injective
    (fun i => ((T116_27 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)) :=
  repsInj_of_reduceAux rK116 T116_27 (by decide)

theorem hcardT116_27 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK116 ⟨27, by decide⟩ R116 hpxR116 hcardq116 (by decide)).symm

/-- **Cell (116, 27).** -/
theorem cell116_27 (e : List (ZMod 25)) (heK : charOK (basisAt rK116) e = true)
    (h : ↥(reps (⟨27, by decide⟩ : Fin 148))) :
    species (reps (⟨27, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK116 e (h : Coordinate 1) T116_27 i :=
  species_entry_eq_sum rK116 ⟨27, by decide⟩ e heK h T116_27 hfix116_27 hinj116_27 hcardT116_27
    (fun i => conj_mem_of_fixedPoints (reps ⟨27, by decide⟩) (reps rK116) (T116_27 i) (hfix116_27 i) h)

/-! ## Cell (116, 28): |T| = 5 -/

def T116_28list : List Coordinates := [(0,0,0,0,0), (1,0,0,0,0), (2,0,0,0,0), (3,0,0,0,0), (4,0,0,0,0)]
def T116_28 : Fin 5 → Coordinate 1 := fun i => T116_28list.getD i.val (0,0,0,0,0)

theorem hfix116_28 : ∀ i, ((T116_28 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116) :=
  repsFix_of_siftB rK116 ⟨28, by decide⟩ T116_28 (by decide)

theorem hinj116_28 : Function.Injective
    (fun i => ((T116_28 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)) :=
  repsInj_of_reduceAux rK116 T116_28 (by decide)

theorem hcardT116_28 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK116 ⟨28, by decide⟩ R116 hpxR116 hcardq116 (by decide)).symm

/-- **Cell (116, 28).** -/
theorem cell116_28 (e : List (ZMod 25)) (heK : charOK (basisAt rK116) e = true)
    (h : ↥(reps (⟨28, by decide⟩ : Fin 148))) :
    species (reps (⟨28, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK116 e (h : Coordinate 1) T116_28 i :=
  species_entry_eq_sum rK116 ⟨28, by decide⟩ e heK h T116_28 hfix116_28 hinj116_28 hcardT116_28
    (fun i => conj_mem_of_fixedPoints (reps ⟨28, by decide⟩) (reps rK116) (T116_28 i) (hfix116_28 i) h)

/-! ## Cell (116, 33): |T| = 5 -/

def T116_33list : List Coordinates := [(0,0,0,0,0), (1,0,0,0,0), (2,0,0,0,0), (3,0,0,0,0), (4,0,0,0,0)]
def T116_33 : Fin 5 → Coordinate 1 := fun i => T116_33list.getD i.val (0,0,0,0,0)

theorem hfix116_33 : ∀ i, ((T116_33 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116) :=
  repsFix_of_siftB rK116 ⟨33, by decide⟩ T116_33 (by decide)

theorem hinj116_33 : Function.Injective
    (fun i => ((T116_33 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)) :=
  repsInj_of_reduceAux rK116 T116_33 (by decide)

theorem hcardT116_33 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK116 ⟨33, by decide⟩ R116 hpxR116 hcardq116 (by decide)).symm

/-- **Cell (116, 33).** -/
theorem cell116_33 (e : List (ZMod 25)) (heK : charOK (basisAt rK116) e = true)
    (h : ↥(reps (⟨33, by decide⟩ : Fin 148))) :
    species (reps (⟨33, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK116 e (h : Coordinate 1) T116_33 i :=
  species_entry_eq_sum rK116 ⟨33, by decide⟩ e heK h T116_33 hfix116_33 hinj116_33 hcardT116_33
    (fun i => conj_mem_of_fixedPoints (reps ⟨33, by decide⟩) (reps rK116) (T116_33 i) (hfix116_33 i) h)

/-! ## Cell (116, 38): |T| = 5 -/

def T116_38list : List Coordinates := [(0,0,0,0,0), (1,0,0,0,0), (2,0,0,0,0), (3,0,0,0,0), (4,0,0,0,0)]
def T116_38 : Fin 5 → Coordinate 1 := fun i => T116_38list.getD i.val (0,0,0,0,0)

theorem hfix116_38 : ∀ i, ((T116_38 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116) :=
  repsFix_of_siftB rK116 ⟨38, by decide⟩ T116_38 (by decide)

theorem hinj116_38 : Function.Injective
    (fun i => ((T116_38 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)) :=
  repsInj_of_reduceAux rK116 T116_38 (by decide)

theorem hcardT116_38 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK116 ⟨38, by decide⟩ R116 hpxR116 hcardq116 (by decide)).symm

/-- **Cell (116, 38).** -/
theorem cell116_38 (e : List (ZMod 25)) (heK : charOK (basisAt rK116) e = true)
    (h : ↥(reps (⟨38, by decide⟩ : Fin 148))) :
    species (reps (⟨38, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK116 e (h : Coordinate 1) T116_38 i :=
  species_entry_eq_sum rK116 ⟨38, by decide⟩ e heK h T116_38 hfix116_38 hinj116_38 hcardT116_38
    (fun i => conj_mem_of_fixedPoints (reps ⟨38, by decide⟩) (reps rK116) (T116_38 i) (hfix116_38 i) h)

/-! ## Cell (116, 43): |T| = 5 -/

def T116_43list : List Coordinates := [(0,0,0,0,0), (1,0,0,0,0), (2,0,0,0,0), (3,0,0,0,0), (4,0,0,0,0)]
def T116_43 : Fin 5 → Coordinate 1 := fun i => T116_43list.getD i.val (0,0,0,0,0)

theorem hfix116_43 : ∀ i, ((T116_43 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116) :=
  repsFix_of_siftB rK116 ⟨43, by decide⟩ T116_43 (by decide)

theorem hinj116_43 : Function.Injective
    (fun i => ((T116_43 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)) :=
  repsInj_of_reduceAux rK116 T116_43 (by decide)

theorem hcardT116_43 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK116 ⟨43, by decide⟩ R116 hpxR116 hcardq116 (by decide)).symm

/-- **Cell (116, 43).** -/
theorem cell116_43 (e : List (ZMod 25)) (heK : charOK (basisAt rK116) e = true)
    (h : ↥(reps (⟨43, by decide⟩ : Fin 148))) :
    species (reps (⟨43, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK116 e (h : Coordinate 1) T116_43 i :=
  species_entry_eq_sum rK116 ⟨43, by decide⟩ e heK h T116_43 hfix116_43 hinj116_43 hcardT116_43
    (fun i => conj_mem_of_fixedPoints (reps ⟨43, by decide⟩) (reps rK116) (T116_43 i) (hfix116_43 i) h)

/-! ## Cell (116, 48): |T| = 5 -/

def T116_48list : List Coordinates := [(0,0,0,0,0), (1,0,0,0,0), (2,0,0,0,0), (3,0,0,0,0), (4,0,0,0,0)]
def T116_48 : Fin 5 → Coordinate 1 := fun i => T116_48list.getD i.val (0,0,0,0,0)

theorem hfix116_48 : ∀ i, ((T116_48 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116) :=
  repsFix_of_siftB rK116 ⟨48, by decide⟩ T116_48 (by decide)

theorem hinj116_48 : Function.Injective
    (fun i => ((T116_48 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)) :=
  repsInj_of_reduceAux rK116 T116_48 (by decide)

theorem hcardT116_48 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK116 ⟨48, by decide⟩ R116 hpxR116 hcardq116 (by decide)).symm

/-- **Cell (116, 48).** -/
theorem cell116_48 (e : List (ZMod 25)) (heK : charOK (basisAt rK116) e = true)
    (h : ↥(reps (⟨48, by decide⟩ : Fin 148))) :
    species (reps (⟨48, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK116 e (h : Coordinate 1) T116_48 i :=
  species_entry_eq_sum rK116 ⟨48, by decide⟩ e heK h T116_48 hfix116_48 hinj116_48 hcardT116_48
    (fun i => conj_mem_of_fixedPoints (reps ⟨48, by decide⟩) (reps rK116) (T116_48 i) (hfix116_48 i) h)

/-! ## Cell (116, 53): |T| = 5 -/

def T116_53list : List Coordinates := [(0,0,0,0,0), (1,0,0,0,0), (2,0,0,0,0), (3,0,0,0,0), (4,0,0,0,0)]
def T116_53 : Fin 5 → Coordinate 1 := fun i => T116_53list.getD i.val (0,0,0,0,0)

theorem hfix116_53 : ∀ i, ((T116_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116) :=
  repsFix_of_siftB rK116 ⟨53, by decide⟩ T116_53 (by decide)

theorem hinj116_53 : Function.Injective
    (fun i => ((T116_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)) :=
  repsInj_of_reduceAux rK116 T116_53 (by decide)

theorem hcardT116_53 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK116 ⟨53, by decide⟩ R116 hpxR116 hcardq116 (by decide)).symm

/-- **Cell (116, 53).** -/
theorem cell116_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK116) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK116 e (h : Coordinate 1) T116_53 i :=
  species_entry_eq_sum rK116 ⟨53, by decide⟩ e heK h T116_53 hfix116_53 hinj116_53 hcardT116_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK116) (T116_53 i) (hfix116_53 i) h)

/-! ## Cell (116, 55): |T| = 5 -/

def T116_55list : List Coordinates := [(0,0,0,0,0), (1,0,0,0,0), (2,0,0,0,0), (3,0,0,0,0), (4,0,0,0,0)]
def T116_55 : Fin 5 → Coordinate 1 := fun i => T116_55list.getD i.val (0,0,0,0,0)

theorem hfix116_55 : ∀ i, ((T116_55 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116) :=
  repsFix_of_siftB rK116 ⟨55, by decide⟩ T116_55 (by decide)

theorem hinj116_55 : Function.Injective
    (fun i => ((T116_55 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)) :=
  repsInj_of_reduceAux rK116 T116_55 (by decide)

theorem hcardT116_55 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK116 ⟨55, by decide⟩ R116 hpxR116 hcardq116 (by decide)).symm

/-- **Cell (116, 55).** -/
theorem cell116_55 (e : List (ZMod 25)) (heK : charOK (basisAt rK116) e = true)
    (h : ↥(reps (⟨55, by decide⟩ : Fin 148))) :
    species (reps (⟨55, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK116 e (h : Coordinate 1) T116_55 i :=
  species_entry_eq_sum rK116 ⟨55, by decide⟩ e heK h T116_55 hfix116_55 hinj116_55 hcardT116_55
    (fun i => conj_mem_of_fixedPoints (reps ⟨55, by decide⟩) (reps rK116) (T116_55 i) (hfix116_55 i) h)

/-! ## Cell (116, 56): |T| = 5 -/

def T116_56list : List Coordinates := [(0,0,0,0,0), (1,0,0,0,0), (2,0,0,0,0), (3,0,0,0,0), (4,0,0,0,0)]
def T116_56 : Fin 5 → Coordinate 1 := fun i => T116_56list.getD i.val (0,0,0,0,0)

theorem hfix116_56 : ∀ i, ((T116_56 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116) :=
  repsFix_of_siftB rK116 ⟨56, by decide⟩ T116_56 (by decide)

theorem hinj116_56 : Function.Injective
    (fun i => ((T116_56 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)) :=
  repsInj_of_reduceAux rK116 T116_56 (by decide)

theorem hcardT116_56 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK116 ⟨56, by decide⟩ R116 hpxR116 hcardq116 (by decide)).symm

/-- **Cell (116, 56).** -/
theorem cell116_56 (e : List (ZMod 25)) (heK : charOK (basisAt rK116) e = true)
    (h : ↥(reps (⟨56, by decide⟩ : Fin 148))) :
    species (reps (⟨56, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK116 e (h : Coordinate 1) T116_56 i :=
  species_entry_eq_sum rK116 ⟨56, by decide⟩ e heK h T116_56 hfix116_56 hinj116_56 hcardT116_56
    (fun i => conj_mem_of_fixedPoints (reps ⟨56, by decide⟩) (reps rK116) (T116_56 i) (hfix116_56 i) h)

/-! ## Cell (116, 57): |T| = 5 -/

def T116_57list : List Coordinates := [(0,0,0,0,0), (1,0,0,0,0), (2,0,0,0,0), (3,0,0,0,0), (4,0,0,0,0)]
def T116_57 : Fin 5 → Coordinate 1 := fun i => T116_57list.getD i.val (0,0,0,0,0)

theorem hfix116_57 : ∀ i, ((T116_57 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116) :=
  repsFix_of_siftB rK116 ⟨57, by decide⟩ T116_57 (by decide)

theorem hinj116_57 : Function.Injective
    (fun i => ((T116_57 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)) :=
  repsInj_of_reduceAux rK116 T116_57 (by decide)

theorem hcardT116_57 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK116 ⟨57, by decide⟩ R116 hpxR116 hcardq116 (by decide)).symm

/-- **Cell (116, 57).** -/
theorem cell116_57 (e : List (ZMod 25)) (heK : charOK (basisAt rK116) e = true)
    (h : ↥(reps (⟨57, by decide⟩ : Fin 148))) :
    species (reps (⟨57, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK116 e (h : Coordinate 1) T116_57 i :=
  species_entry_eq_sum rK116 ⟨57, by decide⟩ e heK h T116_57 hfix116_57 hinj116_57 hcardT116_57
    (fun i => conj_mem_of_fixedPoints (reps ⟨57, by decide⟩) (reps rK116) (T116_57 i) (hfix116_57 i) h)

/-! ## Cell (116, 58): |T| = 5 -/

def T116_58list : List Coordinates := [(0,0,0,0,0), (1,0,0,0,0), (2,0,0,0,0), (3,0,0,0,0), (4,0,0,0,0)]
def T116_58 : Fin 5 → Coordinate 1 := fun i => T116_58list.getD i.val (0,0,0,0,0)

theorem hfix116_58 : ∀ i, ((T116_58 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116) :=
  repsFix_of_siftB rK116 ⟨58, by decide⟩ T116_58 (by decide)

theorem hinj116_58 : Function.Injective
    (fun i => ((T116_58 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)) :=
  repsInj_of_reduceAux rK116 T116_58 (by decide)

theorem hcardT116_58 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK116 ⟨58, by decide⟩ R116 hpxR116 hcardq116 (by decide)).symm

/-- **Cell (116, 58).** -/
theorem cell116_58 (e : List (ZMod 25)) (heK : charOK (basisAt rK116) e = true)
    (h : ↥(reps (⟨58, by decide⟩ : Fin 148))) :
    species (reps (⟨58, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK116 e (h : Coordinate 1) T116_58 i :=
  species_entry_eq_sum rK116 ⟨58, by decide⟩ e heK h T116_58 hfix116_58 hinj116_58 hcardT116_58
    (fun i => conj_mem_of_fixedPoints (reps ⟨58, by decide⟩) (reps rK116) (T116_58 i) (hfix116_58 i) h)

/-! ## Cell (116, 59): |T| = 5 -/

def T116_59list : List Coordinates := [(0,0,0,0,0), (1,0,0,0,0), (2,0,0,0,0), (3,0,0,0,0), (4,0,0,0,0)]
def T116_59 : Fin 5 → Coordinate 1 := fun i => T116_59list.getD i.val (0,0,0,0,0)

theorem hfix116_59 : ∀ i, ((T116_59 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116) :=
  repsFix_of_siftB rK116 ⟨59, by decide⟩ T116_59 (by decide)

theorem hinj116_59 : Function.Injective
    (fun i => ((T116_59 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)) :=
  repsInj_of_reduceAux rK116 T116_59 (by decide)

theorem hcardT116_59 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK116 ⟨59, by decide⟩ R116 hpxR116 hcardq116 (by decide)).symm

/-- **Cell (116, 59).** -/
theorem cell116_59 (e : List (ZMod 25)) (heK : charOK (basisAt rK116) e = true)
    (h : ↥(reps (⟨59, by decide⟩ : Fin 148))) :
    species (reps (⟨59, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK116 e (h : Coordinate 1) T116_59 i :=
  species_entry_eq_sum rK116 ⟨59, by decide⟩ e heK h T116_59 hfix116_59 hinj116_59 hcardT116_59
    (fun i => conj_mem_of_fixedPoints (reps ⟨59, by decide⟩) (reps rK116) (T116_59 i) (hfix116_59 i) h)

/-! ## Cell (116, 80): |T| = 5 -/

def T116_80list : List Coordinates := [(0,0,0,0,0), (1,0,0,0,0), (2,0,0,0,0), (3,0,0,0,0), (4,0,0,0,0)]
def T116_80 : Fin 5 → Coordinate 1 := fun i => T116_80list.getD i.val (0,0,0,0,0)

theorem hfix116_80 : ∀ i, ((T116_80 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116) :=
  repsFix_of_siftB rK116 ⟨80, by decide⟩ T116_80 (by decide)

theorem hinj116_80 : Function.Injective
    (fun i => ((T116_80 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)) :=
  repsInj_of_reduceAux rK116 T116_80 (by decide)

theorem hcardT116_80 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK116 ⟨80, by decide⟩ R116 hpxR116 hcardq116 (by decide)).symm

/-- **Cell (116, 80).** -/
theorem cell116_80 (e : List (ZMod 25)) (heK : charOK (basisAt rK116) e = true)
    (h : ↥(reps (⟨80, by decide⟩ : Fin 148))) :
    species (reps (⟨80, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK116 e (h : Coordinate 1) T116_80 i :=
  species_entry_eq_sum rK116 ⟨80, by decide⟩ e heK h T116_80 hfix116_80 hinj116_80 hcardT116_80
    (fun i => conj_mem_of_fixedPoints (reps ⟨80, by decide⟩) (reps rK116) (T116_80 i) (hfix116_80 i) h)

/-! ## Cell (116, 90): |T| = 5 -/

def T116_90list : List Coordinates := [(0,0,0,0,0), (1,0,0,0,0), (2,0,0,0,0), (3,0,0,0,0), (4,0,0,0,0)]
def T116_90 : Fin 5 → Coordinate 1 := fun i => T116_90list.getD i.val (0,0,0,0,0)

theorem hfix116_90 : ∀ i, ((T116_90 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116) :=
  repsFix_of_siftB rK116 ⟨90, by decide⟩ T116_90 (by decide)

theorem hinj116_90 : Function.Injective
    (fun i => ((T116_90 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)) :=
  repsInj_of_reduceAux rK116 T116_90 (by decide)

theorem hcardT116_90 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK116 ⟨90, by decide⟩ R116 hpxR116 hcardq116 (by decide)).symm

/-- **Cell (116, 90).** -/
theorem cell116_90 (e : List (ZMod 25)) (heK : charOK (basisAt rK116) e = true)
    (h : ↥(reps (⟨90, by decide⟩ : Fin 148))) :
    species (reps (⟨90, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK116 e (h : Coordinate 1) T116_90 i :=
  species_entry_eq_sum rK116 ⟨90, by decide⟩ e heK h T116_90 hfix116_90 hinj116_90 hcardT116_90
    (fun i => conj_mem_of_fixedPoints (reps ⟨90, by decide⟩) (reps rK116) (T116_90 i) (hfix116_90 i) h)

/-! ## Cell (116, 95): |T| = 5 -/

def T116_95list : List Coordinates := [(0,0,0,0,0), (1,0,0,0,0), (2,0,0,0,0), (3,0,0,0,0), (4,0,0,0,0)]
def T116_95 : Fin 5 → Coordinate 1 := fun i => T116_95list.getD i.val (0,0,0,0,0)

theorem hfix116_95 : ∀ i, ((T116_95 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116) :=
  repsFix_of_siftB rK116 ⟨95, by decide⟩ T116_95 (by decide)

theorem hinj116_95 : Function.Injective
    (fun i => ((T116_95 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)) :=
  repsInj_of_reduceAux rK116 T116_95 (by decide)

theorem hcardT116_95 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK116 ⟨95, by decide⟩ R116 hpxR116 hcardq116 (by decide)).symm

/-- **Cell (116, 95).** -/
theorem cell116_95 (e : List (ZMod 25)) (heK : charOK (basisAt rK116) e = true)
    (h : ↥(reps (⟨95, by decide⟩ : Fin 148))) :
    species (reps (⟨95, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK116 e (h : Coordinate 1) T116_95 i :=
  species_entry_eq_sum rK116 ⟨95, by decide⟩ e heK h T116_95 hfix116_95 hinj116_95 hcardT116_95
    (fun i => conj_mem_of_fixedPoints (reps ⟨95, by decide⟩) (reps rK116) (T116_95 i) (hfix116_95 i) h)

/-! ## Cell (116, 100): |T| = 5 -/

def T116_100list : List Coordinates := [(0,0,0,0,0), (1,0,0,0,0), (2,0,0,0,0), (3,0,0,0,0), (4,0,0,0,0)]
def T116_100 : Fin 5 → Coordinate 1 := fun i => T116_100list.getD i.val (0,0,0,0,0)

theorem hfix116_100 : ∀ i, ((T116_100 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116) :=
  repsFix_of_siftB rK116 ⟨100, by decide⟩ T116_100 (by decide)

theorem hinj116_100 : Function.Injective
    (fun i => ((T116_100 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)) :=
  repsInj_of_reduceAux rK116 T116_100 (by decide)

theorem hcardT116_100 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK116 ⟨100, by decide⟩ R116 hpxR116 hcardq116 (by decide)).symm

/-- **Cell (116, 100).** -/
theorem cell116_100 (e : List (ZMod 25)) (heK : charOK (basisAt rK116) e = true)
    (h : ↥(reps (⟨100, by decide⟩ : Fin 148))) :
    species (reps (⟨100, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK116 e (h : Coordinate 1) T116_100 i :=
  species_entry_eq_sum rK116 ⟨100, by decide⟩ e heK h T116_100 hfix116_100 hinj116_100 hcardT116_100
    (fun i => conj_mem_of_fixedPoints (reps ⟨100, by decide⟩) (reps rK116) (T116_100 i) (hfix116_100 i) h)

/-! ## Cell (116, 105): |T| = 5 -/

def T116_105list : List Coordinates := [(0,0,0,0,0), (1,0,0,0,0), (2,0,0,0,0), (3,0,0,0,0), (4,0,0,0,0)]
def T116_105 : Fin 5 → Coordinate 1 := fun i => T116_105list.getD i.val (0,0,0,0,0)

theorem hfix116_105 : ∀ i, ((T116_105 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116) :=
  repsFix_of_siftB rK116 ⟨105, by decide⟩ T116_105 (by decide)

theorem hinj116_105 : Function.Injective
    (fun i => ((T116_105 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)) :=
  repsInj_of_reduceAux rK116 T116_105 (by decide)

theorem hcardT116_105 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK116 ⟨105, by decide⟩ R116 hpxR116 hcardq116 (by decide)).symm

/-- **Cell (116, 105).** -/
theorem cell116_105 (e : List (ZMod 25)) (heK : charOK (basisAt rK116) e = true)
    (h : ↥(reps (⟨105, by decide⟩ : Fin 148))) :
    species (reps (⟨105, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK116 e (h : Coordinate 1) T116_105 i :=
  species_entry_eq_sum rK116 ⟨105, by decide⟩ e heK h T116_105 hfix116_105 hinj116_105 hcardT116_105
    (fun i => conj_mem_of_fixedPoints (reps ⟨105, by decide⟩) (reps rK116) (T116_105 i) (hfix116_105 i) h)

/-! ## Cell (116, 110): |T| = 5 -/

def T116_110list : List Coordinates := [(0,0,0,0,0), (1,0,0,0,0), (2,0,0,0,0), (3,0,0,0,0), (4,0,0,0,0)]
def T116_110 : Fin 5 → Coordinate 1 := fun i => T116_110list.getD i.val (0,0,0,0,0)

theorem hfix116_110 : ∀ i, ((T116_110 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116) :=
  repsFix_of_siftB rK116 ⟨110, by decide⟩ T116_110 (by decide)

theorem hinj116_110 : Function.Injective
    (fun i => ((T116_110 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)) :=
  repsInj_of_reduceAux rK116 T116_110 (by decide)

theorem hcardT116_110 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK116 ⟨110, by decide⟩ R116 hpxR116 hcardq116 (by decide)).symm

/-- **Cell (116, 110).** -/
theorem cell116_110 (e : List (ZMod 25)) (heK : charOK (basisAt rK116) e = true)
    (h : ↥(reps (⟨110, by decide⟩ : Fin 148))) :
    species (reps (⟨110, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK116 e (h : Coordinate 1) T116_110 i :=
  species_entry_eq_sum rK116 ⟨110, by decide⟩ e heK h T116_110 hfix116_110 hinj116_110 hcardT116_110
    (fun i => conj_mem_of_fixedPoints (reps ⟨110, by decide⟩) (reps rK116) (T116_110 i) (hfix116_110 i) h)

/-! ## Cell (116, 116): |T| = 5 -/

def T116_116list : List Coordinates := [(0,0,0,0,0), (1,0,0,0,0), (2,0,0,0,0), (3,0,0,0,0), (4,0,0,0,0)]
def T116_116 : Fin 5 → Coordinate 1 := fun i => T116_116list.getD i.val (0,0,0,0,0)

theorem hfix116_116 : ∀ i, ((T116_116 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116) :=
  repsFix_of_siftB rK116 ⟨116, by decide⟩ T116_116 (by decide)

theorem hinj116_116 : Function.Injective
    (fun i => ((T116_116 i : Coordinate 1) : Coordinate 1 ⧸ reps rK116)) :=
  repsInj_of_reduceAux rK116 T116_116 (by decide)

theorem hcardT116_116 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK116 ⟨116, by decide⟩ R116 hpxR116 hcardq116 (by decide)).symm

/-- **Cell (116, 116).** -/
theorem cell116_116 (e : List (ZMod 25)) (heK : charOK (basisAt rK116) e = true)
    (h : ↥(reps (⟨116, by decide⟩ : Fin 148))) :
    species (reps (⟨116, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK116 e (h : Coordinate 1) T116_116 i :=
  species_entry_eq_sum rK116 ⟨116, by decide⟩ e heK h T116_116 hfix116_116 hinj116_116 hcardT116_116
    (fun i => conj_mem_of_fixedPoints (reps ⟨116, by decide⟩) (reps rK116) (T116_116 i) (hfix116_116 i) h)

namespace Q2

def R116_2 : Fin 5 → Coordinate 2 := fun i => R116list.getD i.val (0,0,0,0,0)
theorem hpxR116_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK116) (R116_2 i)) := by decide
theorem hcardq116_2 : Nat.card (Coordinate 2 ⧸ reps rK116) = 5 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (116, 0) twin -/

def T116_0_2 : Fin 5 → Coordinate 2 := fun i => T116_0list.getD i.val (0,0,0,0,0)

theorem hfix116_0_2 : ∀ i, ((T116_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116) :=
  repsFix_of_siftB2 rK116 ⟨0, by decide⟩ T116_0_2 (by decide)

theorem hinj116_0_2 : Function.Injective
    (fun i => ((T116_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)) :=
  repsInj_of_reduceAux2 rK116 T116_0_2 (by decide)

theorem hcardT116_0_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK116 ⟨0, by decide⟩ R116_2 hpxR116_2 hcardq116_2 (by decide)).symm

/-- **Cell (116, 0) twin (q=2).** -/
theorem cell116_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK116) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec2 rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK116 e (h : Coordinate 2) T116_0_2 i :=
  species_entry_eq_sum rK116 ⟨0, by decide⟩ e heK h T116_0_2 hfix116_0_2 hinj116_0_2 hcardT116_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK116) (T116_0_2 i) (hfix116_0_2 i) h)

/-! ### Cell (116, 1) twin -/

def T116_1_2 : Fin 5 → Coordinate 2 := fun i => T116_1list.getD i.val (0,0,0,0,0)

theorem hfix116_1_2 : ∀ i, ((T116_1_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116) :=
  repsFix_of_siftB2 rK116 ⟨1, by decide⟩ T116_1_2 (by decide)

theorem hinj116_1_2 : Function.Injective
    (fun i => ((T116_1_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)) :=
  repsInj_of_reduceAux2 rK116 T116_1_2 (by decide)

theorem hcardT116_1_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK116 ⟨1, by decide⟩ R116_2 hpxR116_2 hcardq116_2 (by decide)).symm

/-- **Cell (116, 1) twin (q=2).** -/
theorem cell116_1_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK116) e = true)
    (h : ↥(reps (⟨1, by decide⟩ : Fin 148))) :
    species (reps (⟨1, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec2 rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK116 e (h : Coordinate 2) T116_1_2 i :=
  species_entry_eq_sum rK116 ⟨1, by decide⟩ e heK h T116_1_2 hfix116_1_2 hinj116_1_2 hcardT116_1_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨1, by decide⟩) (reps rK116) (T116_1_2 i) (hfix116_1_2 i) h)

/-! ### Cell (116, 6) twin -/

def T116_6_2 : Fin 5 → Coordinate 2 := fun i => T116_6list.getD i.val (0,0,0,0,0)

theorem hfix116_6_2 : ∀ i, ((T116_6_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116) :=
  repsFix_of_siftB2 rK116 ⟨6, by decide⟩ T116_6_2 (by decide)

theorem hinj116_6_2 : Function.Injective
    (fun i => ((T116_6_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)) :=
  repsInj_of_reduceAux2 rK116 T116_6_2 (by decide)

theorem hcardT116_6_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK116 ⟨6, by decide⟩ R116_2 hpxR116_2 hcardq116_2 (by decide)).symm

/-- **Cell (116, 6) twin (q=2).** -/
theorem cell116_6_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK116) e = true)
    (h : ↥(reps (⟨6, by decide⟩ : Fin 148))) :
    species (reps (⟨6, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec2 rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK116 e (h : Coordinate 2) T116_6_2 i :=
  species_entry_eq_sum rK116 ⟨6, by decide⟩ e heK h T116_6_2 hfix116_6_2 hinj116_6_2 hcardT116_6_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨6, by decide⟩) (reps rK116) (T116_6_2 i) (hfix116_6_2 i) h)

/-! ### Cell (116, 7) twin -/

def T116_7_2 : Fin 5 → Coordinate 2 := fun i => T116_7list.getD i.val (0,0,0,0,0)

theorem hfix116_7_2 : ∀ i, ((T116_7_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116) :=
  repsFix_of_siftB2 rK116 ⟨7, by decide⟩ T116_7_2 (by decide)

theorem hinj116_7_2 : Function.Injective
    (fun i => ((T116_7_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)) :=
  repsInj_of_reduceAux2 rK116 T116_7_2 (by decide)

theorem hcardT116_7_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK116 ⟨7, by decide⟩ R116_2 hpxR116_2 hcardq116_2 (by decide)).symm

/-- **Cell (116, 7) twin (q=2).** -/
theorem cell116_7_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK116) e = true)
    (h : ↥(reps (⟨7, by decide⟩ : Fin 148))) :
    species (reps (⟨7, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec2 rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK116 e (h : Coordinate 2) T116_7_2 i :=
  species_entry_eq_sum rK116 ⟨7, by decide⟩ e heK h T116_7_2 hfix116_7_2 hinj116_7_2 hcardT116_7_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨7, by decide⟩) (reps rK116) (T116_7_2 i) (hfix116_7_2 i) h)

/-! ### Cell (116, 8) twin -/

def T116_8_2 : Fin 5 → Coordinate 2 := fun i => T116_8list.getD i.val (0,0,0,0,0)

theorem hfix116_8_2 : ∀ i, ((T116_8_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116) :=
  repsFix_of_siftB2 rK116 ⟨8, by decide⟩ T116_8_2 (by decide)

theorem hinj116_8_2 : Function.Injective
    (fun i => ((T116_8_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)) :=
  repsInj_of_reduceAux2 rK116 T116_8_2 (by decide)

theorem hcardT116_8_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK116 ⟨8, by decide⟩ R116_2 hpxR116_2 hcardq116_2 (by decide)).symm

/-- **Cell (116, 8) twin (q=2).** -/
theorem cell116_8_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK116) e = true)
    (h : ↥(reps (⟨8, by decide⟩ : Fin 148))) :
    species (reps (⟨8, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec2 rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK116 e (h : Coordinate 2) T116_8_2 i :=
  species_entry_eq_sum rK116 ⟨8, by decide⟩ e heK h T116_8_2 hfix116_8_2 hinj116_8_2 hcardT116_8_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨8, by decide⟩) (reps rK116) (T116_8_2 i) (hfix116_8_2 i) h)

/-! ### Cell (116, 9) twin -/

def T116_9_2 : Fin 5 → Coordinate 2 := fun i => T116_9list.getD i.val (0,0,0,0,0)

theorem hfix116_9_2 : ∀ i, ((T116_9_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116) :=
  repsFix_of_siftB2 rK116 ⟨9, by decide⟩ T116_9_2 (by decide)

theorem hinj116_9_2 : Function.Injective
    (fun i => ((T116_9_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)) :=
  repsInj_of_reduceAux2 rK116 T116_9_2 (by decide)

theorem hcardT116_9_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK116 ⟨9, by decide⟩ R116_2 hpxR116_2 hcardq116_2 (by decide)).symm

/-- **Cell (116, 9) twin (q=2).** -/
theorem cell116_9_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK116) e = true)
    (h : ↥(reps (⟨9, by decide⟩ : Fin 148))) :
    species (reps (⟨9, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec2 rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK116 e (h : Coordinate 2) T116_9_2 i :=
  species_entry_eq_sum rK116 ⟨9, by decide⟩ e heK h T116_9_2 hfix116_9_2 hinj116_9_2 hcardT116_9_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨9, by decide⟩) (reps rK116) (T116_9_2 i) (hfix116_9_2 i) h)

/-! ### Cell (116, 10) twin -/

def T116_10_2 : Fin 5 → Coordinate 2 := fun i => T116_10list.getD i.val (0,0,0,0,0)

theorem hfix116_10_2 : ∀ i, ((T116_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116) :=
  repsFix_of_siftB2 rK116 ⟨10, by decide⟩ T116_10_2 (by decide)

theorem hinj116_10_2 : Function.Injective
    (fun i => ((T116_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)) :=
  repsInj_of_reduceAux2 rK116 T116_10_2 (by decide)

theorem hcardT116_10_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK116 ⟨10, by decide⟩ R116_2 hpxR116_2 hcardq116_2 (by decide)).symm

/-- **Cell (116, 10) twin (q=2).** -/
theorem cell116_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK116) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec2 rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK116 e (h : Coordinate 2) T116_10_2 i :=
  species_entry_eq_sum rK116 ⟨10, by decide⟩ e heK h T116_10_2 hfix116_10_2 hinj116_10_2 hcardT116_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK116) (T116_10_2 i) (hfix116_10_2 i) h)

/-! ### Cell (116, 12) twin -/

def T116_12_2 : Fin 5 → Coordinate 2 := fun i => T116_12list.getD i.val (0,0,0,0,0)

theorem hfix116_12_2 : ∀ i, ((T116_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116) :=
  repsFix_of_siftB2 rK116 ⟨12, by decide⟩ T116_12_2 (by decide)

theorem hinj116_12_2 : Function.Injective
    (fun i => ((T116_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)) :=
  repsInj_of_reduceAux2 rK116 T116_12_2 (by decide)

theorem hcardT116_12_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK116 ⟨12, by decide⟩ R116_2 hpxR116_2 hcardq116_2 (by decide)).symm

/-- **Cell (116, 12) twin (q=2).** -/
theorem cell116_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK116) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec2 rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK116 e (h : Coordinate 2) T116_12_2 i :=
  species_entry_eq_sum rK116 ⟨12, by decide⟩ e heK h T116_12_2 hfix116_12_2 hinj116_12_2 hcardT116_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK116) (T116_12_2 i) (hfix116_12_2 i) h)

/-! ### Cell (116, 13) twin -/

def T116_13_2 : Fin 5 → Coordinate 2 := fun i => T116_13list.getD i.val (0,0,0,0,0)

theorem hfix116_13_2 : ∀ i, ((T116_13_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116) :=
  repsFix_of_siftB2 rK116 ⟨13, by decide⟩ T116_13_2 (by decide)

theorem hinj116_13_2 : Function.Injective
    (fun i => ((T116_13_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)) :=
  repsInj_of_reduceAux2 rK116 T116_13_2 (by decide)

theorem hcardT116_13_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK116 ⟨13, by decide⟩ R116_2 hpxR116_2 hcardq116_2 (by decide)).symm

/-- **Cell (116, 13) twin (q=2).** -/
theorem cell116_13_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK116) e = true)
    (h : ↥(reps (⟨13, by decide⟩ : Fin 148))) :
    species (reps (⟨13, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec2 rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK116 e (h : Coordinate 2) T116_13_2 i :=
  species_entry_eq_sum rK116 ⟨13, by decide⟩ e heK h T116_13_2 hfix116_13_2 hinj116_13_2 hcardT116_13_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨13, by decide⟩) (reps rK116) (T116_13_2 i) (hfix116_13_2 i) h)

/-! ### Cell (116, 19) twin -/

def T116_19_2 : Fin 5 → Coordinate 2 := fun i => T116_19list.getD i.val (0,0,0,0,0)

theorem hfix116_19_2 : ∀ i, ((T116_19_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116) :=
  repsFix_of_siftB2 rK116 ⟨19, by decide⟩ T116_19_2 (by decide)

theorem hinj116_19_2 : Function.Injective
    (fun i => ((T116_19_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)) :=
  repsInj_of_reduceAux2 rK116 T116_19_2 (by decide)

theorem hcardT116_19_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK116 ⟨19, by decide⟩ R116_2 hpxR116_2 hcardq116_2 (by decide)).symm

/-- **Cell (116, 19) twin (q=2).** -/
theorem cell116_19_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK116) e = true)
    (h : ↥(reps (⟨19, by decide⟩ : Fin 148))) :
    species (reps (⟨19, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec2 rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK116 e (h : Coordinate 2) T116_19_2 i :=
  species_entry_eq_sum rK116 ⟨19, by decide⟩ e heK h T116_19_2 hfix116_19_2 hinj116_19_2 hcardT116_19_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨19, by decide⟩) (reps rK116) (T116_19_2 i) (hfix116_19_2 i) h)

/-! ### Cell (116, 24) twin -/

def T116_24_2 : Fin 5 → Coordinate 2 := fun i => T116_24list.getD i.val (0,0,0,0,0)

theorem hfix116_24_2 : ∀ i, ((T116_24_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116) :=
  repsFix_of_siftB2 rK116 ⟨24, by decide⟩ T116_24_2 (by decide)

theorem hinj116_24_2 : Function.Injective
    (fun i => ((T116_24_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)) :=
  repsInj_of_reduceAux2 rK116 T116_24_2 (by decide)

theorem hcardT116_24_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK116 ⟨24, by decide⟩ R116_2 hpxR116_2 hcardq116_2 (by decide)).symm

/-- **Cell (116, 24) twin (q=2).** -/
theorem cell116_24_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK116) e = true)
    (h : ↥(reps (⟨24, by decide⟩ : Fin 148))) :
    species (reps (⟨24, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec2 rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK116 e (h : Coordinate 2) T116_24_2 i :=
  species_entry_eq_sum rK116 ⟨24, by decide⟩ e heK h T116_24_2 hfix116_24_2 hinj116_24_2 hcardT116_24_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨24, by decide⟩) (reps rK116) (T116_24_2 i) (hfix116_24_2 i) h)

/-! ### Cell (116, 25) twin -/

def T116_25_2 : Fin 5 → Coordinate 2 := fun i => T116_25list.getD i.val (0,0,0,0,0)

theorem hfix116_25_2 : ∀ i, ((T116_25_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116) :=
  repsFix_of_siftB2 rK116 ⟨25, by decide⟩ T116_25_2 (by decide)

theorem hinj116_25_2 : Function.Injective
    (fun i => ((T116_25_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)) :=
  repsInj_of_reduceAux2 rK116 T116_25_2 (by decide)

theorem hcardT116_25_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK116 ⟨25, by decide⟩ R116_2 hpxR116_2 hcardq116_2 (by decide)).symm

/-- **Cell (116, 25) twin (q=2).** -/
theorem cell116_25_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK116) e = true)
    (h : ↥(reps (⟨25, by decide⟩ : Fin 148))) :
    species (reps (⟨25, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec2 rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK116 e (h : Coordinate 2) T116_25_2 i :=
  species_entry_eq_sum rK116 ⟨25, by decide⟩ e heK h T116_25_2 hfix116_25_2 hinj116_25_2 hcardT116_25_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨25, by decide⟩) (reps rK116) (T116_25_2 i) (hfix116_25_2 i) h)

/-! ### Cell (116, 26) twin -/

def T116_26_2 : Fin 5 → Coordinate 2 := fun i => T116_26list.getD i.val (0,0,0,0,0)

theorem hfix116_26_2 : ∀ i, ((T116_26_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116) :=
  repsFix_of_siftB2 rK116 ⟨26, by decide⟩ T116_26_2 (by decide)

theorem hinj116_26_2 : Function.Injective
    (fun i => ((T116_26_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)) :=
  repsInj_of_reduceAux2 rK116 T116_26_2 (by decide)

theorem hcardT116_26_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK116 ⟨26, by decide⟩ R116_2 hpxR116_2 hcardq116_2 (by decide)).symm

/-- **Cell (116, 26) twin (q=2).** -/
theorem cell116_26_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK116) e = true)
    (h : ↥(reps (⟨26, by decide⟩ : Fin 148))) :
    species (reps (⟨26, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec2 rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK116 e (h : Coordinate 2) T116_26_2 i :=
  species_entry_eq_sum rK116 ⟨26, by decide⟩ e heK h T116_26_2 hfix116_26_2 hinj116_26_2 hcardT116_26_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨26, by decide⟩) (reps rK116) (T116_26_2 i) (hfix116_26_2 i) h)

/-! ### Cell (116, 27) twin -/

def T116_27_2 : Fin 5 → Coordinate 2 := fun i => T116_27list.getD i.val (0,0,0,0,0)

theorem hfix116_27_2 : ∀ i, ((T116_27_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116) :=
  repsFix_of_siftB2 rK116 ⟨27, by decide⟩ T116_27_2 (by decide)

theorem hinj116_27_2 : Function.Injective
    (fun i => ((T116_27_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)) :=
  repsInj_of_reduceAux2 rK116 T116_27_2 (by decide)

theorem hcardT116_27_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK116 ⟨27, by decide⟩ R116_2 hpxR116_2 hcardq116_2 (by decide)).symm

/-- **Cell (116, 27) twin (q=2).** -/
theorem cell116_27_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK116) e = true)
    (h : ↥(reps (⟨27, by decide⟩ : Fin 148))) :
    species (reps (⟨27, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec2 rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK116 e (h : Coordinate 2) T116_27_2 i :=
  species_entry_eq_sum rK116 ⟨27, by decide⟩ e heK h T116_27_2 hfix116_27_2 hinj116_27_2 hcardT116_27_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨27, by decide⟩) (reps rK116) (T116_27_2 i) (hfix116_27_2 i) h)

/-! ### Cell (116, 28) twin -/

def T116_28_2 : Fin 5 → Coordinate 2 := fun i => T116_28list.getD i.val (0,0,0,0,0)

theorem hfix116_28_2 : ∀ i, ((T116_28_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116) :=
  repsFix_of_siftB2 rK116 ⟨28, by decide⟩ T116_28_2 (by decide)

theorem hinj116_28_2 : Function.Injective
    (fun i => ((T116_28_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)) :=
  repsInj_of_reduceAux2 rK116 T116_28_2 (by decide)

theorem hcardT116_28_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK116 ⟨28, by decide⟩ R116_2 hpxR116_2 hcardq116_2 (by decide)).symm

/-- **Cell (116, 28) twin (q=2).** -/
theorem cell116_28_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK116) e = true)
    (h : ↥(reps (⟨28, by decide⟩ : Fin 148))) :
    species (reps (⟨28, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec2 rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK116 e (h : Coordinate 2) T116_28_2 i :=
  species_entry_eq_sum rK116 ⟨28, by decide⟩ e heK h T116_28_2 hfix116_28_2 hinj116_28_2 hcardT116_28_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨28, by decide⟩) (reps rK116) (T116_28_2 i) (hfix116_28_2 i) h)

/-! ### Cell (116, 33) twin -/

def T116_33_2 : Fin 5 → Coordinate 2 := fun i => T116_33list.getD i.val (0,0,0,0,0)

theorem hfix116_33_2 : ∀ i, ((T116_33_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116) :=
  repsFix_of_siftB2 rK116 ⟨33, by decide⟩ T116_33_2 (by decide)

theorem hinj116_33_2 : Function.Injective
    (fun i => ((T116_33_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)) :=
  repsInj_of_reduceAux2 rK116 T116_33_2 (by decide)

theorem hcardT116_33_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK116 ⟨33, by decide⟩ R116_2 hpxR116_2 hcardq116_2 (by decide)).symm

/-- **Cell (116, 33) twin (q=2).** -/
theorem cell116_33_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK116) e = true)
    (h : ↥(reps (⟨33, by decide⟩ : Fin 148))) :
    species (reps (⟨33, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec2 rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK116 e (h : Coordinate 2) T116_33_2 i :=
  species_entry_eq_sum rK116 ⟨33, by decide⟩ e heK h T116_33_2 hfix116_33_2 hinj116_33_2 hcardT116_33_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨33, by decide⟩) (reps rK116) (T116_33_2 i) (hfix116_33_2 i) h)

/-! ### Cell (116, 38) twin -/

def T116_38_2 : Fin 5 → Coordinate 2 := fun i => T116_38list.getD i.val (0,0,0,0,0)

theorem hfix116_38_2 : ∀ i, ((T116_38_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116) :=
  repsFix_of_siftB2 rK116 ⟨38, by decide⟩ T116_38_2 (by decide)

theorem hinj116_38_2 : Function.Injective
    (fun i => ((T116_38_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)) :=
  repsInj_of_reduceAux2 rK116 T116_38_2 (by decide)

theorem hcardT116_38_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK116 ⟨38, by decide⟩ R116_2 hpxR116_2 hcardq116_2 (by decide)).symm

/-- **Cell (116, 38) twin (q=2).** -/
theorem cell116_38_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK116) e = true)
    (h : ↥(reps (⟨38, by decide⟩ : Fin 148))) :
    species (reps (⟨38, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec2 rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK116 e (h : Coordinate 2) T116_38_2 i :=
  species_entry_eq_sum rK116 ⟨38, by decide⟩ e heK h T116_38_2 hfix116_38_2 hinj116_38_2 hcardT116_38_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨38, by decide⟩) (reps rK116) (T116_38_2 i) (hfix116_38_2 i) h)

/-! ### Cell (116, 43) twin -/

def T116_43_2 : Fin 5 → Coordinate 2 := fun i => T116_43list.getD i.val (0,0,0,0,0)

theorem hfix116_43_2 : ∀ i, ((T116_43_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116) :=
  repsFix_of_siftB2 rK116 ⟨43, by decide⟩ T116_43_2 (by decide)

theorem hinj116_43_2 : Function.Injective
    (fun i => ((T116_43_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)) :=
  repsInj_of_reduceAux2 rK116 T116_43_2 (by decide)

theorem hcardT116_43_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK116 ⟨43, by decide⟩ R116_2 hpxR116_2 hcardq116_2 (by decide)).symm

/-- **Cell (116, 43) twin (q=2).** -/
theorem cell116_43_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK116) e = true)
    (h : ↥(reps (⟨43, by decide⟩ : Fin 148))) :
    species (reps (⟨43, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec2 rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK116 e (h : Coordinate 2) T116_43_2 i :=
  species_entry_eq_sum rK116 ⟨43, by decide⟩ e heK h T116_43_2 hfix116_43_2 hinj116_43_2 hcardT116_43_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨43, by decide⟩) (reps rK116) (T116_43_2 i) (hfix116_43_2 i) h)

/-! ### Cell (116, 48) twin -/

def T116_48_2 : Fin 5 → Coordinate 2 := fun i => T116_48list.getD i.val (0,0,0,0,0)

theorem hfix116_48_2 : ∀ i, ((T116_48_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116) :=
  repsFix_of_siftB2 rK116 ⟨48, by decide⟩ T116_48_2 (by decide)

theorem hinj116_48_2 : Function.Injective
    (fun i => ((T116_48_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)) :=
  repsInj_of_reduceAux2 rK116 T116_48_2 (by decide)

theorem hcardT116_48_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK116 ⟨48, by decide⟩ R116_2 hpxR116_2 hcardq116_2 (by decide)).symm

/-- **Cell (116, 48) twin (q=2).** -/
theorem cell116_48_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK116) e = true)
    (h : ↥(reps (⟨48, by decide⟩ : Fin 148))) :
    species (reps (⟨48, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec2 rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK116 e (h : Coordinate 2) T116_48_2 i :=
  species_entry_eq_sum rK116 ⟨48, by decide⟩ e heK h T116_48_2 hfix116_48_2 hinj116_48_2 hcardT116_48_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨48, by decide⟩) (reps rK116) (T116_48_2 i) (hfix116_48_2 i) h)

/-! ### Cell (116, 53) twin -/

def T116_53_2 : Fin 5 → Coordinate 2 := fun i => T116_53list.getD i.val (0,0,0,0,0)

theorem hfix116_53_2 : ∀ i, ((T116_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116) :=
  repsFix_of_siftB2 rK116 ⟨53, by decide⟩ T116_53_2 (by decide)

theorem hinj116_53_2 : Function.Injective
    (fun i => ((T116_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)) :=
  repsInj_of_reduceAux2 rK116 T116_53_2 (by decide)

theorem hcardT116_53_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK116 ⟨53, by decide⟩ R116_2 hpxR116_2 hcardq116_2 (by decide)).symm

/-- **Cell (116, 53) twin (q=2).** -/
theorem cell116_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK116) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec2 rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK116 e (h : Coordinate 2) T116_53_2 i :=
  species_entry_eq_sum rK116 ⟨53, by decide⟩ e heK h T116_53_2 hfix116_53_2 hinj116_53_2 hcardT116_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK116) (T116_53_2 i) (hfix116_53_2 i) h)

/-! ### Cell (116, 55) twin -/

def T116_55_2 : Fin 5 → Coordinate 2 := fun i => T116_55list.getD i.val (0,0,0,0,0)

theorem hfix116_55_2 : ∀ i, ((T116_55_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116) :=
  repsFix_of_siftB2 rK116 ⟨55, by decide⟩ T116_55_2 (by decide)

theorem hinj116_55_2 : Function.Injective
    (fun i => ((T116_55_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)) :=
  repsInj_of_reduceAux2 rK116 T116_55_2 (by decide)

theorem hcardT116_55_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK116 ⟨55, by decide⟩ R116_2 hpxR116_2 hcardq116_2 (by decide)).symm

/-- **Cell (116, 55) twin (q=2).** -/
theorem cell116_55_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK116) e = true)
    (h : ↥(reps (⟨55, by decide⟩ : Fin 148))) :
    species (reps (⟨55, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec2 rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK116 e (h : Coordinate 2) T116_55_2 i :=
  species_entry_eq_sum rK116 ⟨55, by decide⟩ e heK h T116_55_2 hfix116_55_2 hinj116_55_2 hcardT116_55_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨55, by decide⟩) (reps rK116) (T116_55_2 i) (hfix116_55_2 i) h)

/-! ### Cell (116, 56) twin -/

def T116_56_2 : Fin 5 → Coordinate 2 := fun i => T116_56list.getD i.val (0,0,0,0,0)

theorem hfix116_56_2 : ∀ i, ((T116_56_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116) :=
  repsFix_of_siftB2 rK116 ⟨56, by decide⟩ T116_56_2 (by decide)

theorem hinj116_56_2 : Function.Injective
    (fun i => ((T116_56_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)) :=
  repsInj_of_reduceAux2 rK116 T116_56_2 (by decide)

theorem hcardT116_56_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK116 ⟨56, by decide⟩ R116_2 hpxR116_2 hcardq116_2 (by decide)).symm

/-- **Cell (116, 56) twin (q=2).** -/
theorem cell116_56_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK116) e = true)
    (h : ↥(reps (⟨56, by decide⟩ : Fin 148))) :
    species (reps (⟨56, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec2 rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK116 e (h : Coordinate 2) T116_56_2 i :=
  species_entry_eq_sum rK116 ⟨56, by decide⟩ e heK h T116_56_2 hfix116_56_2 hinj116_56_2 hcardT116_56_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨56, by decide⟩) (reps rK116) (T116_56_2 i) (hfix116_56_2 i) h)

/-! ### Cell (116, 57) twin -/

def T116_57_2 : Fin 5 → Coordinate 2 := fun i => T116_57list.getD i.val (0,0,0,0,0)

theorem hfix116_57_2 : ∀ i, ((T116_57_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116) :=
  repsFix_of_siftB2 rK116 ⟨57, by decide⟩ T116_57_2 (by decide)

theorem hinj116_57_2 : Function.Injective
    (fun i => ((T116_57_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)) :=
  repsInj_of_reduceAux2 rK116 T116_57_2 (by decide)

theorem hcardT116_57_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK116 ⟨57, by decide⟩ R116_2 hpxR116_2 hcardq116_2 (by decide)).symm

/-- **Cell (116, 57) twin (q=2).** -/
theorem cell116_57_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK116) e = true)
    (h : ↥(reps (⟨57, by decide⟩ : Fin 148))) :
    species (reps (⟨57, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec2 rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK116 e (h : Coordinate 2) T116_57_2 i :=
  species_entry_eq_sum rK116 ⟨57, by decide⟩ e heK h T116_57_2 hfix116_57_2 hinj116_57_2 hcardT116_57_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨57, by decide⟩) (reps rK116) (T116_57_2 i) (hfix116_57_2 i) h)

/-! ### Cell (116, 58) twin -/

def T116_58_2 : Fin 5 → Coordinate 2 := fun i => T116_58list.getD i.val (0,0,0,0,0)

theorem hfix116_58_2 : ∀ i, ((T116_58_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116) :=
  repsFix_of_siftB2 rK116 ⟨58, by decide⟩ T116_58_2 (by decide)

theorem hinj116_58_2 : Function.Injective
    (fun i => ((T116_58_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)) :=
  repsInj_of_reduceAux2 rK116 T116_58_2 (by decide)

theorem hcardT116_58_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK116 ⟨58, by decide⟩ R116_2 hpxR116_2 hcardq116_2 (by decide)).symm

/-- **Cell (116, 58) twin (q=2).** -/
theorem cell116_58_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK116) e = true)
    (h : ↥(reps (⟨58, by decide⟩ : Fin 148))) :
    species (reps (⟨58, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec2 rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK116 e (h : Coordinate 2) T116_58_2 i :=
  species_entry_eq_sum rK116 ⟨58, by decide⟩ e heK h T116_58_2 hfix116_58_2 hinj116_58_2 hcardT116_58_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨58, by decide⟩) (reps rK116) (T116_58_2 i) (hfix116_58_2 i) h)

/-! ### Cell (116, 59) twin -/

def T116_59_2 : Fin 5 → Coordinate 2 := fun i => T116_59list.getD i.val (0,0,0,0,0)

theorem hfix116_59_2 : ∀ i, ((T116_59_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116) :=
  repsFix_of_siftB2 rK116 ⟨59, by decide⟩ T116_59_2 (by decide)

theorem hinj116_59_2 : Function.Injective
    (fun i => ((T116_59_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)) :=
  repsInj_of_reduceAux2 rK116 T116_59_2 (by decide)

theorem hcardT116_59_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK116 ⟨59, by decide⟩ R116_2 hpxR116_2 hcardq116_2 (by decide)).symm

/-- **Cell (116, 59) twin (q=2).** -/
theorem cell116_59_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK116) e = true)
    (h : ↥(reps (⟨59, by decide⟩ : Fin 148))) :
    species (reps (⟨59, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec2 rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK116 e (h : Coordinate 2) T116_59_2 i :=
  species_entry_eq_sum rK116 ⟨59, by decide⟩ e heK h T116_59_2 hfix116_59_2 hinj116_59_2 hcardT116_59_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨59, by decide⟩) (reps rK116) (T116_59_2 i) (hfix116_59_2 i) h)

/-! ### Cell (116, 80) twin -/

def T116_80_2 : Fin 5 → Coordinate 2 := fun i => T116_80list.getD i.val (0,0,0,0,0)

theorem hfix116_80_2 : ∀ i, ((T116_80_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116) :=
  repsFix_of_siftB2 rK116 ⟨80, by decide⟩ T116_80_2 (by decide)

theorem hinj116_80_2 : Function.Injective
    (fun i => ((T116_80_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)) :=
  repsInj_of_reduceAux2 rK116 T116_80_2 (by decide)

theorem hcardT116_80_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK116 ⟨80, by decide⟩ R116_2 hpxR116_2 hcardq116_2 (by decide)).symm

/-- **Cell (116, 80) twin (q=2).** -/
theorem cell116_80_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK116) e = true)
    (h : ↥(reps (⟨80, by decide⟩ : Fin 148))) :
    species (reps (⟨80, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec2 rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK116 e (h : Coordinate 2) T116_80_2 i :=
  species_entry_eq_sum rK116 ⟨80, by decide⟩ e heK h T116_80_2 hfix116_80_2 hinj116_80_2 hcardT116_80_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨80, by decide⟩) (reps rK116) (T116_80_2 i) (hfix116_80_2 i) h)

/-! ### Cell (116, 90) twin -/

def T116_90_2 : Fin 5 → Coordinate 2 := fun i => T116_90list.getD i.val (0,0,0,0,0)

theorem hfix116_90_2 : ∀ i, ((T116_90_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116) :=
  repsFix_of_siftB2 rK116 ⟨90, by decide⟩ T116_90_2 (by decide)

theorem hinj116_90_2 : Function.Injective
    (fun i => ((T116_90_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)) :=
  repsInj_of_reduceAux2 rK116 T116_90_2 (by decide)

theorem hcardT116_90_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK116 ⟨90, by decide⟩ R116_2 hpxR116_2 hcardq116_2 (by decide)).symm

/-- **Cell (116, 90) twin (q=2).** -/
theorem cell116_90_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK116) e = true)
    (h : ↥(reps (⟨90, by decide⟩ : Fin 148))) :
    species (reps (⟨90, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec2 rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK116 e (h : Coordinate 2) T116_90_2 i :=
  species_entry_eq_sum rK116 ⟨90, by decide⟩ e heK h T116_90_2 hfix116_90_2 hinj116_90_2 hcardT116_90_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨90, by decide⟩) (reps rK116) (T116_90_2 i) (hfix116_90_2 i) h)

/-! ### Cell (116, 95) twin -/

def T116_95_2 : Fin 5 → Coordinate 2 := fun i => T116_95list.getD i.val (0,0,0,0,0)

theorem hfix116_95_2 : ∀ i, ((T116_95_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116) :=
  repsFix_of_siftB2 rK116 ⟨95, by decide⟩ T116_95_2 (by decide)

theorem hinj116_95_2 : Function.Injective
    (fun i => ((T116_95_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)) :=
  repsInj_of_reduceAux2 rK116 T116_95_2 (by decide)

theorem hcardT116_95_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK116 ⟨95, by decide⟩ R116_2 hpxR116_2 hcardq116_2 (by decide)).symm

/-- **Cell (116, 95) twin (q=2).** -/
theorem cell116_95_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK116) e = true)
    (h : ↥(reps (⟨95, by decide⟩ : Fin 148))) :
    species (reps (⟨95, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec2 rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK116 e (h : Coordinate 2) T116_95_2 i :=
  species_entry_eq_sum rK116 ⟨95, by decide⟩ e heK h T116_95_2 hfix116_95_2 hinj116_95_2 hcardT116_95_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨95, by decide⟩) (reps rK116) (T116_95_2 i) (hfix116_95_2 i) h)

/-! ### Cell (116, 100) twin -/

def T116_100_2 : Fin 5 → Coordinate 2 := fun i => T116_100list.getD i.val (0,0,0,0,0)

theorem hfix116_100_2 : ∀ i, ((T116_100_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116) :=
  repsFix_of_siftB2 rK116 ⟨100, by decide⟩ T116_100_2 (by decide)

theorem hinj116_100_2 : Function.Injective
    (fun i => ((T116_100_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)) :=
  repsInj_of_reduceAux2 rK116 T116_100_2 (by decide)

theorem hcardT116_100_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK116 ⟨100, by decide⟩ R116_2 hpxR116_2 hcardq116_2 (by decide)).symm

/-- **Cell (116, 100) twin (q=2).** -/
theorem cell116_100_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK116) e = true)
    (h : ↥(reps (⟨100, by decide⟩ : Fin 148))) :
    species (reps (⟨100, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec2 rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK116 e (h : Coordinate 2) T116_100_2 i :=
  species_entry_eq_sum rK116 ⟨100, by decide⟩ e heK h T116_100_2 hfix116_100_2 hinj116_100_2 hcardT116_100_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨100, by decide⟩) (reps rK116) (T116_100_2 i) (hfix116_100_2 i) h)

/-! ### Cell (116, 105) twin -/

def T116_105_2 : Fin 5 → Coordinate 2 := fun i => T116_105list.getD i.val (0,0,0,0,0)

theorem hfix116_105_2 : ∀ i, ((T116_105_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116) :=
  repsFix_of_siftB2 rK116 ⟨105, by decide⟩ T116_105_2 (by decide)

theorem hinj116_105_2 : Function.Injective
    (fun i => ((T116_105_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)) :=
  repsInj_of_reduceAux2 rK116 T116_105_2 (by decide)

theorem hcardT116_105_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK116 ⟨105, by decide⟩ R116_2 hpxR116_2 hcardq116_2 (by decide)).symm

/-- **Cell (116, 105) twin (q=2).** -/
theorem cell116_105_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK116) e = true)
    (h : ↥(reps (⟨105, by decide⟩ : Fin 148))) :
    species (reps (⟨105, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec2 rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK116 e (h : Coordinate 2) T116_105_2 i :=
  species_entry_eq_sum rK116 ⟨105, by decide⟩ e heK h T116_105_2 hfix116_105_2 hinj116_105_2 hcardT116_105_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨105, by decide⟩) (reps rK116) (T116_105_2 i) (hfix116_105_2 i) h)

/-! ### Cell (116, 110) twin -/

def T116_110_2 : Fin 5 → Coordinate 2 := fun i => T116_110list.getD i.val (0,0,0,0,0)

theorem hfix116_110_2 : ∀ i, ((T116_110_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116) :=
  repsFix_of_siftB2 rK116 ⟨110, by decide⟩ T116_110_2 (by decide)

theorem hinj116_110_2 : Function.Injective
    (fun i => ((T116_110_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)) :=
  repsInj_of_reduceAux2 rK116 T116_110_2 (by decide)

theorem hcardT116_110_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK116 ⟨110, by decide⟩ R116_2 hpxR116_2 hcardq116_2 (by decide)).symm

/-- **Cell (116, 110) twin (q=2).** -/
theorem cell116_110_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK116) e = true)
    (h : ↥(reps (⟨110, by decide⟩ : Fin 148))) :
    species (reps (⟨110, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec2 rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK116 e (h : Coordinate 2) T116_110_2 i :=
  species_entry_eq_sum rK116 ⟨110, by decide⟩ e heK h T116_110_2 hfix116_110_2 hinj116_110_2 hcardT116_110_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨110, by decide⟩) (reps rK116) (T116_110_2 i) (hfix116_110_2 i) h)

/-! ### Cell (116, 116) twin -/

def T116_116_2 : Fin 5 → Coordinate 2 := fun i => T116_116list.getD i.val (0,0,0,0,0)

theorem hfix116_116_2 : ∀ i, ((T116_116_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)
    ∈ fixedPoints (reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116) :=
  repsFix_of_siftB2 rK116 ⟨116, by decide⟩ T116_116_2 (by decide)

theorem hinj116_116_2 : Function.Injective
    (fun i => ((T116_116_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK116)) :=
  repsInj_of_reduceAux2 rK116 T116_116_2 (by decide)

theorem hcardT116_116_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK116)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK116 ⟨116, by decide⟩ R116_2 hpxR116_2 hcardq116_2 (by decide)).symm

/-- **Cell (116, 116) twin (q=2).** -/
theorem cell116_116_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK116) e = true)
    (h : ↥(reps (⟨116, by decide⟩ : Fin 148))) :
    species (reps (⟨116, by decide⟩ : Fin 148)) h (basisElt (reps rK116) (charOfVec2 rK116 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK116 e (h : Coordinate 2) T116_116_2 i :=
  species_entry_eq_sum rK116 ⟨116, by decide⟩ e heK h T116_116_2 hfix116_116_2 hinj116_116_2 hcardT116_116_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨116, by decide⟩) (reps rK116) (T116_116_2 i) (hfix116_116_2 i) h)

end Q2

end LeanDring.P5Presentation
