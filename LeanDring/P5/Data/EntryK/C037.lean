/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, K-strata data (5^4 stratum, rK 136-137): certified per-cell species-entry instantiations, both
twins.

Covers K-classes 136, 137 (order-5^4 K, |R|=5).  For each nonzero `H`-column
(`(G/K)^H ≠ ∅`), the full coset transversal `R136..` and each `H`-fixed
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

/-! # K-class rK = 136  (|G/K| = 5) -/

def rK136 : Fin 148 := ⟨136, by decide⟩

def R136list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def R136 : Fin 5 → Coordinate 1 := fun i => R136list.getD i.val (0,0,0,0,0)

theorem hpxR136 : Function.Injective (fun i => reduceAux 1 (basisAt rK136) (R136 i)) := by decide
theorem hcardq136 : Nat.card (Coordinate 1 ⧸ reps rK136) = 5 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (136, 0): |T| = 5 -/

def T136_0list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T136_0 : Fin 5 → Coordinate 1 := fun i => T136_0list.getD i.val (0,0,0,0,0)

theorem hfix136_0 : ∀ i, ((T136_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK136)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136) :=
  repsFix_of_siftB rK136 ⟨0, by decide⟩ T136_0 (by decide)

theorem hinj136_0 : Function.Injective
    (fun i => ((T136_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK136)) :=
  repsInj_of_reduceAux rK136 T136_0 (by decide)

theorem hcardT136_0 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK136 ⟨0, by decide⟩ R136 hpxR136 hcardq136 (by decide)).symm

/-- **Cell (136, 0).** -/
theorem cell136_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK136) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK136) (charOfVec rK136 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK136 e (h : Coordinate 1) T136_0 i :=
  species_entry_eq_sum rK136 ⟨0, by decide⟩ e heK h T136_0 hfix136_0 hinj136_0 hcardT136_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK136) (T136_0 i) (hfix136_0 i) h)

/-! ## Cell (136, 5): |T| = 5 -/

def T136_5list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T136_5 : Fin 5 → Coordinate 1 := fun i => T136_5list.getD i.val (0,0,0,0,0)

theorem hfix136_5 : ∀ i, ((T136_5 i : Coordinate 1) : Coordinate 1 ⧸ reps rK136)
    ∈ fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136) :=
  repsFix_of_siftB rK136 ⟨5, by decide⟩ T136_5 (by decide)

theorem hinj136_5 : Function.Injective
    (fun i => ((T136_5 i : Coordinate 1) : Coordinate 1 ⧸ reps rK136)) :=
  repsInj_of_reduceAux rK136 T136_5 (by decide)

theorem hcardT136_5 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK136 ⟨5, by decide⟩ R136 hpxR136 hcardq136 (by decide)).symm

/-- **Cell (136, 5).** -/
theorem cell136_5 (e : List (ZMod 25)) (heK : charOK (basisAt rK136) e = true)
    (h : ↥(reps (⟨5, by decide⟩ : Fin 148))) :
    species (reps (⟨5, by decide⟩ : Fin 148)) h (basisElt (reps rK136) (charOfVec rK136 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK136 e (h : Coordinate 1) T136_5 i :=
  species_entry_eq_sum rK136 ⟨5, by decide⟩ e heK h T136_5 hfix136_5 hinj136_5 hcardT136_5
    (fun i => conj_mem_of_fixedPoints (reps ⟨5, by decide⟩) (reps rK136) (T136_5 i) (hfix136_5 i) h)

/-! ## Cell (136, 10): |T| = 5 -/

def T136_10list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T136_10 : Fin 5 → Coordinate 1 := fun i => T136_10list.getD i.val (0,0,0,0,0)

theorem hfix136_10 : ∀ i, ((T136_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK136)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136) :=
  repsFix_of_siftB rK136 ⟨10, by decide⟩ T136_10 (by decide)

theorem hinj136_10 : Function.Injective
    (fun i => ((T136_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK136)) :=
  repsInj_of_reduceAux rK136 T136_10 (by decide)

theorem hcardT136_10 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK136 ⟨10, by decide⟩ R136 hpxR136 hcardq136 (by decide)).symm

/-- **Cell (136, 10).** -/
theorem cell136_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK136) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK136) (charOfVec rK136 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK136 e (h : Coordinate 1) T136_10 i :=
  species_entry_eq_sum rK136 ⟨10, by decide⟩ e heK h T136_10 hfix136_10 hinj136_10 hcardT136_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK136) (T136_10 i) (hfix136_10 i) h)

/-! ## Cell (136, 12): |T| = 5 -/

def T136_12list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T136_12 : Fin 5 → Coordinate 1 := fun i => T136_12list.getD i.val (0,0,0,0,0)

theorem hfix136_12 : ∀ i, ((T136_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK136)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136) :=
  repsFix_of_siftB rK136 ⟨12, by decide⟩ T136_12 (by decide)

theorem hinj136_12 : Function.Injective
    (fun i => ((T136_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK136)) :=
  repsInj_of_reduceAux rK136 T136_12 (by decide)

theorem hcardT136_12 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK136 ⟨12, by decide⟩ R136 hpxR136 hcardq136 (by decide)).symm

/-- **Cell (136, 12).** -/
theorem cell136_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK136) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK136) (charOfVec rK136 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK136 e (h : Coordinate 1) T136_12 i :=
  species_entry_eq_sum rK136 ⟨12, by decide⟩ e heK h T136_12 hfix136_12 hinj136_12 hcardT136_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK136) (T136_12 i) (hfix136_12 i) h)

/-! ## Cell (136, 23): |T| = 5 -/

def T136_23list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T136_23 : Fin 5 → Coordinate 1 := fun i => T136_23list.getD i.val (0,0,0,0,0)

theorem hfix136_23 : ∀ i, ((T136_23 i : Coordinate 1) : Coordinate 1 ⧸ reps rK136)
    ∈ fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136) :=
  repsFix_of_siftB rK136 ⟨23, by decide⟩ T136_23 (by decide)

theorem hinj136_23 : Function.Injective
    (fun i => ((T136_23 i : Coordinate 1) : Coordinate 1 ⧸ reps rK136)) :=
  repsInj_of_reduceAux rK136 T136_23 (by decide)

theorem hcardT136_23 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK136 ⟨23, by decide⟩ R136 hpxR136 hcardq136 (by decide)).symm

/-- **Cell (136, 23).** -/
theorem cell136_23 (e : List (ZMod 25)) (heK : charOK (basisAt rK136) e = true)
    (h : ↥(reps (⟨23, by decide⟩ : Fin 148))) :
    species (reps (⟨23, by decide⟩ : Fin 148)) h (basisElt (reps rK136) (charOfVec rK136 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK136 e (h : Coordinate 1) T136_23 i :=
  species_entry_eq_sum rK136 ⟨23, by decide⟩ e heK h T136_23 hfix136_23 hinj136_23 hcardT136_23
    (fun i => conj_mem_of_fixedPoints (reps ⟨23, by decide⟩) (reps rK136) (T136_23 i) (hfix136_23 i) h)

/-! ## Cell (136, 29): |T| = 5 -/

def T136_29list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T136_29 : Fin 5 → Coordinate 1 := fun i => T136_29list.getD i.val (0,0,0,0,0)

theorem hfix136_29 : ∀ i, ((T136_29 i : Coordinate 1) : Coordinate 1 ⧸ reps rK136)
    ∈ fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136) :=
  repsFix_of_siftB rK136 ⟨29, by decide⟩ T136_29 (by decide)

theorem hinj136_29 : Function.Injective
    (fun i => ((T136_29 i : Coordinate 1) : Coordinate 1 ⧸ reps rK136)) :=
  repsInj_of_reduceAux rK136 T136_29 (by decide)

theorem hcardT136_29 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK136 ⟨29, by decide⟩ R136 hpxR136 hcardq136 (by decide)).symm

/-- **Cell (136, 29).** -/
theorem cell136_29 (e : List (ZMod 25)) (heK : charOK (basisAt rK136) e = true)
    (h : ↥(reps (⟨29, by decide⟩ : Fin 148))) :
    species (reps (⟨29, by decide⟩ : Fin 148)) h (basisElt (reps rK136) (charOfVec rK136 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK136 e (h : Coordinate 1) T136_29 i :=
  species_entry_eq_sum rK136 ⟨29, by decide⟩ e heK h T136_29 hfix136_29 hinj136_29 hcardT136_29
    (fun i => conj_mem_of_fixedPoints (reps ⟨29, by decide⟩) (reps rK136) (T136_29 i) (hfix136_29 i) h)

/-! ## Cell (136, 36): |T| = 5 -/

def T136_36list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T136_36 : Fin 5 → Coordinate 1 := fun i => T136_36list.getD i.val (0,0,0,0,0)

theorem hfix136_36 : ∀ i, ((T136_36 i : Coordinate 1) : Coordinate 1 ⧸ reps rK136)
    ∈ fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136) :=
  repsFix_of_siftB rK136 ⟨36, by decide⟩ T136_36 (by decide)

theorem hinj136_36 : Function.Injective
    (fun i => ((T136_36 i : Coordinate 1) : Coordinate 1 ⧸ reps rK136)) :=
  repsInj_of_reduceAux rK136 T136_36 (by decide)

theorem hcardT136_36 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK136 ⟨36, by decide⟩ R136 hpxR136 hcardq136 (by decide)).symm

/-- **Cell (136, 36).** -/
theorem cell136_36 (e : List (ZMod 25)) (heK : charOK (basisAt rK136) e = true)
    (h : ↥(reps (⟨36, by decide⟩ : Fin 148))) :
    species (reps (⟨36, by decide⟩ : Fin 148)) h (basisElt (reps rK136) (charOfVec rK136 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK136 e (h : Coordinate 1) T136_36 i :=
  species_entry_eq_sum rK136 ⟨36, by decide⟩ e heK h T136_36 hfix136_36 hinj136_36 hcardT136_36
    (fun i => conj_mem_of_fixedPoints (reps ⟨36, by decide⟩) (reps rK136) (T136_36 i) (hfix136_36 i) h)

/-! ## Cell (136, 40): |T| = 5 -/

def T136_40list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T136_40 : Fin 5 → Coordinate 1 := fun i => T136_40list.getD i.val (0,0,0,0,0)

theorem hfix136_40 : ∀ i, ((T136_40 i : Coordinate 1) : Coordinate 1 ⧸ reps rK136)
    ∈ fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136) :=
  repsFix_of_siftB rK136 ⟨40, by decide⟩ T136_40 (by decide)

theorem hinj136_40 : Function.Injective
    (fun i => ((T136_40 i : Coordinate 1) : Coordinate 1 ⧸ reps rK136)) :=
  repsInj_of_reduceAux rK136 T136_40 (by decide)

theorem hcardT136_40 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK136 ⟨40, by decide⟩ R136 hpxR136 hcardq136 (by decide)).symm

/-- **Cell (136, 40).** -/
theorem cell136_40 (e : List (ZMod 25)) (heK : charOK (basisAt rK136) e = true)
    (h : ↥(reps (⟨40, by decide⟩ : Fin 148))) :
    species (reps (⟨40, by decide⟩ : Fin 148)) h (basisElt (reps rK136) (charOfVec rK136 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK136 e (h : Coordinate 1) T136_40 i :=
  species_entry_eq_sum rK136 ⟨40, by decide⟩ e heK h T136_40 hfix136_40 hinj136_40 hcardT136_40
    (fun i => conj_mem_of_fixedPoints (reps ⟨40, by decide⟩) (reps rK136) (T136_40 i) (hfix136_40 i) h)

/-! ## Cell (136, 47): |T| = 5 -/

def T136_47list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T136_47 : Fin 5 → Coordinate 1 := fun i => T136_47list.getD i.val (0,0,0,0,0)

theorem hfix136_47 : ∀ i, ((T136_47 i : Coordinate 1) : Coordinate 1 ⧸ reps rK136)
    ∈ fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136) :=
  repsFix_of_siftB rK136 ⟨47, by decide⟩ T136_47 (by decide)

theorem hinj136_47 : Function.Injective
    (fun i => ((T136_47 i : Coordinate 1) : Coordinate 1 ⧸ reps rK136)) :=
  repsInj_of_reduceAux rK136 T136_47 (by decide)

theorem hcardT136_47 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK136 ⟨47, by decide⟩ R136 hpxR136 hcardq136 (by decide)).symm

/-- **Cell (136, 47).** -/
theorem cell136_47 (e : List (ZMod 25)) (heK : charOK (basisAt rK136) e = true)
    (h : ↥(reps (⟨47, by decide⟩ : Fin 148))) :
    species (reps (⟨47, by decide⟩ : Fin 148)) h (basisElt (reps rK136) (charOfVec rK136 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK136 e (h : Coordinate 1) T136_47 i :=
  species_entry_eq_sum rK136 ⟨47, by decide⟩ e heK h T136_47 hfix136_47 hinj136_47 hcardT136_47
    (fun i => conj_mem_of_fixedPoints (reps ⟨47, by decide⟩) (reps rK136) (T136_47 i) (hfix136_47 i) h)

/-! ## Cell (136, 48): |T| = 5 -/

def T136_48list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T136_48 : Fin 5 → Coordinate 1 := fun i => T136_48list.getD i.val (0,0,0,0,0)

theorem hfix136_48 : ∀ i, ((T136_48 i : Coordinate 1) : Coordinate 1 ⧸ reps rK136)
    ∈ fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136) :=
  repsFix_of_siftB rK136 ⟨48, by decide⟩ T136_48 (by decide)

theorem hinj136_48 : Function.Injective
    (fun i => ((T136_48 i : Coordinate 1) : Coordinate 1 ⧸ reps rK136)) :=
  repsInj_of_reduceAux rK136 T136_48 (by decide)

theorem hcardT136_48 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK136 ⟨48, by decide⟩ R136 hpxR136 hcardq136 (by decide)).symm

/-- **Cell (136, 48).** -/
theorem cell136_48 (e : List (ZMod 25)) (heK : charOK (basisAt rK136) e = true)
    (h : ↥(reps (⟨48, by decide⟩ : Fin 148))) :
    species (reps (⟨48, by decide⟩ : Fin 148)) h (basisElt (reps rK136) (charOfVec rK136 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK136 e (h : Coordinate 1) T136_48 i :=
  species_entry_eq_sum rK136 ⟨48, by decide⟩ e heK h T136_48 hfix136_48 hinj136_48 hcardT136_48
    (fun i => conj_mem_of_fixedPoints (reps ⟨48, by decide⟩) (reps rK136) (T136_48 i) (hfix136_48 i) h)

/-! ## Cell (136, 53): |T| = 5 -/

def T136_53list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T136_53 : Fin 5 → Coordinate 1 := fun i => T136_53list.getD i.val (0,0,0,0,0)

theorem hfix136_53 : ∀ i, ((T136_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK136)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136) :=
  repsFix_of_siftB rK136 ⟨53, by decide⟩ T136_53 (by decide)

theorem hinj136_53 : Function.Injective
    (fun i => ((T136_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK136)) :=
  repsInj_of_reduceAux rK136 T136_53 (by decide)

theorem hcardT136_53 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK136 ⟨53, by decide⟩ R136 hpxR136 hcardq136 (by decide)).symm

/-- **Cell (136, 53).** -/
theorem cell136_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK136) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK136) (charOfVec rK136 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK136 e (h : Coordinate 1) T136_53 i :=
  species_entry_eq_sum rK136 ⟨53, by decide⟩ e heK h T136_53 hfix136_53 hinj136_53 hcardT136_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK136) (T136_53 i) (hfix136_53 i) h)

/-! ## Cell (136, 84): |T| = 5 -/

def T136_84list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T136_84 : Fin 5 → Coordinate 1 := fun i => T136_84list.getD i.val (0,0,0,0,0)

theorem hfix136_84 : ∀ i, ((T136_84 i : Coordinate 1) : Coordinate 1 ⧸ reps rK136)
    ∈ fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136) :=
  repsFix_of_siftB rK136 ⟨84, by decide⟩ T136_84 (by decide)

theorem hinj136_84 : Function.Injective
    (fun i => ((T136_84 i : Coordinate 1) : Coordinate 1 ⧸ reps rK136)) :=
  repsInj_of_reduceAux rK136 T136_84 (by decide)

theorem hcardT136_84 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK136 ⟨84, by decide⟩ R136 hpxR136 hcardq136 (by decide)).symm

/-- **Cell (136, 84).** -/
theorem cell136_84 (e : List (ZMod 25)) (heK : charOK (basisAt rK136) e = true)
    (h : ↥(reps (⟨84, by decide⟩ : Fin 148))) :
    species (reps (⟨84, by decide⟩ : Fin 148)) h (basisElt (reps rK136) (charOfVec rK136 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK136 e (h : Coordinate 1) T136_84 i :=
  species_entry_eq_sum rK136 ⟨84, by decide⟩ e heK h T136_84 hfix136_84 hinj136_84 hcardT136_84
    (fun i => conj_mem_of_fixedPoints (reps ⟨84, by decide⟩) (reps rK136) (T136_84 i) (hfix136_84 i) h)

/-! ## Cell (136, 91): |T| = 5 -/

def T136_91list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T136_91 : Fin 5 → Coordinate 1 := fun i => T136_91list.getD i.val (0,0,0,0,0)

theorem hfix136_91 : ∀ i, ((T136_91 i : Coordinate 1) : Coordinate 1 ⧸ reps rK136)
    ∈ fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136) :=
  repsFix_of_siftB rK136 ⟨91, by decide⟩ T136_91 (by decide)

theorem hinj136_91 : Function.Injective
    (fun i => ((T136_91 i : Coordinate 1) : Coordinate 1 ⧸ reps rK136)) :=
  repsInj_of_reduceAux rK136 T136_91 (by decide)

theorem hcardT136_91 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK136 ⟨91, by decide⟩ R136 hpxR136 hcardq136 (by decide)).symm

/-- **Cell (136, 91).** -/
theorem cell136_91 (e : List (ZMod 25)) (heK : charOK (basisAt rK136) e = true)
    (h : ↥(reps (⟨91, by decide⟩ : Fin 148))) :
    species (reps (⟨91, by decide⟩ : Fin 148)) h (basisElt (reps rK136) (charOfVec rK136 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK136 e (h : Coordinate 1) T136_91 i :=
  species_entry_eq_sum rK136 ⟨91, by decide⟩ e heK h T136_91 hfix136_91 hinj136_91 hcardT136_91
    (fun i => conj_mem_of_fixedPoints (reps ⟨91, by decide⟩) (reps rK136) (T136_91 i) (hfix136_91 i) h)

/-! ## Cell (136, 98): |T| = 5 -/

def T136_98list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T136_98 : Fin 5 → Coordinate 1 := fun i => T136_98list.getD i.val (0,0,0,0,0)

theorem hfix136_98 : ∀ i, ((T136_98 i : Coordinate 1) : Coordinate 1 ⧸ reps rK136)
    ∈ fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136) :=
  repsFix_of_siftB rK136 ⟨98, by decide⟩ T136_98 (by decide)

theorem hinj136_98 : Function.Injective
    (fun i => ((T136_98 i : Coordinate 1) : Coordinate 1 ⧸ reps rK136)) :=
  repsInj_of_reduceAux rK136 T136_98 (by decide)

theorem hcardT136_98 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK136 ⟨98, by decide⟩ R136 hpxR136 hcardq136 (by decide)).symm

/-- **Cell (136, 98).** -/
theorem cell136_98 (e : List (ZMod 25)) (heK : charOK (basisAt rK136) e = true)
    (h : ↥(reps (⟨98, by decide⟩ : Fin 148))) :
    species (reps (⟨98, by decide⟩ : Fin 148)) h (basisElt (reps rK136) (charOfVec rK136 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK136 e (h : Coordinate 1) T136_98 i :=
  species_entry_eq_sum rK136 ⟨98, by decide⟩ e heK h T136_98 hfix136_98 hinj136_98 hcardT136_98
    (fun i => conj_mem_of_fixedPoints (reps ⟨98, by decide⟩) (reps rK136) (T136_98 i) (hfix136_98 i) h)

/-! ## Cell (136, 102): |T| = 5 -/

def T136_102list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T136_102 : Fin 5 → Coordinate 1 := fun i => T136_102list.getD i.val (0,0,0,0,0)

theorem hfix136_102 : ∀ i, ((T136_102 i : Coordinate 1) : Coordinate 1 ⧸ reps rK136)
    ∈ fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136) :=
  repsFix_of_siftB rK136 ⟨102, by decide⟩ T136_102 (by decide)

theorem hinj136_102 : Function.Injective
    (fun i => ((T136_102 i : Coordinate 1) : Coordinate 1 ⧸ reps rK136)) :=
  repsInj_of_reduceAux rK136 T136_102 (by decide)

theorem hcardT136_102 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK136 ⟨102, by decide⟩ R136 hpxR136 hcardq136 (by decide)).symm

/-- **Cell (136, 102).** -/
theorem cell136_102 (e : List (ZMod 25)) (heK : charOK (basisAt rK136) e = true)
    (h : ↥(reps (⟨102, by decide⟩ : Fin 148))) :
    species (reps (⟨102, by decide⟩ : Fin 148)) h (basisElt (reps rK136) (charOfVec rK136 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK136 e (h : Coordinate 1) T136_102 i :=
  species_entry_eq_sum rK136 ⟨102, by decide⟩ e heK h T136_102 hfix136_102 hinj136_102 hcardT136_102
    (fun i => conj_mem_of_fixedPoints (reps ⟨102, by decide⟩) (reps rK136) (T136_102 i) (hfix136_102 i) h)

/-! ## Cell (136, 109): |T| = 5 -/

def T136_109list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T136_109 : Fin 5 → Coordinate 1 := fun i => T136_109list.getD i.val (0,0,0,0,0)

theorem hfix136_109 : ∀ i, ((T136_109 i : Coordinate 1) : Coordinate 1 ⧸ reps rK136)
    ∈ fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136) :=
  repsFix_of_siftB rK136 ⟨109, by decide⟩ T136_109 (by decide)

theorem hinj136_109 : Function.Injective
    (fun i => ((T136_109 i : Coordinate 1) : Coordinate 1 ⧸ reps rK136)) :=
  repsInj_of_reduceAux rK136 T136_109 (by decide)

theorem hcardT136_109 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK136 ⟨109, by decide⟩ R136 hpxR136 hcardq136 (by decide)).symm

/-- **Cell (136, 109).** -/
theorem cell136_109 (e : List (ZMod 25)) (heK : charOK (basisAt rK136) e = true)
    (h : ↥(reps (⟨109, by decide⟩ : Fin 148))) :
    species (reps (⟨109, by decide⟩ : Fin 148)) h (basisElt (reps rK136) (charOfVec rK136 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK136 e (h : Coordinate 1) T136_109 i :=
  species_entry_eq_sum rK136 ⟨109, by decide⟩ e heK h T136_109 hfix136_109 hinj136_109 hcardT136_109
    (fun i => conj_mem_of_fixedPoints (reps ⟨109, by decide⟩) (reps rK136) (T136_109 i) (hfix136_109 i) h)

/-! ## Cell (136, 110): |T| = 5 -/

def T136_110list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T136_110 : Fin 5 → Coordinate 1 := fun i => T136_110list.getD i.val (0,0,0,0,0)

theorem hfix136_110 : ∀ i, ((T136_110 i : Coordinate 1) : Coordinate 1 ⧸ reps rK136)
    ∈ fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136) :=
  repsFix_of_siftB rK136 ⟨110, by decide⟩ T136_110 (by decide)

theorem hinj136_110 : Function.Injective
    (fun i => ((T136_110 i : Coordinate 1) : Coordinate 1 ⧸ reps rK136)) :=
  repsInj_of_reduceAux rK136 T136_110 (by decide)

theorem hcardT136_110 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK136 ⟨110, by decide⟩ R136 hpxR136 hcardq136 (by decide)).symm

/-- **Cell (136, 110).** -/
theorem cell136_110 (e : List (ZMod 25)) (heK : charOK (basisAt rK136) e = true)
    (h : ↥(reps (⟨110, by decide⟩ : Fin 148))) :
    species (reps (⟨110, by decide⟩ : Fin 148)) h (basisElt (reps rK136) (charOfVec rK136 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK136 e (h : Coordinate 1) T136_110 i :=
  species_entry_eq_sum rK136 ⟨110, by decide⟩ e heK h T136_110 hfix136_110 hinj136_110 hcardT136_110
    (fun i => conj_mem_of_fixedPoints (reps ⟨110, by decide⟩) (reps rK136) (T136_110 i) (hfix136_110 i) h)

/-! ## Cell (136, 136): |T| = 5 -/

def T136_136list : List Coordinates := [(0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0)]
def T136_136 : Fin 5 → Coordinate 1 := fun i => T136_136list.getD i.val (0,0,0,0,0)

theorem hfix136_136 : ∀ i, ((T136_136 i : Coordinate 1) : Coordinate 1 ⧸ reps rK136)
    ∈ fixedPoints (reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136) :=
  repsFix_of_siftB rK136 ⟨136, by decide⟩ T136_136 (by decide)

theorem hinj136_136 : Function.Injective
    (fun i => ((T136_136 i : Coordinate 1) : Coordinate 1 ⧸ reps rK136)) :=
  repsInj_of_reduceAux rK136 T136_136 (by decide)

theorem hcardT136_136 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK136 ⟨136, by decide⟩ R136 hpxR136 hcardq136 (by decide)).symm

/-- **Cell (136, 136).** -/
theorem cell136_136 (e : List (ZMod 25)) (heK : charOK (basisAt rK136) e = true)
    (h : ↥(reps (⟨136, by decide⟩ : Fin 148))) :
    species (reps (⟨136, by decide⟩ : Fin 148)) h (basisElt (reps rK136) (charOfVec rK136 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK136 e (h : Coordinate 1) T136_136 i :=
  species_entry_eq_sum rK136 ⟨136, by decide⟩ e heK h T136_136 hfix136_136 hinj136_136 hcardT136_136
    (fun i => conj_mem_of_fixedPoints (reps ⟨136, by decide⟩) (reps rK136) (T136_136 i) (hfix136_136 i) h)

namespace Q2

def R136_2 : Fin 5 → Coordinate 2 := fun i => R136list.getD i.val (0,0,0,0,0)
theorem hpxR136_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK136) (R136_2 i)) := by decide
theorem hcardq136_2 : Nat.card (Coordinate 2 ⧸ reps rK136) = 5 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (136, 0) twin -/

def T136_0_2 : Fin 5 → Coordinate 2 := fun i => T136_0list.getD i.val (0,0,0,0,0)

theorem hfix136_0_2 : ∀ i, ((T136_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK136)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK136) :=
  repsFix_of_siftB2 rK136 ⟨0, by decide⟩ T136_0_2 (by decide)

theorem hinj136_0_2 : Function.Injective
    (fun i => ((T136_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK136)) :=
  repsInj_of_reduceAux2 rK136 T136_0_2 (by decide)

theorem hcardT136_0_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK136)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK136 ⟨0, by decide⟩ R136_2 hpxR136_2 hcardq136_2 (by decide)).symm

/-- **Cell (136, 0) twin (q=2).** -/
theorem cell136_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK136) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK136) (charOfVec2 rK136 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK136 e (h : Coordinate 2) T136_0_2 i :=
  species_entry_eq_sum rK136 ⟨0, by decide⟩ e heK h T136_0_2 hfix136_0_2 hinj136_0_2 hcardT136_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK136) (T136_0_2 i) (hfix136_0_2 i) h)

/-! ### Cell (136, 5) twin -/

def T136_5_2 : Fin 5 → Coordinate 2 := fun i => T136_5list.getD i.val (0,0,0,0,0)

theorem hfix136_5_2 : ∀ i, ((T136_5_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK136)
    ∈ fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK136) :=
  repsFix_of_siftB2 rK136 ⟨5, by decide⟩ T136_5_2 (by decide)

theorem hinj136_5_2 : Function.Injective
    (fun i => ((T136_5_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK136)) :=
  repsInj_of_reduceAux2 rK136 T136_5_2 (by decide)

theorem hcardT136_5_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK136)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK136 ⟨5, by decide⟩ R136_2 hpxR136_2 hcardq136_2 (by decide)).symm

/-- **Cell (136, 5) twin (q=2).** -/
theorem cell136_5_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK136) e = true)
    (h : ↥(reps (⟨5, by decide⟩ : Fin 148))) :
    species (reps (⟨5, by decide⟩ : Fin 148)) h (basisElt (reps rK136) (charOfVec2 rK136 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK136 e (h : Coordinate 2) T136_5_2 i :=
  species_entry_eq_sum rK136 ⟨5, by decide⟩ e heK h T136_5_2 hfix136_5_2 hinj136_5_2 hcardT136_5_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨5, by decide⟩) (reps rK136) (T136_5_2 i) (hfix136_5_2 i) h)

/-! ### Cell (136, 10) twin -/

def T136_10_2 : Fin 5 → Coordinate 2 := fun i => T136_10list.getD i.val (0,0,0,0,0)

theorem hfix136_10_2 : ∀ i, ((T136_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK136)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK136) :=
  repsFix_of_siftB2 rK136 ⟨10, by decide⟩ T136_10_2 (by decide)

theorem hinj136_10_2 : Function.Injective
    (fun i => ((T136_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK136)) :=
  repsInj_of_reduceAux2 rK136 T136_10_2 (by decide)

theorem hcardT136_10_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK136)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK136 ⟨10, by decide⟩ R136_2 hpxR136_2 hcardq136_2 (by decide)).symm

/-- **Cell (136, 10) twin (q=2).** -/
theorem cell136_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK136) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK136) (charOfVec2 rK136 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK136 e (h : Coordinate 2) T136_10_2 i :=
  species_entry_eq_sum rK136 ⟨10, by decide⟩ e heK h T136_10_2 hfix136_10_2 hinj136_10_2 hcardT136_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK136) (T136_10_2 i) (hfix136_10_2 i) h)

/-! ### Cell (136, 12) twin -/

def T136_12_2 : Fin 5 → Coordinate 2 := fun i => T136_12list.getD i.val (0,0,0,0,0)

theorem hfix136_12_2 : ∀ i, ((T136_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK136)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK136) :=
  repsFix_of_siftB2 rK136 ⟨12, by decide⟩ T136_12_2 (by decide)

theorem hinj136_12_2 : Function.Injective
    (fun i => ((T136_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK136)) :=
  repsInj_of_reduceAux2 rK136 T136_12_2 (by decide)

theorem hcardT136_12_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK136)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK136 ⟨12, by decide⟩ R136_2 hpxR136_2 hcardq136_2 (by decide)).symm

/-- **Cell (136, 12) twin (q=2).** -/
theorem cell136_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK136) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK136) (charOfVec2 rK136 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK136 e (h : Coordinate 2) T136_12_2 i :=
  species_entry_eq_sum rK136 ⟨12, by decide⟩ e heK h T136_12_2 hfix136_12_2 hinj136_12_2 hcardT136_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK136) (T136_12_2 i) (hfix136_12_2 i) h)

/-! ### Cell (136, 23) twin -/

def T136_23_2 : Fin 5 → Coordinate 2 := fun i => T136_23list.getD i.val (0,0,0,0,0)

theorem hfix136_23_2 : ∀ i, ((T136_23_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK136)
    ∈ fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK136) :=
  repsFix_of_siftB2 rK136 ⟨23, by decide⟩ T136_23_2 (by decide)

theorem hinj136_23_2 : Function.Injective
    (fun i => ((T136_23_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK136)) :=
  repsInj_of_reduceAux2 rK136 T136_23_2 (by decide)

theorem hcardT136_23_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK136)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK136 ⟨23, by decide⟩ R136_2 hpxR136_2 hcardq136_2 (by decide)).symm

/-- **Cell (136, 23) twin (q=2).** -/
theorem cell136_23_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK136) e = true)
    (h : ↥(reps (⟨23, by decide⟩ : Fin 148))) :
    species (reps (⟨23, by decide⟩ : Fin 148)) h (basisElt (reps rK136) (charOfVec2 rK136 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK136 e (h : Coordinate 2) T136_23_2 i :=
  species_entry_eq_sum rK136 ⟨23, by decide⟩ e heK h T136_23_2 hfix136_23_2 hinj136_23_2 hcardT136_23_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨23, by decide⟩) (reps rK136) (T136_23_2 i) (hfix136_23_2 i) h)

/-! ### Cell (136, 29) twin -/

def T136_29_2 : Fin 5 → Coordinate 2 := fun i => T136_29list.getD i.val (0,0,0,0,0)

theorem hfix136_29_2 : ∀ i, ((T136_29_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK136)
    ∈ fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK136) :=
  repsFix_of_siftB2 rK136 ⟨29, by decide⟩ T136_29_2 (by decide)

theorem hinj136_29_2 : Function.Injective
    (fun i => ((T136_29_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK136)) :=
  repsInj_of_reduceAux2 rK136 T136_29_2 (by decide)

theorem hcardT136_29_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK136)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK136 ⟨29, by decide⟩ R136_2 hpxR136_2 hcardq136_2 (by decide)).symm

/-- **Cell (136, 29) twin (q=2).** -/
theorem cell136_29_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK136) e = true)
    (h : ↥(reps (⟨29, by decide⟩ : Fin 148))) :
    species (reps (⟨29, by decide⟩ : Fin 148)) h (basisElt (reps rK136) (charOfVec2 rK136 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK136 e (h : Coordinate 2) T136_29_2 i :=
  species_entry_eq_sum rK136 ⟨29, by decide⟩ e heK h T136_29_2 hfix136_29_2 hinj136_29_2 hcardT136_29_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨29, by decide⟩) (reps rK136) (T136_29_2 i) (hfix136_29_2 i) h)

/-! ### Cell (136, 36) twin -/

def T136_36_2 : Fin 5 → Coordinate 2 := fun i => T136_36list.getD i.val (0,0,0,0,0)

theorem hfix136_36_2 : ∀ i, ((T136_36_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK136)
    ∈ fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK136) :=
  repsFix_of_siftB2 rK136 ⟨36, by decide⟩ T136_36_2 (by decide)

theorem hinj136_36_2 : Function.Injective
    (fun i => ((T136_36_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK136)) :=
  repsInj_of_reduceAux2 rK136 T136_36_2 (by decide)

theorem hcardT136_36_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK136)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK136 ⟨36, by decide⟩ R136_2 hpxR136_2 hcardq136_2 (by decide)).symm

/-- **Cell (136, 36) twin (q=2).** -/
theorem cell136_36_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK136) e = true)
    (h : ↥(reps (⟨36, by decide⟩ : Fin 148))) :
    species (reps (⟨36, by decide⟩ : Fin 148)) h (basisElt (reps rK136) (charOfVec2 rK136 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK136 e (h : Coordinate 2) T136_36_2 i :=
  species_entry_eq_sum rK136 ⟨36, by decide⟩ e heK h T136_36_2 hfix136_36_2 hinj136_36_2 hcardT136_36_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨36, by decide⟩) (reps rK136) (T136_36_2 i) (hfix136_36_2 i) h)

/-! ### Cell (136, 40) twin -/

def T136_40_2 : Fin 5 → Coordinate 2 := fun i => T136_40list.getD i.val (0,0,0,0,0)

theorem hfix136_40_2 : ∀ i, ((T136_40_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK136)
    ∈ fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK136) :=
  repsFix_of_siftB2 rK136 ⟨40, by decide⟩ T136_40_2 (by decide)

theorem hinj136_40_2 : Function.Injective
    (fun i => ((T136_40_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK136)) :=
  repsInj_of_reduceAux2 rK136 T136_40_2 (by decide)

theorem hcardT136_40_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK136)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK136 ⟨40, by decide⟩ R136_2 hpxR136_2 hcardq136_2 (by decide)).symm

/-- **Cell (136, 40) twin (q=2).** -/
theorem cell136_40_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK136) e = true)
    (h : ↥(reps (⟨40, by decide⟩ : Fin 148))) :
    species (reps (⟨40, by decide⟩ : Fin 148)) h (basisElt (reps rK136) (charOfVec2 rK136 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK136 e (h : Coordinate 2) T136_40_2 i :=
  species_entry_eq_sum rK136 ⟨40, by decide⟩ e heK h T136_40_2 hfix136_40_2 hinj136_40_2 hcardT136_40_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨40, by decide⟩) (reps rK136) (T136_40_2 i) (hfix136_40_2 i) h)

/-! ### Cell (136, 47) twin -/

def T136_47_2 : Fin 5 → Coordinate 2 := fun i => T136_47list.getD i.val (0,0,0,0,0)

theorem hfix136_47_2 : ∀ i, ((T136_47_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK136)
    ∈ fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK136) :=
  repsFix_of_siftB2 rK136 ⟨47, by decide⟩ T136_47_2 (by decide)

theorem hinj136_47_2 : Function.Injective
    (fun i => ((T136_47_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK136)) :=
  repsInj_of_reduceAux2 rK136 T136_47_2 (by decide)

theorem hcardT136_47_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK136)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK136 ⟨47, by decide⟩ R136_2 hpxR136_2 hcardq136_2 (by decide)).symm

/-- **Cell (136, 47) twin (q=2).** -/
theorem cell136_47_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK136) e = true)
    (h : ↥(reps (⟨47, by decide⟩ : Fin 148))) :
    species (reps (⟨47, by decide⟩ : Fin 148)) h (basisElt (reps rK136) (charOfVec2 rK136 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK136 e (h : Coordinate 2) T136_47_2 i :=
  species_entry_eq_sum rK136 ⟨47, by decide⟩ e heK h T136_47_2 hfix136_47_2 hinj136_47_2 hcardT136_47_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨47, by decide⟩) (reps rK136) (T136_47_2 i) (hfix136_47_2 i) h)

/-! ### Cell (136, 48) twin -/

def T136_48_2 : Fin 5 → Coordinate 2 := fun i => T136_48list.getD i.val (0,0,0,0,0)

theorem hfix136_48_2 : ∀ i, ((T136_48_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK136)
    ∈ fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK136) :=
  repsFix_of_siftB2 rK136 ⟨48, by decide⟩ T136_48_2 (by decide)

theorem hinj136_48_2 : Function.Injective
    (fun i => ((T136_48_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK136)) :=
  repsInj_of_reduceAux2 rK136 T136_48_2 (by decide)

theorem hcardT136_48_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK136)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK136 ⟨48, by decide⟩ R136_2 hpxR136_2 hcardq136_2 (by decide)).symm

/-- **Cell (136, 48) twin (q=2).** -/
theorem cell136_48_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK136) e = true)
    (h : ↥(reps (⟨48, by decide⟩ : Fin 148))) :
    species (reps (⟨48, by decide⟩ : Fin 148)) h (basisElt (reps rK136) (charOfVec2 rK136 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK136 e (h : Coordinate 2) T136_48_2 i :=
  species_entry_eq_sum rK136 ⟨48, by decide⟩ e heK h T136_48_2 hfix136_48_2 hinj136_48_2 hcardT136_48_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨48, by decide⟩) (reps rK136) (T136_48_2 i) (hfix136_48_2 i) h)

/-! ### Cell (136, 53) twin -/

def T136_53_2 : Fin 5 → Coordinate 2 := fun i => T136_53list.getD i.val (0,0,0,0,0)

theorem hfix136_53_2 : ∀ i, ((T136_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK136)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK136) :=
  repsFix_of_siftB2 rK136 ⟨53, by decide⟩ T136_53_2 (by decide)

theorem hinj136_53_2 : Function.Injective
    (fun i => ((T136_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK136)) :=
  repsInj_of_reduceAux2 rK136 T136_53_2 (by decide)

theorem hcardT136_53_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK136)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK136 ⟨53, by decide⟩ R136_2 hpxR136_2 hcardq136_2 (by decide)).symm

/-- **Cell (136, 53) twin (q=2).** -/
theorem cell136_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK136) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK136) (charOfVec2 rK136 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK136 e (h : Coordinate 2) T136_53_2 i :=
  species_entry_eq_sum rK136 ⟨53, by decide⟩ e heK h T136_53_2 hfix136_53_2 hinj136_53_2 hcardT136_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK136) (T136_53_2 i) (hfix136_53_2 i) h)

/-! ### Cell (136, 84) twin -/

def T136_84_2 : Fin 5 → Coordinate 2 := fun i => T136_84list.getD i.val (0,0,0,0,0)

theorem hfix136_84_2 : ∀ i, ((T136_84_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK136)
    ∈ fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK136) :=
  repsFix_of_siftB2 rK136 ⟨84, by decide⟩ T136_84_2 (by decide)

theorem hinj136_84_2 : Function.Injective
    (fun i => ((T136_84_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK136)) :=
  repsInj_of_reduceAux2 rK136 T136_84_2 (by decide)

theorem hcardT136_84_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK136)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK136 ⟨84, by decide⟩ R136_2 hpxR136_2 hcardq136_2 (by decide)).symm

/-- **Cell (136, 84) twin (q=2).** -/
theorem cell136_84_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK136) e = true)
    (h : ↥(reps (⟨84, by decide⟩ : Fin 148))) :
    species (reps (⟨84, by decide⟩ : Fin 148)) h (basisElt (reps rK136) (charOfVec2 rK136 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK136 e (h : Coordinate 2) T136_84_2 i :=
  species_entry_eq_sum rK136 ⟨84, by decide⟩ e heK h T136_84_2 hfix136_84_2 hinj136_84_2 hcardT136_84_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨84, by decide⟩) (reps rK136) (T136_84_2 i) (hfix136_84_2 i) h)

/-! ### Cell (136, 91) twin -/

def T136_91_2 : Fin 5 → Coordinate 2 := fun i => T136_91list.getD i.val (0,0,0,0,0)

theorem hfix136_91_2 : ∀ i, ((T136_91_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK136)
    ∈ fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK136) :=
  repsFix_of_siftB2 rK136 ⟨91, by decide⟩ T136_91_2 (by decide)

theorem hinj136_91_2 : Function.Injective
    (fun i => ((T136_91_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK136)) :=
  repsInj_of_reduceAux2 rK136 T136_91_2 (by decide)

theorem hcardT136_91_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK136)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK136 ⟨91, by decide⟩ R136_2 hpxR136_2 hcardq136_2 (by decide)).symm

/-- **Cell (136, 91) twin (q=2).** -/
theorem cell136_91_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK136) e = true)
    (h : ↥(reps (⟨91, by decide⟩ : Fin 148))) :
    species (reps (⟨91, by decide⟩ : Fin 148)) h (basisElt (reps rK136) (charOfVec2 rK136 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK136 e (h : Coordinate 2) T136_91_2 i :=
  species_entry_eq_sum rK136 ⟨91, by decide⟩ e heK h T136_91_2 hfix136_91_2 hinj136_91_2 hcardT136_91_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨91, by decide⟩) (reps rK136) (T136_91_2 i) (hfix136_91_2 i) h)

/-! ### Cell (136, 98) twin -/

def T136_98_2 : Fin 5 → Coordinate 2 := fun i => T136_98list.getD i.val (0,0,0,0,0)

theorem hfix136_98_2 : ∀ i, ((T136_98_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK136)
    ∈ fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK136) :=
  repsFix_of_siftB2 rK136 ⟨98, by decide⟩ T136_98_2 (by decide)

theorem hinj136_98_2 : Function.Injective
    (fun i => ((T136_98_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK136)) :=
  repsInj_of_reduceAux2 rK136 T136_98_2 (by decide)

theorem hcardT136_98_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK136)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK136 ⟨98, by decide⟩ R136_2 hpxR136_2 hcardq136_2 (by decide)).symm

/-- **Cell (136, 98) twin (q=2).** -/
theorem cell136_98_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK136) e = true)
    (h : ↥(reps (⟨98, by decide⟩ : Fin 148))) :
    species (reps (⟨98, by decide⟩ : Fin 148)) h (basisElt (reps rK136) (charOfVec2 rK136 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK136 e (h : Coordinate 2) T136_98_2 i :=
  species_entry_eq_sum rK136 ⟨98, by decide⟩ e heK h T136_98_2 hfix136_98_2 hinj136_98_2 hcardT136_98_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨98, by decide⟩) (reps rK136) (T136_98_2 i) (hfix136_98_2 i) h)

/-! ### Cell (136, 102) twin -/

def T136_102_2 : Fin 5 → Coordinate 2 := fun i => T136_102list.getD i.val (0,0,0,0,0)

theorem hfix136_102_2 : ∀ i, ((T136_102_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK136)
    ∈ fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK136) :=
  repsFix_of_siftB2 rK136 ⟨102, by decide⟩ T136_102_2 (by decide)

theorem hinj136_102_2 : Function.Injective
    (fun i => ((T136_102_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK136)) :=
  repsInj_of_reduceAux2 rK136 T136_102_2 (by decide)

theorem hcardT136_102_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK136)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK136 ⟨102, by decide⟩ R136_2 hpxR136_2 hcardq136_2 (by decide)).symm

/-- **Cell (136, 102) twin (q=2).** -/
theorem cell136_102_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK136) e = true)
    (h : ↥(reps (⟨102, by decide⟩ : Fin 148))) :
    species (reps (⟨102, by decide⟩ : Fin 148)) h (basisElt (reps rK136) (charOfVec2 rK136 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK136 e (h : Coordinate 2) T136_102_2 i :=
  species_entry_eq_sum rK136 ⟨102, by decide⟩ e heK h T136_102_2 hfix136_102_2 hinj136_102_2 hcardT136_102_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨102, by decide⟩) (reps rK136) (T136_102_2 i) (hfix136_102_2 i) h)

/-! ### Cell (136, 109) twin -/

def T136_109_2 : Fin 5 → Coordinate 2 := fun i => T136_109list.getD i.val (0,0,0,0,0)

theorem hfix136_109_2 : ∀ i, ((T136_109_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK136)
    ∈ fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK136) :=
  repsFix_of_siftB2 rK136 ⟨109, by decide⟩ T136_109_2 (by decide)

theorem hinj136_109_2 : Function.Injective
    (fun i => ((T136_109_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK136)) :=
  repsInj_of_reduceAux2 rK136 T136_109_2 (by decide)

theorem hcardT136_109_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK136)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK136 ⟨109, by decide⟩ R136_2 hpxR136_2 hcardq136_2 (by decide)).symm

/-- **Cell (136, 109) twin (q=2).** -/
theorem cell136_109_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK136) e = true)
    (h : ↥(reps (⟨109, by decide⟩ : Fin 148))) :
    species (reps (⟨109, by decide⟩ : Fin 148)) h (basisElt (reps rK136) (charOfVec2 rK136 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK136 e (h : Coordinate 2) T136_109_2 i :=
  species_entry_eq_sum rK136 ⟨109, by decide⟩ e heK h T136_109_2 hfix136_109_2 hinj136_109_2 hcardT136_109_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨109, by decide⟩) (reps rK136) (T136_109_2 i) (hfix136_109_2 i) h)

/-! ### Cell (136, 110) twin -/

def T136_110_2 : Fin 5 → Coordinate 2 := fun i => T136_110list.getD i.val (0,0,0,0,0)

theorem hfix136_110_2 : ∀ i, ((T136_110_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK136)
    ∈ fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK136) :=
  repsFix_of_siftB2 rK136 ⟨110, by decide⟩ T136_110_2 (by decide)

theorem hinj136_110_2 : Function.Injective
    (fun i => ((T136_110_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK136)) :=
  repsInj_of_reduceAux2 rK136 T136_110_2 (by decide)

theorem hcardT136_110_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK136)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK136 ⟨110, by decide⟩ R136_2 hpxR136_2 hcardq136_2 (by decide)).symm

/-- **Cell (136, 110) twin (q=2).** -/
theorem cell136_110_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK136) e = true)
    (h : ↥(reps (⟨110, by decide⟩ : Fin 148))) :
    species (reps (⟨110, by decide⟩ : Fin 148)) h (basisElt (reps rK136) (charOfVec2 rK136 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK136 e (h : Coordinate 2) T136_110_2 i :=
  species_entry_eq_sum rK136 ⟨110, by decide⟩ e heK h T136_110_2 hfix136_110_2 hinj136_110_2 hcardT136_110_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨110, by decide⟩) (reps rK136) (T136_110_2 i) (hfix136_110_2 i) h)

/-! ### Cell (136, 136) twin -/

def T136_136_2 : Fin 5 → Coordinate 2 := fun i => T136_136list.getD i.val (0,0,0,0,0)

theorem hfix136_136_2 : ∀ i, ((T136_136_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK136)
    ∈ fixedPoints (reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK136) :=
  repsFix_of_siftB2 rK136 ⟨136, by decide⟩ T136_136_2 (by decide)

theorem hinj136_136_2 : Function.Injective
    (fun i => ((T136_136_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK136)) :=
  repsInj_of_reduceAux2 rK136 T136_136_2 (by decide)

theorem hcardT136_136_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK136)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK136 ⟨136, by decide⟩ R136_2 hpxR136_2 hcardq136_2 (by decide)).symm

/-- **Cell (136, 136) twin (q=2).** -/
theorem cell136_136_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK136) e = true)
    (h : ↥(reps (⟨136, by decide⟩ : Fin 148))) :
    species (reps (⟨136, by decide⟩ : Fin 148)) h (basisElt (reps rK136) (charOfVec2 rK136 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK136 e (h : Coordinate 2) T136_136_2 i :=
  species_entry_eq_sum rK136 ⟨136, by decide⟩ e heK h T136_136_2 hfix136_136_2 hinj136_136_2 hcardT136_136_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨136, by decide⟩) (reps rK136) (T136_136_2 i) (hfix136_136_2 i) h)

end Q2

/-! # K-class rK = 137  (|G/K| = 5) -/

def rK137 : Fin 148 := ⟨137, by decide⟩

def R137list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def R137 : Fin 5 → Coordinate 1 := fun i => R137list.getD i.val (0,0,0,0,0)

theorem hpxR137 : Function.Injective (fun i => reduceAux 1 (basisAt rK137) (R137 i)) := by decide
theorem hcardq137 : Nat.card (Coordinate 1 ⧸ reps rK137) = 5 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (137, 0): |T| = 5 -/

def T137_0list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T137_0 : Fin 5 → Coordinate 1 := fun i => T137_0list.getD i.val (0,0,0,0,0)

theorem hfix137_0 : ∀ i, ((T137_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK137)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137) :=
  repsFix_of_siftB rK137 ⟨0, by decide⟩ T137_0 (by decide)

theorem hinj137_0 : Function.Injective
    (fun i => ((T137_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK137)) :=
  repsInj_of_reduceAux rK137 T137_0 (by decide)

theorem hcardT137_0 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK137 ⟨0, by decide⟩ R137 hpxR137 hcardq137 (by decide)).symm

/-- **Cell (137, 0).** -/
theorem cell137_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK137) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK137) (charOfVec rK137 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK137 e (h : Coordinate 1) T137_0 i :=
  species_entry_eq_sum rK137 ⟨0, by decide⟩ e heK h T137_0 hfix137_0 hinj137_0 hcardT137_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK137) (T137_0 i) (hfix137_0 i) h)

/-! ## Cell (137, 5): |T| = 5 -/

def T137_5list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T137_5 : Fin 5 → Coordinate 1 := fun i => T137_5list.getD i.val (0,0,0,0,0)

theorem hfix137_5 : ∀ i, ((T137_5 i : Coordinate 1) : Coordinate 1 ⧸ reps rK137)
    ∈ fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137) :=
  repsFix_of_siftB rK137 ⟨5, by decide⟩ T137_5 (by decide)

theorem hinj137_5 : Function.Injective
    (fun i => ((T137_5 i : Coordinate 1) : Coordinate 1 ⧸ reps rK137)) :=
  repsInj_of_reduceAux rK137 T137_5 (by decide)

theorem hcardT137_5 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK137 ⟨5, by decide⟩ R137 hpxR137 hcardq137 (by decide)).symm

/-- **Cell (137, 5).** -/
theorem cell137_5 (e : List (ZMod 25)) (heK : charOK (basisAt rK137) e = true)
    (h : ↥(reps (⟨5, by decide⟩ : Fin 148))) :
    species (reps (⟨5, by decide⟩ : Fin 148)) h (basisElt (reps rK137) (charOfVec rK137 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK137 e (h : Coordinate 1) T137_5 i :=
  species_entry_eq_sum rK137 ⟨5, by decide⟩ e heK h T137_5 hfix137_5 hinj137_5 hcardT137_5
    (fun i => conj_mem_of_fixedPoints (reps ⟨5, by decide⟩) (reps rK137) (T137_5 i) (hfix137_5 i) h)

/-! ## Cell (137, 10): |T| = 5 -/

def T137_10list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T137_10 : Fin 5 → Coordinate 1 := fun i => T137_10list.getD i.val (0,0,0,0,0)

theorem hfix137_10 : ∀ i, ((T137_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK137)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137) :=
  repsFix_of_siftB rK137 ⟨10, by decide⟩ T137_10 (by decide)

theorem hinj137_10 : Function.Injective
    (fun i => ((T137_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK137)) :=
  repsInj_of_reduceAux rK137 T137_10 (by decide)

theorem hcardT137_10 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK137 ⟨10, by decide⟩ R137 hpxR137 hcardq137 (by decide)).symm

/-- **Cell (137, 10).** -/
theorem cell137_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK137) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK137) (charOfVec rK137 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK137 e (h : Coordinate 1) T137_10 i :=
  species_entry_eq_sum rK137 ⟨10, by decide⟩ e heK h T137_10 hfix137_10 hinj137_10 hcardT137_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK137) (T137_10 i) (hfix137_10 i) h)

/-! ## Cell (137, 12): |T| = 5 -/

def T137_12list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T137_12 : Fin 5 → Coordinate 1 := fun i => T137_12list.getD i.val (0,0,0,0,0)

theorem hfix137_12 : ∀ i, ((T137_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK137)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137) :=
  repsFix_of_siftB rK137 ⟨12, by decide⟩ T137_12 (by decide)

theorem hinj137_12 : Function.Injective
    (fun i => ((T137_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK137)) :=
  repsInj_of_reduceAux rK137 T137_12 (by decide)

theorem hcardT137_12 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK137 ⟨12, by decide⟩ R137 hpxR137 hcardq137 (by decide)).symm

/-- **Cell (137, 12).** -/
theorem cell137_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK137) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK137) (charOfVec rK137 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK137 e (h : Coordinate 1) T137_12 i :=
  species_entry_eq_sum rK137 ⟨12, by decide⟩ e heK h T137_12 hfix137_12 hinj137_12 hcardT137_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK137) (T137_12 i) (hfix137_12 i) h)

/-! ## Cell (137, 23): |T| = 5 -/

def T137_23list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T137_23 : Fin 5 → Coordinate 1 := fun i => T137_23list.getD i.val (0,0,0,0,0)

theorem hfix137_23 : ∀ i, ((T137_23 i : Coordinate 1) : Coordinate 1 ⧸ reps rK137)
    ∈ fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137) :=
  repsFix_of_siftB rK137 ⟨23, by decide⟩ T137_23 (by decide)

theorem hinj137_23 : Function.Injective
    (fun i => ((T137_23 i : Coordinate 1) : Coordinate 1 ⧸ reps rK137)) :=
  repsInj_of_reduceAux rK137 T137_23 (by decide)

theorem hcardT137_23 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK137 ⟨23, by decide⟩ R137 hpxR137 hcardq137 (by decide)).symm

/-- **Cell (137, 23).** -/
theorem cell137_23 (e : List (ZMod 25)) (heK : charOK (basisAt rK137) e = true)
    (h : ↥(reps (⟨23, by decide⟩ : Fin 148))) :
    species (reps (⟨23, by decide⟩ : Fin 148)) h (basisElt (reps rK137) (charOfVec rK137 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK137 e (h : Coordinate 1) T137_23 i :=
  species_entry_eq_sum rK137 ⟨23, by decide⟩ e heK h T137_23 hfix137_23 hinj137_23 hcardT137_23
    (fun i => conj_mem_of_fixedPoints (reps ⟨23, by decide⟩) (reps rK137) (T137_23 i) (hfix137_23 i) h)

/-! ## Cell (137, 30): |T| = 5 -/

def T137_30list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T137_30 : Fin 5 → Coordinate 1 := fun i => T137_30list.getD i.val (0,0,0,0,0)

theorem hfix137_30 : ∀ i, ((T137_30 i : Coordinate 1) : Coordinate 1 ⧸ reps rK137)
    ∈ fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137) :=
  repsFix_of_siftB rK137 ⟨30, by decide⟩ T137_30 (by decide)

theorem hinj137_30 : Function.Injective
    (fun i => ((T137_30 i : Coordinate 1) : Coordinate 1 ⧸ reps rK137)) :=
  repsInj_of_reduceAux rK137 T137_30 (by decide)

theorem hcardT137_30 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK137 ⟨30, by decide⟩ R137 hpxR137 hcardq137 (by decide)).symm

/-- **Cell (137, 30).** -/
theorem cell137_30 (e : List (ZMod 25)) (heK : charOK (basisAt rK137) e = true)
    (h : ↥(reps (⟨30, by decide⟩ : Fin 148))) :
    species (reps (⟨30, by decide⟩ : Fin 148)) h (basisElt (reps rK137) (charOfVec rK137 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK137 e (h : Coordinate 1) T137_30 i :=
  species_entry_eq_sum rK137 ⟨30, by decide⟩ e heK h T137_30 hfix137_30 hinj137_30 hcardT137_30
    (fun i => conj_mem_of_fixedPoints (reps ⟨30, by decide⟩) (reps rK137) (T137_30 i) (hfix137_30 i) h)

/-! ## Cell (137, 37): |T| = 5 -/

def T137_37list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T137_37 : Fin 5 → Coordinate 1 := fun i => T137_37list.getD i.val (0,0,0,0,0)

theorem hfix137_37 : ∀ i, ((T137_37 i : Coordinate 1) : Coordinate 1 ⧸ reps rK137)
    ∈ fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137) :=
  repsFix_of_siftB rK137 ⟨37, by decide⟩ T137_37 (by decide)

theorem hinj137_37 : Function.Injective
    (fun i => ((T137_37 i : Coordinate 1) : Coordinate 1 ⧸ reps rK137)) :=
  repsInj_of_reduceAux rK137 T137_37 (by decide)

theorem hcardT137_37 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK137 ⟨37, by decide⟩ R137 hpxR137 hcardq137 (by decide)).symm

/-- **Cell (137, 37).** -/
theorem cell137_37 (e : List (ZMod 25)) (heK : charOK (basisAt rK137) e = true)
    (h : ↥(reps (⟨37, by decide⟩ : Fin 148))) :
    species (reps (⟨37, by decide⟩ : Fin 148)) h (basisElt (reps rK137) (charOfVec rK137 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK137 e (h : Coordinate 1) T137_37 i :=
  species_entry_eq_sum rK137 ⟨37, by decide⟩ e heK h T137_37 hfix137_37 hinj137_37 hcardT137_37
    (fun i => conj_mem_of_fixedPoints (reps ⟨37, by decide⟩) (reps rK137) (T137_37 i) (hfix137_37 i) h)

/-! ## Cell (137, 41): |T| = 5 -/

def T137_41list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T137_41 : Fin 5 → Coordinate 1 := fun i => T137_41list.getD i.val (0,0,0,0,0)

theorem hfix137_41 : ∀ i, ((T137_41 i : Coordinate 1) : Coordinate 1 ⧸ reps rK137)
    ∈ fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137) :=
  repsFix_of_siftB rK137 ⟨41, by decide⟩ T137_41 (by decide)

theorem hinj137_41 : Function.Injective
    (fun i => ((T137_41 i : Coordinate 1) : Coordinate 1 ⧸ reps rK137)) :=
  repsInj_of_reduceAux rK137 T137_41 (by decide)

theorem hcardT137_41 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK137 ⟨41, by decide⟩ R137 hpxR137 hcardq137 (by decide)).symm

/-- **Cell (137, 41).** -/
theorem cell137_41 (e : List (ZMod 25)) (heK : charOK (basisAt rK137) e = true)
    (h : ↥(reps (⟨41, by decide⟩ : Fin 148))) :
    species (reps (⟨41, by decide⟩ : Fin 148)) h (basisElt (reps rK137) (charOfVec rK137 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK137 e (h : Coordinate 1) T137_41 i :=
  species_entry_eq_sum rK137 ⟨41, by decide⟩ e heK h T137_41 hfix137_41 hinj137_41 hcardT137_41
    (fun i => conj_mem_of_fixedPoints (reps ⟨41, by decide⟩) (reps rK137) (T137_41 i) (hfix137_41 i) h)

/-! ## Cell (137, 43): |T| = 5 -/

def T137_43list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T137_43 : Fin 5 → Coordinate 1 := fun i => T137_43list.getD i.val (0,0,0,0,0)

theorem hfix137_43 : ∀ i, ((T137_43 i : Coordinate 1) : Coordinate 1 ⧸ reps rK137)
    ∈ fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137) :=
  repsFix_of_siftB rK137 ⟨43, by decide⟩ T137_43 (by decide)

theorem hinj137_43 : Function.Injective
    (fun i => ((T137_43 i : Coordinate 1) : Coordinate 1 ⧸ reps rK137)) :=
  repsInj_of_reduceAux rK137 T137_43 (by decide)

theorem hcardT137_43 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK137 ⟨43, by decide⟩ R137 hpxR137 hcardq137 (by decide)).symm

/-- **Cell (137, 43).** -/
theorem cell137_43 (e : List (ZMod 25)) (heK : charOK (basisAt rK137) e = true)
    (h : ↥(reps (⟨43, by decide⟩ : Fin 148))) :
    species (reps (⟨43, by decide⟩ : Fin 148)) h (basisElt (reps rK137) (charOfVec rK137 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK137 e (h : Coordinate 1) T137_43 i :=
  species_entry_eq_sum rK137 ⟨43, by decide⟩ e heK h T137_43 hfix137_43 hinj137_43 hcardT137_43
    (fun i => conj_mem_of_fixedPoints (reps ⟨43, by decide⟩) (reps rK137) (T137_43 i) (hfix137_43 i) h)

/-! ## Cell (137, 49): |T| = 5 -/

def T137_49list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T137_49 : Fin 5 → Coordinate 1 := fun i => T137_49list.getD i.val (0,0,0,0,0)

theorem hfix137_49 : ∀ i, ((T137_49 i : Coordinate 1) : Coordinate 1 ⧸ reps rK137)
    ∈ fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137) :=
  repsFix_of_siftB rK137 ⟨49, by decide⟩ T137_49 (by decide)

theorem hinj137_49 : Function.Injective
    (fun i => ((T137_49 i : Coordinate 1) : Coordinate 1 ⧸ reps rK137)) :=
  repsInj_of_reduceAux rK137 T137_49 (by decide)

theorem hcardT137_49 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK137 ⟨49, by decide⟩ R137 hpxR137 hcardq137 (by decide)).symm

/-- **Cell (137, 49).** -/
theorem cell137_49 (e : List (ZMod 25)) (heK : charOK (basisAt rK137) e = true)
    (h : ↥(reps (⟨49, by decide⟩ : Fin 148))) :
    species (reps (⟨49, by decide⟩ : Fin 148)) h (basisElt (reps rK137) (charOfVec rK137 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK137 e (h : Coordinate 1) T137_49 i :=
  species_entry_eq_sum rK137 ⟨49, by decide⟩ e heK h T137_49 hfix137_49 hinj137_49 hcardT137_49
    (fun i => conj_mem_of_fixedPoints (reps ⟨49, by decide⟩) (reps rK137) (T137_49 i) (hfix137_49 i) h)

/-! ## Cell (137, 53): |T| = 5 -/

def T137_53list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T137_53 : Fin 5 → Coordinate 1 := fun i => T137_53list.getD i.val (0,0,0,0,0)

theorem hfix137_53 : ∀ i, ((T137_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK137)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137) :=
  repsFix_of_siftB rK137 ⟨53, by decide⟩ T137_53 (by decide)

theorem hinj137_53 : Function.Injective
    (fun i => ((T137_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK137)) :=
  repsInj_of_reduceAux rK137 T137_53 (by decide)

theorem hcardT137_53 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK137 ⟨53, by decide⟩ R137 hpxR137 hcardq137 (by decide)).symm

/-- **Cell (137, 53).** -/
theorem cell137_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK137) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK137) (charOfVec rK137 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK137 e (h : Coordinate 1) T137_53 i :=
  species_entry_eq_sum rK137 ⟨53, by decide⟩ e heK h T137_53 hfix137_53 hinj137_53 hcardT137_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK137) (T137_53 i) (hfix137_53 i) h)

/-! ## Cell (137, 84): |T| = 5 -/

def T137_84list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T137_84 : Fin 5 → Coordinate 1 := fun i => T137_84list.getD i.val (0,0,0,0,0)

theorem hfix137_84 : ∀ i, ((T137_84 i : Coordinate 1) : Coordinate 1 ⧸ reps rK137)
    ∈ fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137) :=
  repsFix_of_siftB rK137 ⟨84, by decide⟩ T137_84 (by decide)

theorem hinj137_84 : Function.Injective
    (fun i => ((T137_84 i : Coordinate 1) : Coordinate 1 ⧸ reps rK137)) :=
  repsInj_of_reduceAux rK137 T137_84 (by decide)

theorem hcardT137_84 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK137 ⟨84, by decide⟩ R137 hpxR137 hcardq137 (by decide)).symm

/-- **Cell (137, 84).** -/
theorem cell137_84 (e : List (ZMod 25)) (heK : charOK (basisAt rK137) e = true)
    (h : ↥(reps (⟨84, by decide⟩ : Fin 148))) :
    species (reps (⟨84, by decide⟩ : Fin 148)) h (basisElt (reps rK137) (charOfVec rK137 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK137 e (h : Coordinate 1) T137_84 i :=
  species_entry_eq_sum rK137 ⟨84, by decide⟩ e heK h T137_84 hfix137_84 hinj137_84 hcardT137_84
    (fun i => conj_mem_of_fixedPoints (reps ⟨84, by decide⟩) (reps rK137) (T137_84 i) (hfix137_84 i) h)

/-! ## Cell (137, 92): |T| = 5 -/

def T137_92list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T137_92 : Fin 5 → Coordinate 1 := fun i => T137_92list.getD i.val (0,0,0,0,0)

theorem hfix137_92 : ∀ i, ((T137_92 i : Coordinate 1) : Coordinate 1 ⧸ reps rK137)
    ∈ fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137) :=
  repsFix_of_siftB rK137 ⟨92, by decide⟩ T137_92 (by decide)

theorem hinj137_92 : Function.Injective
    (fun i => ((T137_92 i : Coordinate 1) : Coordinate 1 ⧸ reps rK137)) :=
  repsInj_of_reduceAux rK137 T137_92 (by decide)

theorem hcardT137_92 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK137 ⟨92, by decide⟩ R137 hpxR137 hcardq137 (by decide)).symm

/-- **Cell (137, 92).** -/
theorem cell137_92 (e : List (ZMod 25)) (heK : charOK (basisAt rK137) e = true)
    (h : ↥(reps (⟨92, by decide⟩ : Fin 148))) :
    species (reps (⟨92, by decide⟩ : Fin 148)) h (basisElt (reps rK137) (charOfVec rK137 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK137 e (h : Coordinate 1) T137_92 i :=
  species_entry_eq_sum rK137 ⟨92, by decide⟩ e heK h T137_92 hfix137_92 hinj137_92 hcardT137_92
    (fun i => conj_mem_of_fixedPoints (reps ⟨92, by decide⟩) (reps rK137) (T137_92 i) (hfix137_92 i) h)

/-! ## Cell (137, 99): |T| = 5 -/

def T137_99list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T137_99 : Fin 5 → Coordinate 1 := fun i => T137_99list.getD i.val (0,0,0,0,0)

theorem hfix137_99 : ∀ i, ((T137_99 i : Coordinate 1) : Coordinate 1 ⧸ reps rK137)
    ∈ fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137) :=
  repsFix_of_siftB rK137 ⟨99, by decide⟩ T137_99 (by decide)

theorem hinj137_99 : Function.Injective
    (fun i => ((T137_99 i : Coordinate 1) : Coordinate 1 ⧸ reps rK137)) :=
  repsInj_of_reduceAux rK137 T137_99 (by decide)

theorem hcardT137_99 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK137 ⟨99, by decide⟩ R137 hpxR137 hcardq137 (by decide)).symm

/-- **Cell (137, 99).** -/
theorem cell137_99 (e : List (ZMod 25)) (heK : charOK (basisAt rK137) e = true)
    (h : ↥(reps (⟨99, by decide⟩ : Fin 148))) :
    species (reps (⟨99, by decide⟩ : Fin 148)) h (basisElt (reps rK137) (charOfVec rK137 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK137 e (h : Coordinate 1) T137_99 i :=
  species_entry_eq_sum rK137 ⟨99, by decide⟩ e heK h T137_99 hfix137_99 hinj137_99 hcardT137_99
    (fun i => conj_mem_of_fixedPoints (reps ⟨99, by decide⟩) (reps rK137) (T137_99 i) (hfix137_99 i) h)

/-! ## Cell (137, 103): |T| = 5 -/

def T137_103list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T137_103 : Fin 5 → Coordinate 1 := fun i => T137_103list.getD i.val (0,0,0,0,0)

theorem hfix137_103 : ∀ i, ((T137_103 i : Coordinate 1) : Coordinate 1 ⧸ reps rK137)
    ∈ fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137) :=
  repsFix_of_siftB rK137 ⟨103, by decide⟩ T137_103 (by decide)

theorem hinj137_103 : Function.Injective
    (fun i => ((T137_103 i : Coordinate 1) : Coordinate 1 ⧸ reps rK137)) :=
  repsInj_of_reduceAux rK137 T137_103 (by decide)

theorem hcardT137_103 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK137 ⟨103, by decide⟩ R137 hpxR137 hcardq137 (by decide)).symm

/-- **Cell (137, 103).** -/
theorem cell137_103 (e : List (ZMod 25)) (heK : charOK (basisAt rK137) e = true)
    (h : ↥(reps (⟨103, by decide⟩ : Fin 148))) :
    species (reps (⟨103, by decide⟩ : Fin 148)) h (basisElt (reps rK137) (charOfVec rK137 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK137 e (h : Coordinate 1) T137_103 i :=
  species_entry_eq_sum rK137 ⟨103, by decide⟩ e heK h T137_103 hfix137_103 hinj137_103 hcardT137_103
    (fun i => conj_mem_of_fixedPoints (reps ⟨103, by decide⟩) (reps rK137) (T137_103 i) (hfix137_103 i) h)

/-! ## Cell (137, 105): |T| = 5 -/

def T137_105list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T137_105 : Fin 5 → Coordinate 1 := fun i => T137_105list.getD i.val (0,0,0,0,0)

theorem hfix137_105 : ∀ i, ((T137_105 i : Coordinate 1) : Coordinate 1 ⧸ reps rK137)
    ∈ fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137) :=
  repsFix_of_siftB rK137 ⟨105, by decide⟩ T137_105 (by decide)

theorem hinj137_105 : Function.Injective
    (fun i => ((T137_105 i : Coordinate 1) : Coordinate 1 ⧸ reps rK137)) :=
  repsInj_of_reduceAux rK137 T137_105 (by decide)

theorem hcardT137_105 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK137 ⟨105, by decide⟩ R137 hpxR137 hcardq137 (by decide)).symm

/-- **Cell (137, 105).** -/
theorem cell137_105 (e : List (ZMod 25)) (heK : charOK (basisAt rK137) e = true)
    (h : ↥(reps (⟨105, by decide⟩ : Fin 148))) :
    species (reps (⟨105, by decide⟩ : Fin 148)) h (basisElt (reps rK137) (charOfVec rK137 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK137 e (h : Coordinate 1) T137_105 i :=
  species_entry_eq_sum rK137 ⟨105, by decide⟩ e heK h T137_105 hfix137_105 hinj137_105 hcardT137_105
    (fun i => conj_mem_of_fixedPoints (reps ⟨105, by decide⟩) (reps rK137) (T137_105 i) (hfix137_105 i) h)

/-! ## Cell (137, 111): |T| = 5 -/

def T137_111list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T137_111 : Fin 5 → Coordinate 1 := fun i => T137_111list.getD i.val (0,0,0,0,0)

theorem hfix137_111 : ∀ i, ((T137_111 i : Coordinate 1) : Coordinate 1 ⧸ reps rK137)
    ∈ fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137) :=
  repsFix_of_siftB rK137 ⟨111, by decide⟩ T137_111 (by decide)

theorem hinj137_111 : Function.Injective
    (fun i => ((T137_111 i : Coordinate 1) : Coordinate 1 ⧸ reps rK137)) :=
  repsInj_of_reduceAux rK137 T137_111 (by decide)

theorem hcardT137_111 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK137 ⟨111, by decide⟩ R137 hpxR137 hcardq137 (by decide)).symm

/-- **Cell (137, 111).** -/
theorem cell137_111 (e : List (ZMod 25)) (heK : charOK (basisAt rK137) e = true)
    (h : ↥(reps (⟨111, by decide⟩ : Fin 148))) :
    species (reps (⟨111, by decide⟩ : Fin 148)) h (basisElt (reps rK137) (charOfVec rK137 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK137 e (h : Coordinate 1) T137_111 i :=
  species_entry_eq_sum rK137 ⟨111, by decide⟩ e heK h T137_111 hfix137_111 hinj137_111 hcardT137_111
    (fun i => conj_mem_of_fixedPoints (reps ⟨111, by decide⟩) (reps rK137) (T137_111 i) (hfix137_111 i) h)

/-! ## Cell (137, 137): |T| = 5 -/

def T137_137list : List Coordinates := [(0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0), (0,0,0,0,0), (0,0,1,0,0)]
def T137_137 : Fin 5 → Coordinate 1 := fun i => T137_137list.getD i.val (0,0,0,0,0)

theorem hfix137_137 : ∀ i, ((T137_137 i : Coordinate 1) : Coordinate 1 ⧸ reps rK137)
    ∈ fixedPoints (reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137) :=
  repsFix_of_siftB rK137 ⟨137, by decide⟩ T137_137 (by decide)

theorem hinj137_137 : Function.Injective
    (fun i => ((T137_137 i : Coordinate 1) : Coordinate 1 ⧸ reps rK137)) :=
  repsInj_of_reduceAux rK137 T137_137 (by decide)

theorem hcardT137_137 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK137 ⟨137, by decide⟩ R137 hpxR137 hcardq137 (by decide)).symm

/-- **Cell (137, 137).** -/
theorem cell137_137 (e : List (ZMod 25)) (heK : charOK (basisAt rK137) e = true)
    (h : ↥(reps (⟨137, by decide⟩ : Fin 148))) :
    species (reps (⟨137, by decide⟩ : Fin 148)) h (basisElt (reps rK137) (charOfVec rK137 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK137 e (h : Coordinate 1) T137_137 i :=
  species_entry_eq_sum rK137 ⟨137, by decide⟩ e heK h T137_137 hfix137_137 hinj137_137 hcardT137_137
    (fun i => conj_mem_of_fixedPoints (reps ⟨137, by decide⟩) (reps rK137) (T137_137 i) (hfix137_137 i) h)

namespace Q2

def R137_2 : Fin 5 → Coordinate 2 := fun i => R137list.getD i.val (0,0,0,0,0)
theorem hpxR137_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK137) (R137_2 i)) := by decide
theorem hcardq137_2 : Nat.card (Coordinate 2 ⧸ reps rK137) = 5 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (137, 0) twin -/

def T137_0_2 : Fin 5 → Coordinate 2 := fun i => T137_0list.getD i.val (0,0,0,0,0)

theorem hfix137_0_2 : ∀ i, ((T137_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK137)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK137) :=
  repsFix_of_siftB2 rK137 ⟨0, by decide⟩ T137_0_2 (by decide)

theorem hinj137_0_2 : Function.Injective
    (fun i => ((T137_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK137)) :=
  repsInj_of_reduceAux2 rK137 T137_0_2 (by decide)

theorem hcardT137_0_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK137)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK137 ⟨0, by decide⟩ R137_2 hpxR137_2 hcardq137_2 (by decide)).symm

/-- **Cell (137, 0) twin (q=2).** -/
theorem cell137_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK137) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK137) (charOfVec2 rK137 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK137 e (h : Coordinate 2) T137_0_2 i :=
  species_entry_eq_sum rK137 ⟨0, by decide⟩ e heK h T137_0_2 hfix137_0_2 hinj137_0_2 hcardT137_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK137) (T137_0_2 i) (hfix137_0_2 i) h)

/-! ### Cell (137, 5) twin -/

def T137_5_2 : Fin 5 → Coordinate 2 := fun i => T137_5list.getD i.val (0,0,0,0,0)

theorem hfix137_5_2 : ∀ i, ((T137_5_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK137)
    ∈ fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK137) :=
  repsFix_of_siftB2 rK137 ⟨5, by decide⟩ T137_5_2 (by decide)

theorem hinj137_5_2 : Function.Injective
    (fun i => ((T137_5_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK137)) :=
  repsInj_of_reduceAux2 rK137 T137_5_2 (by decide)

theorem hcardT137_5_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK137)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK137 ⟨5, by decide⟩ R137_2 hpxR137_2 hcardq137_2 (by decide)).symm

/-- **Cell (137, 5) twin (q=2).** -/
theorem cell137_5_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK137) e = true)
    (h : ↥(reps (⟨5, by decide⟩ : Fin 148))) :
    species (reps (⟨5, by decide⟩ : Fin 148)) h (basisElt (reps rK137) (charOfVec2 rK137 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK137 e (h : Coordinate 2) T137_5_2 i :=
  species_entry_eq_sum rK137 ⟨5, by decide⟩ e heK h T137_5_2 hfix137_5_2 hinj137_5_2 hcardT137_5_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨5, by decide⟩) (reps rK137) (T137_5_2 i) (hfix137_5_2 i) h)

/-! ### Cell (137, 10) twin -/

def T137_10_2 : Fin 5 → Coordinate 2 := fun i => T137_10list.getD i.val (0,0,0,0,0)

theorem hfix137_10_2 : ∀ i, ((T137_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK137)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK137) :=
  repsFix_of_siftB2 rK137 ⟨10, by decide⟩ T137_10_2 (by decide)

theorem hinj137_10_2 : Function.Injective
    (fun i => ((T137_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK137)) :=
  repsInj_of_reduceAux2 rK137 T137_10_2 (by decide)

theorem hcardT137_10_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK137)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK137 ⟨10, by decide⟩ R137_2 hpxR137_2 hcardq137_2 (by decide)).symm

/-- **Cell (137, 10) twin (q=2).** -/
theorem cell137_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK137) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK137) (charOfVec2 rK137 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK137 e (h : Coordinate 2) T137_10_2 i :=
  species_entry_eq_sum rK137 ⟨10, by decide⟩ e heK h T137_10_2 hfix137_10_2 hinj137_10_2 hcardT137_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK137) (T137_10_2 i) (hfix137_10_2 i) h)

/-! ### Cell (137, 12) twin -/

def T137_12_2 : Fin 5 → Coordinate 2 := fun i => T137_12list.getD i.val (0,0,0,0,0)

theorem hfix137_12_2 : ∀ i, ((T137_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK137)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK137) :=
  repsFix_of_siftB2 rK137 ⟨12, by decide⟩ T137_12_2 (by decide)

theorem hinj137_12_2 : Function.Injective
    (fun i => ((T137_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK137)) :=
  repsInj_of_reduceAux2 rK137 T137_12_2 (by decide)

theorem hcardT137_12_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK137)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK137 ⟨12, by decide⟩ R137_2 hpxR137_2 hcardq137_2 (by decide)).symm

/-- **Cell (137, 12) twin (q=2).** -/
theorem cell137_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK137) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK137) (charOfVec2 rK137 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK137 e (h : Coordinate 2) T137_12_2 i :=
  species_entry_eq_sum rK137 ⟨12, by decide⟩ e heK h T137_12_2 hfix137_12_2 hinj137_12_2 hcardT137_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK137) (T137_12_2 i) (hfix137_12_2 i) h)

/-! ### Cell (137, 23) twin -/

def T137_23_2 : Fin 5 → Coordinate 2 := fun i => T137_23list.getD i.val (0,0,0,0,0)

theorem hfix137_23_2 : ∀ i, ((T137_23_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK137)
    ∈ fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK137) :=
  repsFix_of_siftB2 rK137 ⟨23, by decide⟩ T137_23_2 (by decide)

theorem hinj137_23_2 : Function.Injective
    (fun i => ((T137_23_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK137)) :=
  repsInj_of_reduceAux2 rK137 T137_23_2 (by decide)

theorem hcardT137_23_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK137)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK137 ⟨23, by decide⟩ R137_2 hpxR137_2 hcardq137_2 (by decide)).symm

/-- **Cell (137, 23) twin (q=2).** -/
theorem cell137_23_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK137) e = true)
    (h : ↥(reps (⟨23, by decide⟩ : Fin 148))) :
    species (reps (⟨23, by decide⟩ : Fin 148)) h (basisElt (reps rK137) (charOfVec2 rK137 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK137 e (h : Coordinate 2) T137_23_2 i :=
  species_entry_eq_sum rK137 ⟨23, by decide⟩ e heK h T137_23_2 hfix137_23_2 hinj137_23_2 hcardT137_23_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨23, by decide⟩) (reps rK137) (T137_23_2 i) (hfix137_23_2 i) h)

/-! ### Cell (137, 30) twin -/

def T137_30_2 : Fin 5 → Coordinate 2 := fun i => T137_30list.getD i.val (0,0,0,0,0)

theorem hfix137_30_2 : ∀ i, ((T137_30_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK137)
    ∈ fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK137) :=
  repsFix_of_siftB2 rK137 ⟨30, by decide⟩ T137_30_2 (by decide)

theorem hinj137_30_2 : Function.Injective
    (fun i => ((T137_30_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK137)) :=
  repsInj_of_reduceAux2 rK137 T137_30_2 (by decide)

theorem hcardT137_30_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK137)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK137 ⟨30, by decide⟩ R137_2 hpxR137_2 hcardq137_2 (by decide)).symm

/-- **Cell (137, 30) twin (q=2).** -/
theorem cell137_30_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK137) e = true)
    (h : ↥(reps (⟨30, by decide⟩ : Fin 148))) :
    species (reps (⟨30, by decide⟩ : Fin 148)) h (basisElt (reps rK137) (charOfVec2 rK137 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK137 e (h : Coordinate 2) T137_30_2 i :=
  species_entry_eq_sum rK137 ⟨30, by decide⟩ e heK h T137_30_2 hfix137_30_2 hinj137_30_2 hcardT137_30_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨30, by decide⟩) (reps rK137) (T137_30_2 i) (hfix137_30_2 i) h)

/-! ### Cell (137, 37) twin -/

def T137_37_2 : Fin 5 → Coordinate 2 := fun i => T137_37list.getD i.val (0,0,0,0,0)

theorem hfix137_37_2 : ∀ i, ((T137_37_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK137)
    ∈ fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK137) :=
  repsFix_of_siftB2 rK137 ⟨37, by decide⟩ T137_37_2 (by decide)

theorem hinj137_37_2 : Function.Injective
    (fun i => ((T137_37_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK137)) :=
  repsInj_of_reduceAux2 rK137 T137_37_2 (by decide)

theorem hcardT137_37_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK137)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK137 ⟨37, by decide⟩ R137_2 hpxR137_2 hcardq137_2 (by decide)).symm

/-- **Cell (137, 37) twin (q=2).** -/
theorem cell137_37_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK137) e = true)
    (h : ↥(reps (⟨37, by decide⟩ : Fin 148))) :
    species (reps (⟨37, by decide⟩ : Fin 148)) h (basisElt (reps rK137) (charOfVec2 rK137 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK137 e (h : Coordinate 2) T137_37_2 i :=
  species_entry_eq_sum rK137 ⟨37, by decide⟩ e heK h T137_37_2 hfix137_37_2 hinj137_37_2 hcardT137_37_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨37, by decide⟩) (reps rK137) (T137_37_2 i) (hfix137_37_2 i) h)

/-! ### Cell (137, 41) twin -/

def T137_41_2 : Fin 5 → Coordinate 2 := fun i => T137_41list.getD i.val (0,0,0,0,0)

theorem hfix137_41_2 : ∀ i, ((T137_41_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK137)
    ∈ fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK137) :=
  repsFix_of_siftB2 rK137 ⟨41, by decide⟩ T137_41_2 (by decide)

theorem hinj137_41_2 : Function.Injective
    (fun i => ((T137_41_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK137)) :=
  repsInj_of_reduceAux2 rK137 T137_41_2 (by decide)

theorem hcardT137_41_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK137)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK137 ⟨41, by decide⟩ R137_2 hpxR137_2 hcardq137_2 (by decide)).symm

/-- **Cell (137, 41) twin (q=2).** -/
theorem cell137_41_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK137) e = true)
    (h : ↥(reps (⟨41, by decide⟩ : Fin 148))) :
    species (reps (⟨41, by decide⟩ : Fin 148)) h (basisElt (reps rK137) (charOfVec2 rK137 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK137 e (h : Coordinate 2) T137_41_2 i :=
  species_entry_eq_sum rK137 ⟨41, by decide⟩ e heK h T137_41_2 hfix137_41_2 hinj137_41_2 hcardT137_41_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨41, by decide⟩) (reps rK137) (T137_41_2 i) (hfix137_41_2 i) h)

/-! ### Cell (137, 43) twin -/

def T137_43_2 : Fin 5 → Coordinate 2 := fun i => T137_43list.getD i.val (0,0,0,0,0)

theorem hfix137_43_2 : ∀ i, ((T137_43_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK137)
    ∈ fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK137) :=
  repsFix_of_siftB2 rK137 ⟨43, by decide⟩ T137_43_2 (by decide)

theorem hinj137_43_2 : Function.Injective
    (fun i => ((T137_43_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK137)) :=
  repsInj_of_reduceAux2 rK137 T137_43_2 (by decide)

theorem hcardT137_43_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK137)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK137 ⟨43, by decide⟩ R137_2 hpxR137_2 hcardq137_2 (by decide)).symm

/-- **Cell (137, 43) twin (q=2).** -/
theorem cell137_43_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK137) e = true)
    (h : ↥(reps (⟨43, by decide⟩ : Fin 148))) :
    species (reps (⟨43, by decide⟩ : Fin 148)) h (basisElt (reps rK137) (charOfVec2 rK137 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK137 e (h : Coordinate 2) T137_43_2 i :=
  species_entry_eq_sum rK137 ⟨43, by decide⟩ e heK h T137_43_2 hfix137_43_2 hinj137_43_2 hcardT137_43_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨43, by decide⟩) (reps rK137) (T137_43_2 i) (hfix137_43_2 i) h)

/-! ### Cell (137, 49) twin -/

def T137_49_2 : Fin 5 → Coordinate 2 := fun i => T137_49list.getD i.val (0,0,0,0,0)

theorem hfix137_49_2 : ∀ i, ((T137_49_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK137)
    ∈ fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK137) :=
  repsFix_of_siftB2 rK137 ⟨49, by decide⟩ T137_49_2 (by decide)

theorem hinj137_49_2 : Function.Injective
    (fun i => ((T137_49_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK137)) :=
  repsInj_of_reduceAux2 rK137 T137_49_2 (by decide)

theorem hcardT137_49_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK137)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK137 ⟨49, by decide⟩ R137_2 hpxR137_2 hcardq137_2 (by decide)).symm

/-- **Cell (137, 49) twin (q=2).** -/
theorem cell137_49_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK137) e = true)
    (h : ↥(reps (⟨49, by decide⟩ : Fin 148))) :
    species (reps (⟨49, by decide⟩ : Fin 148)) h (basisElt (reps rK137) (charOfVec2 rK137 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK137 e (h : Coordinate 2) T137_49_2 i :=
  species_entry_eq_sum rK137 ⟨49, by decide⟩ e heK h T137_49_2 hfix137_49_2 hinj137_49_2 hcardT137_49_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨49, by decide⟩) (reps rK137) (T137_49_2 i) (hfix137_49_2 i) h)

/-! ### Cell (137, 53) twin -/

def T137_53_2 : Fin 5 → Coordinate 2 := fun i => T137_53list.getD i.val (0,0,0,0,0)

theorem hfix137_53_2 : ∀ i, ((T137_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK137)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK137) :=
  repsFix_of_siftB2 rK137 ⟨53, by decide⟩ T137_53_2 (by decide)

theorem hinj137_53_2 : Function.Injective
    (fun i => ((T137_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK137)) :=
  repsInj_of_reduceAux2 rK137 T137_53_2 (by decide)

theorem hcardT137_53_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK137)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK137 ⟨53, by decide⟩ R137_2 hpxR137_2 hcardq137_2 (by decide)).symm

/-- **Cell (137, 53) twin (q=2).** -/
theorem cell137_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK137) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK137) (charOfVec2 rK137 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK137 e (h : Coordinate 2) T137_53_2 i :=
  species_entry_eq_sum rK137 ⟨53, by decide⟩ e heK h T137_53_2 hfix137_53_2 hinj137_53_2 hcardT137_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK137) (T137_53_2 i) (hfix137_53_2 i) h)

/-! ### Cell (137, 84) twin -/

def T137_84_2 : Fin 5 → Coordinate 2 := fun i => T137_84list.getD i.val (0,0,0,0,0)

theorem hfix137_84_2 : ∀ i, ((T137_84_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK137)
    ∈ fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK137) :=
  repsFix_of_siftB2 rK137 ⟨84, by decide⟩ T137_84_2 (by decide)

theorem hinj137_84_2 : Function.Injective
    (fun i => ((T137_84_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK137)) :=
  repsInj_of_reduceAux2 rK137 T137_84_2 (by decide)

theorem hcardT137_84_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK137)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK137 ⟨84, by decide⟩ R137_2 hpxR137_2 hcardq137_2 (by decide)).symm

/-- **Cell (137, 84) twin (q=2).** -/
theorem cell137_84_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK137) e = true)
    (h : ↥(reps (⟨84, by decide⟩ : Fin 148))) :
    species (reps (⟨84, by decide⟩ : Fin 148)) h (basisElt (reps rK137) (charOfVec2 rK137 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK137 e (h : Coordinate 2) T137_84_2 i :=
  species_entry_eq_sum rK137 ⟨84, by decide⟩ e heK h T137_84_2 hfix137_84_2 hinj137_84_2 hcardT137_84_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨84, by decide⟩) (reps rK137) (T137_84_2 i) (hfix137_84_2 i) h)

/-! ### Cell (137, 92) twin -/

def T137_92_2 : Fin 5 → Coordinate 2 := fun i => T137_92list.getD i.val (0,0,0,0,0)

theorem hfix137_92_2 : ∀ i, ((T137_92_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK137)
    ∈ fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK137) :=
  repsFix_of_siftB2 rK137 ⟨92, by decide⟩ T137_92_2 (by decide)

theorem hinj137_92_2 : Function.Injective
    (fun i => ((T137_92_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK137)) :=
  repsInj_of_reduceAux2 rK137 T137_92_2 (by decide)

theorem hcardT137_92_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK137)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK137 ⟨92, by decide⟩ R137_2 hpxR137_2 hcardq137_2 (by decide)).symm

/-- **Cell (137, 92) twin (q=2).** -/
theorem cell137_92_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK137) e = true)
    (h : ↥(reps (⟨92, by decide⟩ : Fin 148))) :
    species (reps (⟨92, by decide⟩ : Fin 148)) h (basisElt (reps rK137) (charOfVec2 rK137 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK137 e (h : Coordinate 2) T137_92_2 i :=
  species_entry_eq_sum rK137 ⟨92, by decide⟩ e heK h T137_92_2 hfix137_92_2 hinj137_92_2 hcardT137_92_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨92, by decide⟩) (reps rK137) (T137_92_2 i) (hfix137_92_2 i) h)

/-! ### Cell (137, 99) twin -/

def T137_99_2 : Fin 5 → Coordinate 2 := fun i => T137_99list.getD i.val (0,0,0,0,0)

theorem hfix137_99_2 : ∀ i, ((T137_99_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK137)
    ∈ fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK137) :=
  repsFix_of_siftB2 rK137 ⟨99, by decide⟩ T137_99_2 (by decide)

theorem hinj137_99_2 : Function.Injective
    (fun i => ((T137_99_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK137)) :=
  repsInj_of_reduceAux2 rK137 T137_99_2 (by decide)

theorem hcardT137_99_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK137)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK137 ⟨99, by decide⟩ R137_2 hpxR137_2 hcardq137_2 (by decide)).symm

/-- **Cell (137, 99) twin (q=2).** -/
theorem cell137_99_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK137) e = true)
    (h : ↥(reps (⟨99, by decide⟩ : Fin 148))) :
    species (reps (⟨99, by decide⟩ : Fin 148)) h (basisElt (reps rK137) (charOfVec2 rK137 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK137 e (h : Coordinate 2) T137_99_2 i :=
  species_entry_eq_sum rK137 ⟨99, by decide⟩ e heK h T137_99_2 hfix137_99_2 hinj137_99_2 hcardT137_99_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨99, by decide⟩) (reps rK137) (T137_99_2 i) (hfix137_99_2 i) h)

/-! ### Cell (137, 103) twin -/

def T137_103_2 : Fin 5 → Coordinate 2 := fun i => T137_103list.getD i.val (0,0,0,0,0)

theorem hfix137_103_2 : ∀ i, ((T137_103_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK137)
    ∈ fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK137) :=
  repsFix_of_siftB2 rK137 ⟨103, by decide⟩ T137_103_2 (by decide)

theorem hinj137_103_2 : Function.Injective
    (fun i => ((T137_103_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK137)) :=
  repsInj_of_reduceAux2 rK137 T137_103_2 (by decide)

theorem hcardT137_103_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK137)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK137 ⟨103, by decide⟩ R137_2 hpxR137_2 hcardq137_2 (by decide)).symm

/-- **Cell (137, 103) twin (q=2).** -/
theorem cell137_103_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK137) e = true)
    (h : ↥(reps (⟨103, by decide⟩ : Fin 148))) :
    species (reps (⟨103, by decide⟩ : Fin 148)) h (basisElt (reps rK137) (charOfVec2 rK137 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK137 e (h : Coordinate 2) T137_103_2 i :=
  species_entry_eq_sum rK137 ⟨103, by decide⟩ e heK h T137_103_2 hfix137_103_2 hinj137_103_2 hcardT137_103_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨103, by decide⟩) (reps rK137) (T137_103_2 i) (hfix137_103_2 i) h)

/-! ### Cell (137, 105) twin -/

def T137_105_2 : Fin 5 → Coordinate 2 := fun i => T137_105list.getD i.val (0,0,0,0,0)

theorem hfix137_105_2 : ∀ i, ((T137_105_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK137)
    ∈ fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK137) :=
  repsFix_of_siftB2 rK137 ⟨105, by decide⟩ T137_105_2 (by decide)

theorem hinj137_105_2 : Function.Injective
    (fun i => ((T137_105_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK137)) :=
  repsInj_of_reduceAux2 rK137 T137_105_2 (by decide)

theorem hcardT137_105_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK137)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK137 ⟨105, by decide⟩ R137_2 hpxR137_2 hcardq137_2 (by decide)).symm

/-- **Cell (137, 105) twin (q=2).** -/
theorem cell137_105_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK137) e = true)
    (h : ↥(reps (⟨105, by decide⟩ : Fin 148))) :
    species (reps (⟨105, by decide⟩ : Fin 148)) h (basisElt (reps rK137) (charOfVec2 rK137 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK137 e (h : Coordinate 2) T137_105_2 i :=
  species_entry_eq_sum rK137 ⟨105, by decide⟩ e heK h T137_105_2 hfix137_105_2 hinj137_105_2 hcardT137_105_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨105, by decide⟩) (reps rK137) (T137_105_2 i) (hfix137_105_2 i) h)

/-! ### Cell (137, 111) twin -/

def T137_111_2 : Fin 5 → Coordinate 2 := fun i => T137_111list.getD i.val (0,0,0,0,0)

theorem hfix137_111_2 : ∀ i, ((T137_111_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK137)
    ∈ fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK137) :=
  repsFix_of_siftB2 rK137 ⟨111, by decide⟩ T137_111_2 (by decide)

theorem hinj137_111_2 : Function.Injective
    (fun i => ((T137_111_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK137)) :=
  repsInj_of_reduceAux2 rK137 T137_111_2 (by decide)

theorem hcardT137_111_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK137)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK137 ⟨111, by decide⟩ R137_2 hpxR137_2 hcardq137_2 (by decide)).symm

/-- **Cell (137, 111) twin (q=2).** -/
theorem cell137_111_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK137) e = true)
    (h : ↥(reps (⟨111, by decide⟩ : Fin 148))) :
    species (reps (⟨111, by decide⟩ : Fin 148)) h (basisElt (reps rK137) (charOfVec2 rK137 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK137 e (h : Coordinate 2) T137_111_2 i :=
  species_entry_eq_sum rK137 ⟨111, by decide⟩ e heK h T137_111_2 hfix137_111_2 hinj137_111_2 hcardT137_111_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨111, by decide⟩) (reps rK137) (T137_111_2 i) (hfix137_111_2 i) h)

/-! ### Cell (137, 137) twin -/

def T137_137_2 : Fin 5 → Coordinate 2 := fun i => T137_137list.getD i.val (0,0,0,0,0)

theorem hfix137_137_2 : ∀ i, ((T137_137_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK137)
    ∈ fixedPoints (reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK137) :=
  repsFix_of_siftB2 rK137 ⟨137, by decide⟩ T137_137_2 (by decide)

theorem hinj137_137_2 : Function.Injective
    (fun i => ((T137_137_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK137)) :=
  repsInj_of_reduceAux2 rK137 T137_137_2 (by decide)

theorem hcardT137_137_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK137)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK137 ⟨137, by decide⟩ R137_2 hpxR137_2 hcardq137_2 (by decide)).symm

/-- **Cell (137, 137) twin (q=2).** -/
theorem cell137_137_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK137) e = true)
    (h : ↥(reps (⟨137, by decide⟩ : Fin 148))) :
    species (reps (⟨137, by decide⟩ : Fin 148)) h (basisElt (reps rK137) (charOfVec2 rK137 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK137 e (h : Coordinate 2) T137_137_2 i :=
  species_entry_eq_sum rK137 ⟨137, by decide⟩ e heK h T137_137_2 hfix137_137_2 hinj137_137_2 hcardT137_137_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨137, by decide⟩) (reps rK137) (T137_137_2 i) (hfix137_137_2 i) h)

end Q2

end LeanDring.P5Presentation
