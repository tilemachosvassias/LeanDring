/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, K-strata data (5^4 stratum, rK 146-146): certified per-cell species-entry instantiations, both
twins.

Covers K-classes 146 (order-5^4 K, |R|=5).  For each nonzero `H`-column
(`(G/K)^H ≠ ∅`), the full coset transversal `R146..` and each `H`-fixed
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

/-! # K-class rK = 146  (|G/K| = 5) -/

def rK146 : Fin 148 := ⟨146, by decide⟩

def R146list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def R146 : Fin 5 → Coordinate 1 := fun i => R146list.getD i.val (0,0,0,0,0)

theorem hpxR146 : Function.Injective (fun i => reduceAux 1 (basisAt rK146) (R146 i)) := by decide
theorem hcardq146 : Nat.card (Coordinate 1 ⧸ reps rK146) = 5 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (146, 0): |T| = 5 -/

def T146_0list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T146_0 : Fin 5 → Coordinate 1 := fun i => T146_0list.getD i.val (0,0,0,0,0)

theorem hfix146_0 : ∀ i, ((T146_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK146)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146) :=
  repsFix_of_siftB rK146 ⟨0, by decide⟩ T146_0 (by decide)

theorem hinj146_0 : Function.Injective
    (fun i => ((T146_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK146)) :=
  repsInj_of_reduceAux rK146 T146_0 (by decide)

theorem hcardT146_0 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK146 ⟨0, by decide⟩ R146 hpxR146 hcardq146 (by decide)).symm

/-- **Cell (146, 0).** -/
theorem cell146_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK146) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK146) (charOfVec rK146 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK146 e (h : Coordinate 1) T146_0 i :=
  species_entry_eq_sum rK146 ⟨0, by decide⟩ e heK h T146_0 hfix146_0 hinj146_0 hcardT146_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK146) (T146_0 i) (hfix146_0 i) h)

/-! ## Cell (146, 10): |T| = 5 -/

def T146_10list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T146_10 : Fin 5 → Coordinate 1 := fun i => T146_10list.getD i.val (0,0,0,0,0)

theorem hfix146_10 : ∀ i, ((T146_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK146)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146) :=
  repsFix_of_siftB rK146 ⟨10, by decide⟩ T146_10 (by decide)

theorem hinj146_10 : Function.Injective
    (fun i => ((T146_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK146)) :=
  repsInj_of_reduceAux rK146 T146_10 (by decide)

theorem hcardT146_10 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK146 ⟨10, by decide⟩ R146 hpxR146 hcardq146 (by decide)).symm

/-- **Cell (146, 10).** -/
theorem cell146_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK146) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK146) (charOfVec rK146 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK146 e (h : Coordinate 1) T146_10 i :=
  species_entry_eq_sum rK146 ⟨10, by decide⟩ e heK h T146_10 hfix146_10 hinj146_10 hcardT146_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK146) (T146_10 i) (hfix146_10 i) h)

/-! ## Cell (146, 11): |T| = 5 -/

def T146_11list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T146_11 : Fin 5 → Coordinate 1 := fun i => T146_11list.getD i.val (0,0,0,0,0)

theorem hfix146_11 : ∀ i, ((T146_11 i : Coordinate 1) : Coordinate 1 ⧸ reps rK146)
    ∈ fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146) :=
  repsFix_of_siftB rK146 ⟨11, by decide⟩ T146_11 (by decide)

theorem hinj146_11 : Function.Injective
    (fun i => ((T146_11 i : Coordinate 1) : Coordinate 1 ⧸ reps rK146)) :=
  repsInj_of_reduceAux rK146 T146_11 (by decide)

theorem hcardT146_11 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK146 ⟨11, by decide⟩ R146 hpxR146 hcardq146 (by decide)).symm

/-- **Cell (146, 11).** -/
theorem cell146_11 (e : List (ZMod 25)) (heK : charOK (basisAt rK146) e = true)
    (h : ↥(reps (⟨11, by decide⟩ : Fin 148))) :
    species (reps (⟨11, by decide⟩ : Fin 148)) h (basisElt (reps rK146) (charOfVec rK146 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK146 e (h : Coordinate 1) T146_11 i :=
  species_entry_eq_sum rK146 ⟨11, by decide⟩ e heK h T146_11 hfix146_11 hinj146_11 hcardT146_11
    (fun i => conj_mem_of_fixedPoints (reps ⟨11, by decide⟩) (reps rK146) (T146_11 i) (hfix146_11 i) h)

/-! ## Cell (146, 12): |T| = 5 -/

def T146_12list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T146_12 : Fin 5 → Coordinate 1 := fun i => T146_12list.getD i.val (0,0,0,0,0)

theorem hfix146_12 : ∀ i, ((T146_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK146)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146) :=
  repsFix_of_siftB rK146 ⟨12, by decide⟩ T146_12 (by decide)

theorem hinj146_12 : Function.Injective
    (fun i => ((T146_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK146)) :=
  repsInj_of_reduceAux rK146 T146_12 (by decide)

theorem hcardT146_12 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK146 ⟨12, by decide⟩ R146 hpxR146 hcardq146 (by decide)).symm

/-- **Cell (146, 12).** -/
theorem cell146_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK146) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK146) (charOfVec rK146 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK146 e (h : Coordinate 1) T146_12 i :=
  species_entry_eq_sum rK146 ⟨12, by decide⟩ e heK h T146_12 hfix146_12 hinj146_12 hcardT146_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK146) (T146_12 i) (hfix146_12 i) h)

/-! ## Cell (146, 48): |T| = 5 -/

def T146_48list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T146_48 : Fin 5 → Coordinate 1 := fun i => T146_48list.getD i.val (0,0,0,0,0)

theorem hfix146_48 : ∀ i, ((T146_48 i : Coordinate 1) : Coordinate 1 ⧸ reps rK146)
    ∈ fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146) :=
  repsFix_of_siftB rK146 ⟨48, by decide⟩ T146_48 (by decide)

theorem hinj146_48 : Function.Injective
    (fun i => ((T146_48 i : Coordinate 1) : Coordinate 1 ⧸ reps rK146)) :=
  repsInj_of_reduceAux rK146 T146_48 (by decide)

theorem hcardT146_48 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK146 ⟨48, by decide⟩ R146 hpxR146 hcardq146 (by decide)).symm

/-- **Cell (146, 48).** -/
theorem cell146_48 (e : List (ZMod 25)) (heK : charOK (basisAt rK146) e = true)
    (h : ↥(reps (⟨48, by decide⟩ : Fin 148))) :
    species (reps (⟨48, by decide⟩ : Fin 148)) h (basisElt (reps rK146) (charOfVec rK146 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK146 e (h : Coordinate 1) T146_48 i :=
  species_entry_eq_sum rK146 ⟨48, by decide⟩ e heK h T146_48 hfix146_48 hinj146_48 hcardT146_48
    (fun i => conj_mem_of_fixedPoints (reps ⟨48, by decide⟩) (reps rK146) (T146_48 i) (hfix146_48 i) h)

/-! ## Cell (146, 49): |T| = 5 -/

def T146_49list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T146_49 : Fin 5 → Coordinate 1 := fun i => T146_49list.getD i.val (0,0,0,0,0)

theorem hfix146_49 : ∀ i, ((T146_49 i : Coordinate 1) : Coordinate 1 ⧸ reps rK146)
    ∈ fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146) :=
  repsFix_of_siftB rK146 ⟨49, by decide⟩ T146_49 (by decide)

theorem hinj146_49 : Function.Injective
    (fun i => ((T146_49 i : Coordinate 1) : Coordinate 1 ⧸ reps rK146)) :=
  repsInj_of_reduceAux rK146 T146_49 (by decide)

theorem hcardT146_49 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK146 ⟨49, by decide⟩ R146 hpxR146 hcardq146 (by decide)).symm

/-- **Cell (146, 49).** -/
theorem cell146_49 (e : List (ZMod 25)) (heK : charOK (basisAt rK146) e = true)
    (h : ↥(reps (⟨49, by decide⟩ : Fin 148))) :
    species (reps (⟨49, by decide⟩ : Fin 148)) h (basisElt (reps rK146) (charOfVec rK146 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK146 e (h : Coordinate 1) T146_49 i :=
  species_entry_eq_sum rK146 ⟨49, by decide⟩ e heK h T146_49 hfix146_49 hinj146_49 hcardT146_49
    (fun i => conj_mem_of_fixedPoints (reps ⟨49, by decide⟩) (reps rK146) (T146_49 i) (hfix146_49 i) h)

/-! ## Cell (146, 50): |T| = 5 -/

def T146_50list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T146_50 : Fin 5 → Coordinate 1 := fun i => T146_50list.getD i.val (0,0,0,0,0)

theorem hfix146_50 : ∀ i, ((T146_50 i : Coordinate 1) : Coordinate 1 ⧸ reps rK146)
    ∈ fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146) :=
  repsFix_of_siftB rK146 ⟨50, by decide⟩ T146_50 (by decide)

theorem hinj146_50 : Function.Injective
    (fun i => ((T146_50 i : Coordinate 1) : Coordinate 1 ⧸ reps rK146)) :=
  repsInj_of_reduceAux rK146 T146_50 (by decide)

theorem hcardT146_50 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK146 ⟨50, by decide⟩ R146 hpxR146 hcardq146 (by decide)).symm

/-- **Cell (146, 50).** -/
theorem cell146_50 (e : List (ZMod 25)) (heK : charOK (basisAt rK146) e = true)
    (h : ↥(reps (⟨50, by decide⟩ : Fin 148))) :
    species (reps (⟨50, by decide⟩ : Fin 148)) h (basisElt (reps rK146) (charOfVec rK146 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK146 e (h : Coordinate 1) T146_50 i :=
  species_entry_eq_sum rK146 ⟨50, by decide⟩ e heK h T146_50 hfix146_50 hinj146_50 hcardT146_50
    (fun i => conj_mem_of_fixedPoints (reps ⟨50, by decide⟩) (reps rK146) (T146_50 i) (hfix146_50 i) h)

/-! ## Cell (146, 51): |T| = 5 -/

def T146_51list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T146_51 : Fin 5 → Coordinate 1 := fun i => T146_51list.getD i.val (0,0,0,0,0)

theorem hfix146_51 : ∀ i, ((T146_51 i : Coordinate 1) : Coordinate 1 ⧸ reps rK146)
    ∈ fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146) :=
  repsFix_of_siftB rK146 ⟨51, by decide⟩ T146_51 (by decide)

theorem hinj146_51 : Function.Injective
    (fun i => ((T146_51 i : Coordinate 1) : Coordinate 1 ⧸ reps rK146)) :=
  repsInj_of_reduceAux rK146 T146_51 (by decide)

theorem hcardT146_51 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK146 ⟨51, by decide⟩ R146 hpxR146 hcardq146 (by decide)).symm

/-- **Cell (146, 51).** -/
theorem cell146_51 (e : List (ZMod 25)) (heK : charOK (basisAt rK146) e = true)
    (h : ↥(reps (⟨51, by decide⟩ : Fin 148))) :
    species (reps (⟨51, by decide⟩ : Fin 148)) h (basisElt (reps rK146) (charOfVec rK146 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK146 e (h : Coordinate 1) T146_51 i :=
  species_entry_eq_sum rK146 ⟨51, by decide⟩ e heK h T146_51 hfix146_51 hinj146_51 hcardT146_51
    (fun i => conj_mem_of_fixedPoints (reps ⟨51, by decide⟩) (reps rK146) (T146_51 i) (hfix146_51 i) h)

/-! ## Cell (146, 52): |T| = 5 -/

def T146_52list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T146_52 : Fin 5 → Coordinate 1 := fun i => T146_52list.getD i.val (0,0,0,0,0)

theorem hfix146_52 : ∀ i, ((T146_52 i : Coordinate 1) : Coordinate 1 ⧸ reps rK146)
    ∈ fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146) :=
  repsFix_of_siftB rK146 ⟨52, by decide⟩ T146_52 (by decide)

theorem hinj146_52 : Function.Injective
    (fun i => ((T146_52 i : Coordinate 1) : Coordinate 1 ⧸ reps rK146)) :=
  repsInj_of_reduceAux rK146 T146_52 (by decide)

theorem hcardT146_52 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK146 ⟨52, by decide⟩ R146 hpxR146 hcardq146 (by decide)).symm

/-- **Cell (146, 52).** -/
theorem cell146_52 (e : List (ZMod 25)) (heK : charOK (basisAt rK146) e = true)
    (h : ↥(reps (⟨52, by decide⟩ : Fin 148))) :
    species (reps (⟨52, by decide⟩ : Fin 148)) h (basisElt (reps rK146) (charOfVec rK146 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK146 e (h : Coordinate 1) T146_52 i :=
  species_entry_eq_sum rK146 ⟨52, by decide⟩ e heK h T146_52 hfix146_52 hinj146_52 hcardT146_52
    (fun i => conj_mem_of_fixedPoints (reps ⟨52, by decide⟩) (reps rK146) (T146_52 i) (hfix146_52 i) h)

/-! ## Cell (146, 53): |T| = 5 -/

def T146_53list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T146_53 : Fin 5 → Coordinate 1 := fun i => T146_53list.getD i.val (0,0,0,0,0)

theorem hfix146_53 : ∀ i, ((T146_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK146)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146) :=
  repsFix_of_siftB rK146 ⟨53, by decide⟩ T146_53 (by decide)

theorem hinj146_53 : Function.Injective
    (fun i => ((T146_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK146)) :=
  repsInj_of_reduceAux rK146 T146_53 (by decide)

theorem hcardT146_53 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK146 ⟨53, by decide⟩ R146 hpxR146 hcardq146 (by decide)).symm

/-- **Cell (146, 53).** -/
theorem cell146_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK146) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK146) (charOfVec rK146 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK146 e (h : Coordinate 1) T146_53 i :=
  species_entry_eq_sum rK146 ⟨53, by decide⟩ e heK h T146_53 hfix146_53 hinj146_53 hcardT146_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK146) (T146_53 i) (hfix146_53 i) h)

/-! ## Cell (146, 54): |T| = 5 -/

def T146_54list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T146_54 : Fin 5 → Coordinate 1 := fun i => T146_54list.getD i.val (0,0,0,0,0)

theorem hfix146_54 : ∀ i, ((T146_54 i : Coordinate 1) : Coordinate 1 ⧸ reps rK146)
    ∈ fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146) :=
  repsFix_of_siftB rK146 ⟨54, by decide⟩ T146_54 (by decide)

theorem hinj146_54 : Function.Injective
    (fun i => ((T146_54 i : Coordinate 1) : Coordinate 1 ⧸ reps rK146)) :=
  repsInj_of_reduceAux rK146 T146_54 (by decide)

theorem hcardT146_54 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK146 ⟨54, by decide⟩ R146 hpxR146 hcardq146 (by decide)).symm

/-- **Cell (146, 54).** -/
theorem cell146_54 (e : List (ZMod 25)) (heK : charOK (basisAt rK146) e = true)
    (h : ↥(reps (⟨54, by decide⟩ : Fin 148))) :
    species (reps (⟨54, by decide⟩ : Fin 148)) h (basisElt (reps rK146) (charOfVec rK146 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK146 e (h : Coordinate 1) T146_54 i :=
  species_entry_eq_sum rK146 ⟨54, by decide⟩ e heK h T146_54 hfix146_54 hinj146_54 hcardT146_54
    (fun i => conj_mem_of_fixedPoints (reps ⟨54, by decide⟩) (reps rK146) (T146_54 i) (hfix146_54 i) h)

/-! ## Cell (146, 110): |T| = 5 -/

def T146_110list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T146_110 : Fin 5 → Coordinate 1 := fun i => T146_110list.getD i.val (0,0,0,0,0)

theorem hfix146_110 : ∀ i, ((T146_110 i : Coordinate 1) : Coordinate 1 ⧸ reps rK146)
    ∈ fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146) :=
  repsFix_of_siftB rK146 ⟨110, by decide⟩ T146_110 (by decide)

theorem hinj146_110 : Function.Injective
    (fun i => ((T146_110 i : Coordinate 1) : Coordinate 1 ⧸ reps rK146)) :=
  repsInj_of_reduceAux rK146 T146_110 (by decide)

theorem hcardT146_110 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK146 ⟨110, by decide⟩ R146 hpxR146 hcardq146 (by decide)).symm

/-- **Cell (146, 110).** -/
theorem cell146_110 (e : List (ZMod 25)) (heK : charOK (basisAt rK146) e = true)
    (h : ↥(reps (⟨110, by decide⟩ : Fin 148))) :
    species (reps (⟨110, by decide⟩ : Fin 148)) h (basisElt (reps rK146) (charOfVec rK146 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK146 e (h : Coordinate 1) T146_110 i :=
  species_entry_eq_sum rK146 ⟨110, by decide⟩ e heK h T146_110 hfix146_110 hinj146_110 hcardT146_110
    (fun i => conj_mem_of_fixedPoints (reps ⟨110, by decide⟩) (reps rK146) (T146_110 i) (hfix146_110 i) h)

/-! ## Cell (146, 111): |T| = 5 -/

def T146_111list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T146_111 : Fin 5 → Coordinate 1 := fun i => T146_111list.getD i.val (0,0,0,0,0)

theorem hfix146_111 : ∀ i, ((T146_111 i : Coordinate 1) : Coordinate 1 ⧸ reps rK146)
    ∈ fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146) :=
  repsFix_of_siftB rK146 ⟨111, by decide⟩ T146_111 (by decide)

theorem hinj146_111 : Function.Injective
    (fun i => ((T146_111 i : Coordinate 1) : Coordinate 1 ⧸ reps rK146)) :=
  repsInj_of_reduceAux rK146 T146_111 (by decide)

theorem hcardT146_111 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK146 ⟨111, by decide⟩ R146 hpxR146 hcardq146 (by decide)).symm

/-- **Cell (146, 111).** -/
theorem cell146_111 (e : List (ZMod 25)) (heK : charOK (basisAt rK146) e = true)
    (h : ↥(reps (⟨111, by decide⟩ : Fin 148))) :
    species (reps (⟨111, by decide⟩ : Fin 148)) h (basisElt (reps rK146) (charOfVec rK146 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK146 e (h : Coordinate 1) T146_111 i :=
  species_entry_eq_sum rK146 ⟨111, by decide⟩ e heK h T146_111 hfix146_111 hinj146_111 hcardT146_111
    (fun i => conj_mem_of_fixedPoints (reps ⟨111, by decide⟩) (reps rK146) (T146_111 i) (hfix146_111 i) h)

/-! ## Cell (146, 112): |T| = 5 -/

def T146_112list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T146_112 : Fin 5 → Coordinate 1 := fun i => T146_112list.getD i.val (0,0,0,0,0)

theorem hfix146_112 : ∀ i, ((T146_112 i : Coordinate 1) : Coordinate 1 ⧸ reps rK146)
    ∈ fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146) :=
  repsFix_of_siftB rK146 ⟨112, by decide⟩ T146_112 (by decide)

theorem hinj146_112 : Function.Injective
    (fun i => ((T146_112 i : Coordinate 1) : Coordinate 1 ⧸ reps rK146)) :=
  repsInj_of_reduceAux rK146 T146_112 (by decide)

theorem hcardT146_112 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK146 ⟨112, by decide⟩ R146 hpxR146 hcardq146 (by decide)).symm

/-- **Cell (146, 112).** -/
theorem cell146_112 (e : List (ZMod 25)) (heK : charOK (basisAt rK146) e = true)
    (h : ↥(reps (⟨112, by decide⟩ : Fin 148))) :
    species (reps (⟨112, by decide⟩ : Fin 148)) h (basisElt (reps rK146) (charOfVec rK146 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK146 e (h : Coordinate 1) T146_112 i :=
  species_entry_eq_sum rK146 ⟨112, by decide⟩ e heK h T146_112 hfix146_112 hinj146_112 hcardT146_112
    (fun i => conj_mem_of_fixedPoints (reps ⟨112, by decide⟩) (reps rK146) (T146_112 i) (hfix146_112 i) h)

/-! ## Cell (146, 113): |T| = 5 -/

def T146_113list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T146_113 : Fin 5 → Coordinate 1 := fun i => T146_113list.getD i.val (0,0,0,0,0)

theorem hfix146_113 : ∀ i, ((T146_113 i : Coordinate 1) : Coordinate 1 ⧸ reps rK146)
    ∈ fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146) :=
  repsFix_of_siftB rK146 ⟨113, by decide⟩ T146_113 (by decide)

theorem hinj146_113 : Function.Injective
    (fun i => ((T146_113 i : Coordinate 1) : Coordinate 1 ⧸ reps rK146)) :=
  repsInj_of_reduceAux rK146 T146_113 (by decide)

theorem hcardT146_113 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK146 ⟨113, by decide⟩ R146 hpxR146 hcardq146 (by decide)).symm

/-- **Cell (146, 113).** -/
theorem cell146_113 (e : List (ZMod 25)) (heK : charOK (basisAt rK146) e = true)
    (h : ↥(reps (⟨113, by decide⟩ : Fin 148))) :
    species (reps (⟨113, by decide⟩ : Fin 148)) h (basisElt (reps rK146) (charOfVec rK146 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK146 e (h : Coordinate 1) T146_113 i :=
  species_entry_eq_sum rK146 ⟨113, by decide⟩ e heK h T146_113 hfix146_113 hinj146_113 hcardT146_113
    (fun i => conj_mem_of_fixedPoints (reps ⟨113, by decide⟩) (reps rK146) (T146_113 i) (hfix146_113 i) h)

/-! ## Cell (146, 114): |T| = 5 -/

def T146_114list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T146_114 : Fin 5 → Coordinate 1 := fun i => T146_114list.getD i.val (0,0,0,0,0)

theorem hfix146_114 : ∀ i, ((T146_114 i : Coordinate 1) : Coordinate 1 ⧸ reps rK146)
    ∈ fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146) :=
  repsFix_of_siftB rK146 ⟨114, by decide⟩ T146_114 (by decide)

theorem hinj146_114 : Function.Injective
    (fun i => ((T146_114 i : Coordinate 1) : Coordinate 1 ⧸ reps rK146)) :=
  repsInj_of_reduceAux rK146 T146_114 (by decide)

theorem hcardT146_114 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK146 ⟨114, by decide⟩ R146 hpxR146 hcardq146 (by decide)).symm

/-- **Cell (146, 114).** -/
theorem cell146_114 (e : List (ZMod 25)) (heK : charOK (basisAt rK146) e = true)
    (h : ↥(reps (⟨114, by decide⟩ : Fin 148))) :
    species (reps (⟨114, by decide⟩ : Fin 148)) h (basisElt (reps rK146) (charOfVec rK146 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK146 e (h : Coordinate 1) T146_114 i :=
  species_entry_eq_sum rK146 ⟨114, by decide⟩ e heK h T146_114 hfix146_114 hinj146_114 hcardT146_114
    (fun i => conj_mem_of_fixedPoints (reps ⟨114, by decide⟩) (reps rK146) (T146_114 i) (hfix146_114 i) h)

/-! ## Cell (146, 115): |T| = 5 -/

def T146_115list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T146_115 : Fin 5 → Coordinate 1 := fun i => T146_115list.getD i.val (0,0,0,0,0)

theorem hfix146_115 : ∀ i, ((T146_115 i : Coordinate 1) : Coordinate 1 ⧸ reps rK146)
    ∈ fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146) :=
  repsFix_of_siftB rK146 ⟨115, by decide⟩ T146_115 (by decide)

theorem hinj146_115 : Function.Injective
    (fun i => ((T146_115 i : Coordinate 1) : Coordinate 1 ⧸ reps rK146)) :=
  repsInj_of_reduceAux rK146 T146_115 (by decide)

theorem hcardT146_115 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK146 ⟨115, by decide⟩ R146 hpxR146 hcardq146 (by decide)).symm

/-- **Cell (146, 115).** -/
theorem cell146_115 (e : List (ZMod 25)) (heK : charOK (basisAt rK146) e = true)
    (h : ↥(reps (⟨115, by decide⟩ : Fin 148))) :
    species (reps (⟨115, by decide⟩ : Fin 148)) h (basisElt (reps rK146) (charOfVec rK146 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK146 e (h : Coordinate 1) T146_115 i :=
  species_entry_eq_sum rK146 ⟨115, by decide⟩ e heK h T146_115 hfix146_115 hinj146_115 hcardT146_115
    (fun i => conj_mem_of_fixedPoints (reps ⟨115, by decide⟩) (reps rK146) (T146_115 i) (hfix146_115 i) h)

/-! ## Cell (146, 146): |T| = 5 -/

def T146_146list : List Coordinates := [(0,0,0,0,0), (0,0,1,0,0), (0,0,2,0,0), (0,0,3,0,0), (0,0,4,0,0)]
def T146_146 : Fin 5 → Coordinate 1 := fun i => T146_146list.getD i.val (0,0,0,0,0)

theorem hfix146_146 : ∀ i, ((T146_146 i : Coordinate 1) : Coordinate 1 ⧸ reps rK146)
    ∈ fixedPoints (reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146) :=
  repsFix_of_siftB rK146 ⟨146, by decide⟩ T146_146 (by decide)

theorem hinj146_146 : Function.Injective
    (fun i => ((T146_146 i : Coordinate 1) : Coordinate 1 ⧸ reps rK146)) :=
  repsInj_of_reduceAux rK146 T146_146 (by decide)

theorem hcardT146_146 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK146 ⟨146, by decide⟩ R146 hpxR146 hcardq146 (by decide)).symm

/-- **Cell (146, 146).** -/
theorem cell146_146 (e : List (ZMod 25)) (heK : charOK (basisAt rK146) e = true)
    (h : ↥(reps (⟨146, by decide⟩ : Fin 148))) :
    species (reps (⟨146, by decide⟩ : Fin 148)) h (basisElt (reps rK146) (charOfVec rK146 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK146 e (h : Coordinate 1) T146_146 i :=
  species_entry_eq_sum rK146 ⟨146, by decide⟩ e heK h T146_146 hfix146_146 hinj146_146 hcardT146_146
    (fun i => conj_mem_of_fixedPoints (reps ⟨146, by decide⟩) (reps rK146) (T146_146 i) (hfix146_146 i) h)

namespace Q2

def R146_2 : Fin 5 → Coordinate 2 := fun i => R146list.getD i.val (0,0,0,0,0)
theorem hpxR146_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK146) (R146_2 i)) := by decide
theorem hcardq146_2 : Nat.card (Coordinate 2 ⧸ reps rK146) = 5 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (146, 0) twin -/

def T146_0_2 : Fin 5 → Coordinate 2 := fun i => T146_0list.getD i.val (0,0,0,0,0)

theorem hfix146_0_2 : ∀ i, ((T146_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK146)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK146) :=
  repsFix_of_siftB2 rK146 ⟨0, by decide⟩ T146_0_2 (by decide)

theorem hinj146_0_2 : Function.Injective
    (fun i => ((T146_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK146)) :=
  repsInj_of_reduceAux2 rK146 T146_0_2 (by decide)

theorem hcardT146_0_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK146)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK146 ⟨0, by decide⟩ R146_2 hpxR146_2 hcardq146_2 (by decide)).symm

/-- **Cell (146, 0) twin (q=2).** -/
theorem cell146_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK146) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK146) (charOfVec2 rK146 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK146 e (h : Coordinate 2) T146_0_2 i :=
  species_entry_eq_sum rK146 ⟨0, by decide⟩ e heK h T146_0_2 hfix146_0_2 hinj146_0_2 hcardT146_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK146) (T146_0_2 i) (hfix146_0_2 i) h)

/-! ### Cell (146, 10) twin -/

def T146_10_2 : Fin 5 → Coordinate 2 := fun i => T146_10list.getD i.val (0,0,0,0,0)

theorem hfix146_10_2 : ∀ i, ((T146_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK146)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK146) :=
  repsFix_of_siftB2 rK146 ⟨10, by decide⟩ T146_10_2 (by decide)

theorem hinj146_10_2 : Function.Injective
    (fun i => ((T146_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK146)) :=
  repsInj_of_reduceAux2 rK146 T146_10_2 (by decide)

theorem hcardT146_10_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK146)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK146 ⟨10, by decide⟩ R146_2 hpxR146_2 hcardq146_2 (by decide)).symm

/-- **Cell (146, 10) twin (q=2).** -/
theorem cell146_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK146) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK146) (charOfVec2 rK146 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK146 e (h : Coordinate 2) T146_10_2 i :=
  species_entry_eq_sum rK146 ⟨10, by decide⟩ e heK h T146_10_2 hfix146_10_2 hinj146_10_2 hcardT146_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK146) (T146_10_2 i) (hfix146_10_2 i) h)

/-! ### Cell (146, 11) twin -/

def T146_11_2 : Fin 5 → Coordinate 2 := fun i => T146_11list.getD i.val (0,0,0,0,0)

theorem hfix146_11_2 : ∀ i, ((T146_11_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK146)
    ∈ fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK146) :=
  repsFix_of_siftB2 rK146 ⟨11, by decide⟩ T146_11_2 (by decide)

theorem hinj146_11_2 : Function.Injective
    (fun i => ((T146_11_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK146)) :=
  repsInj_of_reduceAux2 rK146 T146_11_2 (by decide)

theorem hcardT146_11_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK146)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK146 ⟨11, by decide⟩ R146_2 hpxR146_2 hcardq146_2 (by decide)).symm

/-- **Cell (146, 11) twin (q=2).** -/
theorem cell146_11_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK146) e = true)
    (h : ↥(reps (⟨11, by decide⟩ : Fin 148))) :
    species (reps (⟨11, by decide⟩ : Fin 148)) h (basisElt (reps rK146) (charOfVec2 rK146 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK146 e (h : Coordinate 2) T146_11_2 i :=
  species_entry_eq_sum rK146 ⟨11, by decide⟩ e heK h T146_11_2 hfix146_11_2 hinj146_11_2 hcardT146_11_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨11, by decide⟩) (reps rK146) (T146_11_2 i) (hfix146_11_2 i) h)

/-! ### Cell (146, 12) twin -/

def T146_12_2 : Fin 5 → Coordinate 2 := fun i => T146_12list.getD i.val (0,0,0,0,0)

theorem hfix146_12_2 : ∀ i, ((T146_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK146)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK146) :=
  repsFix_of_siftB2 rK146 ⟨12, by decide⟩ T146_12_2 (by decide)

theorem hinj146_12_2 : Function.Injective
    (fun i => ((T146_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK146)) :=
  repsInj_of_reduceAux2 rK146 T146_12_2 (by decide)

theorem hcardT146_12_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK146)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK146 ⟨12, by decide⟩ R146_2 hpxR146_2 hcardq146_2 (by decide)).symm

/-- **Cell (146, 12) twin (q=2).** -/
theorem cell146_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK146) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK146) (charOfVec2 rK146 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK146 e (h : Coordinate 2) T146_12_2 i :=
  species_entry_eq_sum rK146 ⟨12, by decide⟩ e heK h T146_12_2 hfix146_12_2 hinj146_12_2 hcardT146_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK146) (T146_12_2 i) (hfix146_12_2 i) h)

/-! ### Cell (146, 48) twin -/

def T146_48_2 : Fin 5 → Coordinate 2 := fun i => T146_48list.getD i.val (0,0,0,0,0)

theorem hfix146_48_2 : ∀ i, ((T146_48_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK146)
    ∈ fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK146) :=
  repsFix_of_siftB2 rK146 ⟨48, by decide⟩ T146_48_2 (by decide)

theorem hinj146_48_2 : Function.Injective
    (fun i => ((T146_48_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK146)) :=
  repsInj_of_reduceAux2 rK146 T146_48_2 (by decide)

theorem hcardT146_48_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK146)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK146 ⟨48, by decide⟩ R146_2 hpxR146_2 hcardq146_2 (by decide)).symm

/-- **Cell (146, 48) twin (q=2).** -/
theorem cell146_48_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK146) e = true)
    (h : ↥(reps (⟨48, by decide⟩ : Fin 148))) :
    species (reps (⟨48, by decide⟩ : Fin 148)) h (basisElt (reps rK146) (charOfVec2 rK146 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK146 e (h : Coordinate 2) T146_48_2 i :=
  species_entry_eq_sum rK146 ⟨48, by decide⟩ e heK h T146_48_2 hfix146_48_2 hinj146_48_2 hcardT146_48_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨48, by decide⟩) (reps rK146) (T146_48_2 i) (hfix146_48_2 i) h)

/-! ### Cell (146, 49) twin -/

def T146_49_2 : Fin 5 → Coordinate 2 := fun i => T146_49list.getD i.val (0,0,0,0,0)

theorem hfix146_49_2 : ∀ i, ((T146_49_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK146)
    ∈ fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK146) :=
  repsFix_of_siftB2 rK146 ⟨49, by decide⟩ T146_49_2 (by decide)

theorem hinj146_49_2 : Function.Injective
    (fun i => ((T146_49_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK146)) :=
  repsInj_of_reduceAux2 rK146 T146_49_2 (by decide)

theorem hcardT146_49_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK146)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK146 ⟨49, by decide⟩ R146_2 hpxR146_2 hcardq146_2 (by decide)).symm

/-- **Cell (146, 49) twin (q=2).** -/
theorem cell146_49_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK146) e = true)
    (h : ↥(reps (⟨49, by decide⟩ : Fin 148))) :
    species (reps (⟨49, by decide⟩ : Fin 148)) h (basisElt (reps rK146) (charOfVec2 rK146 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK146 e (h : Coordinate 2) T146_49_2 i :=
  species_entry_eq_sum rK146 ⟨49, by decide⟩ e heK h T146_49_2 hfix146_49_2 hinj146_49_2 hcardT146_49_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨49, by decide⟩) (reps rK146) (T146_49_2 i) (hfix146_49_2 i) h)

/-! ### Cell (146, 50) twin -/

def T146_50_2 : Fin 5 → Coordinate 2 := fun i => T146_50list.getD i.val (0,0,0,0,0)

theorem hfix146_50_2 : ∀ i, ((T146_50_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK146)
    ∈ fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK146) :=
  repsFix_of_siftB2 rK146 ⟨50, by decide⟩ T146_50_2 (by decide)

theorem hinj146_50_2 : Function.Injective
    (fun i => ((T146_50_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK146)) :=
  repsInj_of_reduceAux2 rK146 T146_50_2 (by decide)

theorem hcardT146_50_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK146)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK146 ⟨50, by decide⟩ R146_2 hpxR146_2 hcardq146_2 (by decide)).symm

/-- **Cell (146, 50) twin (q=2).** -/
theorem cell146_50_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK146) e = true)
    (h : ↥(reps (⟨50, by decide⟩ : Fin 148))) :
    species (reps (⟨50, by decide⟩ : Fin 148)) h (basisElt (reps rK146) (charOfVec2 rK146 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK146 e (h : Coordinate 2) T146_50_2 i :=
  species_entry_eq_sum rK146 ⟨50, by decide⟩ e heK h T146_50_2 hfix146_50_2 hinj146_50_2 hcardT146_50_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨50, by decide⟩) (reps rK146) (T146_50_2 i) (hfix146_50_2 i) h)

/-! ### Cell (146, 51) twin -/

def T146_51_2 : Fin 5 → Coordinate 2 := fun i => T146_51list.getD i.val (0,0,0,0,0)

theorem hfix146_51_2 : ∀ i, ((T146_51_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK146)
    ∈ fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK146) :=
  repsFix_of_siftB2 rK146 ⟨51, by decide⟩ T146_51_2 (by decide)

theorem hinj146_51_2 : Function.Injective
    (fun i => ((T146_51_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK146)) :=
  repsInj_of_reduceAux2 rK146 T146_51_2 (by decide)

theorem hcardT146_51_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK146)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK146 ⟨51, by decide⟩ R146_2 hpxR146_2 hcardq146_2 (by decide)).symm

/-- **Cell (146, 51) twin (q=2).** -/
theorem cell146_51_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK146) e = true)
    (h : ↥(reps (⟨51, by decide⟩ : Fin 148))) :
    species (reps (⟨51, by decide⟩ : Fin 148)) h (basisElt (reps rK146) (charOfVec2 rK146 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK146 e (h : Coordinate 2) T146_51_2 i :=
  species_entry_eq_sum rK146 ⟨51, by decide⟩ e heK h T146_51_2 hfix146_51_2 hinj146_51_2 hcardT146_51_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨51, by decide⟩) (reps rK146) (T146_51_2 i) (hfix146_51_2 i) h)

/-! ### Cell (146, 52) twin -/

def T146_52_2 : Fin 5 → Coordinate 2 := fun i => T146_52list.getD i.val (0,0,0,0,0)

theorem hfix146_52_2 : ∀ i, ((T146_52_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK146)
    ∈ fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK146) :=
  repsFix_of_siftB2 rK146 ⟨52, by decide⟩ T146_52_2 (by decide)

theorem hinj146_52_2 : Function.Injective
    (fun i => ((T146_52_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK146)) :=
  repsInj_of_reduceAux2 rK146 T146_52_2 (by decide)

theorem hcardT146_52_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK146)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK146 ⟨52, by decide⟩ R146_2 hpxR146_2 hcardq146_2 (by decide)).symm

/-- **Cell (146, 52) twin (q=2).** -/
theorem cell146_52_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK146) e = true)
    (h : ↥(reps (⟨52, by decide⟩ : Fin 148))) :
    species (reps (⟨52, by decide⟩ : Fin 148)) h (basisElt (reps rK146) (charOfVec2 rK146 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK146 e (h : Coordinate 2) T146_52_2 i :=
  species_entry_eq_sum rK146 ⟨52, by decide⟩ e heK h T146_52_2 hfix146_52_2 hinj146_52_2 hcardT146_52_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨52, by decide⟩) (reps rK146) (T146_52_2 i) (hfix146_52_2 i) h)

/-! ### Cell (146, 53) twin -/

def T146_53_2 : Fin 5 → Coordinate 2 := fun i => T146_53list.getD i.val (0,0,0,0,0)

theorem hfix146_53_2 : ∀ i, ((T146_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK146)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK146) :=
  repsFix_of_siftB2 rK146 ⟨53, by decide⟩ T146_53_2 (by decide)

theorem hinj146_53_2 : Function.Injective
    (fun i => ((T146_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK146)) :=
  repsInj_of_reduceAux2 rK146 T146_53_2 (by decide)

theorem hcardT146_53_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK146)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK146 ⟨53, by decide⟩ R146_2 hpxR146_2 hcardq146_2 (by decide)).symm

/-- **Cell (146, 53) twin (q=2).** -/
theorem cell146_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK146) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK146) (charOfVec2 rK146 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK146 e (h : Coordinate 2) T146_53_2 i :=
  species_entry_eq_sum rK146 ⟨53, by decide⟩ e heK h T146_53_2 hfix146_53_2 hinj146_53_2 hcardT146_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK146) (T146_53_2 i) (hfix146_53_2 i) h)

/-! ### Cell (146, 54) twin -/

def T146_54_2 : Fin 5 → Coordinate 2 := fun i => T146_54list.getD i.val (0,0,0,0,0)

theorem hfix146_54_2 : ∀ i, ((T146_54_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK146)
    ∈ fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK146) :=
  repsFix_of_siftB2 rK146 ⟨54, by decide⟩ T146_54_2 (by decide)

theorem hinj146_54_2 : Function.Injective
    (fun i => ((T146_54_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK146)) :=
  repsInj_of_reduceAux2 rK146 T146_54_2 (by decide)

theorem hcardT146_54_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK146)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK146 ⟨54, by decide⟩ R146_2 hpxR146_2 hcardq146_2 (by decide)).symm

/-- **Cell (146, 54) twin (q=2).** -/
theorem cell146_54_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK146) e = true)
    (h : ↥(reps (⟨54, by decide⟩ : Fin 148))) :
    species (reps (⟨54, by decide⟩ : Fin 148)) h (basisElt (reps rK146) (charOfVec2 rK146 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK146 e (h : Coordinate 2) T146_54_2 i :=
  species_entry_eq_sum rK146 ⟨54, by decide⟩ e heK h T146_54_2 hfix146_54_2 hinj146_54_2 hcardT146_54_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨54, by decide⟩) (reps rK146) (T146_54_2 i) (hfix146_54_2 i) h)

/-! ### Cell (146, 110) twin -/

def T146_110_2 : Fin 5 → Coordinate 2 := fun i => T146_110list.getD i.val (0,0,0,0,0)

theorem hfix146_110_2 : ∀ i, ((T146_110_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK146)
    ∈ fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK146) :=
  repsFix_of_siftB2 rK146 ⟨110, by decide⟩ T146_110_2 (by decide)

theorem hinj146_110_2 : Function.Injective
    (fun i => ((T146_110_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK146)) :=
  repsInj_of_reduceAux2 rK146 T146_110_2 (by decide)

theorem hcardT146_110_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK146)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK146 ⟨110, by decide⟩ R146_2 hpxR146_2 hcardq146_2 (by decide)).symm

/-- **Cell (146, 110) twin (q=2).** -/
theorem cell146_110_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK146) e = true)
    (h : ↥(reps (⟨110, by decide⟩ : Fin 148))) :
    species (reps (⟨110, by decide⟩ : Fin 148)) h (basisElt (reps rK146) (charOfVec2 rK146 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK146 e (h : Coordinate 2) T146_110_2 i :=
  species_entry_eq_sum rK146 ⟨110, by decide⟩ e heK h T146_110_2 hfix146_110_2 hinj146_110_2 hcardT146_110_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨110, by decide⟩) (reps rK146) (T146_110_2 i) (hfix146_110_2 i) h)

/-! ### Cell (146, 111) twin -/

def T146_111_2 : Fin 5 → Coordinate 2 := fun i => T146_111list.getD i.val (0,0,0,0,0)

theorem hfix146_111_2 : ∀ i, ((T146_111_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK146)
    ∈ fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK146) :=
  repsFix_of_siftB2 rK146 ⟨111, by decide⟩ T146_111_2 (by decide)

theorem hinj146_111_2 : Function.Injective
    (fun i => ((T146_111_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK146)) :=
  repsInj_of_reduceAux2 rK146 T146_111_2 (by decide)

theorem hcardT146_111_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK146)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK146 ⟨111, by decide⟩ R146_2 hpxR146_2 hcardq146_2 (by decide)).symm

/-- **Cell (146, 111) twin (q=2).** -/
theorem cell146_111_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK146) e = true)
    (h : ↥(reps (⟨111, by decide⟩ : Fin 148))) :
    species (reps (⟨111, by decide⟩ : Fin 148)) h (basisElt (reps rK146) (charOfVec2 rK146 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK146 e (h : Coordinate 2) T146_111_2 i :=
  species_entry_eq_sum rK146 ⟨111, by decide⟩ e heK h T146_111_2 hfix146_111_2 hinj146_111_2 hcardT146_111_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨111, by decide⟩) (reps rK146) (T146_111_2 i) (hfix146_111_2 i) h)

/-! ### Cell (146, 112) twin -/

def T146_112_2 : Fin 5 → Coordinate 2 := fun i => T146_112list.getD i.val (0,0,0,0,0)

theorem hfix146_112_2 : ∀ i, ((T146_112_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK146)
    ∈ fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK146) :=
  repsFix_of_siftB2 rK146 ⟨112, by decide⟩ T146_112_2 (by decide)

theorem hinj146_112_2 : Function.Injective
    (fun i => ((T146_112_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK146)) :=
  repsInj_of_reduceAux2 rK146 T146_112_2 (by decide)

theorem hcardT146_112_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK146)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK146 ⟨112, by decide⟩ R146_2 hpxR146_2 hcardq146_2 (by decide)).symm

/-- **Cell (146, 112) twin (q=2).** -/
theorem cell146_112_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK146) e = true)
    (h : ↥(reps (⟨112, by decide⟩ : Fin 148))) :
    species (reps (⟨112, by decide⟩ : Fin 148)) h (basisElt (reps rK146) (charOfVec2 rK146 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK146 e (h : Coordinate 2) T146_112_2 i :=
  species_entry_eq_sum rK146 ⟨112, by decide⟩ e heK h T146_112_2 hfix146_112_2 hinj146_112_2 hcardT146_112_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨112, by decide⟩) (reps rK146) (T146_112_2 i) (hfix146_112_2 i) h)

/-! ### Cell (146, 113) twin -/

def T146_113_2 : Fin 5 → Coordinate 2 := fun i => T146_113list.getD i.val (0,0,0,0,0)

theorem hfix146_113_2 : ∀ i, ((T146_113_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK146)
    ∈ fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK146) :=
  repsFix_of_siftB2 rK146 ⟨113, by decide⟩ T146_113_2 (by decide)

theorem hinj146_113_2 : Function.Injective
    (fun i => ((T146_113_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK146)) :=
  repsInj_of_reduceAux2 rK146 T146_113_2 (by decide)

theorem hcardT146_113_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK146)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK146 ⟨113, by decide⟩ R146_2 hpxR146_2 hcardq146_2 (by decide)).symm

/-- **Cell (146, 113) twin (q=2).** -/
theorem cell146_113_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK146) e = true)
    (h : ↥(reps (⟨113, by decide⟩ : Fin 148))) :
    species (reps (⟨113, by decide⟩ : Fin 148)) h (basisElt (reps rK146) (charOfVec2 rK146 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK146 e (h : Coordinate 2) T146_113_2 i :=
  species_entry_eq_sum rK146 ⟨113, by decide⟩ e heK h T146_113_2 hfix146_113_2 hinj146_113_2 hcardT146_113_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨113, by decide⟩) (reps rK146) (T146_113_2 i) (hfix146_113_2 i) h)

/-! ### Cell (146, 114) twin -/

def T146_114_2 : Fin 5 → Coordinate 2 := fun i => T146_114list.getD i.val (0,0,0,0,0)

theorem hfix146_114_2 : ∀ i, ((T146_114_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK146)
    ∈ fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK146) :=
  repsFix_of_siftB2 rK146 ⟨114, by decide⟩ T146_114_2 (by decide)

theorem hinj146_114_2 : Function.Injective
    (fun i => ((T146_114_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK146)) :=
  repsInj_of_reduceAux2 rK146 T146_114_2 (by decide)

theorem hcardT146_114_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK146)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK146 ⟨114, by decide⟩ R146_2 hpxR146_2 hcardq146_2 (by decide)).symm

/-- **Cell (146, 114) twin (q=2).** -/
theorem cell146_114_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK146) e = true)
    (h : ↥(reps (⟨114, by decide⟩ : Fin 148))) :
    species (reps (⟨114, by decide⟩ : Fin 148)) h (basisElt (reps rK146) (charOfVec2 rK146 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK146 e (h : Coordinate 2) T146_114_2 i :=
  species_entry_eq_sum rK146 ⟨114, by decide⟩ e heK h T146_114_2 hfix146_114_2 hinj146_114_2 hcardT146_114_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨114, by decide⟩) (reps rK146) (T146_114_2 i) (hfix146_114_2 i) h)

/-! ### Cell (146, 115) twin -/

def T146_115_2 : Fin 5 → Coordinate 2 := fun i => T146_115list.getD i.val (0,0,0,0,0)

theorem hfix146_115_2 : ∀ i, ((T146_115_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK146)
    ∈ fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK146) :=
  repsFix_of_siftB2 rK146 ⟨115, by decide⟩ T146_115_2 (by decide)

theorem hinj146_115_2 : Function.Injective
    (fun i => ((T146_115_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK146)) :=
  repsInj_of_reduceAux2 rK146 T146_115_2 (by decide)

theorem hcardT146_115_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK146)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK146 ⟨115, by decide⟩ R146_2 hpxR146_2 hcardq146_2 (by decide)).symm

/-- **Cell (146, 115) twin (q=2).** -/
theorem cell146_115_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK146) e = true)
    (h : ↥(reps (⟨115, by decide⟩ : Fin 148))) :
    species (reps (⟨115, by decide⟩ : Fin 148)) h (basisElt (reps rK146) (charOfVec2 rK146 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK146 e (h : Coordinate 2) T146_115_2 i :=
  species_entry_eq_sum rK146 ⟨115, by decide⟩ e heK h T146_115_2 hfix146_115_2 hinj146_115_2 hcardT146_115_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨115, by decide⟩) (reps rK146) (T146_115_2 i) (hfix146_115_2 i) h)

/-! ### Cell (146, 146) twin -/

def T146_146_2 : Fin 5 → Coordinate 2 := fun i => T146_146list.getD i.val (0,0,0,0,0)

theorem hfix146_146_2 : ∀ i, ((T146_146_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK146)
    ∈ fixedPoints (reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK146) :=
  repsFix_of_siftB2 rK146 ⟨146, by decide⟩ T146_146_2 (by decide)

theorem hinj146_146_2 : Function.Injective
    (fun i => ((T146_146_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK146)) :=
  repsInj_of_reduceAux2 rK146 T146_146_2 (by decide)

theorem hcardT146_146_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK146)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK146 ⟨146, by decide⟩ R146_2 hpxR146_2 hcardq146_2 (by decide)).symm

/-- **Cell (146, 146) twin (q=2).** -/
theorem cell146_146_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK146) e = true)
    (h : ↥(reps (⟨146, by decide⟩ : Fin 148))) :
    species (reps (⟨146, by decide⟩ : Fin 148)) h (basisElt (reps rK146) (charOfVec2 rK146 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK146 e (h : Coordinate 2) T146_146_2 i :=
  species_entry_eq_sum rK146 ⟨146, by decide⟩ e heK h T146_146_2 hfix146_146_2 hinj146_146_2 hcardT146_146_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨146, by decide⟩) (reps rK146) (T146_146_2 i) (hfix146_146_2 i) h)

end Q2

end LeanDring.P5Presentation
