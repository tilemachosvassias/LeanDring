/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, K-strata data (TOP stratum, rK 147): certified per-cell species-entry instantiations, both
twins.

Covers K-classes 147 (K=G, |R|=1).  For each nonzero `H`-column
(`(G/K)^H ≠ ∅`), the full coset transversal `R147..` and each `H`-fixed
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

/-! # K-class rK = 147  (|G/K| = 1) -/

def rK147 : Fin 148 := ⟨147, by decide⟩

def R147list : List Coordinates := [(0,0,0,0,0)]
def R147 : Fin 1 → Coordinate 1 := fun i => R147list.getD i.val (0,0,0,0,0)

theorem hpxR147 : Function.Injective (fun i => reduceAux 1 (basisAt rK147) (R147 i)) := by decide
theorem hcardq147 : Nat.card (Coordinate 1 ⧸ reps rK147) = 1 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (147, 0): |T| = 1 -/

def T147_0list : List Coordinates := [(0,0,0,0,0)]
def T147_0 : Fin 1 → Coordinate 1 := fun i => T147_0list.getD i.val (0,0,0,0,0)

theorem hfix147_0 : ∀ i, ((T147_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨0, by decide⟩ T147_0 (by decide)

theorem hinj147_0 : Function.Injective
    (fun i => ((T147_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_0 (by decide)

theorem hcardT147_0 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨0, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 0).** -/
theorem cell147_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_0 i :=
  species_entry_eq_sum rK147 ⟨0, by decide⟩ e heK h T147_0 hfix147_0 hinj147_0 hcardT147_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK147) (T147_0 i) (hfix147_0 i) h)

/-! ## Cell (147, 1): |T| = 1 -/

def T147_1list : List Coordinates := [(0,0,0,0,0)]
def T147_1 : Fin 1 → Coordinate 1 := fun i => T147_1list.getD i.val (0,0,0,0,0)

theorem hfix147_1 : ∀ i, ((T147_1 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨1, by decide⟩ T147_1 (by decide)

theorem hinj147_1 : Function.Injective
    (fun i => ((T147_1 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_1 (by decide)

theorem hcardT147_1 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨1, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 1).** -/
theorem cell147_1 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨1, by decide⟩ : Fin 148))) :
    species (reps (⟨1, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_1 i :=
  species_entry_eq_sum rK147 ⟨1, by decide⟩ e heK h T147_1 hfix147_1 hinj147_1 hcardT147_1
    (fun i => conj_mem_of_fixedPoints (reps ⟨1, by decide⟩) (reps rK147) (T147_1 i) (hfix147_1 i) h)

/-! ## Cell (147, 2): |T| = 1 -/

def T147_2list : List Coordinates := [(0,0,0,0,0)]
def T147_2 : Fin 1 → Coordinate 1 := fun i => T147_2list.getD i.val (0,0,0,0,0)

theorem hfix147_2 : ∀ i, ((T147_2 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨2, by decide⟩ T147_2 (by decide)

theorem hinj147_2 : Function.Injective
    (fun i => ((T147_2 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_2 (by decide)

theorem hcardT147_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨2, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 2).** -/
theorem cell147_2 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨2, by decide⟩ : Fin 148))) :
    species (reps (⟨2, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_2 i :=
  species_entry_eq_sum rK147 ⟨2, by decide⟩ e heK h T147_2 hfix147_2 hinj147_2 hcardT147_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨2, by decide⟩) (reps rK147) (T147_2 i) (hfix147_2 i) h)

/-! ## Cell (147, 3): |T| = 1 -/

def T147_3list : List Coordinates := [(0,0,0,0,0)]
def T147_3 : Fin 1 → Coordinate 1 := fun i => T147_3list.getD i.val (0,0,0,0,0)

theorem hfix147_3 : ∀ i, ((T147_3 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨3, by decide⟩ T147_3 (by decide)

theorem hinj147_3 : Function.Injective
    (fun i => ((T147_3 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_3 (by decide)

theorem hcardT147_3 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨3, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 3).** -/
theorem cell147_3 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨3, by decide⟩ : Fin 148))) :
    species (reps (⟨3, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_3 i :=
  species_entry_eq_sum rK147 ⟨3, by decide⟩ e heK h T147_3 hfix147_3 hinj147_3 hcardT147_3
    (fun i => conj_mem_of_fixedPoints (reps ⟨3, by decide⟩) (reps rK147) (T147_3 i) (hfix147_3 i) h)

/-! ## Cell (147, 4): |T| = 1 -/

def T147_4list : List Coordinates := [(0,0,0,0,0)]
def T147_4 : Fin 1 → Coordinate 1 := fun i => T147_4list.getD i.val (0,0,0,0,0)

theorem hfix147_4 : ∀ i, ((T147_4 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨4, by decide⟩ T147_4 (by decide)

theorem hinj147_4 : Function.Injective
    (fun i => ((T147_4 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_4 (by decide)

theorem hcardT147_4 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨4, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 4).** -/
theorem cell147_4 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨4, by decide⟩ : Fin 148))) :
    species (reps (⟨4, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_4 i :=
  species_entry_eq_sum rK147 ⟨4, by decide⟩ e heK h T147_4 hfix147_4 hinj147_4 hcardT147_4
    (fun i => conj_mem_of_fixedPoints (reps ⟨4, by decide⟩) (reps rK147) (T147_4 i) (hfix147_4 i) h)

/-! ## Cell (147, 5): |T| = 1 -/

def T147_5list : List Coordinates := [(0,0,0,0,0)]
def T147_5 : Fin 1 → Coordinate 1 := fun i => T147_5list.getD i.val (0,0,0,0,0)

theorem hfix147_5 : ∀ i, ((T147_5 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨5, by decide⟩ T147_5 (by decide)

theorem hinj147_5 : Function.Injective
    (fun i => ((T147_5 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_5 (by decide)

theorem hcardT147_5 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨5, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 5).** -/
theorem cell147_5 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨5, by decide⟩ : Fin 148))) :
    species (reps (⟨5, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_5 i :=
  species_entry_eq_sum rK147 ⟨5, by decide⟩ e heK h T147_5 hfix147_5 hinj147_5 hcardT147_5
    (fun i => conj_mem_of_fixedPoints (reps ⟨5, by decide⟩) (reps rK147) (T147_5 i) (hfix147_5 i) h)

/-! ## Cell (147, 6): |T| = 1 -/

def T147_6list : List Coordinates := [(0,0,0,0,0)]
def T147_6 : Fin 1 → Coordinate 1 := fun i => T147_6list.getD i.val (0,0,0,0,0)

theorem hfix147_6 : ∀ i, ((T147_6 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨6, by decide⟩ T147_6 (by decide)

theorem hinj147_6 : Function.Injective
    (fun i => ((T147_6 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_6 (by decide)

theorem hcardT147_6 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨6, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 6).** -/
theorem cell147_6 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨6, by decide⟩ : Fin 148))) :
    species (reps (⟨6, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_6 i :=
  species_entry_eq_sum rK147 ⟨6, by decide⟩ e heK h T147_6 hfix147_6 hinj147_6 hcardT147_6
    (fun i => conj_mem_of_fixedPoints (reps ⟨6, by decide⟩) (reps rK147) (T147_6 i) (hfix147_6 i) h)

/-! ## Cell (147, 7): |T| = 1 -/

def T147_7list : List Coordinates := [(0,0,0,0,0)]
def T147_7 : Fin 1 → Coordinate 1 := fun i => T147_7list.getD i.val (0,0,0,0,0)

theorem hfix147_7 : ∀ i, ((T147_7 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨7, by decide⟩ T147_7 (by decide)

theorem hinj147_7 : Function.Injective
    (fun i => ((T147_7 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_7 (by decide)

theorem hcardT147_7 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨7, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 7).** -/
theorem cell147_7 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨7, by decide⟩ : Fin 148))) :
    species (reps (⟨7, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_7 i :=
  species_entry_eq_sum rK147 ⟨7, by decide⟩ e heK h T147_7 hfix147_7 hinj147_7 hcardT147_7
    (fun i => conj_mem_of_fixedPoints (reps ⟨7, by decide⟩) (reps rK147) (T147_7 i) (hfix147_7 i) h)

/-! ## Cell (147, 8): |T| = 1 -/

def T147_8list : List Coordinates := [(0,0,0,0,0)]
def T147_8 : Fin 1 → Coordinate 1 := fun i => T147_8list.getD i.val (0,0,0,0,0)

theorem hfix147_8 : ∀ i, ((T147_8 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨8, by decide⟩ T147_8 (by decide)

theorem hinj147_8 : Function.Injective
    (fun i => ((T147_8 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_8 (by decide)

theorem hcardT147_8 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨8, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 8).** -/
theorem cell147_8 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨8, by decide⟩ : Fin 148))) :
    species (reps (⟨8, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_8 i :=
  species_entry_eq_sum rK147 ⟨8, by decide⟩ e heK h T147_8 hfix147_8 hinj147_8 hcardT147_8
    (fun i => conj_mem_of_fixedPoints (reps ⟨8, by decide⟩) (reps rK147) (T147_8 i) (hfix147_8 i) h)

/-! ## Cell (147, 9): |T| = 1 -/

def T147_9list : List Coordinates := [(0,0,0,0,0)]
def T147_9 : Fin 1 → Coordinate 1 := fun i => T147_9list.getD i.val (0,0,0,0,0)

theorem hfix147_9 : ∀ i, ((T147_9 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨9, by decide⟩ T147_9 (by decide)

theorem hinj147_9 : Function.Injective
    (fun i => ((T147_9 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_9 (by decide)

theorem hcardT147_9 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨9, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 9).** -/
theorem cell147_9 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨9, by decide⟩ : Fin 148))) :
    species (reps (⟨9, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_9 i :=
  species_entry_eq_sum rK147 ⟨9, by decide⟩ e heK h T147_9 hfix147_9 hinj147_9 hcardT147_9
    (fun i => conj_mem_of_fixedPoints (reps ⟨9, by decide⟩) (reps rK147) (T147_9 i) (hfix147_9 i) h)

/-! ## Cell (147, 10): |T| = 1 -/

def T147_10list : List Coordinates := [(0,0,0,0,0)]
def T147_10 : Fin 1 → Coordinate 1 := fun i => T147_10list.getD i.val (0,0,0,0,0)

theorem hfix147_10 : ∀ i, ((T147_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨10, by decide⟩ T147_10 (by decide)

theorem hinj147_10 : Function.Injective
    (fun i => ((T147_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_10 (by decide)

theorem hcardT147_10 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨10, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 10).** -/
theorem cell147_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_10 i :=
  species_entry_eq_sum rK147 ⟨10, by decide⟩ e heK h T147_10 hfix147_10 hinj147_10 hcardT147_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK147) (T147_10 i) (hfix147_10 i) h)

/-! ## Cell (147, 11): |T| = 1 -/

def T147_11list : List Coordinates := [(0,0,0,0,0)]
def T147_11 : Fin 1 → Coordinate 1 := fun i => T147_11list.getD i.val (0,0,0,0,0)

theorem hfix147_11 : ∀ i, ((T147_11 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨11, by decide⟩ T147_11 (by decide)

theorem hinj147_11 : Function.Injective
    (fun i => ((T147_11 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_11 (by decide)

theorem hcardT147_11 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨11, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 11).** -/
theorem cell147_11 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨11, by decide⟩ : Fin 148))) :
    species (reps (⟨11, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_11 i :=
  species_entry_eq_sum rK147 ⟨11, by decide⟩ e heK h T147_11 hfix147_11 hinj147_11 hcardT147_11
    (fun i => conj_mem_of_fixedPoints (reps ⟨11, by decide⟩) (reps rK147) (T147_11 i) (hfix147_11 i) h)

/-! ## Cell (147, 12): |T| = 1 -/

def T147_12list : List Coordinates := [(0,0,0,0,0)]
def T147_12 : Fin 1 → Coordinate 1 := fun i => T147_12list.getD i.val (0,0,0,0,0)

theorem hfix147_12 : ∀ i, ((T147_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨12, by decide⟩ T147_12 (by decide)

theorem hinj147_12 : Function.Injective
    (fun i => ((T147_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_12 (by decide)

theorem hcardT147_12 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨12, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 12).** -/
theorem cell147_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_12 i :=
  species_entry_eq_sum rK147 ⟨12, by decide⟩ e heK h T147_12 hfix147_12 hinj147_12 hcardT147_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK147) (T147_12 i) (hfix147_12 i) h)

/-! ## Cell (147, 13): |T| = 1 -/

def T147_13list : List Coordinates := [(0,0,0,0,0)]
def T147_13 : Fin 1 → Coordinate 1 := fun i => T147_13list.getD i.val (0,0,0,0,0)

theorem hfix147_13 : ∀ i, ((T147_13 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨13, by decide⟩ T147_13 (by decide)

theorem hinj147_13 : Function.Injective
    (fun i => ((T147_13 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_13 (by decide)

theorem hcardT147_13 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨13, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 13).** -/
theorem cell147_13 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨13, by decide⟩ : Fin 148))) :
    species (reps (⟨13, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_13 i :=
  species_entry_eq_sum rK147 ⟨13, by decide⟩ e heK h T147_13 hfix147_13 hinj147_13 hcardT147_13
    (fun i => conj_mem_of_fixedPoints (reps ⟨13, by decide⟩) (reps rK147) (T147_13 i) (hfix147_13 i) h)

/-! ## Cell (147, 14): |T| = 1 -/

def T147_14list : List Coordinates := [(0,0,0,0,0)]
def T147_14 : Fin 1 → Coordinate 1 := fun i => T147_14list.getD i.val (0,0,0,0,0)

theorem hfix147_14 : ∀ i, ((T147_14 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨14, by decide⟩ T147_14 (by decide)

theorem hinj147_14 : Function.Injective
    (fun i => ((T147_14 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_14 (by decide)

theorem hcardT147_14 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨14, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 14).** -/
theorem cell147_14 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨14, by decide⟩ : Fin 148))) :
    species (reps (⟨14, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_14 i :=
  species_entry_eq_sum rK147 ⟨14, by decide⟩ e heK h T147_14 hfix147_14 hinj147_14 hcardT147_14
    (fun i => conj_mem_of_fixedPoints (reps ⟨14, by decide⟩) (reps rK147) (T147_14 i) (hfix147_14 i) h)

/-! ## Cell (147, 15): |T| = 1 -/

def T147_15list : List Coordinates := [(0,0,0,0,0)]
def T147_15 : Fin 1 → Coordinate 1 := fun i => T147_15list.getD i.val (0,0,0,0,0)

theorem hfix147_15 : ∀ i, ((T147_15 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨15, by decide⟩ T147_15 (by decide)

theorem hinj147_15 : Function.Injective
    (fun i => ((T147_15 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_15 (by decide)

theorem hcardT147_15 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨15, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 15).** -/
theorem cell147_15 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨15, by decide⟩ : Fin 148))) :
    species (reps (⟨15, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_15 i :=
  species_entry_eq_sum rK147 ⟨15, by decide⟩ e heK h T147_15 hfix147_15 hinj147_15 hcardT147_15
    (fun i => conj_mem_of_fixedPoints (reps ⟨15, by decide⟩) (reps rK147) (T147_15 i) (hfix147_15 i) h)

/-! ## Cell (147, 16): |T| = 1 -/

def T147_16list : List Coordinates := [(0,0,0,0,0)]
def T147_16 : Fin 1 → Coordinate 1 := fun i => T147_16list.getD i.val (0,0,0,0,0)

theorem hfix147_16 : ∀ i, ((T147_16 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨16, by decide⟩ T147_16 (by decide)

theorem hinj147_16 : Function.Injective
    (fun i => ((T147_16 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_16 (by decide)

theorem hcardT147_16 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨16, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 16).** -/
theorem cell147_16 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨16, by decide⟩ : Fin 148))) :
    species (reps (⟨16, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_16 i :=
  species_entry_eq_sum rK147 ⟨16, by decide⟩ e heK h T147_16 hfix147_16 hinj147_16 hcardT147_16
    (fun i => conj_mem_of_fixedPoints (reps ⟨16, by decide⟩) (reps rK147) (T147_16 i) (hfix147_16 i) h)

/-! ## Cell (147, 17): |T| = 1 -/

def T147_17list : List Coordinates := [(0,0,0,0,0)]
def T147_17 : Fin 1 → Coordinate 1 := fun i => T147_17list.getD i.val (0,0,0,0,0)

theorem hfix147_17 : ∀ i, ((T147_17 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨17, by decide⟩ T147_17 (by decide)

theorem hinj147_17 : Function.Injective
    (fun i => ((T147_17 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_17 (by decide)

theorem hcardT147_17 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨17, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 17).** -/
theorem cell147_17 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨17, by decide⟩ : Fin 148))) :
    species (reps (⟨17, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_17 i :=
  species_entry_eq_sum rK147 ⟨17, by decide⟩ e heK h T147_17 hfix147_17 hinj147_17 hcardT147_17
    (fun i => conj_mem_of_fixedPoints (reps ⟨17, by decide⟩) (reps rK147) (T147_17 i) (hfix147_17 i) h)

/-! ## Cell (147, 18): |T| = 1 -/

def T147_18list : List Coordinates := [(0,0,0,0,0)]
def T147_18 : Fin 1 → Coordinate 1 := fun i => T147_18list.getD i.val (0,0,0,0,0)

theorem hfix147_18 : ∀ i, ((T147_18 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨18, by decide⟩ T147_18 (by decide)

theorem hinj147_18 : Function.Injective
    (fun i => ((T147_18 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_18 (by decide)

theorem hcardT147_18 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨18, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 18).** -/
theorem cell147_18 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨18, by decide⟩ : Fin 148))) :
    species (reps (⟨18, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_18 i :=
  species_entry_eq_sum rK147 ⟨18, by decide⟩ e heK h T147_18 hfix147_18 hinj147_18 hcardT147_18
    (fun i => conj_mem_of_fixedPoints (reps ⟨18, by decide⟩) (reps rK147) (T147_18 i) (hfix147_18 i) h)

/-! ## Cell (147, 19): |T| = 1 -/

def T147_19list : List Coordinates := [(0,0,0,0,0)]
def T147_19 : Fin 1 → Coordinate 1 := fun i => T147_19list.getD i.val (0,0,0,0,0)

theorem hfix147_19 : ∀ i, ((T147_19 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨19, by decide⟩ T147_19 (by decide)

theorem hinj147_19 : Function.Injective
    (fun i => ((T147_19 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_19 (by decide)

theorem hcardT147_19 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨19, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 19).** -/
theorem cell147_19 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨19, by decide⟩ : Fin 148))) :
    species (reps (⟨19, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_19 i :=
  species_entry_eq_sum rK147 ⟨19, by decide⟩ e heK h T147_19 hfix147_19 hinj147_19 hcardT147_19
    (fun i => conj_mem_of_fixedPoints (reps ⟨19, by decide⟩) (reps rK147) (T147_19 i) (hfix147_19 i) h)

/-! ## Cell (147, 20): |T| = 1 -/

def T147_20list : List Coordinates := [(0,0,0,0,0)]
def T147_20 : Fin 1 → Coordinate 1 := fun i => T147_20list.getD i.val (0,0,0,0,0)

theorem hfix147_20 : ∀ i, ((T147_20 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨20, by decide⟩ T147_20 (by decide)

theorem hinj147_20 : Function.Injective
    (fun i => ((T147_20 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_20 (by decide)

theorem hcardT147_20 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨20, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 20).** -/
theorem cell147_20 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨20, by decide⟩ : Fin 148))) :
    species (reps (⟨20, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_20 i :=
  species_entry_eq_sum rK147 ⟨20, by decide⟩ e heK h T147_20 hfix147_20 hinj147_20 hcardT147_20
    (fun i => conj_mem_of_fixedPoints (reps ⟨20, by decide⟩) (reps rK147) (T147_20 i) (hfix147_20 i) h)

/-! ## Cell (147, 21): |T| = 1 -/

def T147_21list : List Coordinates := [(0,0,0,0,0)]
def T147_21 : Fin 1 → Coordinate 1 := fun i => T147_21list.getD i.val (0,0,0,0,0)

theorem hfix147_21 : ∀ i, ((T147_21 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨21, by decide⟩ T147_21 (by decide)

theorem hinj147_21 : Function.Injective
    (fun i => ((T147_21 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_21 (by decide)

theorem hcardT147_21 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨21, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 21).** -/
theorem cell147_21 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨21, by decide⟩ : Fin 148))) :
    species (reps (⟨21, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_21 i :=
  species_entry_eq_sum rK147 ⟨21, by decide⟩ e heK h T147_21 hfix147_21 hinj147_21 hcardT147_21
    (fun i => conj_mem_of_fixedPoints (reps ⟨21, by decide⟩) (reps rK147) (T147_21 i) (hfix147_21 i) h)

/-! ## Cell (147, 22): |T| = 1 -/

def T147_22list : List Coordinates := [(0,0,0,0,0)]
def T147_22 : Fin 1 → Coordinate 1 := fun i => T147_22list.getD i.val (0,0,0,0,0)

theorem hfix147_22 : ∀ i, ((T147_22 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨22, by decide⟩ T147_22 (by decide)

theorem hinj147_22 : Function.Injective
    (fun i => ((T147_22 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_22 (by decide)

theorem hcardT147_22 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨22, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 22).** -/
theorem cell147_22 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨22, by decide⟩ : Fin 148))) :
    species (reps (⟨22, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_22 i :=
  species_entry_eq_sum rK147 ⟨22, by decide⟩ e heK h T147_22 hfix147_22 hinj147_22 hcardT147_22
    (fun i => conj_mem_of_fixedPoints (reps ⟨22, by decide⟩) (reps rK147) (T147_22 i) (hfix147_22 i) h)

/-! ## Cell (147, 23): |T| = 1 -/

def T147_23list : List Coordinates := [(0,0,0,0,0)]
def T147_23 : Fin 1 → Coordinate 1 := fun i => T147_23list.getD i.val (0,0,0,0,0)

theorem hfix147_23 : ∀ i, ((T147_23 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨23, by decide⟩ T147_23 (by decide)

theorem hinj147_23 : Function.Injective
    (fun i => ((T147_23 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_23 (by decide)

theorem hcardT147_23 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨23, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 23).** -/
theorem cell147_23 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨23, by decide⟩ : Fin 148))) :
    species (reps (⟨23, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_23 i :=
  species_entry_eq_sum rK147 ⟨23, by decide⟩ e heK h T147_23 hfix147_23 hinj147_23 hcardT147_23
    (fun i => conj_mem_of_fixedPoints (reps ⟨23, by decide⟩) (reps rK147) (T147_23 i) (hfix147_23 i) h)

/-! ## Cell (147, 24): |T| = 1 -/

def T147_24list : List Coordinates := [(0,0,0,0,0)]
def T147_24 : Fin 1 → Coordinate 1 := fun i => T147_24list.getD i.val (0,0,0,0,0)

theorem hfix147_24 : ∀ i, ((T147_24 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨24, by decide⟩ T147_24 (by decide)

theorem hinj147_24 : Function.Injective
    (fun i => ((T147_24 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_24 (by decide)

theorem hcardT147_24 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨24, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 24).** -/
theorem cell147_24 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨24, by decide⟩ : Fin 148))) :
    species (reps (⟨24, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_24 i :=
  species_entry_eq_sum rK147 ⟨24, by decide⟩ e heK h T147_24 hfix147_24 hinj147_24 hcardT147_24
    (fun i => conj_mem_of_fixedPoints (reps ⟨24, by decide⟩) (reps rK147) (T147_24 i) (hfix147_24 i) h)

/-! ## Cell (147, 25): |T| = 1 -/

def T147_25list : List Coordinates := [(0,0,0,0,0)]
def T147_25 : Fin 1 → Coordinate 1 := fun i => T147_25list.getD i.val (0,0,0,0,0)

theorem hfix147_25 : ∀ i, ((T147_25 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨25, by decide⟩ T147_25 (by decide)

theorem hinj147_25 : Function.Injective
    (fun i => ((T147_25 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_25 (by decide)

theorem hcardT147_25 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨25, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 25).** -/
theorem cell147_25 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨25, by decide⟩ : Fin 148))) :
    species (reps (⟨25, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_25 i :=
  species_entry_eq_sum rK147 ⟨25, by decide⟩ e heK h T147_25 hfix147_25 hinj147_25 hcardT147_25
    (fun i => conj_mem_of_fixedPoints (reps ⟨25, by decide⟩) (reps rK147) (T147_25 i) (hfix147_25 i) h)

/-! ## Cell (147, 26): |T| = 1 -/

def T147_26list : List Coordinates := [(0,0,0,0,0)]
def T147_26 : Fin 1 → Coordinate 1 := fun i => T147_26list.getD i.val (0,0,0,0,0)

theorem hfix147_26 : ∀ i, ((T147_26 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨26, by decide⟩ T147_26 (by decide)

theorem hinj147_26 : Function.Injective
    (fun i => ((T147_26 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_26 (by decide)

theorem hcardT147_26 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨26, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 26).** -/
theorem cell147_26 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨26, by decide⟩ : Fin 148))) :
    species (reps (⟨26, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_26 i :=
  species_entry_eq_sum rK147 ⟨26, by decide⟩ e heK h T147_26 hfix147_26 hinj147_26 hcardT147_26
    (fun i => conj_mem_of_fixedPoints (reps ⟨26, by decide⟩) (reps rK147) (T147_26 i) (hfix147_26 i) h)

/-! ## Cell (147, 27): |T| = 1 -/

def T147_27list : List Coordinates := [(0,0,0,0,0)]
def T147_27 : Fin 1 → Coordinate 1 := fun i => T147_27list.getD i.val (0,0,0,0,0)

theorem hfix147_27 : ∀ i, ((T147_27 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨27, by decide⟩ T147_27 (by decide)

theorem hinj147_27 : Function.Injective
    (fun i => ((T147_27 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_27 (by decide)

theorem hcardT147_27 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨27, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 27).** -/
theorem cell147_27 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨27, by decide⟩ : Fin 148))) :
    species (reps (⟨27, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_27 i :=
  species_entry_eq_sum rK147 ⟨27, by decide⟩ e heK h T147_27 hfix147_27 hinj147_27 hcardT147_27
    (fun i => conj_mem_of_fixedPoints (reps ⟨27, by decide⟩) (reps rK147) (T147_27 i) (hfix147_27 i) h)

/-! ## Cell (147, 28): |T| = 1 -/

def T147_28list : List Coordinates := [(0,0,0,0,0)]
def T147_28 : Fin 1 → Coordinate 1 := fun i => T147_28list.getD i.val (0,0,0,0,0)

theorem hfix147_28 : ∀ i, ((T147_28 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨28, by decide⟩ T147_28 (by decide)

theorem hinj147_28 : Function.Injective
    (fun i => ((T147_28 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_28 (by decide)

theorem hcardT147_28 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨28, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 28).** -/
theorem cell147_28 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨28, by decide⟩ : Fin 148))) :
    species (reps (⟨28, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_28 i :=
  species_entry_eq_sum rK147 ⟨28, by decide⟩ e heK h T147_28 hfix147_28 hinj147_28 hcardT147_28
    (fun i => conj_mem_of_fixedPoints (reps ⟨28, by decide⟩) (reps rK147) (T147_28 i) (hfix147_28 i) h)

/-! ## Cell (147, 29): |T| = 1 -/

def T147_29list : List Coordinates := [(0,0,0,0,0)]
def T147_29 : Fin 1 → Coordinate 1 := fun i => T147_29list.getD i.val (0,0,0,0,0)

theorem hfix147_29 : ∀ i, ((T147_29 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨29, by decide⟩ T147_29 (by decide)

theorem hinj147_29 : Function.Injective
    (fun i => ((T147_29 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_29 (by decide)

theorem hcardT147_29 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨29, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 29).** -/
theorem cell147_29 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨29, by decide⟩ : Fin 148))) :
    species (reps (⟨29, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_29 i :=
  species_entry_eq_sum rK147 ⟨29, by decide⟩ e heK h T147_29 hfix147_29 hinj147_29 hcardT147_29
    (fun i => conj_mem_of_fixedPoints (reps ⟨29, by decide⟩) (reps rK147) (T147_29 i) (hfix147_29 i) h)

/-! ## Cell (147, 30): |T| = 1 -/

def T147_30list : List Coordinates := [(0,0,0,0,0)]
def T147_30 : Fin 1 → Coordinate 1 := fun i => T147_30list.getD i.val (0,0,0,0,0)

theorem hfix147_30 : ∀ i, ((T147_30 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨30, by decide⟩ T147_30 (by decide)

theorem hinj147_30 : Function.Injective
    (fun i => ((T147_30 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_30 (by decide)

theorem hcardT147_30 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨30, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 30).** -/
theorem cell147_30 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨30, by decide⟩ : Fin 148))) :
    species (reps (⟨30, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_30 i :=
  species_entry_eq_sum rK147 ⟨30, by decide⟩ e heK h T147_30 hfix147_30 hinj147_30 hcardT147_30
    (fun i => conj_mem_of_fixedPoints (reps ⟨30, by decide⟩) (reps rK147) (T147_30 i) (hfix147_30 i) h)

/-! ## Cell (147, 31): |T| = 1 -/

def T147_31list : List Coordinates := [(0,0,0,0,0)]
def T147_31 : Fin 1 → Coordinate 1 := fun i => T147_31list.getD i.val (0,0,0,0,0)

theorem hfix147_31 : ∀ i, ((T147_31 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨31, by decide⟩ T147_31 (by decide)

theorem hinj147_31 : Function.Injective
    (fun i => ((T147_31 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_31 (by decide)

theorem hcardT147_31 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨31, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 31).** -/
theorem cell147_31 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨31, by decide⟩ : Fin 148))) :
    species (reps (⟨31, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_31 i :=
  species_entry_eq_sum rK147 ⟨31, by decide⟩ e heK h T147_31 hfix147_31 hinj147_31 hcardT147_31
    (fun i => conj_mem_of_fixedPoints (reps ⟨31, by decide⟩) (reps rK147) (T147_31 i) (hfix147_31 i) h)

/-! ## Cell (147, 32): |T| = 1 -/

def T147_32list : List Coordinates := [(0,0,0,0,0)]
def T147_32 : Fin 1 → Coordinate 1 := fun i => T147_32list.getD i.val (0,0,0,0,0)

theorem hfix147_32 : ∀ i, ((T147_32 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨32, by decide⟩ T147_32 (by decide)

theorem hinj147_32 : Function.Injective
    (fun i => ((T147_32 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_32 (by decide)

theorem hcardT147_32 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨32, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 32).** -/
theorem cell147_32 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨32, by decide⟩ : Fin 148))) :
    species (reps (⟨32, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_32 i :=
  species_entry_eq_sum rK147 ⟨32, by decide⟩ e heK h T147_32 hfix147_32 hinj147_32 hcardT147_32
    (fun i => conj_mem_of_fixedPoints (reps ⟨32, by decide⟩) (reps rK147) (T147_32 i) (hfix147_32 i) h)

/-! ## Cell (147, 33): |T| = 1 -/

def T147_33list : List Coordinates := [(0,0,0,0,0)]
def T147_33 : Fin 1 → Coordinate 1 := fun i => T147_33list.getD i.val (0,0,0,0,0)

theorem hfix147_33 : ∀ i, ((T147_33 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨33, by decide⟩ T147_33 (by decide)

theorem hinj147_33 : Function.Injective
    (fun i => ((T147_33 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_33 (by decide)

theorem hcardT147_33 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨33, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 33).** -/
theorem cell147_33 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨33, by decide⟩ : Fin 148))) :
    species (reps (⟨33, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_33 i :=
  species_entry_eq_sum rK147 ⟨33, by decide⟩ e heK h T147_33 hfix147_33 hinj147_33 hcardT147_33
    (fun i => conj_mem_of_fixedPoints (reps ⟨33, by decide⟩) (reps rK147) (T147_33 i) (hfix147_33 i) h)

/-! ## Cell (147, 34): |T| = 1 -/

def T147_34list : List Coordinates := [(0,0,0,0,0)]
def T147_34 : Fin 1 → Coordinate 1 := fun i => T147_34list.getD i.val (0,0,0,0,0)

theorem hfix147_34 : ∀ i, ((T147_34 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨34, by decide⟩ T147_34 (by decide)

theorem hinj147_34 : Function.Injective
    (fun i => ((T147_34 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_34 (by decide)

theorem hcardT147_34 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨34, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 34).** -/
theorem cell147_34 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨34, by decide⟩ : Fin 148))) :
    species (reps (⟨34, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_34 i :=
  species_entry_eq_sum rK147 ⟨34, by decide⟩ e heK h T147_34 hfix147_34 hinj147_34 hcardT147_34
    (fun i => conj_mem_of_fixedPoints (reps ⟨34, by decide⟩) (reps rK147) (T147_34 i) (hfix147_34 i) h)

/-! ## Cell (147, 35): |T| = 1 -/

def T147_35list : List Coordinates := [(0,0,0,0,0)]
def T147_35 : Fin 1 → Coordinate 1 := fun i => T147_35list.getD i.val (0,0,0,0,0)

theorem hfix147_35 : ∀ i, ((T147_35 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨35, by decide⟩ T147_35 (by decide)

theorem hinj147_35 : Function.Injective
    (fun i => ((T147_35 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_35 (by decide)

theorem hcardT147_35 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨35, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 35).** -/
theorem cell147_35 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨35, by decide⟩ : Fin 148))) :
    species (reps (⟨35, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_35 i :=
  species_entry_eq_sum rK147 ⟨35, by decide⟩ e heK h T147_35 hfix147_35 hinj147_35 hcardT147_35
    (fun i => conj_mem_of_fixedPoints (reps ⟨35, by decide⟩) (reps rK147) (T147_35 i) (hfix147_35 i) h)

/-! ## Cell (147, 36): |T| = 1 -/

def T147_36list : List Coordinates := [(0,0,0,0,0)]
def T147_36 : Fin 1 → Coordinate 1 := fun i => T147_36list.getD i.val (0,0,0,0,0)

theorem hfix147_36 : ∀ i, ((T147_36 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨36, by decide⟩ T147_36 (by decide)

theorem hinj147_36 : Function.Injective
    (fun i => ((T147_36 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_36 (by decide)

theorem hcardT147_36 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨36, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 36).** -/
theorem cell147_36 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨36, by decide⟩ : Fin 148))) :
    species (reps (⟨36, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_36 i :=
  species_entry_eq_sum rK147 ⟨36, by decide⟩ e heK h T147_36 hfix147_36 hinj147_36 hcardT147_36
    (fun i => conj_mem_of_fixedPoints (reps ⟨36, by decide⟩) (reps rK147) (T147_36 i) (hfix147_36 i) h)

/-! ## Cell (147, 37): |T| = 1 -/

def T147_37list : List Coordinates := [(0,0,0,0,0)]
def T147_37 : Fin 1 → Coordinate 1 := fun i => T147_37list.getD i.val (0,0,0,0,0)

theorem hfix147_37 : ∀ i, ((T147_37 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨37, by decide⟩ T147_37 (by decide)

theorem hinj147_37 : Function.Injective
    (fun i => ((T147_37 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_37 (by decide)

theorem hcardT147_37 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨37, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 37).** -/
theorem cell147_37 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨37, by decide⟩ : Fin 148))) :
    species (reps (⟨37, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_37 i :=
  species_entry_eq_sum rK147 ⟨37, by decide⟩ e heK h T147_37 hfix147_37 hinj147_37 hcardT147_37
    (fun i => conj_mem_of_fixedPoints (reps ⟨37, by decide⟩) (reps rK147) (T147_37 i) (hfix147_37 i) h)

/-! ## Cell (147, 38): |T| = 1 -/

def T147_38list : List Coordinates := [(0,0,0,0,0)]
def T147_38 : Fin 1 → Coordinate 1 := fun i => T147_38list.getD i.val (0,0,0,0,0)

theorem hfix147_38 : ∀ i, ((T147_38 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨38, by decide⟩ T147_38 (by decide)

theorem hinj147_38 : Function.Injective
    (fun i => ((T147_38 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_38 (by decide)

theorem hcardT147_38 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨38, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 38).** -/
theorem cell147_38 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨38, by decide⟩ : Fin 148))) :
    species (reps (⟨38, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_38 i :=
  species_entry_eq_sum rK147 ⟨38, by decide⟩ e heK h T147_38 hfix147_38 hinj147_38 hcardT147_38
    (fun i => conj_mem_of_fixedPoints (reps ⟨38, by decide⟩) (reps rK147) (T147_38 i) (hfix147_38 i) h)

/-! ## Cell (147, 39): |T| = 1 -/

def T147_39list : List Coordinates := [(0,0,0,0,0)]
def T147_39 : Fin 1 → Coordinate 1 := fun i => T147_39list.getD i.val (0,0,0,0,0)

theorem hfix147_39 : ∀ i, ((T147_39 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨39, by decide⟩ T147_39 (by decide)

theorem hinj147_39 : Function.Injective
    (fun i => ((T147_39 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_39 (by decide)

theorem hcardT147_39 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨39, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 39).** -/
theorem cell147_39 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨39, by decide⟩ : Fin 148))) :
    species (reps (⟨39, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_39 i :=
  species_entry_eq_sum rK147 ⟨39, by decide⟩ e heK h T147_39 hfix147_39 hinj147_39 hcardT147_39
    (fun i => conj_mem_of_fixedPoints (reps ⟨39, by decide⟩) (reps rK147) (T147_39 i) (hfix147_39 i) h)

/-! ## Cell (147, 40): |T| = 1 -/

def T147_40list : List Coordinates := [(0,0,0,0,0)]
def T147_40 : Fin 1 → Coordinate 1 := fun i => T147_40list.getD i.val (0,0,0,0,0)

theorem hfix147_40 : ∀ i, ((T147_40 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨40, by decide⟩ T147_40 (by decide)

theorem hinj147_40 : Function.Injective
    (fun i => ((T147_40 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_40 (by decide)

theorem hcardT147_40 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨40, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 40).** -/
theorem cell147_40 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨40, by decide⟩ : Fin 148))) :
    species (reps (⟨40, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_40 i :=
  species_entry_eq_sum rK147 ⟨40, by decide⟩ e heK h T147_40 hfix147_40 hinj147_40 hcardT147_40
    (fun i => conj_mem_of_fixedPoints (reps ⟨40, by decide⟩) (reps rK147) (T147_40 i) (hfix147_40 i) h)

/-! ## Cell (147, 41): |T| = 1 -/

def T147_41list : List Coordinates := [(0,0,0,0,0)]
def T147_41 : Fin 1 → Coordinate 1 := fun i => T147_41list.getD i.val (0,0,0,0,0)

theorem hfix147_41 : ∀ i, ((T147_41 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨41, by decide⟩ T147_41 (by decide)

theorem hinj147_41 : Function.Injective
    (fun i => ((T147_41 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_41 (by decide)

theorem hcardT147_41 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨41, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 41).** -/
theorem cell147_41 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨41, by decide⟩ : Fin 148))) :
    species (reps (⟨41, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_41 i :=
  species_entry_eq_sum rK147 ⟨41, by decide⟩ e heK h T147_41 hfix147_41 hinj147_41 hcardT147_41
    (fun i => conj_mem_of_fixedPoints (reps ⟨41, by decide⟩) (reps rK147) (T147_41 i) (hfix147_41 i) h)

/-! ## Cell (147, 42): |T| = 1 -/

def T147_42list : List Coordinates := [(0,0,0,0,0)]
def T147_42 : Fin 1 → Coordinate 1 := fun i => T147_42list.getD i.val (0,0,0,0,0)

theorem hfix147_42 : ∀ i, ((T147_42 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨42, by decide⟩ T147_42 (by decide)

theorem hinj147_42 : Function.Injective
    (fun i => ((T147_42 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_42 (by decide)

theorem hcardT147_42 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨42, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 42).** -/
theorem cell147_42 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨42, by decide⟩ : Fin 148))) :
    species (reps (⟨42, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_42 i :=
  species_entry_eq_sum rK147 ⟨42, by decide⟩ e heK h T147_42 hfix147_42 hinj147_42 hcardT147_42
    (fun i => conj_mem_of_fixedPoints (reps ⟨42, by decide⟩) (reps rK147) (T147_42 i) (hfix147_42 i) h)

/-! ## Cell (147, 43): |T| = 1 -/

def T147_43list : List Coordinates := [(0,0,0,0,0)]
def T147_43 : Fin 1 → Coordinate 1 := fun i => T147_43list.getD i.val (0,0,0,0,0)

theorem hfix147_43 : ∀ i, ((T147_43 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨43, by decide⟩ T147_43 (by decide)

theorem hinj147_43 : Function.Injective
    (fun i => ((T147_43 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_43 (by decide)

theorem hcardT147_43 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨43, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 43).** -/
theorem cell147_43 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨43, by decide⟩ : Fin 148))) :
    species (reps (⟨43, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_43 i :=
  species_entry_eq_sum rK147 ⟨43, by decide⟩ e heK h T147_43 hfix147_43 hinj147_43 hcardT147_43
    (fun i => conj_mem_of_fixedPoints (reps ⟨43, by decide⟩) (reps rK147) (T147_43 i) (hfix147_43 i) h)

/-! ## Cell (147, 44): |T| = 1 -/

def T147_44list : List Coordinates := [(0,0,0,0,0)]
def T147_44 : Fin 1 → Coordinate 1 := fun i => T147_44list.getD i.val (0,0,0,0,0)

theorem hfix147_44 : ∀ i, ((T147_44 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨44, by decide⟩ T147_44 (by decide)

theorem hinj147_44 : Function.Injective
    (fun i => ((T147_44 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_44 (by decide)

theorem hcardT147_44 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨44, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 44).** -/
theorem cell147_44 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨44, by decide⟩ : Fin 148))) :
    species (reps (⟨44, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_44 i :=
  species_entry_eq_sum rK147 ⟨44, by decide⟩ e heK h T147_44 hfix147_44 hinj147_44 hcardT147_44
    (fun i => conj_mem_of_fixedPoints (reps ⟨44, by decide⟩) (reps rK147) (T147_44 i) (hfix147_44 i) h)

/-! ## Cell (147, 45): |T| = 1 -/

def T147_45list : List Coordinates := [(0,0,0,0,0)]
def T147_45 : Fin 1 → Coordinate 1 := fun i => T147_45list.getD i.val (0,0,0,0,0)

theorem hfix147_45 : ∀ i, ((T147_45 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨45, by decide⟩ T147_45 (by decide)

theorem hinj147_45 : Function.Injective
    (fun i => ((T147_45 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_45 (by decide)

theorem hcardT147_45 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨45, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 45).** -/
theorem cell147_45 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨45, by decide⟩ : Fin 148))) :
    species (reps (⟨45, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_45 i :=
  species_entry_eq_sum rK147 ⟨45, by decide⟩ e heK h T147_45 hfix147_45 hinj147_45 hcardT147_45
    (fun i => conj_mem_of_fixedPoints (reps ⟨45, by decide⟩) (reps rK147) (T147_45 i) (hfix147_45 i) h)

/-! ## Cell (147, 46): |T| = 1 -/

def T147_46list : List Coordinates := [(0,0,0,0,0)]
def T147_46 : Fin 1 → Coordinate 1 := fun i => T147_46list.getD i.val (0,0,0,0,0)

theorem hfix147_46 : ∀ i, ((T147_46 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨46, by decide⟩ T147_46 (by decide)

theorem hinj147_46 : Function.Injective
    (fun i => ((T147_46 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_46 (by decide)

theorem hcardT147_46 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨46, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 46).** -/
theorem cell147_46 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨46, by decide⟩ : Fin 148))) :
    species (reps (⟨46, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_46 i :=
  species_entry_eq_sum rK147 ⟨46, by decide⟩ e heK h T147_46 hfix147_46 hinj147_46 hcardT147_46
    (fun i => conj_mem_of_fixedPoints (reps ⟨46, by decide⟩) (reps rK147) (T147_46 i) (hfix147_46 i) h)

/-! ## Cell (147, 47): |T| = 1 -/

def T147_47list : List Coordinates := [(0,0,0,0,0)]
def T147_47 : Fin 1 → Coordinate 1 := fun i => T147_47list.getD i.val (0,0,0,0,0)

theorem hfix147_47 : ∀ i, ((T147_47 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨47, by decide⟩ T147_47 (by decide)

theorem hinj147_47 : Function.Injective
    (fun i => ((T147_47 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_47 (by decide)

theorem hcardT147_47 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨47, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 47).** -/
theorem cell147_47 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨47, by decide⟩ : Fin 148))) :
    species (reps (⟨47, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_47 i :=
  species_entry_eq_sum rK147 ⟨47, by decide⟩ e heK h T147_47 hfix147_47 hinj147_47 hcardT147_47
    (fun i => conj_mem_of_fixedPoints (reps ⟨47, by decide⟩) (reps rK147) (T147_47 i) (hfix147_47 i) h)

/-! ## Cell (147, 48): |T| = 1 -/

def T147_48list : List Coordinates := [(0,0,0,0,0)]
def T147_48 : Fin 1 → Coordinate 1 := fun i => T147_48list.getD i.val (0,0,0,0,0)

theorem hfix147_48 : ∀ i, ((T147_48 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨48, by decide⟩ T147_48 (by decide)

theorem hinj147_48 : Function.Injective
    (fun i => ((T147_48 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_48 (by decide)

theorem hcardT147_48 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨48, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 48).** -/
theorem cell147_48 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨48, by decide⟩ : Fin 148))) :
    species (reps (⟨48, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_48 i :=
  species_entry_eq_sum rK147 ⟨48, by decide⟩ e heK h T147_48 hfix147_48 hinj147_48 hcardT147_48
    (fun i => conj_mem_of_fixedPoints (reps ⟨48, by decide⟩) (reps rK147) (T147_48 i) (hfix147_48 i) h)

/-! ## Cell (147, 49): |T| = 1 -/

def T147_49list : List Coordinates := [(0,0,0,0,0)]
def T147_49 : Fin 1 → Coordinate 1 := fun i => T147_49list.getD i.val (0,0,0,0,0)

theorem hfix147_49 : ∀ i, ((T147_49 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨49, by decide⟩ T147_49 (by decide)

theorem hinj147_49 : Function.Injective
    (fun i => ((T147_49 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_49 (by decide)

theorem hcardT147_49 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨49, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 49).** -/
theorem cell147_49 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨49, by decide⟩ : Fin 148))) :
    species (reps (⟨49, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_49 i :=
  species_entry_eq_sum rK147 ⟨49, by decide⟩ e heK h T147_49 hfix147_49 hinj147_49 hcardT147_49
    (fun i => conj_mem_of_fixedPoints (reps ⟨49, by decide⟩) (reps rK147) (T147_49 i) (hfix147_49 i) h)

/-! ## Cell (147, 50): |T| = 1 -/

def T147_50list : List Coordinates := [(0,0,0,0,0)]
def T147_50 : Fin 1 → Coordinate 1 := fun i => T147_50list.getD i.val (0,0,0,0,0)

theorem hfix147_50 : ∀ i, ((T147_50 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨50, by decide⟩ T147_50 (by decide)

theorem hinj147_50 : Function.Injective
    (fun i => ((T147_50 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_50 (by decide)

theorem hcardT147_50 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨50, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 50).** -/
theorem cell147_50 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨50, by decide⟩ : Fin 148))) :
    species (reps (⟨50, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_50 i :=
  species_entry_eq_sum rK147 ⟨50, by decide⟩ e heK h T147_50 hfix147_50 hinj147_50 hcardT147_50
    (fun i => conj_mem_of_fixedPoints (reps ⟨50, by decide⟩) (reps rK147) (T147_50 i) (hfix147_50 i) h)

/-! ## Cell (147, 51): |T| = 1 -/

def T147_51list : List Coordinates := [(0,0,0,0,0)]
def T147_51 : Fin 1 → Coordinate 1 := fun i => T147_51list.getD i.val (0,0,0,0,0)

theorem hfix147_51 : ∀ i, ((T147_51 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨51, by decide⟩ T147_51 (by decide)

theorem hinj147_51 : Function.Injective
    (fun i => ((T147_51 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_51 (by decide)

theorem hcardT147_51 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨51, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 51).** -/
theorem cell147_51 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨51, by decide⟩ : Fin 148))) :
    species (reps (⟨51, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_51 i :=
  species_entry_eq_sum rK147 ⟨51, by decide⟩ e heK h T147_51 hfix147_51 hinj147_51 hcardT147_51
    (fun i => conj_mem_of_fixedPoints (reps ⟨51, by decide⟩) (reps rK147) (T147_51 i) (hfix147_51 i) h)

/-! ## Cell (147, 52): |T| = 1 -/

def T147_52list : List Coordinates := [(0,0,0,0,0)]
def T147_52 : Fin 1 → Coordinate 1 := fun i => T147_52list.getD i.val (0,0,0,0,0)

theorem hfix147_52 : ∀ i, ((T147_52 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨52, by decide⟩ T147_52 (by decide)

theorem hinj147_52 : Function.Injective
    (fun i => ((T147_52 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_52 (by decide)

theorem hcardT147_52 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨52, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 52).** -/
theorem cell147_52 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨52, by decide⟩ : Fin 148))) :
    species (reps (⟨52, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_52 i :=
  species_entry_eq_sum rK147 ⟨52, by decide⟩ e heK h T147_52 hfix147_52 hinj147_52 hcardT147_52
    (fun i => conj_mem_of_fixedPoints (reps ⟨52, by decide⟩) (reps rK147) (T147_52 i) (hfix147_52 i) h)

/-! ## Cell (147, 53): |T| = 1 -/

def T147_53list : List Coordinates := [(0,0,0,0,0)]
def T147_53 : Fin 1 → Coordinate 1 := fun i => T147_53list.getD i.val (0,0,0,0,0)

theorem hfix147_53 : ∀ i, ((T147_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨53, by decide⟩ T147_53 (by decide)

theorem hinj147_53 : Function.Injective
    (fun i => ((T147_53 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_53 (by decide)

theorem hcardT147_53 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨53, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 53).** -/
theorem cell147_53 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_53 i :=
  species_entry_eq_sum rK147 ⟨53, by decide⟩ e heK h T147_53 hfix147_53 hinj147_53 hcardT147_53
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK147) (T147_53 i) (hfix147_53 i) h)

/-! ## Cell (147, 54): |T| = 1 -/

def T147_54list : List Coordinates := [(0,0,0,0,0)]
def T147_54 : Fin 1 → Coordinate 1 := fun i => T147_54list.getD i.val (0,0,0,0,0)

theorem hfix147_54 : ∀ i, ((T147_54 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨54, by decide⟩ T147_54 (by decide)

theorem hinj147_54 : Function.Injective
    (fun i => ((T147_54 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_54 (by decide)

theorem hcardT147_54 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨54, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 54).** -/
theorem cell147_54 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨54, by decide⟩ : Fin 148))) :
    species (reps (⟨54, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_54 i :=
  species_entry_eq_sum rK147 ⟨54, by decide⟩ e heK h T147_54 hfix147_54 hinj147_54 hcardT147_54
    (fun i => conj_mem_of_fixedPoints (reps ⟨54, by decide⟩) (reps rK147) (T147_54 i) (hfix147_54 i) h)

/-! ## Cell (147, 55): |T| = 1 -/

def T147_55list : List Coordinates := [(0,0,0,0,0)]
def T147_55 : Fin 1 → Coordinate 1 := fun i => T147_55list.getD i.val (0,0,0,0,0)

theorem hfix147_55 : ∀ i, ((T147_55 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨55, by decide⟩ T147_55 (by decide)

theorem hinj147_55 : Function.Injective
    (fun i => ((T147_55 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_55 (by decide)

theorem hcardT147_55 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨55, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 55).** -/
theorem cell147_55 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨55, by decide⟩ : Fin 148))) :
    species (reps (⟨55, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_55 i :=
  species_entry_eq_sum rK147 ⟨55, by decide⟩ e heK h T147_55 hfix147_55 hinj147_55 hcardT147_55
    (fun i => conj_mem_of_fixedPoints (reps ⟨55, by decide⟩) (reps rK147) (T147_55 i) (hfix147_55 i) h)

/-! ## Cell (147, 56): |T| = 1 -/

def T147_56list : List Coordinates := [(0,0,0,0,0)]
def T147_56 : Fin 1 → Coordinate 1 := fun i => T147_56list.getD i.val (0,0,0,0,0)

theorem hfix147_56 : ∀ i, ((T147_56 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨56, by decide⟩ T147_56 (by decide)

theorem hinj147_56 : Function.Injective
    (fun i => ((T147_56 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_56 (by decide)

theorem hcardT147_56 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨56, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 56).** -/
theorem cell147_56 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨56, by decide⟩ : Fin 148))) :
    species (reps (⟨56, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_56 i :=
  species_entry_eq_sum rK147 ⟨56, by decide⟩ e heK h T147_56 hfix147_56 hinj147_56 hcardT147_56
    (fun i => conj_mem_of_fixedPoints (reps ⟨56, by decide⟩) (reps rK147) (T147_56 i) (hfix147_56 i) h)

/-! ## Cell (147, 57): |T| = 1 -/

def T147_57list : List Coordinates := [(0,0,0,0,0)]
def T147_57 : Fin 1 → Coordinate 1 := fun i => T147_57list.getD i.val (0,0,0,0,0)

theorem hfix147_57 : ∀ i, ((T147_57 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨57, by decide⟩ T147_57 (by decide)

theorem hinj147_57 : Function.Injective
    (fun i => ((T147_57 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_57 (by decide)

theorem hcardT147_57 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨57, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 57).** -/
theorem cell147_57 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨57, by decide⟩ : Fin 148))) :
    species (reps (⟨57, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_57 i :=
  species_entry_eq_sum rK147 ⟨57, by decide⟩ e heK h T147_57 hfix147_57 hinj147_57 hcardT147_57
    (fun i => conj_mem_of_fixedPoints (reps ⟨57, by decide⟩) (reps rK147) (T147_57 i) (hfix147_57 i) h)

/-! ## Cell (147, 58): |T| = 1 -/

def T147_58list : List Coordinates := [(0,0,0,0,0)]
def T147_58 : Fin 1 → Coordinate 1 := fun i => T147_58list.getD i.val (0,0,0,0,0)

theorem hfix147_58 : ∀ i, ((T147_58 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨58, by decide⟩ T147_58 (by decide)

theorem hinj147_58 : Function.Injective
    (fun i => ((T147_58 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_58 (by decide)

theorem hcardT147_58 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨58, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 58).** -/
theorem cell147_58 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨58, by decide⟩ : Fin 148))) :
    species (reps (⟨58, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_58 i :=
  species_entry_eq_sum rK147 ⟨58, by decide⟩ e heK h T147_58 hfix147_58 hinj147_58 hcardT147_58
    (fun i => conj_mem_of_fixedPoints (reps ⟨58, by decide⟩) (reps rK147) (T147_58 i) (hfix147_58 i) h)

/-! ## Cell (147, 59): |T| = 1 -/

def T147_59list : List Coordinates := [(0,0,0,0,0)]
def T147_59 : Fin 1 → Coordinate 1 := fun i => T147_59list.getD i.val (0,0,0,0,0)

theorem hfix147_59 : ∀ i, ((T147_59 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨59, by decide⟩ T147_59 (by decide)

theorem hinj147_59 : Function.Injective
    (fun i => ((T147_59 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_59 (by decide)

theorem hcardT147_59 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨59, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 59).** -/
theorem cell147_59 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨59, by decide⟩ : Fin 148))) :
    species (reps (⟨59, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_59 i :=
  species_entry_eq_sum rK147 ⟨59, by decide⟩ e heK h T147_59 hfix147_59 hinj147_59 hcardT147_59
    (fun i => conj_mem_of_fixedPoints (reps ⟨59, by decide⟩) (reps rK147) (T147_59 i) (hfix147_59 i) h)

/-! ## Cell (147, 60): |T| = 1 -/

def T147_60list : List Coordinates := [(0,0,0,0,0)]
def T147_60 : Fin 1 → Coordinate 1 := fun i => T147_60list.getD i.val (0,0,0,0,0)

theorem hfix147_60 : ∀ i, ((T147_60 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨60, by decide⟩ T147_60 (by decide)

theorem hinj147_60 : Function.Injective
    (fun i => ((T147_60 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_60 (by decide)

theorem hcardT147_60 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨60, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 60).** -/
theorem cell147_60 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨60, by decide⟩ : Fin 148))) :
    species (reps (⟨60, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_60 i :=
  species_entry_eq_sum rK147 ⟨60, by decide⟩ e heK h T147_60 hfix147_60 hinj147_60 hcardT147_60
    (fun i => conj_mem_of_fixedPoints (reps ⟨60, by decide⟩) (reps rK147) (T147_60 i) (hfix147_60 i) h)

/-! ## Cell (147, 61): |T| = 1 -/

def T147_61list : List Coordinates := [(0,0,0,0,0)]
def T147_61 : Fin 1 → Coordinate 1 := fun i => T147_61list.getD i.val (0,0,0,0,0)

theorem hfix147_61 : ∀ i, ((T147_61 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨61, by decide⟩ T147_61 (by decide)

theorem hinj147_61 : Function.Injective
    (fun i => ((T147_61 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_61 (by decide)

theorem hcardT147_61 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨61, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 61).** -/
theorem cell147_61 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨61, by decide⟩ : Fin 148))) :
    species (reps (⟨61, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_61 i :=
  species_entry_eq_sum rK147 ⟨61, by decide⟩ e heK h T147_61 hfix147_61 hinj147_61 hcardT147_61
    (fun i => conj_mem_of_fixedPoints (reps ⟨61, by decide⟩) (reps rK147) (T147_61 i) (hfix147_61 i) h)

/-! ## Cell (147, 62): |T| = 1 -/

def T147_62list : List Coordinates := [(0,0,0,0,0)]
def T147_62 : Fin 1 → Coordinate 1 := fun i => T147_62list.getD i.val (0,0,0,0,0)

theorem hfix147_62 : ∀ i, ((T147_62 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨62, by decide⟩ T147_62 (by decide)

theorem hinj147_62 : Function.Injective
    (fun i => ((T147_62 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_62 (by decide)

theorem hcardT147_62 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨62, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 62).** -/
theorem cell147_62 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨62, by decide⟩ : Fin 148))) :
    species (reps (⟨62, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_62 i :=
  species_entry_eq_sum rK147 ⟨62, by decide⟩ e heK h T147_62 hfix147_62 hinj147_62 hcardT147_62
    (fun i => conj_mem_of_fixedPoints (reps ⟨62, by decide⟩) (reps rK147) (T147_62 i) (hfix147_62 i) h)

/-! ## Cell (147, 63): |T| = 1 -/

def T147_63list : List Coordinates := [(0,0,0,0,0)]
def T147_63 : Fin 1 → Coordinate 1 := fun i => T147_63list.getD i.val (0,0,0,0,0)

theorem hfix147_63 : ∀ i, ((T147_63 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨63, by decide⟩ T147_63 (by decide)

theorem hinj147_63 : Function.Injective
    (fun i => ((T147_63 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_63 (by decide)

theorem hcardT147_63 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨63, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 63).** -/
theorem cell147_63 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨63, by decide⟩ : Fin 148))) :
    species (reps (⟨63, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_63 i :=
  species_entry_eq_sum rK147 ⟨63, by decide⟩ e heK h T147_63 hfix147_63 hinj147_63 hcardT147_63
    (fun i => conj_mem_of_fixedPoints (reps ⟨63, by decide⟩) (reps rK147) (T147_63 i) (hfix147_63 i) h)

/-! ## Cell (147, 64): |T| = 1 -/

def T147_64list : List Coordinates := [(0,0,0,0,0)]
def T147_64 : Fin 1 → Coordinate 1 := fun i => T147_64list.getD i.val (0,0,0,0,0)

theorem hfix147_64 : ∀ i, ((T147_64 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨64, by decide⟩ T147_64 (by decide)

theorem hinj147_64 : Function.Injective
    (fun i => ((T147_64 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_64 (by decide)

theorem hcardT147_64 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨64, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 64).** -/
theorem cell147_64 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨64, by decide⟩ : Fin 148))) :
    species (reps (⟨64, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_64 i :=
  species_entry_eq_sum rK147 ⟨64, by decide⟩ e heK h T147_64 hfix147_64 hinj147_64 hcardT147_64
    (fun i => conj_mem_of_fixedPoints (reps ⟨64, by decide⟩) (reps rK147) (T147_64 i) (hfix147_64 i) h)

/-! ## Cell (147, 65): |T| = 1 -/

def T147_65list : List Coordinates := [(0,0,0,0,0)]
def T147_65 : Fin 1 → Coordinate 1 := fun i => T147_65list.getD i.val (0,0,0,0,0)

theorem hfix147_65 : ∀ i, ((T147_65 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨65, by decide⟩ T147_65 (by decide)

theorem hinj147_65 : Function.Injective
    (fun i => ((T147_65 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_65 (by decide)

theorem hcardT147_65 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨65, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 65).** -/
theorem cell147_65 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨65, by decide⟩ : Fin 148))) :
    species (reps (⟨65, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_65 i :=
  species_entry_eq_sum rK147 ⟨65, by decide⟩ e heK h T147_65 hfix147_65 hinj147_65 hcardT147_65
    (fun i => conj_mem_of_fixedPoints (reps ⟨65, by decide⟩) (reps rK147) (T147_65 i) (hfix147_65 i) h)

/-! ## Cell (147, 66): |T| = 1 -/

def T147_66list : List Coordinates := [(0,0,0,0,0)]
def T147_66 : Fin 1 → Coordinate 1 := fun i => T147_66list.getD i.val (0,0,0,0,0)

theorem hfix147_66 : ∀ i, ((T147_66 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨66, by decide⟩ T147_66 (by decide)

theorem hinj147_66 : Function.Injective
    (fun i => ((T147_66 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_66 (by decide)

theorem hcardT147_66 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨66, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 66).** -/
theorem cell147_66 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨66, by decide⟩ : Fin 148))) :
    species (reps (⟨66, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_66 i :=
  species_entry_eq_sum rK147 ⟨66, by decide⟩ e heK h T147_66 hfix147_66 hinj147_66 hcardT147_66
    (fun i => conj_mem_of_fixedPoints (reps ⟨66, by decide⟩) (reps rK147) (T147_66 i) (hfix147_66 i) h)

/-! ## Cell (147, 67): |T| = 1 -/

def T147_67list : List Coordinates := [(0,0,0,0,0)]
def T147_67 : Fin 1 → Coordinate 1 := fun i => T147_67list.getD i.val (0,0,0,0,0)

theorem hfix147_67 : ∀ i, ((T147_67 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨67, by decide⟩ T147_67 (by decide)

theorem hinj147_67 : Function.Injective
    (fun i => ((T147_67 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_67 (by decide)

theorem hcardT147_67 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨67, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 67).** -/
theorem cell147_67 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨67, by decide⟩ : Fin 148))) :
    species (reps (⟨67, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_67 i :=
  species_entry_eq_sum rK147 ⟨67, by decide⟩ e heK h T147_67 hfix147_67 hinj147_67 hcardT147_67
    (fun i => conj_mem_of_fixedPoints (reps ⟨67, by decide⟩) (reps rK147) (T147_67 i) (hfix147_67 i) h)

/-! ## Cell (147, 68): |T| = 1 -/

def T147_68list : List Coordinates := [(0,0,0,0,0)]
def T147_68 : Fin 1 → Coordinate 1 := fun i => T147_68list.getD i.val (0,0,0,0,0)

theorem hfix147_68 : ∀ i, ((T147_68 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨68, by decide⟩ T147_68 (by decide)

theorem hinj147_68 : Function.Injective
    (fun i => ((T147_68 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_68 (by decide)

theorem hcardT147_68 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨68, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 68).** -/
theorem cell147_68 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨68, by decide⟩ : Fin 148))) :
    species (reps (⟨68, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_68 i :=
  species_entry_eq_sum rK147 ⟨68, by decide⟩ e heK h T147_68 hfix147_68 hinj147_68 hcardT147_68
    (fun i => conj_mem_of_fixedPoints (reps ⟨68, by decide⟩) (reps rK147) (T147_68 i) (hfix147_68 i) h)

/-! ## Cell (147, 69): |T| = 1 -/

def T147_69list : List Coordinates := [(0,0,0,0,0)]
def T147_69 : Fin 1 → Coordinate 1 := fun i => T147_69list.getD i.val (0,0,0,0,0)

theorem hfix147_69 : ∀ i, ((T147_69 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨69, by decide⟩ T147_69 (by decide)

theorem hinj147_69 : Function.Injective
    (fun i => ((T147_69 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_69 (by decide)

theorem hcardT147_69 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨69, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 69).** -/
theorem cell147_69 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨69, by decide⟩ : Fin 148))) :
    species (reps (⟨69, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_69 i :=
  species_entry_eq_sum rK147 ⟨69, by decide⟩ e heK h T147_69 hfix147_69 hinj147_69 hcardT147_69
    (fun i => conj_mem_of_fixedPoints (reps ⟨69, by decide⟩) (reps rK147) (T147_69 i) (hfix147_69 i) h)

/-! ## Cell (147, 70): |T| = 1 -/

def T147_70list : List Coordinates := [(0,0,0,0,0)]
def T147_70 : Fin 1 → Coordinate 1 := fun i => T147_70list.getD i.val (0,0,0,0,0)

theorem hfix147_70 : ∀ i, ((T147_70 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨70, by decide⟩ T147_70 (by decide)

theorem hinj147_70 : Function.Injective
    (fun i => ((T147_70 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_70 (by decide)

theorem hcardT147_70 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨70, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 70).** -/
theorem cell147_70 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨70, by decide⟩ : Fin 148))) :
    species (reps (⟨70, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_70 i :=
  species_entry_eq_sum rK147 ⟨70, by decide⟩ e heK h T147_70 hfix147_70 hinj147_70 hcardT147_70
    (fun i => conj_mem_of_fixedPoints (reps ⟨70, by decide⟩) (reps rK147) (T147_70 i) (hfix147_70 i) h)

/-! ## Cell (147, 71): |T| = 1 -/

def T147_71list : List Coordinates := [(0,0,0,0,0)]
def T147_71 : Fin 1 → Coordinate 1 := fun i => T147_71list.getD i.val (0,0,0,0,0)

theorem hfix147_71 : ∀ i, ((T147_71 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨71, by decide⟩ T147_71 (by decide)

theorem hinj147_71 : Function.Injective
    (fun i => ((T147_71 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_71 (by decide)

theorem hcardT147_71 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨71, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 71).** -/
theorem cell147_71 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨71, by decide⟩ : Fin 148))) :
    species (reps (⟨71, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_71 i :=
  species_entry_eq_sum rK147 ⟨71, by decide⟩ e heK h T147_71 hfix147_71 hinj147_71 hcardT147_71
    (fun i => conj_mem_of_fixedPoints (reps ⟨71, by decide⟩) (reps rK147) (T147_71 i) (hfix147_71 i) h)

/-! ## Cell (147, 72): |T| = 1 -/

def T147_72list : List Coordinates := [(0,0,0,0,0)]
def T147_72 : Fin 1 → Coordinate 1 := fun i => T147_72list.getD i.val (0,0,0,0,0)

theorem hfix147_72 : ∀ i, ((T147_72 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨72, by decide⟩ T147_72 (by decide)

theorem hinj147_72 : Function.Injective
    (fun i => ((T147_72 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_72 (by decide)

theorem hcardT147_72 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨72, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 72).** -/
theorem cell147_72 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨72, by decide⟩ : Fin 148))) :
    species (reps (⟨72, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_72 i :=
  species_entry_eq_sum rK147 ⟨72, by decide⟩ e heK h T147_72 hfix147_72 hinj147_72 hcardT147_72
    (fun i => conj_mem_of_fixedPoints (reps ⟨72, by decide⟩) (reps rK147) (T147_72 i) (hfix147_72 i) h)

/-! ## Cell (147, 73): |T| = 1 -/

def T147_73list : List Coordinates := [(0,0,0,0,0)]
def T147_73 : Fin 1 → Coordinate 1 := fun i => T147_73list.getD i.val (0,0,0,0,0)

theorem hfix147_73 : ∀ i, ((T147_73 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨73, by decide⟩ T147_73 (by decide)

theorem hinj147_73 : Function.Injective
    (fun i => ((T147_73 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_73 (by decide)

theorem hcardT147_73 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨73, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 73).** -/
theorem cell147_73 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨73, by decide⟩ : Fin 148))) :
    species (reps (⟨73, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_73 i :=
  species_entry_eq_sum rK147 ⟨73, by decide⟩ e heK h T147_73 hfix147_73 hinj147_73 hcardT147_73
    (fun i => conj_mem_of_fixedPoints (reps ⟨73, by decide⟩) (reps rK147) (T147_73 i) (hfix147_73 i) h)

/-! ## Cell (147, 74): |T| = 1 -/

def T147_74list : List Coordinates := [(0,0,0,0,0)]
def T147_74 : Fin 1 → Coordinate 1 := fun i => T147_74list.getD i.val (0,0,0,0,0)

theorem hfix147_74 : ∀ i, ((T147_74 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨74, by decide⟩ T147_74 (by decide)

theorem hinj147_74 : Function.Injective
    (fun i => ((T147_74 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_74 (by decide)

theorem hcardT147_74 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨74, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 74).** -/
theorem cell147_74 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨74, by decide⟩ : Fin 148))) :
    species (reps (⟨74, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_74 i :=
  species_entry_eq_sum rK147 ⟨74, by decide⟩ e heK h T147_74 hfix147_74 hinj147_74 hcardT147_74
    (fun i => conj_mem_of_fixedPoints (reps ⟨74, by decide⟩) (reps rK147) (T147_74 i) (hfix147_74 i) h)

/-! ## Cell (147, 75): |T| = 1 -/

def T147_75list : List Coordinates := [(0,0,0,0,0)]
def T147_75 : Fin 1 → Coordinate 1 := fun i => T147_75list.getD i.val (0,0,0,0,0)

theorem hfix147_75 : ∀ i, ((T147_75 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨75, by decide⟩ T147_75 (by decide)

theorem hinj147_75 : Function.Injective
    (fun i => ((T147_75 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_75 (by decide)

theorem hcardT147_75 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨75, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 75).** -/
theorem cell147_75 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨75, by decide⟩ : Fin 148))) :
    species (reps (⟨75, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_75 i :=
  species_entry_eq_sum rK147 ⟨75, by decide⟩ e heK h T147_75 hfix147_75 hinj147_75 hcardT147_75
    (fun i => conj_mem_of_fixedPoints (reps ⟨75, by decide⟩) (reps rK147) (T147_75 i) (hfix147_75 i) h)

/-! ## Cell (147, 76): |T| = 1 -/

def T147_76list : List Coordinates := [(0,0,0,0,0)]
def T147_76 : Fin 1 → Coordinate 1 := fun i => T147_76list.getD i.val (0,0,0,0,0)

theorem hfix147_76 : ∀ i, ((T147_76 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨76, by decide⟩ T147_76 (by decide)

theorem hinj147_76 : Function.Injective
    (fun i => ((T147_76 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_76 (by decide)

theorem hcardT147_76 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨76, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 76).** -/
theorem cell147_76 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨76, by decide⟩ : Fin 148))) :
    species (reps (⟨76, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_76 i :=
  species_entry_eq_sum rK147 ⟨76, by decide⟩ e heK h T147_76 hfix147_76 hinj147_76 hcardT147_76
    (fun i => conj_mem_of_fixedPoints (reps ⟨76, by decide⟩) (reps rK147) (T147_76 i) (hfix147_76 i) h)

/-! ## Cell (147, 77): |T| = 1 -/

def T147_77list : List Coordinates := [(0,0,0,0,0)]
def T147_77 : Fin 1 → Coordinate 1 := fun i => T147_77list.getD i.val (0,0,0,0,0)

theorem hfix147_77 : ∀ i, ((T147_77 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨77, by decide⟩ T147_77 (by decide)

theorem hinj147_77 : Function.Injective
    (fun i => ((T147_77 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_77 (by decide)

theorem hcardT147_77 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨77, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 77).** -/
theorem cell147_77 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨77, by decide⟩ : Fin 148))) :
    species (reps (⟨77, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_77 i :=
  species_entry_eq_sum rK147 ⟨77, by decide⟩ e heK h T147_77 hfix147_77 hinj147_77 hcardT147_77
    (fun i => conj_mem_of_fixedPoints (reps ⟨77, by decide⟩) (reps rK147) (T147_77 i) (hfix147_77 i) h)

/-! ## Cell (147, 78): |T| = 1 -/

def T147_78list : List Coordinates := [(0,0,0,0,0)]
def T147_78 : Fin 1 → Coordinate 1 := fun i => T147_78list.getD i.val (0,0,0,0,0)

theorem hfix147_78 : ∀ i, ((T147_78 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨78, by decide⟩ T147_78 (by decide)

theorem hinj147_78 : Function.Injective
    (fun i => ((T147_78 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_78 (by decide)

theorem hcardT147_78 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨78, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 78).** -/
theorem cell147_78 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨78, by decide⟩ : Fin 148))) :
    species (reps (⟨78, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_78 i :=
  species_entry_eq_sum rK147 ⟨78, by decide⟩ e heK h T147_78 hfix147_78 hinj147_78 hcardT147_78
    (fun i => conj_mem_of_fixedPoints (reps ⟨78, by decide⟩) (reps rK147) (T147_78 i) (hfix147_78 i) h)

/-! ## Cell (147, 79): |T| = 1 -/

def T147_79list : List Coordinates := [(0,0,0,0,0)]
def T147_79 : Fin 1 → Coordinate 1 := fun i => T147_79list.getD i.val (0,0,0,0,0)

theorem hfix147_79 : ∀ i, ((T147_79 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨79, by decide⟩ T147_79 (by decide)

theorem hinj147_79 : Function.Injective
    (fun i => ((T147_79 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_79 (by decide)

theorem hcardT147_79 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨79, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 79).** -/
theorem cell147_79 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨79, by decide⟩ : Fin 148))) :
    species (reps (⟨79, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_79 i :=
  species_entry_eq_sum rK147 ⟨79, by decide⟩ e heK h T147_79 hfix147_79 hinj147_79 hcardT147_79
    (fun i => conj_mem_of_fixedPoints (reps ⟨79, by decide⟩) (reps rK147) (T147_79 i) (hfix147_79 i) h)

/-! ## Cell (147, 80): |T| = 1 -/

def T147_80list : List Coordinates := [(0,0,0,0,0)]
def T147_80 : Fin 1 → Coordinate 1 := fun i => T147_80list.getD i.val (0,0,0,0,0)

theorem hfix147_80 : ∀ i, ((T147_80 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨80, by decide⟩ T147_80 (by decide)

theorem hinj147_80 : Function.Injective
    (fun i => ((T147_80 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_80 (by decide)

theorem hcardT147_80 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨80, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 80).** -/
theorem cell147_80 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨80, by decide⟩ : Fin 148))) :
    species (reps (⟨80, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_80 i :=
  species_entry_eq_sum rK147 ⟨80, by decide⟩ e heK h T147_80 hfix147_80 hinj147_80 hcardT147_80
    (fun i => conj_mem_of_fixedPoints (reps ⟨80, by decide⟩) (reps rK147) (T147_80 i) (hfix147_80 i) h)

/-! ## Cell (147, 81): |T| = 1 -/

def T147_81list : List Coordinates := [(0,0,0,0,0)]
def T147_81 : Fin 1 → Coordinate 1 := fun i => T147_81list.getD i.val (0,0,0,0,0)

theorem hfix147_81 : ∀ i, ((T147_81 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨81, by decide⟩ T147_81 (by decide)

theorem hinj147_81 : Function.Injective
    (fun i => ((T147_81 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_81 (by decide)

theorem hcardT147_81 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨81, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 81).** -/
theorem cell147_81 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨81, by decide⟩ : Fin 148))) :
    species (reps (⟨81, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_81 i :=
  species_entry_eq_sum rK147 ⟨81, by decide⟩ e heK h T147_81 hfix147_81 hinj147_81 hcardT147_81
    (fun i => conj_mem_of_fixedPoints (reps ⟨81, by decide⟩) (reps rK147) (T147_81 i) (hfix147_81 i) h)

/-! ## Cell (147, 82): |T| = 1 -/

def T147_82list : List Coordinates := [(0,0,0,0,0)]
def T147_82 : Fin 1 → Coordinate 1 := fun i => T147_82list.getD i.val (0,0,0,0,0)

theorem hfix147_82 : ∀ i, ((T147_82 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨82, by decide⟩ T147_82 (by decide)

theorem hinj147_82 : Function.Injective
    (fun i => ((T147_82 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_82 (by decide)

theorem hcardT147_82 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨82, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 82).** -/
theorem cell147_82 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨82, by decide⟩ : Fin 148))) :
    species (reps (⟨82, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_82 i :=
  species_entry_eq_sum rK147 ⟨82, by decide⟩ e heK h T147_82 hfix147_82 hinj147_82 hcardT147_82
    (fun i => conj_mem_of_fixedPoints (reps ⟨82, by decide⟩) (reps rK147) (T147_82 i) (hfix147_82 i) h)

/-! ## Cell (147, 83): |T| = 1 -/

def T147_83list : List Coordinates := [(0,0,0,0,0)]
def T147_83 : Fin 1 → Coordinate 1 := fun i => T147_83list.getD i.val (0,0,0,0,0)

theorem hfix147_83 : ∀ i, ((T147_83 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨83, by decide⟩ T147_83 (by decide)

theorem hinj147_83 : Function.Injective
    (fun i => ((T147_83 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_83 (by decide)

theorem hcardT147_83 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨83, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 83).** -/
theorem cell147_83 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨83, by decide⟩ : Fin 148))) :
    species (reps (⟨83, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_83 i :=
  species_entry_eq_sum rK147 ⟨83, by decide⟩ e heK h T147_83 hfix147_83 hinj147_83 hcardT147_83
    (fun i => conj_mem_of_fixedPoints (reps ⟨83, by decide⟩) (reps rK147) (T147_83 i) (hfix147_83 i) h)

/-! ## Cell (147, 84): |T| = 1 -/

def T147_84list : List Coordinates := [(0,0,0,0,0)]
def T147_84 : Fin 1 → Coordinate 1 := fun i => T147_84list.getD i.val (0,0,0,0,0)

theorem hfix147_84 : ∀ i, ((T147_84 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨84, by decide⟩ T147_84 (by decide)

theorem hinj147_84 : Function.Injective
    (fun i => ((T147_84 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_84 (by decide)

theorem hcardT147_84 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨84, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 84).** -/
theorem cell147_84 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨84, by decide⟩ : Fin 148))) :
    species (reps (⟨84, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_84 i :=
  species_entry_eq_sum rK147 ⟨84, by decide⟩ e heK h T147_84 hfix147_84 hinj147_84 hcardT147_84
    (fun i => conj_mem_of_fixedPoints (reps ⟨84, by decide⟩) (reps rK147) (T147_84 i) (hfix147_84 i) h)

/-! ## Cell (147, 85): |T| = 1 -/

def T147_85list : List Coordinates := [(0,0,0,0,0)]
def T147_85 : Fin 1 → Coordinate 1 := fun i => T147_85list.getD i.val (0,0,0,0,0)

theorem hfix147_85 : ∀ i, ((T147_85 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨85, by decide⟩ T147_85 (by decide)

theorem hinj147_85 : Function.Injective
    (fun i => ((T147_85 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_85 (by decide)

theorem hcardT147_85 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨85, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 85).** -/
theorem cell147_85 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨85, by decide⟩ : Fin 148))) :
    species (reps (⟨85, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_85 i :=
  species_entry_eq_sum rK147 ⟨85, by decide⟩ e heK h T147_85 hfix147_85 hinj147_85 hcardT147_85
    (fun i => conj_mem_of_fixedPoints (reps ⟨85, by decide⟩) (reps rK147) (T147_85 i) (hfix147_85 i) h)

/-! ## Cell (147, 86): |T| = 1 -/

def T147_86list : List Coordinates := [(0,0,0,0,0)]
def T147_86 : Fin 1 → Coordinate 1 := fun i => T147_86list.getD i.val (0,0,0,0,0)

theorem hfix147_86 : ∀ i, ((T147_86 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨86, by decide⟩ T147_86 (by decide)

theorem hinj147_86 : Function.Injective
    (fun i => ((T147_86 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_86 (by decide)

theorem hcardT147_86 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨86, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 86).** -/
theorem cell147_86 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨86, by decide⟩ : Fin 148))) :
    species (reps (⟨86, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_86 i :=
  species_entry_eq_sum rK147 ⟨86, by decide⟩ e heK h T147_86 hfix147_86 hinj147_86 hcardT147_86
    (fun i => conj_mem_of_fixedPoints (reps ⟨86, by decide⟩) (reps rK147) (T147_86 i) (hfix147_86 i) h)

/-! ## Cell (147, 87): |T| = 1 -/

def T147_87list : List Coordinates := [(0,0,0,0,0)]
def T147_87 : Fin 1 → Coordinate 1 := fun i => T147_87list.getD i.val (0,0,0,0,0)

theorem hfix147_87 : ∀ i, ((T147_87 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨87, by decide⟩ T147_87 (by decide)

theorem hinj147_87 : Function.Injective
    (fun i => ((T147_87 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_87 (by decide)

theorem hcardT147_87 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨87, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 87).** -/
theorem cell147_87 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨87, by decide⟩ : Fin 148))) :
    species (reps (⟨87, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_87 i :=
  species_entry_eq_sum rK147 ⟨87, by decide⟩ e heK h T147_87 hfix147_87 hinj147_87 hcardT147_87
    (fun i => conj_mem_of_fixedPoints (reps ⟨87, by decide⟩) (reps rK147) (T147_87 i) (hfix147_87 i) h)

/-! ## Cell (147, 88): |T| = 1 -/

def T147_88list : List Coordinates := [(0,0,0,0,0)]
def T147_88 : Fin 1 → Coordinate 1 := fun i => T147_88list.getD i.val (0,0,0,0,0)

theorem hfix147_88 : ∀ i, ((T147_88 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨88, by decide⟩ T147_88 (by decide)

theorem hinj147_88 : Function.Injective
    (fun i => ((T147_88 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_88 (by decide)

theorem hcardT147_88 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨88, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 88).** -/
theorem cell147_88 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨88, by decide⟩ : Fin 148))) :
    species (reps (⟨88, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_88 i :=
  species_entry_eq_sum rK147 ⟨88, by decide⟩ e heK h T147_88 hfix147_88 hinj147_88 hcardT147_88
    (fun i => conj_mem_of_fixedPoints (reps ⟨88, by decide⟩) (reps rK147) (T147_88 i) (hfix147_88 i) h)

/-! ## Cell (147, 89): |T| = 1 -/

def T147_89list : List Coordinates := [(0,0,0,0,0)]
def T147_89 : Fin 1 → Coordinate 1 := fun i => T147_89list.getD i.val (0,0,0,0,0)

theorem hfix147_89 : ∀ i, ((T147_89 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨89, by decide⟩ T147_89 (by decide)

theorem hinj147_89 : Function.Injective
    (fun i => ((T147_89 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_89 (by decide)

theorem hcardT147_89 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨89, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 89).** -/
theorem cell147_89 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨89, by decide⟩ : Fin 148))) :
    species (reps (⟨89, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_89 i :=
  species_entry_eq_sum rK147 ⟨89, by decide⟩ e heK h T147_89 hfix147_89 hinj147_89 hcardT147_89
    (fun i => conj_mem_of_fixedPoints (reps ⟨89, by decide⟩) (reps rK147) (T147_89 i) (hfix147_89 i) h)

/-! ## Cell (147, 90): |T| = 1 -/

def T147_90list : List Coordinates := [(0,0,0,0,0)]
def T147_90 : Fin 1 → Coordinate 1 := fun i => T147_90list.getD i.val (0,0,0,0,0)

theorem hfix147_90 : ∀ i, ((T147_90 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨90, by decide⟩ T147_90 (by decide)

theorem hinj147_90 : Function.Injective
    (fun i => ((T147_90 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_90 (by decide)

theorem hcardT147_90 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨90, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 90).** -/
theorem cell147_90 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨90, by decide⟩ : Fin 148))) :
    species (reps (⟨90, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_90 i :=
  species_entry_eq_sum rK147 ⟨90, by decide⟩ e heK h T147_90 hfix147_90 hinj147_90 hcardT147_90
    (fun i => conj_mem_of_fixedPoints (reps ⟨90, by decide⟩) (reps rK147) (T147_90 i) (hfix147_90 i) h)

/-! ## Cell (147, 91): |T| = 1 -/

def T147_91list : List Coordinates := [(0,0,0,0,0)]
def T147_91 : Fin 1 → Coordinate 1 := fun i => T147_91list.getD i.val (0,0,0,0,0)

theorem hfix147_91 : ∀ i, ((T147_91 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨91, by decide⟩ T147_91 (by decide)

theorem hinj147_91 : Function.Injective
    (fun i => ((T147_91 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_91 (by decide)

theorem hcardT147_91 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨91, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 91).** -/
theorem cell147_91 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨91, by decide⟩ : Fin 148))) :
    species (reps (⟨91, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_91 i :=
  species_entry_eq_sum rK147 ⟨91, by decide⟩ e heK h T147_91 hfix147_91 hinj147_91 hcardT147_91
    (fun i => conj_mem_of_fixedPoints (reps ⟨91, by decide⟩) (reps rK147) (T147_91 i) (hfix147_91 i) h)

/-! ## Cell (147, 92): |T| = 1 -/

def T147_92list : List Coordinates := [(0,0,0,0,0)]
def T147_92 : Fin 1 → Coordinate 1 := fun i => T147_92list.getD i.val (0,0,0,0,0)

theorem hfix147_92 : ∀ i, ((T147_92 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨92, by decide⟩ T147_92 (by decide)

theorem hinj147_92 : Function.Injective
    (fun i => ((T147_92 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_92 (by decide)

theorem hcardT147_92 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨92, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 92).** -/
theorem cell147_92 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨92, by decide⟩ : Fin 148))) :
    species (reps (⟨92, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_92 i :=
  species_entry_eq_sum rK147 ⟨92, by decide⟩ e heK h T147_92 hfix147_92 hinj147_92 hcardT147_92
    (fun i => conj_mem_of_fixedPoints (reps ⟨92, by decide⟩) (reps rK147) (T147_92 i) (hfix147_92 i) h)

/-! ## Cell (147, 93): |T| = 1 -/

def T147_93list : List Coordinates := [(0,0,0,0,0)]
def T147_93 : Fin 1 → Coordinate 1 := fun i => T147_93list.getD i.val (0,0,0,0,0)

theorem hfix147_93 : ∀ i, ((T147_93 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨93, by decide⟩ T147_93 (by decide)

theorem hinj147_93 : Function.Injective
    (fun i => ((T147_93 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_93 (by decide)

theorem hcardT147_93 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨93, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 93).** -/
theorem cell147_93 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨93, by decide⟩ : Fin 148))) :
    species (reps (⟨93, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_93 i :=
  species_entry_eq_sum rK147 ⟨93, by decide⟩ e heK h T147_93 hfix147_93 hinj147_93 hcardT147_93
    (fun i => conj_mem_of_fixedPoints (reps ⟨93, by decide⟩) (reps rK147) (T147_93 i) (hfix147_93 i) h)

/-! ## Cell (147, 94): |T| = 1 -/

def T147_94list : List Coordinates := [(0,0,0,0,0)]
def T147_94 : Fin 1 → Coordinate 1 := fun i => T147_94list.getD i.val (0,0,0,0,0)

theorem hfix147_94 : ∀ i, ((T147_94 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨94, by decide⟩ T147_94 (by decide)

theorem hinj147_94 : Function.Injective
    (fun i => ((T147_94 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_94 (by decide)

theorem hcardT147_94 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨94, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 94).** -/
theorem cell147_94 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨94, by decide⟩ : Fin 148))) :
    species (reps (⟨94, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_94 i :=
  species_entry_eq_sum rK147 ⟨94, by decide⟩ e heK h T147_94 hfix147_94 hinj147_94 hcardT147_94
    (fun i => conj_mem_of_fixedPoints (reps ⟨94, by decide⟩) (reps rK147) (T147_94 i) (hfix147_94 i) h)

/-! ## Cell (147, 95): |T| = 1 -/

def T147_95list : List Coordinates := [(0,0,0,0,0)]
def T147_95 : Fin 1 → Coordinate 1 := fun i => T147_95list.getD i.val (0,0,0,0,0)

theorem hfix147_95 : ∀ i, ((T147_95 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨95, by decide⟩ T147_95 (by decide)

theorem hinj147_95 : Function.Injective
    (fun i => ((T147_95 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_95 (by decide)

theorem hcardT147_95 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨95, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 95).** -/
theorem cell147_95 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨95, by decide⟩ : Fin 148))) :
    species (reps (⟨95, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_95 i :=
  species_entry_eq_sum rK147 ⟨95, by decide⟩ e heK h T147_95 hfix147_95 hinj147_95 hcardT147_95
    (fun i => conj_mem_of_fixedPoints (reps ⟨95, by decide⟩) (reps rK147) (T147_95 i) (hfix147_95 i) h)

/-! ## Cell (147, 96): |T| = 1 -/

def T147_96list : List Coordinates := [(0,0,0,0,0)]
def T147_96 : Fin 1 → Coordinate 1 := fun i => T147_96list.getD i.val (0,0,0,0,0)

theorem hfix147_96 : ∀ i, ((T147_96 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨96, by decide⟩ T147_96 (by decide)

theorem hinj147_96 : Function.Injective
    (fun i => ((T147_96 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_96 (by decide)

theorem hcardT147_96 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨96, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 96).** -/
theorem cell147_96 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨96, by decide⟩ : Fin 148))) :
    species (reps (⟨96, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_96 i :=
  species_entry_eq_sum rK147 ⟨96, by decide⟩ e heK h T147_96 hfix147_96 hinj147_96 hcardT147_96
    (fun i => conj_mem_of_fixedPoints (reps ⟨96, by decide⟩) (reps rK147) (T147_96 i) (hfix147_96 i) h)

/-! ## Cell (147, 97): |T| = 1 -/

def T147_97list : List Coordinates := [(0,0,0,0,0)]
def T147_97 : Fin 1 → Coordinate 1 := fun i => T147_97list.getD i.val (0,0,0,0,0)

theorem hfix147_97 : ∀ i, ((T147_97 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨97, by decide⟩ T147_97 (by decide)

theorem hinj147_97 : Function.Injective
    (fun i => ((T147_97 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_97 (by decide)

theorem hcardT147_97 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨97, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 97).** -/
theorem cell147_97 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨97, by decide⟩ : Fin 148))) :
    species (reps (⟨97, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_97 i :=
  species_entry_eq_sum rK147 ⟨97, by decide⟩ e heK h T147_97 hfix147_97 hinj147_97 hcardT147_97
    (fun i => conj_mem_of_fixedPoints (reps ⟨97, by decide⟩) (reps rK147) (T147_97 i) (hfix147_97 i) h)

/-! ## Cell (147, 98): |T| = 1 -/

def T147_98list : List Coordinates := [(0,0,0,0,0)]
def T147_98 : Fin 1 → Coordinate 1 := fun i => T147_98list.getD i.val (0,0,0,0,0)

theorem hfix147_98 : ∀ i, ((T147_98 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨98, by decide⟩ T147_98 (by decide)

theorem hinj147_98 : Function.Injective
    (fun i => ((T147_98 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_98 (by decide)

theorem hcardT147_98 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨98, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 98).** -/
theorem cell147_98 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨98, by decide⟩ : Fin 148))) :
    species (reps (⟨98, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_98 i :=
  species_entry_eq_sum rK147 ⟨98, by decide⟩ e heK h T147_98 hfix147_98 hinj147_98 hcardT147_98
    (fun i => conj_mem_of_fixedPoints (reps ⟨98, by decide⟩) (reps rK147) (T147_98 i) (hfix147_98 i) h)

/-! ## Cell (147, 99): |T| = 1 -/

def T147_99list : List Coordinates := [(0,0,0,0,0)]
def T147_99 : Fin 1 → Coordinate 1 := fun i => T147_99list.getD i.val (0,0,0,0,0)

theorem hfix147_99 : ∀ i, ((T147_99 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨99, by decide⟩ T147_99 (by decide)

theorem hinj147_99 : Function.Injective
    (fun i => ((T147_99 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_99 (by decide)

theorem hcardT147_99 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨99, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 99).** -/
theorem cell147_99 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨99, by decide⟩ : Fin 148))) :
    species (reps (⟨99, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_99 i :=
  species_entry_eq_sum rK147 ⟨99, by decide⟩ e heK h T147_99 hfix147_99 hinj147_99 hcardT147_99
    (fun i => conj_mem_of_fixedPoints (reps ⟨99, by decide⟩) (reps rK147) (T147_99 i) (hfix147_99 i) h)

/-! ## Cell (147, 100): |T| = 1 -/

def T147_100list : List Coordinates := [(0,0,0,0,0)]
def T147_100 : Fin 1 → Coordinate 1 := fun i => T147_100list.getD i.val (0,0,0,0,0)

theorem hfix147_100 : ∀ i, ((T147_100 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨100, by decide⟩ T147_100 (by decide)

theorem hinj147_100 : Function.Injective
    (fun i => ((T147_100 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_100 (by decide)

theorem hcardT147_100 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨100, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 100).** -/
theorem cell147_100 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨100, by decide⟩ : Fin 148))) :
    species (reps (⟨100, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_100 i :=
  species_entry_eq_sum rK147 ⟨100, by decide⟩ e heK h T147_100 hfix147_100 hinj147_100 hcardT147_100
    (fun i => conj_mem_of_fixedPoints (reps ⟨100, by decide⟩) (reps rK147) (T147_100 i) (hfix147_100 i) h)

/-! ## Cell (147, 101): |T| = 1 -/

def T147_101list : List Coordinates := [(0,0,0,0,0)]
def T147_101 : Fin 1 → Coordinate 1 := fun i => T147_101list.getD i.val (0,0,0,0,0)

theorem hfix147_101 : ∀ i, ((T147_101 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨101, by decide⟩ T147_101 (by decide)

theorem hinj147_101 : Function.Injective
    (fun i => ((T147_101 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_101 (by decide)

theorem hcardT147_101 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨101, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 101).** -/
theorem cell147_101 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨101, by decide⟩ : Fin 148))) :
    species (reps (⟨101, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_101 i :=
  species_entry_eq_sum rK147 ⟨101, by decide⟩ e heK h T147_101 hfix147_101 hinj147_101 hcardT147_101
    (fun i => conj_mem_of_fixedPoints (reps ⟨101, by decide⟩) (reps rK147) (T147_101 i) (hfix147_101 i) h)

/-! ## Cell (147, 102): |T| = 1 -/

def T147_102list : List Coordinates := [(0,0,0,0,0)]
def T147_102 : Fin 1 → Coordinate 1 := fun i => T147_102list.getD i.val (0,0,0,0,0)

theorem hfix147_102 : ∀ i, ((T147_102 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨102, by decide⟩ T147_102 (by decide)

theorem hinj147_102 : Function.Injective
    (fun i => ((T147_102 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_102 (by decide)

theorem hcardT147_102 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨102, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 102).** -/
theorem cell147_102 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨102, by decide⟩ : Fin 148))) :
    species (reps (⟨102, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_102 i :=
  species_entry_eq_sum rK147 ⟨102, by decide⟩ e heK h T147_102 hfix147_102 hinj147_102 hcardT147_102
    (fun i => conj_mem_of_fixedPoints (reps ⟨102, by decide⟩) (reps rK147) (T147_102 i) (hfix147_102 i) h)

/-! ## Cell (147, 103): |T| = 1 -/

def T147_103list : List Coordinates := [(0,0,0,0,0)]
def T147_103 : Fin 1 → Coordinate 1 := fun i => T147_103list.getD i.val (0,0,0,0,0)

theorem hfix147_103 : ∀ i, ((T147_103 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨103, by decide⟩ T147_103 (by decide)

theorem hinj147_103 : Function.Injective
    (fun i => ((T147_103 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_103 (by decide)

theorem hcardT147_103 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨103, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 103).** -/
theorem cell147_103 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨103, by decide⟩ : Fin 148))) :
    species (reps (⟨103, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_103 i :=
  species_entry_eq_sum rK147 ⟨103, by decide⟩ e heK h T147_103 hfix147_103 hinj147_103 hcardT147_103
    (fun i => conj_mem_of_fixedPoints (reps ⟨103, by decide⟩) (reps rK147) (T147_103 i) (hfix147_103 i) h)

/-! ## Cell (147, 104): |T| = 1 -/

def T147_104list : List Coordinates := [(0,0,0,0,0)]
def T147_104 : Fin 1 → Coordinate 1 := fun i => T147_104list.getD i.val (0,0,0,0,0)

theorem hfix147_104 : ∀ i, ((T147_104 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨104, by decide⟩ T147_104 (by decide)

theorem hinj147_104 : Function.Injective
    (fun i => ((T147_104 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_104 (by decide)

theorem hcardT147_104 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨104, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 104).** -/
theorem cell147_104 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨104, by decide⟩ : Fin 148))) :
    species (reps (⟨104, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_104 i :=
  species_entry_eq_sum rK147 ⟨104, by decide⟩ e heK h T147_104 hfix147_104 hinj147_104 hcardT147_104
    (fun i => conj_mem_of_fixedPoints (reps ⟨104, by decide⟩) (reps rK147) (T147_104 i) (hfix147_104 i) h)

/-! ## Cell (147, 105): |T| = 1 -/

def T147_105list : List Coordinates := [(0,0,0,0,0)]
def T147_105 : Fin 1 → Coordinate 1 := fun i => T147_105list.getD i.val (0,0,0,0,0)

theorem hfix147_105 : ∀ i, ((T147_105 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨105, by decide⟩ T147_105 (by decide)

theorem hinj147_105 : Function.Injective
    (fun i => ((T147_105 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_105 (by decide)

theorem hcardT147_105 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨105, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 105).** -/
theorem cell147_105 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨105, by decide⟩ : Fin 148))) :
    species (reps (⟨105, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_105 i :=
  species_entry_eq_sum rK147 ⟨105, by decide⟩ e heK h T147_105 hfix147_105 hinj147_105 hcardT147_105
    (fun i => conj_mem_of_fixedPoints (reps ⟨105, by decide⟩) (reps rK147) (T147_105 i) (hfix147_105 i) h)

/-! ## Cell (147, 106): |T| = 1 -/

def T147_106list : List Coordinates := [(0,0,0,0,0)]
def T147_106 : Fin 1 → Coordinate 1 := fun i => T147_106list.getD i.val (0,0,0,0,0)

theorem hfix147_106 : ∀ i, ((T147_106 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨106, by decide⟩ T147_106 (by decide)

theorem hinj147_106 : Function.Injective
    (fun i => ((T147_106 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_106 (by decide)

theorem hcardT147_106 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨106, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 106).** -/
theorem cell147_106 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨106, by decide⟩ : Fin 148))) :
    species (reps (⟨106, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_106 i :=
  species_entry_eq_sum rK147 ⟨106, by decide⟩ e heK h T147_106 hfix147_106 hinj147_106 hcardT147_106
    (fun i => conj_mem_of_fixedPoints (reps ⟨106, by decide⟩) (reps rK147) (T147_106 i) (hfix147_106 i) h)

/-! ## Cell (147, 107): |T| = 1 -/

def T147_107list : List Coordinates := [(0,0,0,0,0)]
def T147_107 : Fin 1 → Coordinate 1 := fun i => T147_107list.getD i.val (0,0,0,0,0)

theorem hfix147_107 : ∀ i, ((T147_107 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨107, by decide⟩ T147_107 (by decide)

theorem hinj147_107 : Function.Injective
    (fun i => ((T147_107 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_107 (by decide)

theorem hcardT147_107 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨107, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 107).** -/
theorem cell147_107 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨107, by decide⟩ : Fin 148))) :
    species (reps (⟨107, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_107 i :=
  species_entry_eq_sum rK147 ⟨107, by decide⟩ e heK h T147_107 hfix147_107 hinj147_107 hcardT147_107
    (fun i => conj_mem_of_fixedPoints (reps ⟨107, by decide⟩) (reps rK147) (T147_107 i) (hfix147_107 i) h)

/-! ## Cell (147, 108): |T| = 1 -/

def T147_108list : List Coordinates := [(0,0,0,0,0)]
def T147_108 : Fin 1 → Coordinate 1 := fun i => T147_108list.getD i.val (0,0,0,0,0)

theorem hfix147_108 : ∀ i, ((T147_108 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨108, by decide⟩ T147_108 (by decide)

theorem hinj147_108 : Function.Injective
    (fun i => ((T147_108 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_108 (by decide)

theorem hcardT147_108 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨108, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 108).** -/
theorem cell147_108 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨108, by decide⟩ : Fin 148))) :
    species (reps (⟨108, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_108 i :=
  species_entry_eq_sum rK147 ⟨108, by decide⟩ e heK h T147_108 hfix147_108 hinj147_108 hcardT147_108
    (fun i => conj_mem_of_fixedPoints (reps ⟨108, by decide⟩) (reps rK147) (T147_108 i) (hfix147_108 i) h)

/-! ## Cell (147, 109): |T| = 1 -/

def T147_109list : List Coordinates := [(0,0,0,0,0)]
def T147_109 : Fin 1 → Coordinate 1 := fun i => T147_109list.getD i.val (0,0,0,0,0)

theorem hfix147_109 : ∀ i, ((T147_109 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨109, by decide⟩ T147_109 (by decide)

theorem hinj147_109 : Function.Injective
    (fun i => ((T147_109 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_109 (by decide)

theorem hcardT147_109 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨109, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 109).** -/
theorem cell147_109 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨109, by decide⟩ : Fin 148))) :
    species (reps (⟨109, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_109 i :=
  species_entry_eq_sum rK147 ⟨109, by decide⟩ e heK h T147_109 hfix147_109 hinj147_109 hcardT147_109
    (fun i => conj_mem_of_fixedPoints (reps ⟨109, by decide⟩) (reps rK147) (T147_109 i) (hfix147_109 i) h)

/-! ## Cell (147, 110): |T| = 1 -/

def T147_110list : List Coordinates := [(0,0,0,0,0)]
def T147_110 : Fin 1 → Coordinate 1 := fun i => T147_110list.getD i.val (0,0,0,0,0)

theorem hfix147_110 : ∀ i, ((T147_110 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨110, by decide⟩ T147_110 (by decide)

theorem hinj147_110 : Function.Injective
    (fun i => ((T147_110 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_110 (by decide)

theorem hcardT147_110 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨110, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 110).** -/
theorem cell147_110 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨110, by decide⟩ : Fin 148))) :
    species (reps (⟨110, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_110 i :=
  species_entry_eq_sum rK147 ⟨110, by decide⟩ e heK h T147_110 hfix147_110 hinj147_110 hcardT147_110
    (fun i => conj_mem_of_fixedPoints (reps ⟨110, by decide⟩) (reps rK147) (T147_110 i) (hfix147_110 i) h)

/-! ## Cell (147, 111): |T| = 1 -/

def T147_111list : List Coordinates := [(0,0,0,0,0)]
def T147_111 : Fin 1 → Coordinate 1 := fun i => T147_111list.getD i.val (0,0,0,0,0)

theorem hfix147_111 : ∀ i, ((T147_111 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨111, by decide⟩ T147_111 (by decide)

theorem hinj147_111 : Function.Injective
    (fun i => ((T147_111 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_111 (by decide)

theorem hcardT147_111 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨111, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 111).** -/
theorem cell147_111 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨111, by decide⟩ : Fin 148))) :
    species (reps (⟨111, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_111 i :=
  species_entry_eq_sum rK147 ⟨111, by decide⟩ e heK h T147_111 hfix147_111 hinj147_111 hcardT147_111
    (fun i => conj_mem_of_fixedPoints (reps ⟨111, by decide⟩) (reps rK147) (T147_111 i) (hfix147_111 i) h)

/-! ## Cell (147, 112): |T| = 1 -/

def T147_112list : List Coordinates := [(0,0,0,0,0)]
def T147_112 : Fin 1 → Coordinate 1 := fun i => T147_112list.getD i.val (0,0,0,0,0)

theorem hfix147_112 : ∀ i, ((T147_112 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨112, by decide⟩ T147_112 (by decide)

theorem hinj147_112 : Function.Injective
    (fun i => ((T147_112 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_112 (by decide)

theorem hcardT147_112 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨112, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 112).** -/
theorem cell147_112 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨112, by decide⟩ : Fin 148))) :
    species (reps (⟨112, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_112 i :=
  species_entry_eq_sum rK147 ⟨112, by decide⟩ e heK h T147_112 hfix147_112 hinj147_112 hcardT147_112
    (fun i => conj_mem_of_fixedPoints (reps ⟨112, by decide⟩) (reps rK147) (T147_112 i) (hfix147_112 i) h)

/-! ## Cell (147, 113): |T| = 1 -/

def T147_113list : List Coordinates := [(0,0,0,0,0)]
def T147_113 : Fin 1 → Coordinate 1 := fun i => T147_113list.getD i.val (0,0,0,0,0)

theorem hfix147_113 : ∀ i, ((T147_113 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨113, by decide⟩ T147_113 (by decide)

theorem hinj147_113 : Function.Injective
    (fun i => ((T147_113 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_113 (by decide)

theorem hcardT147_113 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨113, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 113).** -/
theorem cell147_113 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨113, by decide⟩ : Fin 148))) :
    species (reps (⟨113, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_113 i :=
  species_entry_eq_sum rK147 ⟨113, by decide⟩ e heK h T147_113 hfix147_113 hinj147_113 hcardT147_113
    (fun i => conj_mem_of_fixedPoints (reps ⟨113, by decide⟩) (reps rK147) (T147_113 i) (hfix147_113 i) h)

/-! ## Cell (147, 114): |T| = 1 -/

def T147_114list : List Coordinates := [(0,0,0,0,0)]
def T147_114 : Fin 1 → Coordinate 1 := fun i => T147_114list.getD i.val (0,0,0,0,0)

theorem hfix147_114 : ∀ i, ((T147_114 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨114, by decide⟩ T147_114 (by decide)

theorem hinj147_114 : Function.Injective
    (fun i => ((T147_114 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_114 (by decide)

theorem hcardT147_114 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨114, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 114).** -/
theorem cell147_114 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨114, by decide⟩ : Fin 148))) :
    species (reps (⟨114, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_114 i :=
  species_entry_eq_sum rK147 ⟨114, by decide⟩ e heK h T147_114 hfix147_114 hinj147_114 hcardT147_114
    (fun i => conj_mem_of_fixedPoints (reps ⟨114, by decide⟩) (reps rK147) (T147_114 i) (hfix147_114 i) h)

/-! ## Cell (147, 115): |T| = 1 -/

def T147_115list : List Coordinates := [(0,0,0,0,0)]
def T147_115 : Fin 1 → Coordinate 1 := fun i => T147_115list.getD i.val (0,0,0,0,0)

theorem hfix147_115 : ∀ i, ((T147_115 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨115, by decide⟩ T147_115 (by decide)

theorem hinj147_115 : Function.Injective
    (fun i => ((T147_115 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_115 (by decide)

theorem hcardT147_115 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨115, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 115).** -/
theorem cell147_115 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨115, by decide⟩ : Fin 148))) :
    species (reps (⟨115, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_115 i :=
  species_entry_eq_sum rK147 ⟨115, by decide⟩ e heK h T147_115 hfix147_115 hinj147_115 hcardT147_115
    (fun i => conj_mem_of_fixedPoints (reps ⟨115, by decide⟩) (reps rK147) (T147_115 i) (hfix147_115 i) h)

/-! ## Cell (147, 116): |T| = 1 -/

def T147_116list : List Coordinates := [(0,0,0,0,0)]
def T147_116 : Fin 1 → Coordinate 1 := fun i => T147_116list.getD i.val (0,0,0,0,0)

theorem hfix147_116 : ∀ i, ((T147_116 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨116, by decide⟩ T147_116 (by decide)

theorem hinj147_116 : Function.Injective
    (fun i => ((T147_116 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_116 (by decide)

theorem hcardT147_116 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨116, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 116).** -/
theorem cell147_116 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨116, by decide⟩ : Fin 148))) :
    species (reps (⟨116, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_116 i :=
  species_entry_eq_sum rK147 ⟨116, by decide⟩ e heK h T147_116 hfix147_116 hinj147_116 hcardT147_116
    (fun i => conj_mem_of_fixedPoints (reps ⟨116, by decide⟩) (reps rK147) (T147_116 i) (hfix147_116 i) h)

/-! ## Cell (147, 117): |T| = 1 -/

def T147_117list : List Coordinates := [(0,0,0,0,0)]
def T147_117 : Fin 1 → Coordinate 1 := fun i => T147_117list.getD i.val (0,0,0,0,0)

theorem hfix147_117 : ∀ i, ((T147_117 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨117, by decide⟩ T147_117 (by decide)

theorem hinj147_117 : Function.Injective
    (fun i => ((T147_117 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_117 (by decide)

theorem hcardT147_117 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨117, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 117).** -/
theorem cell147_117 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨117, by decide⟩ : Fin 148))) :
    species (reps (⟨117, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_117 i :=
  species_entry_eq_sum rK147 ⟨117, by decide⟩ e heK h T147_117 hfix147_117 hinj147_117 hcardT147_117
    (fun i => conj_mem_of_fixedPoints (reps ⟨117, by decide⟩) (reps rK147) (T147_117 i) (hfix147_117 i) h)

/-! ## Cell (147, 118): |T| = 1 -/

def T147_118list : List Coordinates := [(0,0,0,0,0)]
def T147_118 : Fin 1 → Coordinate 1 := fun i => T147_118list.getD i.val (0,0,0,0,0)

theorem hfix147_118 : ∀ i, ((T147_118 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨118, by decide⟩ T147_118 (by decide)

theorem hinj147_118 : Function.Injective
    (fun i => ((T147_118 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_118 (by decide)

theorem hcardT147_118 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨118, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 118).** -/
theorem cell147_118 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨118, by decide⟩ : Fin 148))) :
    species (reps (⟨118, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_118 i :=
  species_entry_eq_sum rK147 ⟨118, by decide⟩ e heK h T147_118 hfix147_118 hinj147_118 hcardT147_118
    (fun i => conj_mem_of_fixedPoints (reps ⟨118, by decide⟩) (reps rK147) (T147_118 i) (hfix147_118 i) h)

/-! ## Cell (147, 119): |T| = 1 -/

def T147_119list : List Coordinates := [(0,0,0,0,0)]
def T147_119 : Fin 1 → Coordinate 1 := fun i => T147_119list.getD i.val (0,0,0,0,0)

theorem hfix147_119 : ∀ i, ((T147_119 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨119, by decide⟩ T147_119 (by decide)

theorem hinj147_119 : Function.Injective
    (fun i => ((T147_119 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_119 (by decide)

theorem hcardT147_119 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨119, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 119).** -/
theorem cell147_119 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨119, by decide⟩ : Fin 148))) :
    species (reps (⟨119, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_119 i :=
  species_entry_eq_sum rK147 ⟨119, by decide⟩ e heK h T147_119 hfix147_119 hinj147_119 hcardT147_119
    (fun i => conj_mem_of_fixedPoints (reps ⟨119, by decide⟩) (reps rK147) (T147_119 i) (hfix147_119 i) h)

/-! ## Cell (147, 120): |T| = 1 -/

def T147_120list : List Coordinates := [(0,0,0,0,0)]
def T147_120 : Fin 1 → Coordinate 1 := fun i => T147_120list.getD i.val (0,0,0,0,0)

theorem hfix147_120 : ∀ i, ((T147_120 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨120, by decide⟩ T147_120 (by decide)

theorem hinj147_120 : Function.Injective
    (fun i => ((T147_120 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_120 (by decide)

theorem hcardT147_120 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨120, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 120).** -/
theorem cell147_120 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨120, by decide⟩ : Fin 148))) :
    species (reps (⟨120, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_120 i :=
  species_entry_eq_sum rK147 ⟨120, by decide⟩ e heK h T147_120 hfix147_120 hinj147_120 hcardT147_120
    (fun i => conj_mem_of_fixedPoints (reps ⟨120, by decide⟩) (reps rK147) (T147_120 i) (hfix147_120 i) h)

/-! ## Cell (147, 121): |T| = 1 -/

def T147_121list : List Coordinates := [(0,0,0,0,0)]
def T147_121 : Fin 1 → Coordinate 1 := fun i => T147_121list.getD i.val (0,0,0,0,0)

theorem hfix147_121 : ∀ i, ((T147_121 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨121, by decide⟩ T147_121 (by decide)

theorem hinj147_121 : Function.Injective
    (fun i => ((T147_121 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_121 (by decide)

theorem hcardT147_121 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨121, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 121).** -/
theorem cell147_121 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨121, by decide⟩ : Fin 148))) :
    species (reps (⟨121, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_121 i :=
  species_entry_eq_sum rK147 ⟨121, by decide⟩ e heK h T147_121 hfix147_121 hinj147_121 hcardT147_121
    (fun i => conj_mem_of_fixedPoints (reps ⟨121, by decide⟩) (reps rK147) (T147_121 i) (hfix147_121 i) h)

/-! ## Cell (147, 122): |T| = 1 -/

def T147_122list : List Coordinates := [(0,0,0,0,0)]
def T147_122 : Fin 1 → Coordinate 1 := fun i => T147_122list.getD i.val (0,0,0,0,0)

theorem hfix147_122 : ∀ i, ((T147_122 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨122, by decide⟩ T147_122 (by decide)

theorem hinj147_122 : Function.Injective
    (fun i => ((T147_122 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_122 (by decide)

theorem hcardT147_122 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨122, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 122).** -/
theorem cell147_122 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨122, by decide⟩ : Fin 148))) :
    species (reps (⟨122, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_122 i :=
  species_entry_eq_sum rK147 ⟨122, by decide⟩ e heK h T147_122 hfix147_122 hinj147_122 hcardT147_122
    (fun i => conj_mem_of_fixedPoints (reps ⟨122, by decide⟩) (reps rK147) (T147_122 i) (hfix147_122 i) h)

/-! ## Cell (147, 123): |T| = 1 -/

def T147_123list : List Coordinates := [(0,0,0,0,0)]
def T147_123 : Fin 1 → Coordinate 1 := fun i => T147_123list.getD i.val (0,0,0,0,0)

theorem hfix147_123 : ∀ i, ((T147_123 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨123, by decide⟩ T147_123 (by decide)

theorem hinj147_123 : Function.Injective
    (fun i => ((T147_123 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_123 (by decide)

theorem hcardT147_123 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨123, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 123).** -/
theorem cell147_123 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨123, by decide⟩ : Fin 148))) :
    species (reps (⟨123, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_123 i :=
  species_entry_eq_sum rK147 ⟨123, by decide⟩ e heK h T147_123 hfix147_123 hinj147_123 hcardT147_123
    (fun i => conj_mem_of_fixedPoints (reps ⟨123, by decide⟩) (reps rK147) (T147_123 i) (hfix147_123 i) h)

/-! ## Cell (147, 124): |T| = 1 -/

def T147_124list : List Coordinates := [(0,0,0,0,0)]
def T147_124 : Fin 1 → Coordinate 1 := fun i => T147_124list.getD i.val (0,0,0,0,0)

theorem hfix147_124 : ∀ i, ((T147_124 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨124, by decide⟩ T147_124 (by decide)

theorem hinj147_124 : Function.Injective
    (fun i => ((T147_124 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_124 (by decide)

theorem hcardT147_124 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨124, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 124).** -/
theorem cell147_124 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨124, by decide⟩ : Fin 148))) :
    species (reps (⟨124, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_124 i :=
  species_entry_eq_sum rK147 ⟨124, by decide⟩ e heK h T147_124 hfix147_124 hinj147_124 hcardT147_124
    (fun i => conj_mem_of_fixedPoints (reps ⟨124, by decide⟩) (reps rK147) (T147_124 i) (hfix147_124 i) h)

/-! ## Cell (147, 125): |T| = 1 -/

def T147_125list : List Coordinates := [(0,0,0,0,0)]
def T147_125 : Fin 1 → Coordinate 1 := fun i => T147_125list.getD i.val (0,0,0,0,0)

theorem hfix147_125 : ∀ i, ((T147_125 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨125, by decide⟩ T147_125 (by decide)

theorem hinj147_125 : Function.Injective
    (fun i => ((T147_125 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_125 (by decide)

theorem hcardT147_125 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨125, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 125).** -/
theorem cell147_125 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨125, by decide⟩ : Fin 148))) :
    species (reps (⟨125, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_125 i :=
  species_entry_eq_sum rK147 ⟨125, by decide⟩ e heK h T147_125 hfix147_125 hinj147_125 hcardT147_125
    (fun i => conj_mem_of_fixedPoints (reps ⟨125, by decide⟩) (reps rK147) (T147_125 i) (hfix147_125 i) h)

/-! ## Cell (147, 126): |T| = 1 -/

def T147_126list : List Coordinates := [(0,0,0,0,0)]
def T147_126 : Fin 1 → Coordinate 1 := fun i => T147_126list.getD i.val (0,0,0,0,0)

theorem hfix147_126 : ∀ i, ((T147_126 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨126, by decide⟩ T147_126 (by decide)

theorem hinj147_126 : Function.Injective
    (fun i => ((T147_126 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_126 (by decide)

theorem hcardT147_126 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨126, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 126).** -/
theorem cell147_126 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨126, by decide⟩ : Fin 148))) :
    species (reps (⟨126, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_126 i :=
  species_entry_eq_sum rK147 ⟨126, by decide⟩ e heK h T147_126 hfix147_126 hinj147_126 hcardT147_126
    (fun i => conj_mem_of_fixedPoints (reps ⟨126, by decide⟩) (reps rK147) (T147_126 i) (hfix147_126 i) h)

/-! ## Cell (147, 127): |T| = 1 -/

def T147_127list : List Coordinates := [(0,0,0,0,0)]
def T147_127 : Fin 1 → Coordinate 1 := fun i => T147_127list.getD i.val (0,0,0,0,0)

theorem hfix147_127 : ∀ i, ((T147_127 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨127, by decide⟩ T147_127 (by decide)

theorem hinj147_127 : Function.Injective
    (fun i => ((T147_127 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_127 (by decide)

theorem hcardT147_127 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨127, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 127).** -/
theorem cell147_127 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨127, by decide⟩ : Fin 148))) :
    species (reps (⟨127, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_127 i :=
  species_entry_eq_sum rK147 ⟨127, by decide⟩ e heK h T147_127 hfix147_127 hinj147_127 hcardT147_127
    (fun i => conj_mem_of_fixedPoints (reps ⟨127, by decide⟩) (reps rK147) (T147_127 i) (hfix147_127 i) h)

/-! ## Cell (147, 128): |T| = 1 -/

def T147_128list : List Coordinates := [(0,0,0,0,0)]
def T147_128 : Fin 1 → Coordinate 1 := fun i => T147_128list.getD i.val (0,0,0,0,0)

theorem hfix147_128 : ∀ i, ((T147_128 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨128, by decide⟩ T147_128 (by decide)

theorem hinj147_128 : Function.Injective
    (fun i => ((T147_128 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_128 (by decide)

theorem hcardT147_128 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨128, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 128).** -/
theorem cell147_128 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨128, by decide⟩ : Fin 148))) :
    species (reps (⟨128, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_128 i :=
  species_entry_eq_sum rK147 ⟨128, by decide⟩ e heK h T147_128 hfix147_128 hinj147_128 hcardT147_128
    (fun i => conj_mem_of_fixedPoints (reps ⟨128, by decide⟩) (reps rK147) (T147_128 i) (hfix147_128 i) h)

/-! ## Cell (147, 129): |T| = 1 -/

def T147_129list : List Coordinates := [(0,0,0,0,0)]
def T147_129 : Fin 1 → Coordinate 1 := fun i => T147_129list.getD i.val (0,0,0,0,0)

theorem hfix147_129 : ∀ i, ((T147_129 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨129, by decide⟩ T147_129 (by decide)

theorem hinj147_129 : Function.Injective
    (fun i => ((T147_129 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_129 (by decide)

theorem hcardT147_129 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨129, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 129).** -/
theorem cell147_129 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨129, by decide⟩ : Fin 148))) :
    species (reps (⟨129, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_129 i :=
  species_entry_eq_sum rK147 ⟨129, by decide⟩ e heK h T147_129 hfix147_129 hinj147_129 hcardT147_129
    (fun i => conj_mem_of_fixedPoints (reps ⟨129, by decide⟩) (reps rK147) (T147_129 i) (hfix147_129 i) h)

/-! ## Cell (147, 130): |T| = 1 -/

def T147_130list : List Coordinates := [(0,0,0,0,0)]
def T147_130 : Fin 1 → Coordinate 1 := fun i => T147_130list.getD i.val (0,0,0,0,0)

theorem hfix147_130 : ∀ i, ((T147_130 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨130, by decide⟩ T147_130 (by decide)

theorem hinj147_130 : Function.Injective
    (fun i => ((T147_130 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_130 (by decide)

theorem hcardT147_130 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨130, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 130).** -/
theorem cell147_130 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨130, by decide⟩ : Fin 148))) :
    species (reps (⟨130, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_130 i :=
  species_entry_eq_sum rK147 ⟨130, by decide⟩ e heK h T147_130 hfix147_130 hinj147_130 hcardT147_130
    (fun i => conj_mem_of_fixedPoints (reps ⟨130, by decide⟩) (reps rK147) (T147_130 i) (hfix147_130 i) h)

/-! ## Cell (147, 131): |T| = 1 -/

def T147_131list : List Coordinates := [(0,0,0,0,0)]
def T147_131 : Fin 1 → Coordinate 1 := fun i => T147_131list.getD i.val (0,0,0,0,0)

theorem hfix147_131 : ∀ i, ((T147_131 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨131, by decide⟩ T147_131 (by decide)

theorem hinj147_131 : Function.Injective
    (fun i => ((T147_131 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_131 (by decide)

theorem hcardT147_131 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨131, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 131).** -/
theorem cell147_131 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨131, by decide⟩ : Fin 148))) :
    species (reps (⟨131, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_131 i :=
  species_entry_eq_sum rK147 ⟨131, by decide⟩ e heK h T147_131 hfix147_131 hinj147_131 hcardT147_131
    (fun i => conj_mem_of_fixedPoints (reps ⟨131, by decide⟩) (reps rK147) (T147_131 i) (hfix147_131 i) h)

/-! ## Cell (147, 132): |T| = 1 -/

def T147_132list : List Coordinates := [(0,0,0,0,0)]
def T147_132 : Fin 1 → Coordinate 1 := fun i => T147_132list.getD i.val (0,0,0,0,0)

theorem hfix147_132 : ∀ i, ((T147_132 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨132, by decide⟩ T147_132 (by decide)

theorem hinj147_132 : Function.Injective
    (fun i => ((T147_132 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_132 (by decide)

theorem hcardT147_132 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨132, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 132).** -/
theorem cell147_132 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨132, by decide⟩ : Fin 148))) :
    species (reps (⟨132, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_132 i :=
  species_entry_eq_sum rK147 ⟨132, by decide⟩ e heK h T147_132 hfix147_132 hinj147_132 hcardT147_132
    (fun i => conj_mem_of_fixedPoints (reps ⟨132, by decide⟩) (reps rK147) (T147_132 i) (hfix147_132 i) h)

/-! ## Cell (147, 133): |T| = 1 -/

def T147_133list : List Coordinates := [(0,0,0,0,0)]
def T147_133 : Fin 1 → Coordinate 1 := fun i => T147_133list.getD i.val (0,0,0,0,0)

theorem hfix147_133 : ∀ i, ((T147_133 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨133, by decide⟩ T147_133 (by decide)

theorem hinj147_133 : Function.Injective
    (fun i => ((T147_133 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_133 (by decide)

theorem hcardT147_133 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨133, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 133).** -/
theorem cell147_133 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨133, by decide⟩ : Fin 148))) :
    species (reps (⟨133, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_133 i :=
  species_entry_eq_sum rK147 ⟨133, by decide⟩ e heK h T147_133 hfix147_133 hinj147_133 hcardT147_133
    (fun i => conj_mem_of_fixedPoints (reps ⟨133, by decide⟩) (reps rK147) (T147_133 i) (hfix147_133 i) h)

/-! ## Cell (147, 134): |T| = 1 -/

def T147_134list : List Coordinates := [(0,0,0,0,0)]
def T147_134 : Fin 1 → Coordinate 1 := fun i => T147_134list.getD i.val (0,0,0,0,0)

theorem hfix147_134 : ∀ i, ((T147_134 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨134, by decide⟩ T147_134 (by decide)

theorem hinj147_134 : Function.Injective
    (fun i => ((T147_134 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_134 (by decide)

theorem hcardT147_134 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨134, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 134).** -/
theorem cell147_134 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨134, by decide⟩ : Fin 148))) :
    species (reps (⟨134, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_134 i :=
  species_entry_eq_sum rK147 ⟨134, by decide⟩ e heK h T147_134 hfix147_134 hinj147_134 hcardT147_134
    (fun i => conj_mem_of_fixedPoints (reps ⟨134, by decide⟩) (reps rK147) (T147_134 i) (hfix147_134 i) h)

/-! ## Cell (147, 135): |T| = 1 -/

def T147_135list : List Coordinates := [(0,0,0,0,0)]
def T147_135 : Fin 1 → Coordinate 1 := fun i => T147_135list.getD i.val (0,0,0,0,0)

theorem hfix147_135 : ∀ i, ((T147_135 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨135, by decide⟩ T147_135 (by decide)

theorem hinj147_135 : Function.Injective
    (fun i => ((T147_135 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_135 (by decide)

theorem hcardT147_135 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨135, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 135).** -/
theorem cell147_135 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨135, by decide⟩ : Fin 148))) :
    species (reps (⟨135, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_135 i :=
  species_entry_eq_sum rK147 ⟨135, by decide⟩ e heK h T147_135 hfix147_135 hinj147_135 hcardT147_135
    (fun i => conj_mem_of_fixedPoints (reps ⟨135, by decide⟩) (reps rK147) (T147_135 i) (hfix147_135 i) h)

/-! ## Cell (147, 136): |T| = 1 -/

def T147_136list : List Coordinates := [(0,0,0,0,0)]
def T147_136 : Fin 1 → Coordinate 1 := fun i => T147_136list.getD i.val (0,0,0,0,0)

theorem hfix147_136 : ∀ i, ((T147_136 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨136, by decide⟩ T147_136 (by decide)

theorem hinj147_136 : Function.Injective
    (fun i => ((T147_136 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_136 (by decide)

theorem hcardT147_136 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨136, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 136).** -/
theorem cell147_136 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨136, by decide⟩ : Fin 148))) :
    species (reps (⟨136, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_136 i :=
  species_entry_eq_sum rK147 ⟨136, by decide⟩ e heK h T147_136 hfix147_136 hinj147_136 hcardT147_136
    (fun i => conj_mem_of_fixedPoints (reps ⟨136, by decide⟩) (reps rK147) (T147_136 i) (hfix147_136 i) h)

/-! ## Cell (147, 137): |T| = 1 -/

def T147_137list : List Coordinates := [(0,0,0,0,0)]
def T147_137 : Fin 1 → Coordinate 1 := fun i => T147_137list.getD i.val (0,0,0,0,0)

theorem hfix147_137 : ∀ i, ((T147_137 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨137, by decide⟩ T147_137 (by decide)

theorem hinj147_137 : Function.Injective
    (fun i => ((T147_137 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_137 (by decide)

theorem hcardT147_137 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨137, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 137).** -/
theorem cell147_137 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨137, by decide⟩ : Fin 148))) :
    species (reps (⟨137, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_137 i :=
  species_entry_eq_sum rK147 ⟨137, by decide⟩ e heK h T147_137 hfix147_137 hinj147_137 hcardT147_137
    (fun i => conj_mem_of_fixedPoints (reps ⟨137, by decide⟩) (reps rK147) (T147_137 i) (hfix147_137 i) h)

/-! ## Cell (147, 138): |T| = 1 -/

def T147_138list : List Coordinates := [(0,0,0,0,0)]
def T147_138 : Fin 1 → Coordinate 1 := fun i => T147_138list.getD i.val (0,0,0,0,0)

theorem hfix147_138 : ∀ i, ((T147_138 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨138, by decide⟩ T147_138 (by decide)

theorem hinj147_138 : Function.Injective
    (fun i => ((T147_138 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_138 (by decide)

theorem hcardT147_138 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨138, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 138).** -/
theorem cell147_138 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨138, by decide⟩ : Fin 148))) :
    species (reps (⟨138, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_138 i :=
  species_entry_eq_sum rK147 ⟨138, by decide⟩ e heK h T147_138 hfix147_138 hinj147_138 hcardT147_138
    (fun i => conj_mem_of_fixedPoints (reps ⟨138, by decide⟩) (reps rK147) (T147_138 i) (hfix147_138 i) h)

/-! ## Cell (147, 139): |T| = 1 -/

def T147_139list : List Coordinates := [(0,0,0,0,0)]
def T147_139 : Fin 1 → Coordinate 1 := fun i => T147_139list.getD i.val (0,0,0,0,0)

theorem hfix147_139 : ∀ i, ((T147_139 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨139, by decide⟩ T147_139 (by decide)

theorem hinj147_139 : Function.Injective
    (fun i => ((T147_139 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_139 (by decide)

theorem hcardT147_139 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨139, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 139).** -/
theorem cell147_139 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨139, by decide⟩ : Fin 148))) :
    species (reps (⟨139, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_139 i :=
  species_entry_eq_sum rK147 ⟨139, by decide⟩ e heK h T147_139 hfix147_139 hinj147_139 hcardT147_139
    (fun i => conj_mem_of_fixedPoints (reps ⟨139, by decide⟩) (reps rK147) (T147_139 i) (hfix147_139 i) h)

/-! ## Cell (147, 140): |T| = 1 -/

def T147_140list : List Coordinates := [(0,0,0,0,0)]
def T147_140 : Fin 1 → Coordinate 1 := fun i => T147_140list.getD i.val (0,0,0,0,0)

theorem hfix147_140 : ∀ i, ((T147_140 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨140, by decide⟩ T147_140 (by decide)

theorem hinj147_140 : Function.Injective
    (fun i => ((T147_140 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_140 (by decide)

theorem hcardT147_140 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨140, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 140).** -/
theorem cell147_140 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨140, by decide⟩ : Fin 148))) :
    species (reps (⟨140, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_140 i :=
  species_entry_eq_sum rK147 ⟨140, by decide⟩ e heK h T147_140 hfix147_140 hinj147_140 hcardT147_140
    (fun i => conj_mem_of_fixedPoints (reps ⟨140, by decide⟩) (reps rK147) (T147_140 i) (hfix147_140 i) h)

/-! ## Cell (147, 141): |T| = 1 -/

def T147_141list : List Coordinates := [(0,0,0,0,0)]
def T147_141 : Fin 1 → Coordinate 1 := fun i => T147_141list.getD i.val (0,0,0,0,0)

theorem hfix147_141 : ∀ i, ((T147_141 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨141, by decide⟩ T147_141 (by decide)

theorem hinj147_141 : Function.Injective
    (fun i => ((T147_141 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_141 (by decide)

theorem hcardT147_141 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨141, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 141).** -/
theorem cell147_141 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨141, by decide⟩ : Fin 148))) :
    species (reps (⟨141, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_141 i :=
  species_entry_eq_sum rK147 ⟨141, by decide⟩ e heK h T147_141 hfix147_141 hinj147_141 hcardT147_141
    (fun i => conj_mem_of_fixedPoints (reps ⟨141, by decide⟩) (reps rK147) (T147_141 i) (hfix147_141 i) h)

/-! ## Cell (147, 142): |T| = 1 -/

def T147_142list : List Coordinates := [(0,0,0,0,0)]
def T147_142 : Fin 1 → Coordinate 1 := fun i => T147_142list.getD i.val (0,0,0,0,0)

theorem hfix147_142 : ∀ i, ((T147_142 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨142, by decide⟩ T147_142 (by decide)

theorem hinj147_142 : Function.Injective
    (fun i => ((T147_142 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_142 (by decide)

theorem hcardT147_142 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨142, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 142).** -/
theorem cell147_142 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨142, by decide⟩ : Fin 148))) :
    species (reps (⟨142, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_142 i :=
  species_entry_eq_sum rK147 ⟨142, by decide⟩ e heK h T147_142 hfix147_142 hinj147_142 hcardT147_142
    (fun i => conj_mem_of_fixedPoints (reps ⟨142, by decide⟩) (reps rK147) (T147_142 i) (hfix147_142 i) h)

/-! ## Cell (147, 143): |T| = 1 -/

def T147_143list : List Coordinates := [(0,0,0,0,0)]
def T147_143 : Fin 1 → Coordinate 1 := fun i => T147_143list.getD i.val (0,0,0,0,0)

theorem hfix147_143 : ∀ i, ((T147_143 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨143, by decide⟩ T147_143 (by decide)

theorem hinj147_143 : Function.Injective
    (fun i => ((T147_143 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_143 (by decide)

theorem hcardT147_143 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨143, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 143).** -/
theorem cell147_143 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨143, by decide⟩ : Fin 148))) :
    species (reps (⟨143, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_143 i :=
  species_entry_eq_sum rK147 ⟨143, by decide⟩ e heK h T147_143 hfix147_143 hinj147_143 hcardT147_143
    (fun i => conj_mem_of_fixedPoints (reps ⟨143, by decide⟩) (reps rK147) (T147_143 i) (hfix147_143 i) h)

/-! ## Cell (147, 144): |T| = 1 -/

def T147_144list : List Coordinates := [(0,0,0,0,0)]
def T147_144 : Fin 1 → Coordinate 1 := fun i => T147_144list.getD i.val (0,0,0,0,0)

theorem hfix147_144 : ∀ i, ((T147_144 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨144, by decide⟩ T147_144 (by decide)

theorem hinj147_144 : Function.Injective
    (fun i => ((T147_144 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_144 (by decide)

theorem hcardT147_144 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨144, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 144).** -/
theorem cell147_144 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨144, by decide⟩ : Fin 148))) :
    species (reps (⟨144, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_144 i :=
  species_entry_eq_sum rK147 ⟨144, by decide⟩ e heK h T147_144 hfix147_144 hinj147_144 hcardT147_144
    (fun i => conj_mem_of_fixedPoints (reps ⟨144, by decide⟩) (reps rK147) (T147_144 i) (hfix147_144 i) h)

/-! ## Cell (147, 145): |T| = 1 -/

def T147_145list : List Coordinates := [(0,0,0,0,0)]
def T147_145 : Fin 1 → Coordinate 1 := fun i => T147_145list.getD i.val (0,0,0,0,0)

theorem hfix147_145 : ∀ i, ((T147_145 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨145, by decide⟩ T147_145 (by decide)

theorem hinj147_145 : Function.Injective
    (fun i => ((T147_145 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_145 (by decide)

theorem hcardT147_145 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨145, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 145).** -/
theorem cell147_145 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨145, by decide⟩ : Fin 148))) :
    species (reps (⟨145, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_145 i :=
  species_entry_eq_sum rK147 ⟨145, by decide⟩ e heK h T147_145 hfix147_145 hinj147_145 hcardT147_145
    (fun i => conj_mem_of_fixedPoints (reps ⟨145, by decide⟩) (reps rK147) (T147_145 i) (hfix147_145 i) h)

/-! ## Cell (147, 146): |T| = 1 -/

def T147_146list : List Coordinates := [(0,0,0,0,0)]
def T147_146 : Fin 1 → Coordinate 1 := fun i => T147_146list.getD i.val (0,0,0,0,0)

theorem hfix147_146 : ∀ i, ((T147_146 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨146, by decide⟩ T147_146 (by decide)

theorem hinj147_146 : Function.Injective
    (fun i => ((T147_146 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_146 (by decide)

theorem hcardT147_146 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨146, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 146).** -/
theorem cell147_146 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨146, by decide⟩ : Fin 148))) :
    species (reps (⟨146, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_146 i :=
  species_entry_eq_sum rK147 ⟨146, by decide⟩ e heK h T147_146 hfix147_146 hinj147_146 hcardT147_146
    (fun i => conj_mem_of_fixedPoints (reps ⟨146, by decide⟩) (reps rK147) (T147_146 i) (hfix147_146 i) h)

/-! ## Cell (147, 147): |T| = 1 -/

def T147_147list : List Coordinates := [(0,0,0,0,0)]
def T147_147 : Fin 1 → Coordinate 1 := fun i => T147_147list.getD i.val (0,0,0,0,0)

theorem hfix147_147 : ∀ i, ((T147_147 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨147, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147) :=
  repsFix_of_siftB rK147 ⟨147, by decide⟩ T147_147 (by decide)

theorem hinj147_147 : Function.Injective
    (fun i => ((T147_147 i : Coordinate 1) : Coordinate 1 ⧸ reps rK147)) :=
  repsInj_of_reduceAux rK147 T147_147 (by decide)

theorem hcardT147_147 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨147, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK147 ⟨147, by decide⟩ R147 hpxR147 hcardq147 (by decide)).symm

/-- **Cell (147, 147).** -/
theorem cell147_147 (e : List (ZMod 25)) (heK : charOK (basisAt rK147) e = true)
    (h : ↥(reps (⟨147, by decide⟩ : Fin 148))) :
    species (reps (⟨147, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK147 e (h : Coordinate 1) T147_147 i :=
  species_entry_eq_sum rK147 ⟨147, by decide⟩ e heK h T147_147 hfix147_147 hinj147_147 hcardT147_147
    (fun i => conj_mem_of_fixedPoints (reps ⟨147, by decide⟩) (reps rK147) (T147_147 i) (hfix147_147 i) h)

namespace Q2

def R147_2 : Fin 1 → Coordinate 2 := fun i => R147list.getD i.val (0,0,0,0,0)
theorem hpxR147_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK147) (R147_2 i)) := by decide
theorem hcardq147_2 : Nat.card (Coordinate 2 ⧸ reps rK147) = 1 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (147, 0) twin -/

def T147_0_2 : Fin 1 → Coordinate 2 := fun i => T147_0list.getD i.val (0,0,0,0,0)

theorem hfix147_0_2 : ∀ i, ((T147_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨0, by decide⟩ T147_0_2 (by decide)

theorem hinj147_0_2 : Function.Injective
    (fun i => ((T147_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_0_2 (by decide)

theorem hcardT147_0_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨0, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 0) twin (q=2).** -/
theorem cell147_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_0_2 i :=
  species_entry_eq_sum rK147 ⟨0, by decide⟩ e heK h T147_0_2 hfix147_0_2 hinj147_0_2 hcardT147_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK147) (T147_0_2 i) (hfix147_0_2 i) h)

/-! ### Cell (147, 1) twin -/

def T147_1_2 : Fin 1 → Coordinate 2 := fun i => T147_1list.getD i.val (0,0,0,0,0)

theorem hfix147_1_2 : ∀ i, ((T147_1_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨1, by decide⟩ T147_1_2 (by decide)

theorem hinj147_1_2 : Function.Injective
    (fun i => ((T147_1_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_1_2 (by decide)

theorem hcardT147_1_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨1, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 1) twin (q=2).** -/
theorem cell147_1_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨1, by decide⟩ : Fin 148))) :
    species (reps (⟨1, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_1_2 i :=
  species_entry_eq_sum rK147 ⟨1, by decide⟩ e heK h T147_1_2 hfix147_1_2 hinj147_1_2 hcardT147_1_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨1, by decide⟩) (reps rK147) (T147_1_2 i) (hfix147_1_2 i) h)

/-! ### Cell (147, 2) twin -/

def T147_2_2 : Fin 1 → Coordinate 2 := fun i => T147_2list.getD i.val (0,0,0,0,0)

theorem hfix147_2_2 : ∀ i, ((T147_2_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨2, by decide⟩ T147_2_2 (by decide)

theorem hinj147_2_2 : Function.Injective
    (fun i => ((T147_2_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_2_2 (by decide)

theorem hcardT147_2_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨2, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 2) twin (q=2).** -/
theorem cell147_2_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨2, by decide⟩ : Fin 148))) :
    species (reps (⟨2, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_2_2 i :=
  species_entry_eq_sum rK147 ⟨2, by decide⟩ e heK h T147_2_2 hfix147_2_2 hinj147_2_2 hcardT147_2_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨2, by decide⟩) (reps rK147) (T147_2_2 i) (hfix147_2_2 i) h)

/-! ### Cell (147, 3) twin -/

def T147_3_2 : Fin 1 → Coordinate 2 := fun i => T147_3list.getD i.val (0,0,0,0,0)

theorem hfix147_3_2 : ∀ i, ((T147_3_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨3, by decide⟩ T147_3_2 (by decide)

theorem hinj147_3_2 : Function.Injective
    (fun i => ((T147_3_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_3_2 (by decide)

theorem hcardT147_3_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨3, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 3) twin (q=2).** -/
theorem cell147_3_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨3, by decide⟩ : Fin 148))) :
    species (reps (⟨3, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_3_2 i :=
  species_entry_eq_sum rK147 ⟨3, by decide⟩ e heK h T147_3_2 hfix147_3_2 hinj147_3_2 hcardT147_3_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨3, by decide⟩) (reps rK147) (T147_3_2 i) (hfix147_3_2 i) h)

/-! ### Cell (147, 4) twin -/

def T147_4_2 : Fin 1 → Coordinate 2 := fun i => T147_4list.getD i.val (0,0,0,0,0)

theorem hfix147_4_2 : ∀ i, ((T147_4_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨4, by decide⟩ T147_4_2 (by decide)

theorem hinj147_4_2 : Function.Injective
    (fun i => ((T147_4_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_4_2 (by decide)

theorem hcardT147_4_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨4, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 4) twin (q=2).** -/
theorem cell147_4_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨4, by decide⟩ : Fin 148))) :
    species (reps (⟨4, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_4_2 i :=
  species_entry_eq_sum rK147 ⟨4, by decide⟩ e heK h T147_4_2 hfix147_4_2 hinj147_4_2 hcardT147_4_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨4, by decide⟩) (reps rK147) (T147_4_2 i) (hfix147_4_2 i) h)

/-! ### Cell (147, 5) twin -/

def T147_5_2 : Fin 1 → Coordinate 2 := fun i => T147_5list.getD i.val (0,0,0,0,0)

theorem hfix147_5_2 : ∀ i, ((T147_5_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨5, by decide⟩ T147_5_2 (by decide)

theorem hinj147_5_2 : Function.Injective
    (fun i => ((T147_5_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_5_2 (by decide)

theorem hcardT147_5_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨5, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 5) twin (q=2).** -/
theorem cell147_5_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨5, by decide⟩ : Fin 148))) :
    species (reps (⟨5, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_5_2 i :=
  species_entry_eq_sum rK147 ⟨5, by decide⟩ e heK h T147_5_2 hfix147_5_2 hinj147_5_2 hcardT147_5_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨5, by decide⟩) (reps rK147) (T147_5_2 i) (hfix147_5_2 i) h)

/-! ### Cell (147, 6) twin -/

def T147_6_2 : Fin 1 → Coordinate 2 := fun i => T147_6list.getD i.val (0,0,0,0,0)

theorem hfix147_6_2 : ∀ i, ((T147_6_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨6, by decide⟩ T147_6_2 (by decide)

theorem hinj147_6_2 : Function.Injective
    (fun i => ((T147_6_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_6_2 (by decide)

theorem hcardT147_6_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨6, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 6) twin (q=2).** -/
theorem cell147_6_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨6, by decide⟩ : Fin 148))) :
    species (reps (⟨6, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_6_2 i :=
  species_entry_eq_sum rK147 ⟨6, by decide⟩ e heK h T147_6_2 hfix147_6_2 hinj147_6_2 hcardT147_6_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨6, by decide⟩) (reps rK147) (T147_6_2 i) (hfix147_6_2 i) h)

/-! ### Cell (147, 7) twin -/

def T147_7_2 : Fin 1 → Coordinate 2 := fun i => T147_7list.getD i.val (0,0,0,0,0)

theorem hfix147_7_2 : ∀ i, ((T147_7_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨7, by decide⟩ T147_7_2 (by decide)

theorem hinj147_7_2 : Function.Injective
    (fun i => ((T147_7_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_7_2 (by decide)

theorem hcardT147_7_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨7, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 7) twin (q=2).** -/
theorem cell147_7_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨7, by decide⟩ : Fin 148))) :
    species (reps (⟨7, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_7_2 i :=
  species_entry_eq_sum rK147 ⟨7, by decide⟩ e heK h T147_7_2 hfix147_7_2 hinj147_7_2 hcardT147_7_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨7, by decide⟩) (reps rK147) (T147_7_2 i) (hfix147_7_2 i) h)

/-! ### Cell (147, 8) twin -/

def T147_8_2 : Fin 1 → Coordinate 2 := fun i => T147_8list.getD i.val (0,0,0,0,0)

theorem hfix147_8_2 : ∀ i, ((T147_8_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨8, by decide⟩ T147_8_2 (by decide)

theorem hinj147_8_2 : Function.Injective
    (fun i => ((T147_8_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_8_2 (by decide)

theorem hcardT147_8_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨8, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 8) twin (q=2).** -/
theorem cell147_8_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨8, by decide⟩ : Fin 148))) :
    species (reps (⟨8, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_8_2 i :=
  species_entry_eq_sum rK147 ⟨8, by decide⟩ e heK h T147_8_2 hfix147_8_2 hinj147_8_2 hcardT147_8_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨8, by decide⟩) (reps rK147) (T147_8_2 i) (hfix147_8_2 i) h)

/-! ### Cell (147, 9) twin -/

def T147_9_2 : Fin 1 → Coordinate 2 := fun i => T147_9list.getD i.val (0,0,0,0,0)

theorem hfix147_9_2 : ∀ i, ((T147_9_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨9, by decide⟩ T147_9_2 (by decide)

theorem hinj147_9_2 : Function.Injective
    (fun i => ((T147_9_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_9_2 (by decide)

theorem hcardT147_9_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨9, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 9) twin (q=2).** -/
theorem cell147_9_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨9, by decide⟩ : Fin 148))) :
    species (reps (⟨9, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_9_2 i :=
  species_entry_eq_sum rK147 ⟨9, by decide⟩ e heK h T147_9_2 hfix147_9_2 hinj147_9_2 hcardT147_9_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨9, by decide⟩) (reps rK147) (T147_9_2 i) (hfix147_9_2 i) h)

/-! ### Cell (147, 10) twin -/

def T147_10_2 : Fin 1 → Coordinate 2 := fun i => T147_10list.getD i.val (0,0,0,0,0)

theorem hfix147_10_2 : ∀ i, ((T147_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨10, by decide⟩ T147_10_2 (by decide)

theorem hinj147_10_2 : Function.Injective
    (fun i => ((T147_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_10_2 (by decide)

theorem hcardT147_10_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨10, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 10) twin (q=2).** -/
theorem cell147_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_10_2 i :=
  species_entry_eq_sum rK147 ⟨10, by decide⟩ e heK h T147_10_2 hfix147_10_2 hinj147_10_2 hcardT147_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK147) (T147_10_2 i) (hfix147_10_2 i) h)

/-! ### Cell (147, 11) twin -/

def T147_11_2 : Fin 1 → Coordinate 2 := fun i => T147_11list.getD i.val (0,0,0,0,0)

theorem hfix147_11_2 : ∀ i, ((T147_11_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨11, by decide⟩ T147_11_2 (by decide)

theorem hinj147_11_2 : Function.Injective
    (fun i => ((T147_11_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_11_2 (by decide)

theorem hcardT147_11_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨11, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 11) twin (q=2).** -/
theorem cell147_11_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨11, by decide⟩ : Fin 148))) :
    species (reps (⟨11, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_11_2 i :=
  species_entry_eq_sum rK147 ⟨11, by decide⟩ e heK h T147_11_2 hfix147_11_2 hinj147_11_2 hcardT147_11_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨11, by decide⟩) (reps rK147) (T147_11_2 i) (hfix147_11_2 i) h)

/-! ### Cell (147, 12) twin -/

def T147_12_2 : Fin 1 → Coordinate 2 := fun i => T147_12list.getD i.val (0,0,0,0,0)

theorem hfix147_12_2 : ∀ i, ((T147_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨12, by decide⟩ T147_12_2 (by decide)

theorem hinj147_12_2 : Function.Injective
    (fun i => ((T147_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_12_2 (by decide)

theorem hcardT147_12_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨12, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 12) twin (q=2).** -/
theorem cell147_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_12_2 i :=
  species_entry_eq_sum rK147 ⟨12, by decide⟩ e heK h T147_12_2 hfix147_12_2 hinj147_12_2 hcardT147_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK147) (T147_12_2 i) (hfix147_12_2 i) h)

/-! ### Cell (147, 13) twin -/

def T147_13_2 : Fin 1 → Coordinate 2 := fun i => T147_13list.getD i.val (0,0,0,0,0)

theorem hfix147_13_2 : ∀ i, ((T147_13_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨13, by decide⟩ T147_13_2 (by decide)

theorem hinj147_13_2 : Function.Injective
    (fun i => ((T147_13_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_13_2 (by decide)

theorem hcardT147_13_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨13, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 13) twin (q=2).** -/
theorem cell147_13_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨13, by decide⟩ : Fin 148))) :
    species (reps (⟨13, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_13_2 i :=
  species_entry_eq_sum rK147 ⟨13, by decide⟩ e heK h T147_13_2 hfix147_13_2 hinj147_13_2 hcardT147_13_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨13, by decide⟩) (reps rK147) (T147_13_2 i) (hfix147_13_2 i) h)

/-! ### Cell (147, 14) twin -/

def T147_14_2 : Fin 1 → Coordinate 2 := fun i => T147_14list.getD i.val (0,0,0,0,0)

theorem hfix147_14_2 : ∀ i, ((T147_14_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨14, by decide⟩ T147_14_2 (by decide)

theorem hinj147_14_2 : Function.Injective
    (fun i => ((T147_14_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_14_2 (by decide)

theorem hcardT147_14_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨14, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 14) twin (q=2).** -/
theorem cell147_14_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨14, by decide⟩ : Fin 148))) :
    species (reps (⟨14, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_14_2 i :=
  species_entry_eq_sum rK147 ⟨14, by decide⟩ e heK h T147_14_2 hfix147_14_2 hinj147_14_2 hcardT147_14_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨14, by decide⟩) (reps rK147) (T147_14_2 i) (hfix147_14_2 i) h)

/-! ### Cell (147, 15) twin -/

def T147_15_2 : Fin 1 → Coordinate 2 := fun i => T147_15list.getD i.val (0,0,0,0,0)

theorem hfix147_15_2 : ∀ i, ((T147_15_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨15, by decide⟩ T147_15_2 (by decide)

theorem hinj147_15_2 : Function.Injective
    (fun i => ((T147_15_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_15_2 (by decide)

theorem hcardT147_15_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨15, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 15) twin (q=2).** -/
theorem cell147_15_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨15, by decide⟩ : Fin 148))) :
    species (reps (⟨15, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_15_2 i :=
  species_entry_eq_sum rK147 ⟨15, by decide⟩ e heK h T147_15_2 hfix147_15_2 hinj147_15_2 hcardT147_15_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨15, by decide⟩) (reps rK147) (T147_15_2 i) (hfix147_15_2 i) h)

/-! ### Cell (147, 16) twin -/

def T147_16_2 : Fin 1 → Coordinate 2 := fun i => T147_16list.getD i.val (0,0,0,0,0)

theorem hfix147_16_2 : ∀ i, ((T147_16_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨16, by decide⟩ T147_16_2 (by decide)

theorem hinj147_16_2 : Function.Injective
    (fun i => ((T147_16_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_16_2 (by decide)

theorem hcardT147_16_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨16, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 16) twin (q=2).** -/
theorem cell147_16_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨16, by decide⟩ : Fin 148))) :
    species (reps (⟨16, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_16_2 i :=
  species_entry_eq_sum rK147 ⟨16, by decide⟩ e heK h T147_16_2 hfix147_16_2 hinj147_16_2 hcardT147_16_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨16, by decide⟩) (reps rK147) (T147_16_2 i) (hfix147_16_2 i) h)

/-! ### Cell (147, 17) twin -/

def T147_17_2 : Fin 1 → Coordinate 2 := fun i => T147_17list.getD i.val (0,0,0,0,0)

theorem hfix147_17_2 : ∀ i, ((T147_17_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨17, by decide⟩ T147_17_2 (by decide)

theorem hinj147_17_2 : Function.Injective
    (fun i => ((T147_17_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_17_2 (by decide)

theorem hcardT147_17_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨17, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 17) twin (q=2).** -/
theorem cell147_17_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨17, by decide⟩ : Fin 148))) :
    species (reps (⟨17, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_17_2 i :=
  species_entry_eq_sum rK147 ⟨17, by decide⟩ e heK h T147_17_2 hfix147_17_2 hinj147_17_2 hcardT147_17_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨17, by decide⟩) (reps rK147) (T147_17_2 i) (hfix147_17_2 i) h)

/-! ### Cell (147, 18) twin -/

def T147_18_2 : Fin 1 → Coordinate 2 := fun i => T147_18list.getD i.val (0,0,0,0,0)

theorem hfix147_18_2 : ∀ i, ((T147_18_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨18, by decide⟩ T147_18_2 (by decide)

theorem hinj147_18_2 : Function.Injective
    (fun i => ((T147_18_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_18_2 (by decide)

theorem hcardT147_18_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨18, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 18) twin (q=2).** -/
theorem cell147_18_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨18, by decide⟩ : Fin 148))) :
    species (reps (⟨18, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_18_2 i :=
  species_entry_eq_sum rK147 ⟨18, by decide⟩ e heK h T147_18_2 hfix147_18_2 hinj147_18_2 hcardT147_18_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨18, by decide⟩) (reps rK147) (T147_18_2 i) (hfix147_18_2 i) h)

/-! ### Cell (147, 19) twin -/

def T147_19_2 : Fin 1 → Coordinate 2 := fun i => T147_19list.getD i.val (0,0,0,0,0)

theorem hfix147_19_2 : ∀ i, ((T147_19_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨19, by decide⟩ T147_19_2 (by decide)

theorem hinj147_19_2 : Function.Injective
    (fun i => ((T147_19_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_19_2 (by decide)

theorem hcardT147_19_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨19, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 19) twin (q=2).** -/
theorem cell147_19_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨19, by decide⟩ : Fin 148))) :
    species (reps (⟨19, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_19_2 i :=
  species_entry_eq_sum rK147 ⟨19, by decide⟩ e heK h T147_19_2 hfix147_19_2 hinj147_19_2 hcardT147_19_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨19, by decide⟩) (reps rK147) (T147_19_2 i) (hfix147_19_2 i) h)

/-! ### Cell (147, 20) twin -/

def T147_20_2 : Fin 1 → Coordinate 2 := fun i => T147_20list.getD i.val (0,0,0,0,0)

theorem hfix147_20_2 : ∀ i, ((T147_20_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨20, by decide⟩ T147_20_2 (by decide)

theorem hinj147_20_2 : Function.Injective
    (fun i => ((T147_20_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_20_2 (by decide)

theorem hcardT147_20_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨20, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 20) twin (q=2).** -/
theorem cell147_20_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨20, by decide⟩ : Fin 148))) :
    species (reps (⟨20, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_20_2 i :=
  species_entry_eq_sum rK147 ⟨20, by decide⟩ e heK h T147_20_2 hfix147_20_2 hinj147_20_2 hcardT147_20_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨20, by decide⟩) (reps rK147) (T147_20_2 i) (hfix147_20_2 i) h)

/-! ### Cell (147, 21) twin -/

def T147_21_2 : Fin 1 → Coordinate 2 := fun i => T147_21list.getD i.val (0,0,0,0,0)

theorem hfix147_21_2 : ∀ i, ((T147_21_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨21, by decide⟩ T147_21_2 (by decide)

theorem hinj147_21_2 : Function.Injective
    (fun i => ((T147_21_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_21_2 (by decide)

theorem hcardT147_21_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨21, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 21) twin (q=2).** -/
theorem cell147_21_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨21, by decide⟩ : Fin 148))) :
    species (reps (⟨21, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_21_2 i :=
  species_entry_eq_sum rK147 ⟨21, by decide⟩ e heK h T147_21_2 hfix147_21_2 hinj147_21_2 hcardT147_21_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨21, by decide⟩) (reps rK147) (T147_21_2 i) (hfix147_21_2 i) h)

/-! ### Cell (147, 22) twin -/

def T147_22_2 : Fin 1 → Coordinate 2 := fun i => T147_22list.getD i.val (0,0,0,0,0)

theorem hfix147_22_2 : ∀ i, ((T147_22_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨22, by decide⟩ T147_22_2 (by decide)

theorem hinj147_22_2 : Function.Injective
    (fun i => ((T147_22_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_22_2 (by decide)

theorem hcardT147_22_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨22, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 22) twin (q=2).** -/
theorem cell147_22_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨22, by decide⟩ : Fin 148))) :
    species (reps (⟨22, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_22_2 i :=
  species_entry_eq_sum rK147 ⟨22, by decide⟩ e heK h T147_22_2 hfix147_22_2 hinj147_22_2 hcardT147_22_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨22, by decide⟩) (reps rK147) (T147_22_2 i) (hfix147_22_2 i) h)

/-! ### Cell (147, 23) twin -/

def T147_23_2 : Fin 1 → Coordinate 2 := fun i => T147_23list.getD i.val (0,0,0,0,0)

theorem hfix147_23_2 : ∀ i, ((T147_23_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨23, by decide⟩ T147_23_2 (by decide)

theorem hinj147_23_2 : Function.Injective
    (fun i => ((T147_23_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_23_2 (by decide)

theorem hcardT147_23_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨23, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 23) twin (q=2).** -/
theorem cell147_23_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨23, by decide⟩ : Fin 148))) :
    species (reps (⟨23, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_23_2 i :=
  species_entry_eq_sum rK147 ⟨23, by decide⟩ e heK h T147_23_2 hfix147_23_2 hinj147_23_2 hcardT147_23_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨23, by decide⟩) (reps rK147) (T147_23_2 i) (hfix147_23_2 i) h)

/-! ### Cell (147, 24) twin -/

def T147_24_2 : Fin 1 → Coordinate 2 := fun i => T147_24list.getD i.val (0,0,0,0,0)

theorem hfix147_24_2 : ∀ i, ((T147_24_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨24, by decide⟩ T147_24_2 (by decide)

theorem hinj147_24_2 : Function.Injective
    (fun i => ((T147_24_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_24_2 (by decide)

theorem hcardT147_24_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨24, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 24) twin (q=2).** -/
theorem cell147_24_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨24, by decide⟩ : Fin 148))) :
    species (reps (⟨24, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_24_2 i :=
  species_entry_eq_sum rK147 ⟨24, by decide⟩ e heK h T147_24_2 hfix147_24_2 hinj147_24_2 hcardT147_24_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨24, by decide⟩) (reps rK147) (T147_24_2 i) (hfix147_24_2 i) h)

/-! ### Cell (147, 25) twin -/

def T147_25_2 : Fin 1 → Coordinate 2 := fun i => T147_25list.getD i.val (0,0,0,0,0)

theorem hfix147_25_2 : ∀ i, ((T147_25_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨25, by decide⟩ T147_25_2 (by decide)

theorem hinj147_25_2 : Function.Injective
    (fun i => ((T147_25_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_25_2 (by decide)

theorem hcardT147_25_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨25, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 25) twin (q=2).** -/
theorem cell147_25_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨25, by decide⟩ : Fin 148))) :
    species (reps (⟨25, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_25_2 i :=
  species_entry_eq_sum rK147 ⟨25, by decide⟩ e heK h T147_25_2 hfix147_25_2 hinj147_25_2 hcardT147_25_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨25, by decide⟩) (reps rK147) (T147_25_2 i) (hfix147_25_2 i) h)

/-! ### Cell (147, 26) twin -/

def T147_26_2 : Fin 1 → Coordinate 2 := fun i => T147_26list.getD i.val (0,0,0,0,0)

theorem hfix147_26_2 : ∀ i, ((T147_26_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨26, by decide⟩ T147_26_2 (by decide)

theorem hinj147_26_2 : Function.Injective
    (fun i => ((T147_26_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_26_2 (by decide)

theorem hcardT147_26_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨26, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 26) twin (q=2).** -/
theorem cell147_26_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨26, by decide⟩ : Fin 148))) :
    species (reps (⟨26, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_26_2 i :=
  species_entry_eq_sum rK147 ⟨26, by decide⟩ e heK h T147_26_2 hfix147_26_2 hinj147_26_2 hcardT147_26_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨26, by decide⟩) (reps rK147) (T147_26_2 i) (hfix147_26_2 i) h)

/-! ### Cell (147, 27) twin -/

def T147_27_2 : Fin 1 → Coordinate 2 := fun i => T147_27list.getD i.val (0,0,0,0,0)

theorem hfix147_27_2 : ∀ i, ((T147_27_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨27, by decide⟩ T147_27_2 (by decide)

theorem hinj147_27_2 : Function.Injective
    (fun i => ((T147_27_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_27_2 (by decide)

theorem hcardT147_27_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨27, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 27) twin (q=2).** -/
theorem cell147_27_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨27, by decide⟩ : Fin 148))) :
    species (reps (⟨27, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_27_2 i :=
  species_entry_eq_sum rK147 ⟨27, by decide⟩ e heK h T147_27_2 hfix147_27_2 hinj147_27_2 hcardT147_27_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨27, by decide⟩) (reps rK147) (T147_27_2 i) (hfix147_27_2 i) h)

/-! ### Cell (147, 28) twin -/

def T147_28_2 : Fin 1 → Coordinate 2 := fun i => T147_28list.getD i.val (0,0,0,0,0)

theorem hfix147_28_2 : ∀ i, ((T147_28_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨28, by decide⟩ T147_28_2 (by decide)

theorem hinj147_28_2 : Function.Injective
    (fun i => ((T147_28_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_28_2 (by decide)

theorem hcardT147_28_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨28, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 28) twin (q=2).** -/
theorem cell147_28_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨28, by decide⟩ : Fin 148))) :
    species (reps (⟨28, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_28_2 i :=
  species_entry_eq_sum rK147 ⟨28, by decide⟩ e heK h T147_28_2 hfix147_28_2 hinj147_28_2 hcardT147_28_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨28, by decide⟩) (reps rK147) (T147_28_2 i) (hfix147_28_2 i) h)

/-! ### Cell (147, 29) twin -/

def T147_29_2 : Fin 1 → Coordinate 2 := fun i => T147_29list.getD i.val (0,0,0,0,0)

theorem hfix147_29_2 : ∀ i, ((T147_29_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨29, by decide⟩ T147_29_2 (by decide)

theorem hinj147_29_2 : Function.Injective
    (fun i => ((T147_29_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_29_2 (by decide)

theorem hcardT147_29_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨29, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 29) twin (q=2).** -/
theorem cell147_29_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨29, by decide⟩ : Fin 148))) :
    species (reps (⟨29, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_29_2 i :=
  species_entry_eq_sum rK147 ⟨29, by decide⟩ e heK h T147_29_2 hfix147_29_2 hinj147_29_2 hcardT147_29_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨29, by decide⟩) (reps rK147) (T147_29_2 i) (hfix147_29_2 i) h)

/-! ### Cell (147, 30) twin -/

def T147_30_2 : Fin 1 → Coordinate 2 := fun i => T147_30list.getD i.val (0,0,0,0,0)

theorem hfix147_30_2 : ∀ i, ((T147_30_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨30, by decide⟩ T147_30_2 (by decide)

theorem hinj147_30_2 : Function.Injective
    (fun i => ((T147_30_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_30_2 (by decide)

theorem hcardT147_30_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨30, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 30) twin (q=2).** -/
theorem cell147_30_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨30, by decide⟩ : Fin 148))) :
    species (reps (⟨30, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_30_2 i :=
  species_entry_eq_sum rK147 ⟨30, by decide⟩ e heK h T147_30_2 hfix147_30_2 hinj147_30_2 hcardT147_30_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨30, by decide⟩) (reps rK147) (T147_30_2 i) (hfix147_30_2 i) h)

/-! ### Cell (147, 31) twin -/

def T147_31_2 : Fin 1 → Coordinate 2 := fun i => T147_31list.getD i.val (0,0,0,0,0)

theorem hfix147_31_2 : ∀ i, ((T147_31_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨31, by decide⟩ T147_31_2 (by decide)

theorem hinj147_31_2 : Function.Injective
    (fun i => ((T147_31_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_31_2 (by decide)

theorem hcardT147_31_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨31, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 31) twin (q=2).** -/
theorem cell147_31_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨31, by decide⟩ : Fin 148))) :
    species (reps (⟨31, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_31_2 i :=
  species_entry_eq_sum rK147 ⟨31, by decide⟩ e heK h T147_31_2 hfix147_31_2 hinj147_31_2 hcardT147_31_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨31, by decide⟩) (reps rK147) (T147_31_2 i) (hfix147_31_2 i) h)

/-! ### Cell (147, 32) twin -/

def T147_32_2 : Fin 1 → Coordinate 2 := fun i => T147_32list.getD i.val (0,0,0,0,0)

theorem hfix147_32_2 : ∀ i, ((T147_32_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨32, by decide⟩ T147_32_2 (by decide)

theorem hinj147_32_2 : Function.Injective
    (fun i => ((T147_32_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_32_2 (by decide)

theorem hcardT147_32_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨32, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 32) twin (q=2).** -/
theorem cell147_32_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨32, by decide⟩ : Fin 148))) :
    species (reps (⟨32, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_32_2 i :=
  species_entry_eq_sum rK147 ⟨32, by decide⟩ e heK h T147_32_2 hfix147_32_2 hinj147_32_2 hcardT147_32_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨32, by decide⟩) (reps rK147) (T147_32_2 i) (hfix147_32_2 i) h)

/-! ### Cell (147, 33) twin -/

def T147_33_2 : Fin 1 → Coordinate 2 := fun i => T147_33list.getD i.val (0,0,0,0,0)

theorem hfix147_33_2 : ∀ i, ((T147_33_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨33, by decide⟩ T147_33_2 (by decide)

theorem hinj147_33_2 : Function.Injective
    (fun i => ((T147_33_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_33_2 (by decide)

theorem hcardT147_33_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨33, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 33) twin (q=2).** -/
theorem cell147_33_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨33, by decide⟩ : Fin 148))) :
    species (reps (⟨33, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_33_2 i :=
  species_entry_eq_sum rK147 ⟨33, by decide⟩ e heK h T147_33_2 hfix147_33_2 hinj147_33_2 hcardT147_33_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨33, by decide⟩) (reps rK147) (T147_33_2 i) (hfix147_33_2 i) h)

/-! ### Cell (147, 34) twin -/

def T147_34_2 : Fin 1 → Coordinate 2 := fun i => T147_34list.getD i.val (0,0,0,0,0)

theorem hfix147_34_2 : ∀ i, ((T147_34_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨34, by decide⟩ T147_34_2 (by decide)

theorem hinj147_34_2 : Function.Injective
    (fun i => ((T147_34_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_34_2 (by decide)

theorem hcardT147_34_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨34, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 34) twin (q=2).** -/
theorem cell147_34_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨34, by decide⟩ : Fin 148))) :
    species (reps (⟨34, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_34_2 i :=
  species_entry_eq_sum rK147 ⟨34, by decide⟩ e heK h T147_34_2 hfix147_34_2 hinj147_34_2 hcardT147_34_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨34, by decide⟩) (reps rK147) (T147_34_2 i) (hfix147_34_2 i) h)

/-! ### Cell (147, 35) twin -/

def T147_35_2 : Fin 1 → Coordinate 2 := fun i => T147_35list.getD i.val (0,0,0,0,0)

theorem hfix147_35_2 : ∀ i, ((T147_35_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨35, by decide⟩ T147_35_2 (by decide)

theorem hinj147_35_2 : Function.Injective
    (fun i => ((T147_35_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_35_2 (by decide)

theorem hcardT147_35_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨35, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 35) twin (q=2).** -/
theorem cell147_35_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨35, by decide⟩ : Fin 148))) :
    species (reps (⟨35, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_35_2 i :=
  species_entry_eq_sum rK147 ⟨35, by decide⟩ e heK h T147_35_2 hfix147_35_2 hinj147_35_2 hcardT147_35_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨35, by decide⟩) (reps rK147) (T147_35_2 i) (hfix147_35_2 i) h)

/-! ### Cell (147, 36) twin -/

def T147_36_2 : Fin 1 → Coordinate 2 := fun i => T147_36list.getD i.val (0,0,0,0,0)

theorem hfix147_36_2 : ∀ i, ((T147_36_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨36, by decide⟩ T147_36_2 (by decide)

theorem hinj147_36_2 : Function.Injective
    (fun i => ((T147_36_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_36_2 (by decide)

theorem hcardT147_36_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨36, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 36) twin (q=2).** -/
theorem cell147_36_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨36, by decide⟩ : Fin 148))) :
    species (reps (⟨36, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_36_2 i :=
  species_entry_eq_sum rK147 ⟨36, by decide⟩ e heK h T147_36_2 hfix147_36_2 hinj147_36_2 hcardT147_36_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨36, by decide⟩) (reps rK147) (T147_36_2 i) (hfix147_36_2 i) h)

/-! ### Cell (147, 37) twin -/

def T147_37_2 : Fin 1 → Coordinate 2 := fun i => T147_37list.getD i.val (0,0,0,0,0)

theorem hfix147_37_2 : ∀ i, ((T147_37_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨37, by decide⟩ T147_37_2 (by decide)

theorem hinj147_37_2 : Function.Injective
    (fun i => ((T147_37_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_37_2 (by decide)

theorem hcardT147_37_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨37, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 37) twin (q=2).** -/
theorem cell147_37_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨37, by decide⟩ : Fin 148))) :
    species (reps (⟨37, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_37_2 i :=
  species_entry_eq_sum rK147 ⟨37, by decide⟩ e heK h T147_37_2 hfix147_37_2 hinj147_37_2 hcardT147_37_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨37, by decide⟩) (reps rK147) (T147_37_2 i) (hfix147_37_2 i) h)

/-! ### Cell (147, 38) twin -/

def T147_38_2 : Fin 1 → Coordinate 2 := fun i => T147_38list.getD i.val (0,0,0,0,0)

theorem hfix147_38_2 : ∀ i, ((T147_38_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨38, by decide⟩ T147_38_2 (by decide)

theorem hinj147_38_2 : Function.Injective
    (fun i => ((T147_38_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_38_2 (by decide)

theorem hcardT147_38_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨38, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 38) twin (q=2).** -/
theorem cell147_38_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨38, by decide⟩ : Fin 148))) :
    species (reps (⟨38, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_38_2 i :=
  species_entry_eq_sum rK147 ⟨38, by decide⟩ e heK h T147_38_2 hfix147_38_2 hinj147_38_2 hcardT147_38_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨38, by decide⟩) (reps rK147) (T147_38_2 i) (hfix147_38_2 i) h)

/-! ### Cell (147, 39) twin -/

def T147_39_2 : Fin 1 → Coordinate 2 := fun i => T147_39list.getD i.val (0,0,0,0,0)

theorem hfix147_39_2 : ∀ i, ((T147_39_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨39, by decide⟩ T147_39_2 (by decide)

theorem hinj147_39_2 : Function.Injective
    (fun i => ((T147_39_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_39_2 (by decide)

theorem hcardT147_39_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨39, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 39) twin (q=2).** -/
theorem cell147_39_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨39, by decide⟩ : Fin 148))) :
    species (reps (⟨39, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_39_2 i :=
  species_entry_eq_sum rK147 ⟨39, by decide⟩ e heK h T147_39_2 hfix147_39_2 hinj147_39_2 hcardT147_39_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨39, by decide⟩) (reps rK147) (T147_39_2 i) (hfix147_39_2 i) h)

/-! ### Cell (147, 40) twin -/

def T147_40_2 : Fin 1 → Coordinate 2 := fun i => T147_40list.getD i.val (0,0,0,0,0)

theorem hfix147_40_2 : ∀ i, ((T147_40_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨40, by decide⟩ T147_40_2 (by decide)

theorem hinj147_40_2 : Function.Injective
    (fun i => ((T147_40_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_40_2 (by decide)

theorem hcardT147_40_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨40, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 40) twin (q=2).** -/
theorem cell147_40_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨40, by decide⟩ : Fin 148))) :
    species (reps (⟨40, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_40_2 i :=
  species_entry_eq_sum rK147 ⟨40, by decide⟩ e heK h T147_40_2 hfix147_40_2 hinj147_40_2 hcardT147_40_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨40, by decide⟩) (reps rK147) (T147_40_2 i) (hfix147_40_2 i) h)

/-! ### Cell (147, 41) twin -/

def T147_41_2 : Fin 1 → Coordinate 2 := fun i => T147_41list.getD i.val (0,0,0,0,0)

theorem hfix147_41_2 : ∀ i, ((T147_41_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨41, by decide⟩ T147_41_2 (by decide)

theorem hinj147_41_2 : Function.Injective
    (fun i => ((T147_41_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_41_2 (by decide)

theorem hcardT147_41_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨41, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 41) twin (q=2).** -/
theorem cell147_41_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨41, by decide⟩ : Fin 148))) :
    species (reps (⟨41, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_41_2 i :=
  species_entry_eq_sum rK147 ⟨41, by decide⟩ e heK h T147_41_2 hfix147_41_2 hinj147_41_2 hcardT147_41_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨41, by decide⟩) (reps rK147) (T147_41_2 i) (hfix147_41_2 i) h)

/-! ### Cell (147, 42) twin -/

def T147_42_2 : Fin 1 → Coordinate 2 := fun i => T147_42list.getD i.val (0,0,0,0,0)

theorem hfix147_42_2 : ∀ i, ((T147_42_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨42, by decide⟩ T147_42_2 (by decide)

theorem hinj147_42_2 : Function.Injective
    (fun i => ((T147_42_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_42_2 (by decide)

theorem hcardT147_42_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨42, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 42) twin (q=2).** -/
theorem cell147_42_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨42, by decide⟩ : Fin 148))) :
    species (reps (⟨42, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_42_2 i :=
  species_entry_eq_sum rK147 ⟨42, by decide⟩ e heK h T147_42_2 hfix147_42_2 hinj147_42_2 hcardT147_42_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨42, by decide⟩) (reps rK147) (T147_42_2 i) (hfix147_42_2 i) h)

/-! ### Cell (147, 43) twin -/

def T147_43_2 : Fin 1 → Coordinate 2 := fun i => T147_43list.getD i.val (0,0,0,0,0)

theorem hfix147_43_2 : ∀ i, ((T147_43_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨43, by decide⟩ T147_43_2 (by decide)

theorem hinj147_43_2 : Function.Injective
    (fun i => ((T147_43_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_43_2 (by decide)

theorem hcardT147_43_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨43, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 43) twin (q=2).** -/
theorem cell147_43_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨43, by decide⟩ : Fin 148))) :
    species (reps (⟨43, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_43_2 i :=
  species_entry_eq_sum rK147 ⟨43, by decide⟩ e heK h T147_43_2 hfix147_43_2 hinj147_43_2 hcardT147_43_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨43, by decide⟩) (reps rK147) (T147_43_2 i) (hfix147_43_2 i) h)

/-! ### Cell (147, 44) twin -/

def T147_44_2 : Fin 1 → Coordinate 2 := fun i => T147_44list.getD i.val (0,0,0,0,0)

theorem hfix147_44_2 : ∀ i, ((T147_44_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨44, by decide⟩ T147_44_2 (by decide)

theorem hinj147_44_2 : Function.Injective
    (fun i => ((T147_44_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_44_2 (by decide)

theorem hcardT147_44_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨44, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 44) twin (q=2).** -/
theorem cell147_44_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨44, by decide⟩ : Fin 148))) :
    species (reps (⟨44, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_44_2 i :=
  species_entry_eq_sum rK147 ⟨44, by decide⟩ e heK h T147_44_2 hfix147_44_2 hinj147_44_2 hcardT147_44_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨44, by decide⟩) (reps rK147) (T147_44_2 i) (hfix147_44_2 i) h)

/-! ### Cell (147, 45) twin -/

def T147_45_2 : Fin 1 → Coordinate 2 := fun i => T147_45list.getD i.val (0,0,0,0,0)

theorem hfix147_45_2 : ∀ i, ((T147_45_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨45, by decide⟩ T147_45_2 (by decide)

theorem hinj147_45_2 : Function.Injective
    (fun i => ((T147_45_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_45_2 (by decide)

theorem hcardT147_45_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨45, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 45) twin (q=2).** -/
theorem cell147_45_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨45, by decide⟩ : Fin 148))) :
    species (reps (⟨45, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_45_2 i :=
  species_entry_eq_sum rK147 ⟨45, by decide⟩ e heK h T147_45_2 hfix147_45_2 hinj147_45_2 hcardT147_45_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨45, by decide⟩) (reps rK147) (T147_45_2 i) (hfix147_45_2 i) h)

/-! ### Cell (147, 46) twin -/

def T147_46_2 : Fin 1 → Coordinate 2 := fun i => T147_46list.getD i.val (0,0,0,0,0)

theorem hfix147_46_2 : ∀ i, ((T147_46_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨46, by decide⟩ T147_46_2 (by decide)

theorem hinj147_46_2 : Function.Injective
    (fun i => ((T147_46_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_46_2 (by decide)

theorem hcardT147_46_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨46, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 46) twin (q=2).** -/
theorem cell147_46_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨46, by decide⟩ : Fin 148))) :
    species (reps (⟨46, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_46_2 i :=
  species_entry_eq_sum rK147 ⟨46, by decide⟩ e heK h T147_46_2 hfix147_46_2 hinj147_46_2 hcardT147_46_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨46, by decide⟩) (reps rK147) (T147_46_2 i) (hfix147_46_2 i) h)

/-! ### Cell (147, 47) twin -/

def T147_47_2 : Fin 1 → Coordinate 2 := fun i => T147_47list.getD i.val (0,0,0,0,0)

theorem hfix147_47_2 : ∀ i, ((T147_47_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨47, by decide⟩ T147_47_2 (by decide)

theorem hinj147_47_2 : Function.Injective
    (fun i => ((T147_47_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_47_2 (by decide)

theorem hcardT147_47_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨47, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 47) twin (q=2).** -/
theorem cell147_47_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨47, by decide⟩ : Fin 148))) :
    species (reps (⟨47, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_47_2 i :=
  species_entry_eq_sum rK147 ⟨47, by decide⟩ e heK h T147_47_2 hfix147_47_2 hinj147_47_2 hcardT147_47_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨47, by decide⟩) (reps rK147) (T147_47_2 i) (hfix147_47_2 i) h)

/-! ### Cell (147, 48) twin -/

def T147_48_2 : Fin 1 → Coordinate 2 := fun i => T147_48list.getD i.val (0,0,0,0,0)

theorem hfix147_48_2 : ∀ i, ((T147_48_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨48, by decide⟩ T147_48_2 (by decide)

theorem hinj147_48_2 : Function.Injective
    (fun i => ((T147_48_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_48_2 (by decide)

theorem hcardT147_48_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨48, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 48) twin (q=2).** -/
theorem cell147_48_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨48, by decide⟩ : Fin 148))) :
    species (reps (⟨48, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_48_2 i :=
  species_entry_eq_sum rK147 ⟨48, by decide⟩ e heK h T147_48_2 hfix147_48_2 hinj147_48_2 hcardT147_48_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨48, by decide⟩) (reps rK147) (T147_48_2 i) (hfix147_48_2 i) h)

/-! ### Cell (147, 49) twin -/

def T147_49_2 : Fin 1 → Coordinate 2 := fun i => T147_49list.getD i.val (0,0,0,0,0)

theorem hfix147_49_2 : ∀ i, ((T147_49_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨49, by decide⟩ T147_49_2 (by decide)

theorem hinj147_49_2 : Function.Injective
    (fun i => ((T147_49_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_49_2 (by decide)

theorem hcardT147_49_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨49, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 49) twin (q=2).** -/
theorem cell147_49_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨49, by decide⟩ : Fin 148))) :
    species (reps (⟨49, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_49_2 i :=
  species_entry_eq_sum rK147 ⟨49, by decide⟩ e heK h T147_49_2 hfix147_49_2 hinj147_49_2 hcardT147_49_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨49, by decide⟩) (reps rK147) (T147_49_2 i) (hfix147_49_2 i) h)

/-! ### Cell (147, 50) twin -/

def T147_50_2 : Fin 1 → Coordinate 2 := fun i => T147_50list.getD i.val (0,0,0,0,0)

theorem hfix147_50_2 : ∀ i, ((T147_50_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨50, by decide⟩ T147_50_2 (by decide)

theorem hinj147_50_2 : Function.Injective
    (fun i => ((T147_50_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_50_2 (by decide)

theorem hcardT147_50_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨50, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 50) twin (q=2).** -/
theorem cell147_50_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨50, by decide⟩ : Fin 148))) :
    species (reps (⟨50, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_50_2 i :=
  species_entry_eq_sum rK147 ⟨50, by decide⟩ e heK h T147_50_2 hfix147_50_2 hinj147_50_2 hcardT147_50_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨50, by decide⟩) (reps rK147) (T147_50_2 i) (hfix147_50_2 i) h)

/-! ### Cell (147, 51) twin -/

def T147_51_2 : Fin 1 → Coordinate 2 := fun i => T147_51list.getD i.val (0,0,0,0,0)

theorem hfix147_51_2 : ∀ i, ((T147_51_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨51, by decide⟩ T147_51_2 (by decide)

theorem hinj147_51_2 : Function.Injective
    (fun i => ((T147_51_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_51_2 (by decide)

theorem hcardT147_51_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨51, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 51) twin (q=2).** -/
theorem cell147_51_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨51, by decide⟩ : Fin 148))) :
    species (reps (⟨51, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_51_2 i :=
  species_entry_eq_sum rK147 ⟨51, by decide⟩ e heK h T147_51_2 hfix147_51_2 hinj147_51_2 hcardT147_51_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨51, by decide⟩) (reps rK147) (T147_51_2 i) (hfix147_51_2 i) h)

/-! ### Cell (147, 52) twin -/

def T147_52_2 : Fin 1 → Coordinate 2 := fun i => T147_52list.getD i.val (0,0,0,0,0)

theorem hfix147_52_2 : ∀ i, ((T147_52_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨52, by decide⟩ T147_52_2 (by decide)

theorem hinj147_52_2 : Function.Injective
    (fun i => ((T147_52_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_52_2 (by decide)

theorem hcardT147_52_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨52, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 52) twin (q=2).** -/
theorem cell147_52_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨52, by decide⟩ : Fin 148))) :
    species (reps (⟨52, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_52_2 i :=
  species_entry_eq_sum rK147 ⟨52, by decide⟩ e heK h T147_52_2 hfix147_52_2 hinj147_52_2 hcardT147_52_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨52, by decide⟩) (reps rK147) (T147_52_2 i) (hfix147_52_2 i) h)

/-! ### Cell (147, 53) twin -/

def T147_53_2 : Fin 1 → Coordinate 2 := fun i => T147_53list.getD i.val (0,0,0,0,0)

theorem hfix147_53_2 : ∀ i, ((T147_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨53, by decide⟩ T147_53_2 (by decide)

theorem hinj147_53_2 : Function.Injective
    (fun i => ((T147_53_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_53_2 (by decide)

theorem hcardT147_53_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨53, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 53) twin (q=2).** -/
theorem cell147_53_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨53, by decide⟩ : Fin 148))) :
    species (reps (⟨53, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_53_2 i :=
  species_entry_eq_sum rK147 ⟨53, by decide⟩ e heK h T147_53_2 hfix147_53_2 hinj147_53_2 hcardT147_53_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨53, by decide⟩) (reps rK147) (T147_53_2 i) (hfix147_53_2 i) h)

/-! ### Cell (147, 54) twin -/

def T147_54_2 : Fin 1 → Coordinate 2 := fun i => T147_54list.getD i.val (0,0,0,0,0)

theorem hfix147_54_2 : ∀ i, ((T147_54_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨54, by decide⟩ T147_54_2 (by decide)

theorem hinj147_54_2 : Function.Injective
    (fun i => ((T147_54_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_54_2 (by decide)

theorem hcardT147_54_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨54, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 54) twin (q=2).** -/
theorem cell147_54_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨54, by decide⟩ : Fin 148))) :
    species (reps (⟨54, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_54_2 i :=
  species_entry_eq_sum rK147 ⟨54, by decide⟩ e heK h T147_54_2 hfix147_54_2 hinj147_54_2 hcardT147_54_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨54, by decide⟩) (reps rK147) (T147_54_2 i) (hfix147_54_2 i) h)

/-! ### Cell (147, 55) twin -/

def T147_55_2 : Fin 1 → Coordinate 2 := fun i => T147_55list.getD i.val (0,0,0,0,0)

theorem hfix147_55_2 : ∀ i, ((T147_55_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨55, by decide⟩ T147_55_2 (by decide)

theorem hinj147_55_2 : Function.Injective
    (fun i => ((T147_55_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_55_2 (by decide)

theorem hcardT147_55_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨55, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 55) twin (q=2).** -/
theorem cell147_55_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨55, by decide⟩ : Fin 148))) :
    species (reps (⟨55, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_55_2 i :=
  species_entry_eq_sum rK147 ⟨55, by decide⟩ e heK h T147_55_2 hfix147_55_2 hinj147_55_2 hcardT147_55_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨55, by decide⟩) (reps rK147) (T147_55_2 i) (hfix147_55_2 i) h)

/-! ### Cell (147, 56) twin -/

def T147_56_2 : Fin 1 → Coordinate 2 := fun i => T147_56list.getD i.val (0,0,0,0,0)

theorem hfix147_56_2 : ∀ i, ((T147_56_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨56, by decide⟩ T147_56_2 (by decide)

theorem hinj147_56_2 : Function.Injective
    (fun i => ((T147_56_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_56_2 (by decide)

theorem hcardT147_56_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨56, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 56) twin (q=2).** -/
theorem cell147_56_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨56, by decide⟩ : Fin 148))) :
    species (reps (⟨56, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_56_2 i :=
  species_entry_eq_sum rK147 ⟨56, by decide⟩ e heK h T147_56_2 hfix147_56_2 hinj147_56_2 hcardT147_56_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨56, by decide⟩) (reps rK147) (T147_56_2 i) (hfix147_56_2 i) h)

/-! ### Cell (147, 57) twin -/

def T147_57_2 : Fin 1 → Coordinate 2 := fun i => T147_57list.getD i.val (0,0,0,0,0)

theorem hfix147_57_2 : ∀ i, ((T147_57_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨57, by decide⟩ T147_57_2 (by decide)

theorem hinj147_57_2 : Function.Injective
    (fun i => ((T147_57_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_57_2 (by decide)

theorem hcardT147_57_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨57, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 57) twin (q=2).** -/
theorem cell147_57_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨57, by decide⟩ : Fin 148))) :
    species (reps (⟨57, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_57_2 i :=
  species_entry_eq_sum rK147 ⟨57, by decide⟩ e heK h T147_57_2 hfix147_57_2 hinj147_57_2 hcardT147_57_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨57, by decide⟩) (reps rK147) (T147_57_2 i) (hfix147_57_2 i) h)

/-! ### Cell (147, 58) twin -/

def T147_58_2 : Fin 1 → Coordinate 2 := fun i => T147_58list.getD i.val (0,0,0,0,0)

theorem hfix147_58_2 : ∀ i, ((T147_58_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨58, by decide⟩ T147_58_2 (by decide)

theorem hinj147_58_2 : Function.Injective
    (fun i => ((T147_58_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_58_2 (by decide)

theorem hcardT147_58_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨58, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 58) twin (q=2).** -/
theorem cell147_58_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨58, by decide⟩ : Fin 148))) :
    species (reps (⟨58, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_58_2 i :=
  species_entry_eq_sum rK147 ⟨58, by decide⟩ e heK h T147_58_2 hfix147_58_2 hinj147_58_2 hcardT147_58_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨58, by decide⟩) (reps rK147) (T147_58_2 i) (hfix147_58_2 i) h)

/-! ### Cell (147, 59) twin -/

def T147_59_2 : Fin 1 → Coordinate 2 := fun i => T147_59list.getD i.val (0,0,0,0,0)

theorem hfix147_59_2 : ∀ i, ((T147_59_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨59, by decide⟩ T147_59_2 (by decide)

theorem hinj147_59_2 : Function.Injective
    (fun i => ((T147_59_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_59_2 (by decide)

theorem hcardT147_59_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨59, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 59) twin (q=2).** -/
theorem cell147_59_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨59, by decide⟩ : Fin 148))) :
    species (reps (⟨59, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_59_2 i :=
  species_entry_eq_sum rK147 ⟨59, by decide⟩ e heK h T147_59_2 hfix147_59_2 hinj147_59_2 hcardT147_59_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨59, by decide⟩) (reps rK147) (T147_59_2 i) (hfix147_59_2 i) h)

/-! ### Cell (147, 60) twin -/

def T147_60_2 : Fin 1 → Coordinate 2 := fun i => T147_60list.getD i.val (0,0,0,0,0)

theorem hfix147_60_2 : ∀ i, ((T147_60_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨60, by decide⟩ T147_60_2 (by decide)

theorem hinj147_60_2 : Function.Injective
    (fun i => ((T147_60_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_60_2 (by decide)

theorem hcardT147_60_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨60, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 60) twin (q=2).** -/
theorem cell147_60_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨60, by decide⟩ : Fin 148))) :
    species (reps (⟨60, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_60_2 i :=
  species_entry_eq_sum rK147 ⟨60, by decide⟩ e heK h T147_60_2 hfix147_60_2 hinj147_60_2 hcardT147_60_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨60, by decide⟩) (reps rK147) (T147_60_2 i) (hfix147_60_2 i) h)

/-! ### Cell (147, 61) twin -/

def T147_61_2 : Fin 1 → Coordinate 2 := fun i => T147_61list.getD i.val (0,0,0,0,0)

theorem hfix147_61_2 : ∀ i, ((T147_61_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨61, by decide⟩ T147_61_2 (by decide)

theorem hinj147_61_2 : Function.Injective
    (fun i => ((T147_61_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_61_2 (by decide)

theorem hcardT147_61_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨61, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 61) twin (q=2).** -/
theorem cell147_61_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨61, by decide⟩ : Fin 148))) :
    species (reps (⟨61, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_61_2 i :=
  species_entry_eq_sum rK147 ⟨61, by decide⟩ e heK h T147_61_2 hfix147_61_2 hinj147_61_2 hcardT147_61_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨61, by decide⟩) (reps rK147) (T147_61_2 i) (hfix147_61_2 i) h)

/-! ### Cell (147, 62) twin -/

def T147_62_2 : Fin 1 → Coordinate 2 := fun i => T147_62list.getD i.val (0,0,0,0,0)

theorem hfix147_62_2 : ∀ i, ((T147_62_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨62, by decide⟩ T147_62_2 (by decide)

theorem hinj147_62_2 : Function.Injective
    (fun i => ((T147_62_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_62_2 (by decide)

theorem hcardT147_62_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨62, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 62) twin (q=2).** -/
theorem cell147_62_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨62, by decide⟩ : Fin 148))) :
    species (reps (⟨62, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_62_2 i :=
  species_entry_eq_sum rK147 ⟨62, by decide⟩ e heK h T147_62_2 hfix147_62_2 hinj147_62_2 hcardT147_62_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨62, by decide⟩) (reps rK147) (T147_62_2 i) (hfix147_62_2 i) h)

/-! ### Cell (147, 63) twin -/

def T147_63_2 : Fin 1 → Coordinate 2 := fun i => T147_63list.getD i.val (0,0,0,0,0)

theorem hfix147_63_2 : ∀ i, ((T147_63_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨63, by decide⟩ T147_63_2 (by decide)

theorem hinj147_63_2 : Function.Injective
    (fun i => ((T147_63_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_63_2 (by decide)

theorem hcardT147_63_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨63, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 63) twin (q=2).** -/
theorem cell147_63_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨63, by decide⟩ : Fin 148))) :
    species (reps (⟨63, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_63_2 i :=
  species_entry_eq_sum rK147 ⟨63, by decide⟩ e heK h T147_63_2 hfix147_63_2 hinj147_63_2 hcardT147_63_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨63, by decide⟩) (reps rK147) (T147_63_2 i) (hfix147_63_2 i) h)

/-! ### Cell (147, 64) twin -/

def T147_64_2 : Fin 1 → Coordinate 2 := fun i => T147_64list.getD i.val (0,0,0,0,0)

theorem hfix147_64_2 : ∀ i, ((T147_64_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨64, by decide⟩ T147_64_2 (by decide)

theorem hinj147_64_2 : Function.Injective
    (fun i => ((T147_64_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_64_2 (by decide)

theorem hcardT147_64_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨64, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 64) twin (q=2).** -/
theorem cell147_64_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨64, by decide⟩ : Fin 148))) :
    species (reps (⟨64, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_64_2 i :=
  species_entry_eq_sum rK147 ⟨64, by decide⟩ e heK h T147_64_2 hfix147_64_2 hinj147_64_2 hcardT147_64_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨64, by decide⟩) (reps rK147) (T147_64_2 i) (hfix147_64_2 i) h)

/-! ### Cell (147, 65) twin -/

def T147_65_2 : Fin 1 → Coordinate 2 := fun i => T147_65list.getD i.val (0,0,0,0,0)

theorem hfix147_65_2 : ∀ i, ((T147_65_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨65, by decide⟩ T147_65_2 (by decide)

theorem hinj147_65_2 : Function.Injective
    (fun i => ((T147_65_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_65_2 (by decide)

theorem hcardT147_65_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨65, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 65) twin (q=2).** -/
theorem cell147_65_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨65, by decide⟩ : Fin 148))) :
    species (reps (⟨65, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_65_2 i :=
  species_entry_eq_sum rK147 ⟨65, by decide⟩ e heK h T147_65_2 hfix147_65_2 hinj147_65_2 hcardT147_65_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨65, by decide⟩) (reps rK147) (T147_65_2 i) (hfix147_65_2 i) h)

/-! ### Cell (147, 66) twin -/

def T147_66_2 : Fin 1 → Coordinate 2 := fun i => T147_66list.getD i.val (0,0,0,0,0)

theorem hfix147_66_2 : ∀ i, ((T147_66_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨66, by decide⟩ T147_66_2 (by decide)

theorem hinj147_66_2 : Function.Injective
    (fun i => ((T147_66_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_66_2 (by decide)

theorem hcardT147_66_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨66, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 66) twin (q=2).** -/
theorem cell147_66_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨66, by decide⟩ : Fin 148))) :
    species (reps (⟨66, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_66_2 i :=
  species_entry_eq_sum rK147 ⟨66, by decide⟩ e heK h T147_66_2 hfix147_66_2 hinj147_66_2 hcardT147_66_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨66, by decide⟩) (reps rK147) (T147_66_2 i) (hfix147_66_2 i) h)

/-! ### Cell (147, 67) twin -/

def T147_67_2 : Fin 1 → Coordinate 2 := fun i => T147_67list.getD i.val (0,0,0,0,0)

theorem hfix147_67_2 : ∀ i, ((T147_67_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨67, by decide⟩ T147_67_2 (by decide)

theorem hinj147_67_2 : Function.Injective
    (fun i => ((T147_67_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_67_2 (by decide)

theorem hcardT147_67_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨67, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 67) twin (q=2).** -/
theorem cell147_67_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨67, by decide⟩ : Fin 148))) :
    species (reps (⟨67, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_67_2 i :=
  species_entry_eq_sum rK147 ⟨67, by decide⟩ e heK h T147_67_2 hfix147_67_2 hinj147_67_2 hcardT147_67_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨67, by decide⟩) (reps rK147) (T147_67_2 i) (hfix147_67_2 i) h)

/-! ### Cell (147, 68) twin -/

def T147_68_2 : Fin 1 → Coordinate 2 := fun i => T147_68list.getD i.val (0,0,0,0,0)

theorem hfix147_68_2 : ∀ i, ((T147_68_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨68, by decide⟩ T147_68_2 (by decide)

theorem hinj147_68_2 : Function.Injective
    (fun i => ((T147_68_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_68_2 (by decide)

theorem hcardT147_68_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨68, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 68) twin (q=2).** -/
theorem cell147_68_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨68, by decide⟩ : Fin 148))) :
    species (reps (⟨68, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_68_2 i :=
  species_entry_eq_sum rK147 ⟨68, by decide⟩ e heK h T147_68_2 hfix147_68_2 hinj147_68_2 hcardT147_68_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨68, by decide⟩) (reps rK147) (T147_68_2 i) (hfix147_68_2 i) h)

/-! ### Cell (147, 69) twin -/

def T147_69_2 : Fin 1 → Coordinate 2 := fun i => T147_69list.getD i.val (0,0,0,0,0)

theorem hfix147_69_2 : ∀ i, ((T147_69_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨69, by decide⟩ T147_69_2 (by decide)

theorem hinj147_69_2 : Function.Injective
    (fun i => ((T147_69_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_69_2 (by decide)

theorem hcardT147_69_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨69, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 69) twin (q=2).** -/
theorem cell147_69_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨69, by decide⟩ : Fin 148))) :
    species (reps (⟨69, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_69_2 i :=
  species_entry_eq_sum rK147 ⟨69, by decide⟩ e heK h T147_69_2 hfix147_69_2 hinj147_69_2 hcardT147_69_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨69, by decide⟩) (reps rK147) (T147_69_2 i) (hfix147_69_2 i) h)

/-! ### Cell (147, 70) twin -/

def T147_70_2 : Fin 1 → Coordinate 2 := fun i => T147_70list.getD i.val (0,0,0,0,0)

theorem hfix147_70_2 : ∀ i, ((T147_70_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨70, by decide⟩ T147_70_2 (by decide)

theorem hinj147_70_2 : Function.Injective
    (fun i => ((T147_70_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_70_2 (by decide)

theorem hcardT147_70_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨70, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 70) twin (q=2).** -/
theorem cell147_70_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨70, by decide⟩ : Fin 148))) :
    species (reps (⟨70, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_70_2 i :=
  species_entry_eq_sum rK147 ⟨70, by decide⟩ e heK h T147_70_2 hfix147_70_2 hinj147_70_2 hcardT147_70_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨70, by decide⟩) (reps rK147) (T147_70_2 i) (hfix147_70_2 i) h)

/-! ### Cell (147, 71) twin -/

def T147_71_2 : Fin 1 → Coordinate 2 := fun i => T147_71list.getD i.val (0,0,0,0,0)

theorem hfix147_71_2 : ∀ i, ((T147_71_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨71, by decide⟩ T147_71_2 (by decide)

theorem hinj147_71_2 : Function.Injective
    (fun i => ((T147_71_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_71_2 (by decide)

theorem hcardT147_71_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨71, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 71) twin (q=2).** -/
theorem cell147_71_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨71, by decide⟩ : Fin 148))) :
    species (reps (⟨71, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_71_2 i :=
  species_entry_eq_sum rK147 ⟨71, by decide⟩ e heK h T147_71_2 hfix147_71_2 hinj147_71_2 hcardT147_71_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨71, by decide⟩) (reps rK147) (T147_71_2 i) (hfix147_71_2 i) h)

/-! ### Cell (147, 72) twin -/

def T147_72_2 : Fin 1 → Coordinate 2 := fun i => T147_72list.getD i.val (0,0,0,0,0)

theorem hfix147_72_2 : ∀ i, ((T147_72_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨72, by decide⟩ T147_72_2 (by decide)

theorem hinj147_72_2 : Function.Injective
    (fun i => ((T147_72_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_72_2 (by decide)

theorem hcardT147_72_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨72, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 72) twin (q=2).** -/
theorem cell147_72_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨72, by decide⟩ : Fin 148))) :
    species (reps (⟨72, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_72_2 i :=
  species_entry_eq_sum rK147 ⟨72, by decide⟩ e heK h T147_72_2 hfix147_72_2 hinj147_72_2 hcardT147_72_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨72, by decide⟩) (reps rK147) (T147_72_2 i) (hfix147_72_2 i) h)

/-! ### Cell (147, 73) twin -/

def T147_73_2 : Fin 1 → Coordinate 2 := fun i => T147_73list.getD i.val (0,0,0,0,0)

theorem hfix147_73_2 : ∀ i, ((T147_73_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨73, by decide⟩ T147_73_2 (by decide)

theorem hinj147_73_2 : Function.Injective
    (fun i => ((T147_73_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_73_2 (by decide)

theorem hcardT147_73_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨73, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 73) twin (q=2).** -/
theorem cell147_73_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨73, by decide⟩ : Fin 148))) :
    species (reps (⟨73, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_73_2 i :=
  species_entry_eq_sum rK147 ⟨73, by decide⟩ e heK h T147_73_2 hfix147_73_2 hinj147_73_2 hcardT147_73_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨73, by decide⟩) (reps rK147) (T147_73_2 i) (hfix147_73_2 i) h)

/-! ### Cell (147, 74) twin -/

def T147_74_2 : Fin 1 → Coordinate 2 := fun i => T147_74list.getD i.val (0,0,0,0,0)

theorem hfix147_74_2 : ∀ i, ((T147_74_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨74, by decide⟩ T147_74_2 (by decide)

theorem hinj147_74_2 : Function.Injective
    (fun i => ((T147_74_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_74_2 (by decide)

theorem hcardT147_74_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨74, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 74) twin (q=2).** -/
theorem cell147_74_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨74, by decide⟩ : Fin 148))) :
    species (reps (⟨74, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_74_2 i :=
  species_entry_eq_sum rK147 ⟨74, by decide⟩ e heK h T147_74_2 hfix147_74_2 hinj147_74_2 hcardT147_74_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨74, by decide⟩) (reps rK147) (T147_74_2 i) (hfix147_74_2 i) h)

/-! ### Cell (147, 75) twin -/

def T147_75_2 : Fin 1 → Coordinate 2 := fun i => T147_75list.getD i.val (0,0,0,0,0)

theorem hfix147_75_2 : ∀ i, ((T147_75_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨75, by decide⟩ T147_75_2 (by decide)

theorem hinj147_75_2 : Function.Injective
    (fun i => ((T147_75_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_75_2 (by decide)

theorem hcardT147_75_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨75, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 75) twin (q=2).** -/
theorem cell147_75_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨75, by decide⟩ : Fin 148))) :
    species (reps (⟨75, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_75_2 i :=
  species_entry_eq_sum rK147 ⟨75, by decide⟩ e heK h T147_75_2 hfix147_75_2 hinj147_75_2 hcardT147_75_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨75, by decide⟩) (reps rK147) (T147_75_2 i) (hfix147_75_2 i) h)

/-! ### Cell (147, 76) twin -/

def T147_76_2 : Fin 1 → Coordinate 2 := fun i => T147_76list.getD i.val (0,0,0,0,0)

theorem hfix147_76_2 : ∀ i, ((T147_76_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨76, by decide⟩ T147_76_2 (by decide)

theorem hinj147_76_2 : Function.Injective
    (fun i => ((T147_76_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_76_2 (by decide)

theorem hcardT147_76_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨76, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 76) twin (q=2).** -/
theorem cell147_76_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨76, by decide⟩ : Fin 148))) :
    species (reps (⟨76, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_76_2 i :=
  species_entry_eq_sum rK147 ⟨76, by decide⟩ e heK h T147_76_2 hfix147_76_2 hinj147_76_2 hcardT147_76_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨76, by decide⟩) (reps rK147) (T147_76_2 i) (hfix147_76_2 i) h)

/-! ### Cell (147, 77) twin -/

def T147_77_2 : Fin 1 → Coordinate 2 := fun i => T147_77list.getD i.val (0,0,0,0,0)

theorem hfix147_77_2 : ∀ i, ((T147_77_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨77, by decide⟩ T147_77_2 (by decide)

theorem hinj147_77_2 : Function.Injective
    (fun i => ((T147_77_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_77_2 (by decide)

theorem hcardT147_77_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨77, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 77) twin (q=2).** -/
theorem cell147_77_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨77, by decide⟩ : Fin 148))) :
    species (reps (⟨77, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_77_2 i :=
  species_entry_eq_sum rK147 ⟨77, by decide⟩ e heK h T147_77_2 hfix147_77_2 hinj147_77_2 hcardT147_77_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨77, by decide⟩) (reps rK147) (T147_77_2 i) (hfix147_77_2 i) h)

/-! ### Cell (147, 78) twin -/

def T147_78_2 : Fin 1 → Coordinate 2 := fun i => T147_78list.getD i.val (0,0,0,0,0)

theorem hfix147_78_2 : ∀ i, ((T147_78_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨78, by decide⟩ T147_78_2 (by decide)

theorem hinj147_78_2 : Function.Injective
    (fun i => ((T147_78_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_78_2 (by decide)

theorem hcardT147_78_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨78, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 78) twin (q=2).** -/
theorem cell147_78_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨78, by decide⟩ : Fin 148))) :
    species (reps (⟨78, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_78_2 i :=
  species_entry_eq_sum rK147 ⟨78, by decide⟩ e heK h T147_78_2 hfix147_78_2 hinj147_78_2 hcardT147_78_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨78, by decide⟩) (reps rK147) (T147_78_2 i) (hfix147_78_2 i) h)

/-! ### Cell (147, 79) twin -/

def T147_79_2 : Fin 1 → Coordinate 2 := fun i => T147_79list.getD i.val (0,0,0,0,0)

theorem hfix147_79_2 : ∀ i, ((T147_79_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨79, by decide⟩ T147_79_2 (by decide)

theorem hinj147_79_2 : Function.Injective
    (fun i => ((T147_79_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_79_2 (by decide)

theorem hcardT147_79_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨79, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 79) twin (q=2).** -/
theorem cell147_79_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨79, by decide⟩ : Fin 148))) :
    species (reps (⟨79, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_79_2 i :=
  species_entry_eq_sum rK147 ⟨79, by decide⟩ e heK h T147_79_2 hfix147_79_2 hinj147_79_2 hcardT147_79_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨79, by decide⟩) (reps rK147) (T147_79_2 i) (hfix147_79_2 i) h)

/-! ### Cell (147, 80) twin -/

def T147_80_2 : Fin 1 → Coordinate 2 := fun i => T147_80list.getD i.val (0,0,0,0,0)

theorem hfix147_80_2 : ∀ i, ((T147_80_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨80, by decide⟩ T147_80_2 (by decide)

theorem hinj147_80_2 : Function.Injective
    (fun i => ((T147_80_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_80_2 (by decide)

theorem hcardT147_80_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨80, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 80) twin (q=2).** -/
theorem cell147_80_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨80, by decide⟩ : Fin 148))) :
    species (reps (⟨80, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_80_2 i :=
  species_entry_eq_sum rK147 ⟨80, by decide⟩ e heK h T147_80_2 hfix147_80_2 hinj147_80_2 hcardT147_80_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨80, by decide⟩) (reps rK147) (T147_80_2 i) (hfix147_80_2 i) h)

/-! ### Cell (147, 81) twin -/

def T147_81_2 : Fin 1 → Coordinate 2 := fun i => T147_81list.getD i.val (0,0,0,0,0)

theorem hfix147_81_2 : ∀ i, ((T147_81_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨81, by decide⟩ T147_81_2 (by decide)

theorem hinj147_81_2 : Function.Injective
    (fun i => ((T147_81_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_81_2 (by decide)

theorem hcardT147_81_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨81, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 81) twin (q=2).** -/
theorem cell147_81_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨81, by decide⟩ : Fin 148))) :
    species (reps (⟨81, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_81_2 i :=
  species_entry_eq_sum rK147 ⟨81, by decide⟩ e heK h T147_81_2 hfix147_81_2 hinj147_81_2 hcardT147_81_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨81, by decide⟩) (reps rK147) (T147_81_2 i) (hfix147_81_2 i) h)

/-! ### Cell (147, 82) twin -/

def T147_82_2 : Fin 1 → Coordinate 2 := fun i => T147_82list.getD i.val (0,0,0,0,0)

theorem hfix147_82_2 : ∀ i, ((T147_82_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨82, by decide⟩ T147_82_2 (by decide)

theorem hinj147_82_2 : Function.Injective
    (fun i => ((T147_82_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_82_2 (by decide)

theorem hcardT147_82_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨82, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 82) twin (q=2).** -/
theorem cell147_82_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨82, by decide⟩ : Fin 148))) :
    species (reps (⟨82, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_82_2 i :=
  species_entry_eq_sum rK147 ⟨82, by decide⟩ e heK h T147_82_2 hfix147_82_2 hinj147_82_2 hcardT147_82_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨82, by decide⟩) (reps rK147) (T147_82_2 i) (hfix147_82_2 i) h)

/-! ### Cell (147, 83) twin -/

def T147_83_2 : Fin 1 → Coordinate 2 := fun i => T147_83list.getD i.val (0,0,0,0,0)

theorem hfix147_83_2 : ∀ i, ((T147_83_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨83, by decide⟩ T147_83_2 (by decide)

theorem hinj147_83_2 : Function.Injective
    (fun i => ((T147_83_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_83_2 (by decide)

theorem hcardT147_83_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨83, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 83) twin (q=2).** -/
theorem cell147_83_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨83, by decide⟩ : Fin 148))) :
    species (reps (⟨83, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_83_2 i :=
  species_entry_eq_sum rK147 ⟨83, by decide⟩ e heK h T147_83_2 hfix147_83_2 hinj147_83_2 hcardT147_83_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨83, by decide⟩) (reps rK147) (T147_83_2 i) (hfix147_83_2 i) h)

/-! ### Cell (147, 84) twin -/

def T147_84_2 : Fin 1 → Coordinate 2 := fun i => T147_84list.getD i.val (0,0,0,0,0)

theorem hfix147_84_2 : ∀ i, ((T147_84_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨84, by decide⟩ T147_84_2 (by decide)

theorem hinj147_84_2 : Function.Injective
    (fun i => ((T147_84_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_84_2 (by decide)

theorem hcardT147_84_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨84, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 84) twin (q=2).** -/
theorem cell147_84_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨84, by decide⟩ : Fin 148))) :
    species (reps (⟨84, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_84_2 i :=
  species_entry_eq_sum rK147 ⟨84, by decide⟩ e heK h T147_84_2 hfix147_84_2 hinj147_84_2 hcardT147_84_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨84, by decide⟩) (reps rK147) (T147_84_2 i) (hfix147_84_2 i) h)

/-! ### Cell (147, 85) twin -/

def T147_85_2 : Fin 1 → Coordinate 2 := fun i => T147_85list.getD i.val (0,0,0,0,0)

theorem hfix147_85_2 : ∀ i, ((T147_85_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨85, by decide⟩ T147_85_2 (by decide)

theorem hinj147_85_2 : Function.Injective
    (fun i => ((T147_85_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_85_2 (by decide)

theorem hcardT147_85_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨85, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 85) twin (q=2).** -/
theorem cell147_85_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨85, by decide⟩ : Fin 148))) :
    species (reps (⟨85, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_85_2 i :=
  species_entry_eq_sum rK147 ⟨85, by decide⟩ e heK h T147_85_2 hfix147_85_2 hinj147_85_2 hcardT147_85_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨85, by decide⟩) (reps rK147) (T147_85_2 i) (hfix147_85_2 i) h)

/-! ### Cell (147, 86) twin -/

def T147_86_2 : Fin 1 → Coordinate 2 := fun i => T147_86list.getD i.val (0,0,0,0,0)

theorem hfix147_86_2 : ∀ i, ((T147_86_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨86, by decide⟩ T147_86_2 (by decide)

theorem hinj147_86_2 : Function.Injective
    (fun i => ((T147_86_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_86_2 (by decide)

theorem hcardT147_86_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨86, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 86) twin (q=2).** -/
theorem cell147_86_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨86, by decide⟩ : Fin 148))) :
    species (reps (⟨86, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_86_2 i :=
  species_entry_eq_sum rK147 ⟨86, by decide⟩ e heK h T147_86_2 hfix147_86_2 hinj147_86_2 hcardT147_86_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨86, by decide⟩) (reps rK147) (T147_86_2 i) (hfix147_86_2 i) h)

/-! ### Cell (147, 87) twin -/

def T147_87_2 : Fin 1 → Coordinate 2 := fun i => T147_87list.getD i.val (0,0,0,0,0)

theorem hfix147_87_2 : ∀ i, ((T147_87_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨87, by decide⟩ T147_87_2 (by decide)

theorem hinj147_87_2 : Function.Injective
    (fun i => ((T147_87_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_87_2 (by decide)

theorem hcardT147_87_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨87, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 87) twin (q=2).** -/
theorem cell147_87_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨87, by decide⟩ : Fin 148))) :
    species (reps (⟨87, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_87_2 i :=
  species_entry_eq_sum rK147 ⟨87, by decide⟩ e heK h T147_87_2 hfix147_87_2 hinj147_87_2 hcardT147_87_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨87, by decide⟩) (reps rK147) (T147_87_2 i) (hfix147_87_2 i) h)

/-! ### Cell (147, 88) twin -/

def T147_88_2 : Fin 1 → Coordinate 2 := fun i => T147_88list.getD i.val (0,0,0,0,0)

theorem hfix147_88_2 : ∀ i, ((T147_88_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨88, by decide⟩ T147_88_2 (by decide)

theorem hinj147_88_2 : Function.Injective
    (fun i => ((T147_88_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_88_2 (by decide)

theorem hcardT147_88_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨88, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 88) twin (q=2).** -/
theorem cell147_88_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨88, by decide⟩ : Fin 148))) :
    species (reps (⟨88, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_88_2 i :=
  species_entry_eq_sum rK147 ⟨88, by decide⟩ e heK h T147_88_2 hfix147_88_2 hinj147_88_2 hcardT147_88_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨88, by decide⟩) (reps rK147) (T147_88_2 i) (hfix147_88_2 i) h)

/-! ### Cell (147, 89) twin -/

def T147_89_2 : Fin 1 → Coordinate 2 := fun i => T147_89list.getD i.val (0,0,0,0,0)

theorem hfix147_89_2 : ∀ i, ((T147_89_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨89, by decide⟩ T147_89_2 (by decide)

theorem hinj147_89_2 : Function.Injective
    (fun i => ((T147_89_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_89_2 (by decide)

theorem hcardT147_89_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨89, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 89) twin (q=2).** -/
theorem cell147_89_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨89, by decide⟩ : Fin 148))) :
    species (reps (⟨89, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_89_2 i :=
  species_entry_eq_sum rK147 ⟨89, by decide⟩ e heK h T147_89_2 hfix147_89_2 hinj147_89_2 hcardT147_89_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨89, by decide⟩) (reps rK147) (T147_89_2 i) (hfix147_89_2 i) h)

/-! ### Cell (147, 90) twin -/

def T147_90_2 : Fin 1 → Coordinate 2 := fun i => T147_90list.getD i.val (0,0,0,0,0)

theorem hfix147_90_2 : ∀ i, ((T147_90_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨90, by decide⟩ T147_90_2 (by decide)

theorem hinj147_90_2 : Function.Injective
    (fun i => ((T147_90_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_90_2 (by decide)

theorem hcardT147_90_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨90, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 90) twin (q=2).** -/
theorem cell147_90_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨90, by decide⟩ : Fin 148))) :
    species (reps (⟨90, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_90_2 i :=
  species_entry_eq_sum rK147 ⟨90, by decide⟩ e heK h T147_90_2 hfix147_90_2 hinj147_90_2 hcardT147_90_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨90, by decide⟩) (reps rK147) (T147_90_2 i) (hfix147_90_2 i) h)

/-! ### Cell (147, 91) twin -/

def T147_91_2 : Fin 1 → Coordinate 2 := fun i => T147_91list.getD i.val (0,0,0,0,0)

theorem hfix147_91_2 : ∀ i, ((T147_91_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨91, by decide⟩ T147_91_2 (by decide)

theorem hinj147_91_2 : Function.Injective
    (fun i => ((T147_91_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_91_2 (by decide)

theorem hcardT147_91_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨91, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 91) twin (q=2).** -/
theorem cell147_91_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨91, by decide⟩ : Fin 148))) :
    species (reps (⟨91, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_91_2 i :=
  species_entry_eq_sum rK147 ⟨91, by decide⟩ e heK h T147_91_2 hfix147_91_2 hinj147_91_2 hcardT147_91_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨91, by decide⟩) (reps rK147) (T147_91_2 i) (hfix147_91_2 i) h)

/-! ### Cell (147, 92) twin -/

def T147_92_2 : Fin 1 → Coordinate 2 := fun i => T147_92list.getD i.val (0,0,0,0,0)

theorem hfix147_92_2 : ∀ i, ((T147_92_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨92, by decide⟩ T147_92_2 (by decide)

theorem hinj147_92_2 : Function.Injective
    (fun i => ((T147_92_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_92_2 (by decide)

theorem hcardT147_92_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨92, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 92) twin (q=2).** -/
theorem cell147_92_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨92, by decide⟩ : Fin 148))) :
    species (reps (⟨92, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_92_2 i :=
  species_entry_eq_sum rK147 ⟨92, by decide⟩ e heK h T147_92_2 hfix147_92_2 hinj147_92_2 hcardT147_92_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨92, by decide⟩) (reps rK147) (T147_92_2 i) (hfix147_92_2 i) h)

/-! ### Cell (147, 93) twin -/

def T147_93_2 : Fin 1 → Coordinate 2 := fun i => T147_93list.getD i.val (0,0,0,0,0)

theorem hfix147_93_2 : ∀ i, ((T147_93_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨93, by decide⟩ T147_93_2 (by decide)

theorem hinj147_93_2 : Function.Injective
    (fun i => ((T147_93_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_93_2 (by decide)

theorem hcardT147_93_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨93, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 93) twin (q=2).** -/
theorem cell147_93_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨93, by decide⟩ : Fin 148))) :
    species (reps (⟨93, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_93_2 i :=
  species_entry_eq_sum rK147 ⟨93, by decide⟩ e heK h T147_93_2 hfix147_93_2 hinj147_93_2 hcardT147_93_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨93, by decide⟩) (reps rK147) (T147_93_2 i) (hfix147_93_2 i) h)

/-! ### Cell (147, 94) twin -/

def T147_94_2 : Fin 1 → Coordinate 2 := fun i => T147_94list.getD i.val (0,0,0,0,0)

theorem hfix147_94_2 : ∀ i, ((T147_94_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨94, by decide⟩ T147_94_2 (by decide)

theorem hinj147_94_2 : Function.Injective
    (fun i => ((T147_94_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_94_2 (by decide)

theorem hcardT147_94_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨94, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 94) twin (q=2).** -/
theorem cell147_94_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨94, by decide⟩ : Fin 148))) :
    species (reps (⟨94, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_94_2 i :=
  species_entry_eq_sum rK147 ⟨94, by decide⟩ e heK h T147_94_2 hfix147_94_2 hinj147_94_2 hcardT147_94_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨94, by decide⟩) (reps rK147) (T147_94_2 i) (hfix147_94_2 i) h)

/-! ### Cell (147, 95) twin -/

def T147_95_2 : Fin 1 → Coordinate 2 := fun i => T147_95list.getD i.val (0,0,0,0,0)

theorem hfix147_95_2 : ∀ i, ((T147_95_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨95, by decide⟩ T147_95_2 (by decide)

theorem hinj147_95_2 : Function.Injective
    (fun i => ((T147_95_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_95_2 (by decide)

theorem hcardT147_95_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨95, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 95) twin (q=2).** -/
theorem cell147_95_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨95, by decide⟩ : Fin 148))) :
    species (reps (⟨95, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_95_2 i :=
  species_entry_eq_sum rK147 ⟨95, by decide⟩ e heK h T147_95_2 hfix147_95_2 hinj147_95_2 hcardT147_95_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨95, by decide⟩) (reps rK147) (T147_95_2 i) (hfix147_95_2 i) h)

/-! ### Cell (147, 96) twin -/

def T147_96_2 : Fin 1 → Coordinate 2 := fun i => T147_96list.getD i.val (0,0,0,0,0)

theorem hfix147_96_2 : ∀ i, ((T147_96_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨96, by decide⟩ T147_96_2 (by decide)

theorem hinj147_96_2 : Function.Injective
    (fun i => ((T147_96_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_96_2 (by decide)

theorem hcardT147_96_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨96, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 96) twin (q=2).** -/
theorem cell147_96_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨96, by decide⟩ : Fin 148))) :
    species (reps (⟨96, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_96_2 i :=
  species_entry_eq_sum rK147 ⟨96, by decide⟩ e heK h T147_96_2 hfix147_96_2 hinj147_96_2 hcardT147_96_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨96, by decide⟩) (reps rK147) (T147_96_2 i) (hfix147_96_2 i) h)

/-! ### Cell (147, 97) twin -/

def T147_97_2 : Fin 1 → Coordinate 2 := fun i => T147_97list.getD i.val (0,0,0,0,0)

theorem hfix147_97_2 : ∀ i, ((T147_97_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨97, by decide⟩ T147_97_2 (by decide)

theorem hinj147_97_2 : Function.Injective
    (fun i => ((T147_97_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_97_2 (by decide)

theorem hcardT147_97_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨97, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 97) twin (q=2).** -/
theorem cell147_97_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨97, by decide⟩ : Fin 148))) :
    species (reps (⟨97, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_97_2 i :=
  species_entry_eq_sum rK147 ⟨97, by decide⟩ e heK h T147_97_2 hfix147_97_2 hinj147_97_2 hcardT147_97_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨97, by decide⟩) (reps rK147) (T147_97_2 i) (hfix147_97_2 i) h)

/-! ### Cell (147, 98) twin -/

def T147_98_2 : Fin 1 → Coordinate 2 := fun i => T147_98list.getD i.val (0,0,0,0,0)

theorem hfix147_98_2 : ∀ i, ((T147_98_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨98, by decide⟩ T147_98_2 (by decide)

theorem hinj147_98_2 : Function.Injective
    (fun i => ((T147_98_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_98_2 (by decide)

theorem hcardT147_98_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨98, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 98) twin (q=2).** -/
theorem cell147_98_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨98, by decide⟩ : Fin 148))) :
    species (reps (⟨98, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_98_2 i :=
  species_entry_eq_sum rK147 ⟨98, by decide⟩ e heK h T147_98_2 hfix147_98_2 hinj147_98_2 hcardT147_98_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨98, by decide⟩) (reps rK147) (T147_98_2 i) (hfix147_98_2 i) h)

/-! ### Cell (147, 99) twin -/

def T147_99_2 : Fin 1 → Coordinate 2 := fun i => T147_99list.getD i.val (0,0,0,0,0)

theorem hfix147_99_2 : ∀ i, ((T147_99_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨99, by decide⟩ T147_99_2 (by decide)

theorem hinj147_99_2 : Function.Injective
    (fun i => ((T147_99_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_99_2 (by decide)

theorem hcardT147_99_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨99, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 99) twin (q=2).** -/
theorem cell147_99_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨99, by decide⟩ : Fin 148))) :
    species (reps (⟨99, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_99_2 i :=
  species_entry_eq_sum rK147 ⟨99, by decide⟩ e heK h T147_99_2 hfix147_99_2 hinj147_99_2 hcardT147_99_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨99, by decide⟩) (reps rK147) (T147_99_2 i) (hfix147_99_2 i) h)

/-! ### Cell (147, 100) twin -/

def T147_100_2 : Fin 1 → Coordinate 2 := fun i => T147_100list.getD i.val (0,0,0,0,0)

theorem hfix147_100_2 : ∀ i, ((T147_100_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨100, by decide⟩ T147_100_2 (by decide)

theorem hinj147_100_2 : Function.Injective
    (fun i => ((T147_100_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_100_2 (by decide)

theorem hcardT147_100_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨100, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 100) twin (q=2).** -/
theorem cell147_100_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨100, by decide⟩ : Fin 148))) :
    species (reps (⟨100, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_100_2 i :=
  species_entry_eq_sum rK147 ⟨100, by decide⟩ e heK h T147_100_2 hfix147_100_2 hinj147_100_2 hcardT147_100_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨100, by decide⟩) (reps rK147) (T147_100_2 i) (hfix147_100_2 i) h)

/-! ### Cell (147, 101) twin -/

def T147_101_2 : Fin 1 → Coordinate 2 := fun i => T147_101list.getD i.val (0,0,0,0,0)

theorem hfix147_101_2 : ∀ i, ((T147_101_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨101, by decide⟩ T147_101_2 (by decide)

theorem hinj147_101_2 : Function.Injective
    (fun i => ((T147_101_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_101_2 (by decide)

theorem hcardT147_101_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨101, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 101) twin (q=2).** -/
theorem cell147_101_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨101, by decide⟩ : Fin 148))) :
    species (reps (⟨101, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_101_2 i :=
  species_entry_eq_sum rK147 ⟨101, by decide⟩ e heK h T147_101_2 hfix147_101_2 hinj147_101_2 hcardT147_101_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨101, by decide⟩) (reps rK147) (T147_101_2 i) (hfix147_101_2 i) h)

/-! ### Cell (147, 102) twin -/

def T147_102_2 : Fin 1 → Coordinate 2 := fun i => T147_102list.getD i.val (0,0,0,0,0)

theorem hfix147_102_2 : ∀ i, ((T147_102_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨102, by decide⟩ T147_102_2 (by decide)

theorem hinj147_102_2 : Function.Injective
    (fun i => ((T147_102_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_102_2 (by decide)

theorem hcardT147_102_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨102, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 102) twin (q=2).** -/
theorem cell147_102_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨102, by decide⟩ : Fin 148))) :
    species (reps (⟨102, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_102_2 i :=
  species_entry_eq_sum rK147 ⟨102, by decide⟩ e heK h T147_102_2 hfix147_102_2 hinj147_102_2 hcardT147_102_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨102, by decide⟩) (reps rK147) (T147_102_2 i) (hfix147_102_2 i) h)

/-! ### Cell (147, 103) twin -/

def T147_103_2 : Fin 1 → Coordinate 2 := fun i => T147_103list.getD i.val (0,0,0,0,0)

theorem hfix147_103_2 : ∀ i, ((T147_103_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨103, by decide⟩ T147_103_2 (by decide)

theorem hinj147_103_2 : Function.Injective
    (fun i => ((T147_103_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_103_2 (by decide)

theorem hcardT147_103_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨103, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 103) twin (q=2).** -/
theorem cell147_103_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨103, by decide⟩ : Fin 148))) :
    species (reps (⟨103, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_103_2 i :=
  species_entry_eq_sum rK147 ⟨103, by decide⟩ e heK h T147_103_2 hfix147_103_2 hinj147_103_2 hcardT147_103_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨103, by decide⟩) (reps rK147) (T147_103_2 i) (hfix147_103_2 i) h)

/-! ### Cell (147, 104) twin -/

def T147_104_2 : Fin 1 → Coordinate 2 := fun i => T147_104list.getD i.val (0,0,0,0,0)

theorem hfix147_104_2 : ∀ i, ((T147_104_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨104, by decide⟩ T147_104_2 (by decide)

theorem hinj147_104_2 : Function.Injective
    (fun i => ((T147_104_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_104_2 (by decide)

theorem hcardT147_104_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨104, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 104) twin (q=2).** -/
theorem cell147_104_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨104, by decide⟩ : Fin 148))) :
    species (reps (⟨104, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_104_2 i :=
  species_entry_eq_sum rK147 ⟨104, by decide⟩ e heK h T147_104_2 hfix147_104_2 hinj147_104_2 hcardT147_104_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨104, by decide⟩) (reps rK147) (T147_104_2 i) (hfix147_104_2 i) h)

/-! ### Cell (147, 105) twin -/

def T147_105_2 : Fin 1 → Coordinate 2 := fun i => T147_105list.getD i.val (0,0,0,0,0)

theorem hfix147_105_2 : ∀ i, ((T147_105_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨105, by decide⟩ T147_105_2 (by decide)

theorem hinj147_105_2 : Function.Injective
    (fun i => ((T147_105_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_105_2 (by decide)

theorem hcardT147_105_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨105, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 105) twin (q=2).** -/
theorem cell147_105_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨105, by decide⟩ : Fin 148))) :
    species (reps (⟨105, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_105_2 i :=
  species_entry_eq_sum rK147 ⟨105, by decide⟩ e heK h T147_105_2 hfix147_105_2 hinj147_105_2 hcardT147_105_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨105, by decide⟩) (reps rK147) (T147_105_2 i) (hfix147_105_2 i) h)

/-! ### Cell (147, 106) twin -/

def T147_106_2 : Fin 1 → Coordinate 2 := fun i => T147_106list.getD i.val (0,0,0,0,0)

theorem hfix147_106_2 : ∀ i, ((T147_106_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨106, by decide⟩ T147_106_2 (by decide)

theorem hinj147_106_2 : Function.Injective
    (fun i => ((T147_106_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_106_2 (by decide)

theorem hcardT147_106_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨106, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 106) twin (q=2).** -/
theorem cell147_106_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨106, by decide⟩ : Fin 148))) :
    species (reps (⟨106, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_106_2 i :=
  species_entry_eq_sum rK147 ⟨106, by decide⟩ e heK h T147_106_2 hfix147_106_2 hinj147_106_2 hcardT147_106_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨106, by decide⟩) (reps rK147) (T147_106_2 i) (hfix147_106_2 i) h)

/-! ### Cell (147, 107) twin -/

def T147_107_2 : Fin 1 → Coordinate 2 := fun i => T147_107list.getD i.val (0,0,0,0,0)

theorem hfix147_107_2 : ∀ i, ((T147_107_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨107, by decide⟩ T147_107_2 (by decide)

theorem hinj147_107_2 : Function.Injective
    (fun i => ((T147_107_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_107_2 (by decide)

theorem hcardT147_107_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨107, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 107) twin (q=2).** -/
theorem cell147_107_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨107, by decide⟩ : Fin 148))) :
    species (reps (⟨107, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_107_2 i :=
  species_entry_eq_sum rK147 ⟨107, by decide⟩ e heK h T147_107_2 hfix147_107_2 hinj147_107_2 hcardT147_107_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨107, by decide⟩) (reps rK147) (T147_107_2 i) (hfix147_107_2 i) h)

/-! ### Cell (147, 108) twin -/

def T147_108_2 : Fin 1 → Coordinate 2 := fun i => T147_108list.getD i.val (0,0,0,0,0)

theorem hfix147_108_2 : ∀ i, ((T147_108_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨108, by decide⟩ T147_108_2 (by decide)

theorem hinj147_108_2 : Function.Injective
    (fun i => ((T147_108_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_108_2 (by decide)

theorem hcardT147_108_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨108, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 108) twin (q=2).** -/
theorem cell147_108_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨108, by decide⟩ : Fin 148))) :
    species (reps (⟨108, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_108_2 i :=
  species_entry_eq_sum rK147 ⟨108, by decide⟩ e heK h T147_108_2 hfix147_108_2 hinj147_108_2 hcardT147_108_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨108, by decide⟩) (reps rK147) (T147_108_2 i) (hfix147_108_2 i) h)

/-! ### Cell (147, 109) twin -/

def T147_109_2 : Fin 1 → Coordinate 2 := fun i => T147_109list.getD i.val (0,0,0,0,0)

theorem hfix147_109_2 : ∀ i, ((T147_109_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨109, by decide⟩ T147_109_2 (by decide)

theorem hinj147_109_2 : Function.Injective
    (fun i => ((T147_109_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_109_2 (by decide)

theorem hcardT147_109_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨109, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 109) twin (q=2).** -/
theorem cell147_109_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨109, by decide⟩ : Fin 148))) :
    species (reps (⟨109, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_109_2 i :=
  species_entry_eq_sum rK147 ⟨109, by decide⟩ e heK h T147_109_2 hfix147_109_2 hinj147_109_2 hcardT147_109_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨109, by decide⟩) (reps rK147) (T147_109_2 i) (hfix147_109_2 i) h)

/-! ### Cell (147, 110) twin -/

def T147_110_2 : Fin 1 → Coordinate 2 := fun i => T147_110list.getD i.val (0,0,0,0,0)

theorem hfix147_110_2 : ∀ i, ((T147_110_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨110, by decide⟩ T147_110_2 (by decide)

theorem hinj147_110_2 : Function.Injective
    (fun i => ((T147_110_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_110_2 (by decide)

theorem hcardT147_110_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨110, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 110) twin (q=2).** -/
theorem cell147_110_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨110, by decide⟩ : Fin 148))) :
    species (reps (⟨110, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_110_2 i :=
  species_entry_eq_sum rK147 ⟨110, by decide⟩ e heK h T147_110_2 hfix147_110_2 hinj147_110_2 hcardT147_110_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨110, by decide⟩) (reps rK147) (T147_110_2 i) (hfix147_110_2 i) h)

/-! ### Cell (147, 111) twin -/

def T147_111_2 : Fin 1 → Coordinate 2 := fun i => T147_111list.getD i.val (0,0,0,0,0)

theorem hfix147_111_2 : ∀ i, ((T147_111_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨111, by decide⟩ T147_111_2 (by decide)

theorem hinj147_111_2 : Function.Injective
    (fun i => ((T147_111_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_111_2 (by decide)

theorem hcardT147_111_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨111, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 111) twin (q=2).** -/
theorem cell147_111_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨111, by decide⟩ : Fin 148))) :
    species (reps (⟨111, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_111_2 i :=
  species_entry_eq_sum rK147 ⟨111, by decide⟩ e heK h T147_111_2 hfix147_111_2 hinj147_111_2 hcardT147_111_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨111, by decide⟩) (reps rK147) (T147_111_2 i) (hfix147_111_2 i) h)

/-! ### Cell (147, 112) twin -/

def T147_112_2 : Fin 1 → Coordinate 2 := fun i => T147_112list.getD i.val (0,0,0,0,0)

theorem hfix147_112_2 : ∀ i, ((T147_112_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨112, by decide⟩ T147_112_2 (by decide)

theorem hinj147_112_2 : Function.Injective
    (fun i => ((T147_112_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_112_2 (by decide)

theorem hcardT147_112_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨112, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 112) twin (q=2).** -/
theorem cell147_112_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨112, by decide⟩ : Fin 148))) :
    species (reps (⟨112, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_112_2 i :=
  species_entry_eq_sum rK147 ⟨112, by decide⟩ e heK h T147_112_2 hfix147_112_2 hinj147_112_2 hcardT147_112_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨112, by decide⟩) (reps rK147) (T147_112_2 i) (hfix147_112_2 i) h)

/-! ### Cell (147, 113) twin -/

def T147_113_2 : Fin 1 → Coordinate 2 := fun i => T147_113list.getD i.val (0,0,0,0,0)

theorem hfix147_113_2 : ∀ i, ((T147_113_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨113, by decide⟩ T147_113_2 (by decide)

theorem hinj147_113_2 : Function.Injective
    (fun i => ((T147_113_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_113_2 (by decide)

theorem hcardT147_113_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨113, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 113) twin (q=2).** -/
theorem cell147_113_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨113, by decide⟩ : Fin 148))) :
    species (reps (⟨113, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_113_2 i :=
  species_entry_eq_sum rK147 ⟨113, by decide⟩ e heK h T147_113_2 hfix147_113_2 hinj147_113_2 hcardT147_113_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨113, by decide⟩) (reps rK147) (T147_113_2 i) (hfix147_113_2 i) h)

/-! ### Cell (147, 114) twin -/

def T147_114_2 : Fin 1 → Coordinate 2 := fun i => T147_114list.getD i.val (0,0,0,0,0)

theorem hfix147_114_2 : ∀ i, ((T147_114_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨114, by decide⟩ T147_114_2 (by decide)

theorem hinj147_114_2 : Function.Injective
    (fun i => ((T147_114_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_114_2 (by decide)

theorem hcardT147_114_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨114, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 114) twin (q=2).** -/
theorem cell147_114_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨114, by decide⟩ : Fin 148))) :
    species (reps (⟨114, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_114_2 i :=
  species_entry_eq_sum rK147 ⟨114, by decide⟩ e heK h T147_114_2 hfix147_114_2 hinj147_114_2 hcardT147_114_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨114, by decide⟩) (reps rK147) (T147_114_2 i) (hfix147_114_2 i) h)

/-! ### Cell (147, 115) twin -/

def T147_115_2 : Fin 1 → Coordinate 2 := fun i => T147_115list.getD i.val (0,0,0,0,0)

theorem hfix147_115_2 : ∀ i, ((T147_115_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨115, by decide⟩ T147_115_2 (by decide)

theorem hinj147_115_2 : Function.Injective
    (fun i => ((T147_115_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_115_2 (by decide)

theorem hcardT147_115_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨115, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 115) twin (q=2).** -/
theorem cell147_115_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨115, by decide⟩ : Fin 148))) :
    species (reps (⟨115, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_115_2 i :=
  species_entry_eq_sum rK147 ⟨115, by decide⟩ e heK h T147_115_2 hfix147_115_2 hinj147_115_2 hcardT147_115_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨115, by decide⟩) (reps rK147) (T147_115_2 i) (hfix147_115_2 i) h)

/-! ### Cell (147, 116) twin -/

def T147_116_2 : Fin 1 → Coordinate 2 := fun i => T147_116list.getD i.val (0,0,0,0,0)

theorem hfix147_116_2 : ∀ i, ((T147_116_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨116, by decide⟩ T147_116_2 (by decide)

theorem hinj147_116_2 : Function.Injective
    (fun i => ((T147_116_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_116_2 (by decide)

theorem hcardT147_116_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨116, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 116) twin (q=2).** -/
theorem cell147_116_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨116, by decide⟩ : Fin 148))) :
    species (reps (⟨116, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_116_2 i :=
  species_entry_eq_sum rK147 ⟨116, by decide⟩ e heK h T147_116_2 hfix147_116_2 hinj147_116_2 hcardT147_116_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨116, by decide⟩) (reps rK147) (T147_116_2 i) (hfix147_116_2 i) h)

/-! ### Cell (147, 117) twin -/

def T147_117_2 : Fin 1 → Coordinate 2 := fun i => T147_117list.getD i.val (0,0,0,0,0)

theorem hfix147_117_2 : ∀ i, ((T147_117_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨117, by decide⟩ T147_117_2 (by decide)

theorem hinj147_117_2 : Function.Injective
    (fun i => ((T147_117_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_117_2 (by decide)

theorem hcardT147_117_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨117, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 117) twin (q=2).** -/
theorem cell147_117_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨117, by decide⟩ : Fin 148))) :
    species (reps (⟨117, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_117_2 i :=
  species_entry_eq_sum rK147 ⟨117, by decide⟩ e heK h T147_117_2 hfix147_117_2 hinj147_117_2 hcardT147_117_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨117, by decide⟩) (reps rK147) (T147_117_2 i) (hfix147_117_2 i) h)

/-! ### Cell (147, 118) twin -/

def T147_118_2 : Fin 1 → Coordinate 2 := fun i => T147_118list.getD i.val (0,0,0,0,0)

theorem hfix147_118_2 : ∀ i, ((T147_118_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨118, by decide⟩ T147_118_2 (by decide)

theorem hinj147_118_2 : Function.Injective
    (fun i => ((T147_118_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_118_2 (by decide)

theorem hcardT147_118_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨118, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 118) twin (q=2).** -/
theorem cell147_118_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨118, by decide⟩ : Fin 148))) :
    species (reps (⟨118, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_118_2 i :=
  species_entry_eq_sum rK147 ⟨118, by decide⟩ e heK h T147_118_2 hfix147_118_2 hinj147_118_2 hcardT147_118_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨118, by decide⟩) (reps rK147) (T147_118_2 i) (hfix147_118_2 i) h)

/-! ### Cell (147, 119) twin -/

def T147_119_2 : Fin 1 → Coordinate 2 := fun i => T147_119list.getD i.val (0,0,0,0,0)

theorem hfix147_119_2 : ∀ i, ((T147_119_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨119, by decide⟩ T147_119_2 (by decide)

theorem hinj147_119_2 : Function.Injective
    (fun i => ((T147_119_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_119_2 (by decide)

theorem hcardT147_119_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨119, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 119) twin (q=2).** -/
theorem cell147_119_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨119, by decide⟩ : Fin 148))) :
    species (reps (⟨119, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_119_2 i :=
  species_entry_eq_sum rK147 ⟨119, by decide⟩ e heK h T147_119_2 hfix147_119_2 hinj147_119_2 hcardT147_119_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨119, by decide⟩) (reps rK147) (T147_119_2 i) (hfix147_119_2 i) h)

/-! ### Cell (147, 120) twin -/

def T147_120_2 : Fin 1 → Coordinate 2 := fun i => T147_120list.getD i.val (0,0,0,0,0)

theorem hfix147_120_2 : ∀ i, ((T147_120_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨120, by decide⟩ T147_120_2 (by decide)

theorem hinj147_120_2 : Function.Injective
    (fun i => ((T147_120_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_120_2 (by decide)

theorem hcardT147_120_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨120, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 120) twin (q=2).** -/
theorem cell147_120_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨120, by decide⟩ : Fin 148))) :
    species (reps (⟨120, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_120_2 i :=
  species_entry_eq_sum rK147 ⟨120, by decide⟩ e heK h T147_120_2 hfix147_120_2 hinj147_120_2 hcardT147_120_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨120, by decide⟩) (reps rK147) (T147_120_2 i) (hfix147_120_2 i) h)

/-! ### Cell (147, 121) twin -/

def T147_121_2 : Fin 1 → Coordinate 2 := fun i => T147_121list.getD i.val (0,0,0,0,0)

theorem hfix147_121_2 : ∀ i, ((T147_121_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨121, by decide⟩ T147_121_2 (by decide)

theorem hinj147_121_2 : Function.Injective
    (fun i => ((T147_121_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_121_2 (by decide)

theorem hcardT147_121_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨121, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 121) twin (q=2).** -/
theorem cell147_121_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨121, by decide⟩ : Fin 148))) :
    species (reps (⟨121, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_121_2 i :=
  species_entry_eq_sum rK147 ⟨121, by decide⟩ e heK h T147_121_2 hfix147_121_2 hinj147_121_2 hcardT147_121_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨121, by decide⟩) (reps rK147) (T147_121_2 i) (hfix147_121_2 i) h)

/-! ### Cell (147, 122) twin -/

def T147_122_2 : Fin 1 → Coordinate 2 := fun i => T147_122list.getD i.val (0,0,0,0,0)

theorem hfix147_122_2 : ∀ i, ((T147_122_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨122, by decide⟩ T147_122_2 (by decide)

theorem hinj147_122_2 : Function.Injective
    (fun i => ((T147_122_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_122_2 (by decide)

theorem hcardT147_122_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨122, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 122) twin (q=2).** -/
theorem cell147_122_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨122, by decide⟩ : Fin 148))) :
    species (reps (⟨122, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_122_2 i :=
  species_entry_eq_sum rK147 ⟨122, by decide⟩ e heK h T147_122_2 hfix147_122_2 hinj147_122_2 hcardT147_122_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨122, by decide⟩) (reps rK147) (T147_122_2 i) (hfix147_122_2 i) h)

/-! ### Cell (147, 123) twin -/

def T147_123_2 : Fin 1 → Coordinate 2 := fun i => T147_123list.getD i.val (0,0,0,0,0)

theorem hfix147_123_2 : ∀ i, ((T147_123_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨123, by decide⟩ T147_123_2 (by decide)

theorem hinj147_123_2 : Function.Injective
    (fun i => ((T147_123_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_123_2 (by decide)

theorem hcardT147_123_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨123, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 123) twin (q=2).** -/
theorem cell147_123_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨123, by decide⟩ : Fin 148))) :
    species (reps (⟨123, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_123_2 i :=
  species_entry_eq_sum rK147 ⟨123, by decide⟩ e heK h T147_123_2 hfix147_123_2 hinj147_123_2 hcardT147_123_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨123, by decide⟩) (reps rK147) (T147_123_2 i) (hfix147_123_2 i) h)

/-! ### Cell (147, 124) twin -/

def T147_124_2 : Fin 1 → Coordinate 2 := fun i => T147_124list.getD i.val (0,0,0,0,0)

theorem hfix147_124_2 : ∀ i, ((T147_124_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨124, by decide⟩ T147_124_2 (by decide)

theorem hinj147_124_2 : Function.Injective
    (fun i => ((T147_124_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_124_2 (by decide)

theorem hcardT147_124_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨124, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 124) twin (q=2).** -/
theorem cell147_124_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨124, by decide⟩ : Fin 148))) :
    species (reps (⟨124, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_124_2 i :=
  species_entry_eq_sum rK147 ⟨124, by decide⟩ e heK h T147_124_2 hfix147_124_2 hinj147_124_2 hcardT147_124_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨124, by decide⟩) (reps rK147) (T147_124_2 i) (hfix147_124_2 i) h)

/-! ### Cell (147, 125) twin -/

def T147_125_2 : Fin 1 → Coordinate 2 := fun i => T147_125list.getD i.val (0,0,0,0,0)

theorem hfix147_125_2 : ∀ i, ((T147_125_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨125, by decide⟩ T147_125_2 (by decide)

theorem hinj147_125_2 : Function.Injective
    (fun i => ((T147_125_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_125_2 (by decide)

theorem hcardT147_125_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨125, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 125) twin (q=2).** -/
theorem cell147_125_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨125, by decide⟩ : Fin 148))) :
    species (reps (⟨125, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_125_2 i :=
  species_entry_eq_sum rK147 ⟨125, by decide⟩ e heK h T147_125_2 hfix147_125_2 hinj147_125_2 hcardT147_125_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨125, by decide⟩) (reps rK147) (T147_125_2 i) (hfix147_125_2 i) h)

/-! ### Cell (147, 126) twin -/

def T147_126_2 : Fin 1 → Coordinate 2 := fun i => T147_126list.getD i.val (0,0,0,0,0)

theorem hfix147_126_2 : ∀ i, ((T147_126_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨126, by decide⟩ T147_126_2 (by decide)

theorem hinj147_126_2 : Function.Injective
    (fun i => ((T147_126_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_126_2 (by decide)

theorem hcardT147_126_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨126, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 126) twin (q=2).** -/
theorem cell147_126_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨126, by decide⟩ : Fin 148))) :
    species (reps (⟨126, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_126_2 i :=
  species_entry_eq_sum rK147 ⟨126, by decide⟩ e heK h T147_126_2 hfix147_126_2 hinj147_126_2 hcardT147_126_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨126, by decide⟩) (reps rK147) (T147_126_2 i) (hfix147_126_2 i) h)

/-! ### Cell (147, 127) twin -/

def T147_127_2 : Fin 1 → Coordinate 2 := fun i => T147_127list.getD i.val (0,0,0,0,0)

theorem hfix147_127_2 : ∀ i, ((T147_127_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨127, by decide⟩ T147_127_2 (by decide)

theorem hinj147_127_2 : Function.Injective
    (fun i => ((T147_127_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_127_2 (by decide)

theorem hcardT147_127_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨127, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 127) twin (q=2).** -/
theorem cell147_127_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨127, by decide⟩ : Fin 148))) :
    species (reps (⟨127, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_127_2 i :=
  species_entry_eq_sum rK147 ⟨127, by decide⟩ e heK h T147_127_2 hfix147_127_2 hinj147_127_2 hcardT147_127_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨127, by decide⟩) (reps rK147) (T147_127_2 i) (hfix147_127_2 i) h)

/-! ### Cell (147, 128) twin -/

def T147_128_2 : Fin 1 → Coordinate 2 := fun i => T147_128list.getD i.val (0,0,0,0,0)

theorem hfix147_128_2 : ∀ i, ((T147_128_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨128, by decide⟩ T147_128_2 (by decide)

theorem hinj147_128_2 : Function.Injective
    (fun i => ((T147_128_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_128_2 (by decide)

theorem hcardT147_128_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨128, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 128) twin (q=2).** -/
theorem cell147_128_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨128, by decide⟩ : Fin 148))) :
    species (reps (⟨128, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_128_2 i :=
  species_entry_eq_sum rK147 ⟨128, by decide⟩ e heK h T147_128_2 hfix147_128_2 hinj147_128_2 hcardT147_128_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨128, by decide⟩) (reps rK147) (T147_128_2 i) (hfix147_128_2 i) h)

/-! ### Cell (147, 129) twin -/

def T147_129_2 : Fin 1 → Coordinate 2 := fun i => T147_129list.getD i.val (0,0,0,0,0)

theorem hfix147_129_2 : ∀ i, ((T147_129_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨129, by decide⟩ T147_129_2 (by decide)

theorem hinj147_129_2 : Function.Injective
    (fun i => ((T147_129_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_129_2 (by decide)

theorem hcardT147_129_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨129, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 129) twin (q=2).** -/
theorem cell147_129_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨129, by decide⟩ : Fin 148))) :
    species (reps (⟨129, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_129_2 i :=
  species_entry_eq_sum rK147 ⟨129, by decide⟩ e heK h T147_129_2 hfix147_129_2 hinj147_129_2 hcardT147_129_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨129, by decide⟩) (reps rK147) (T147_129_2 i) (hfix147_129_2 i) h)

/-! ### Cell (147, 130) twin -/

def T147_130_2 : Fin 1 → Coordinate 2 := fun i => T147_130list.getD i.val (0,0,0,0,0)

theorem hfix147_130_2 : ∀ i, ((T147_130_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨130, by decide⟩ T147_130_2 (by decide)

theorem hinj147_130_2 : Function.Injective
    (fun i => ((T147_130_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_130_2 (by decide)

theorem hcardT147_130_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨130, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 130) twin (q=2).** -/
theorem cell147_130_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨130, by decide⟩ : Fin 148))) :
    species (reps (⟨130, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_130_2 i :=
  species_entry_eq_sum rK147 ⟨130, by decide⟩ e heK h T147_130_2 hfix147_130_2 hinj147_130_2 hcardT147_130_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨130, by decide⟩) (reps rK147) (T147_130_2 i) (hfix147_130_2 i) h)

/-! ### Cell (147, 131) twin -/

def T147_131_2 : Fin 1 → Coordinate 2 := fun i => T147_131list.getD i.val (0,0,0,0,0)

theorem hfix147_131_2 : ∀ i, ((T147_131_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨131, by decide⟩ T147_131_2 (by decide)

theorem hinj147_131_2 : Function.Injective
    (fun i => ((T147_131_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_131_2 (by decide)

theorem hcardT147_131_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨131, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 131) twin (q=2).** -/
theorem cell147_131_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨131, by decide⟩ : Fin 148))) :
    species (reps (⟨131, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_131_2 i :=
  species_entry_eq_sum rK147 ⟨131, by decide⟩ e heK h T147_131_2 hfix147_131_2 hinj147_131_2 hcardT147_131_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨131, by decide⟩) (reps rK147) (T147_131_2 i) (hfix147_131_2 i) h)

/-! ### Cell (147, 132) twin -/

def T147_132_2 : Fin 1 → Coordinate 2 := fun i => T147_132list.getD i.val (0,0,0,0,0)

theorem hfix147_132_2 : ∀ i, ((T147_132_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨132, by decide⟩ T147_132_2 (by decide)

theorem hinj147_132_2 : Function.Injective
    (fun i => ((T147_132_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_132_2 (by decide)

theorem hcardT147_132_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨132, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 132) twin (q=2).** -/
theorem cell147_132_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨132, by decide⟩ : Fin 148))) :
    species (reps (⟨132, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_132_2 i :=
  species_entry_eq_sum rK147 ⟨132, by decide⟩ e heK h T147_132_2 hfix147_132_2 hinj147_132_2 hcardT147_132_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨132, by decide⟩) (reps rK147) (T147_132_2 i) (hfix147_132_2 i) h)

/-! ### Cell (147, 133) twin -/

def T147_133_2 : Fin 1 → Coordinate 2 := fun i => T147_133list.getD i.val (0,0,0,0,0)

theorem hfix147_133_2 : ∀ i, ((T147_133_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨133, by decide⟩ T147_133_2 (by decide)

theorem hinj147_133_2 : Function.Injective
    (fun i => ((T147_133_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_133_2 (by decide)

theorem hcardT147_133_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨133, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 133) twin (q=2).** -/
theorem cell147_133_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨133, by decide⟩ : Fin 148))) :
    species (reps (⟨133, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_133_2 i :=
  species_entry_eq_sum rK147 ⟨133, by decide⟩ e heK h T147_133_2 hfix147_133_2 hinj147_133_2 hcardT147_133_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨133, by decide⟩) (reps rK147) (T147_133_2 i) (hfix147_133_2 i) h)

/-! ### Cell (147, 134) twin -/

def T147_134_2 : Fin 1 → Coordinate 2 := fun i => T147_134list.getD i.val (0,0,0,0,0)

theorem hfix147_134_2 : ∀ i, ((T147_134_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨134, by decide⟩ T147_134_2 (by decide)

theorem hinj147_134_2 : Function.Injective
    (fun i => ((T147_134_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_134_2 (by decide)

theorem hcardT147_134_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨134, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 134) twin (q=2).** -/
theorem cell147_134_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨134, by decide⟩ : Fin 148))) :
    species (reps (⟨134, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_134_2 i :=
  species_entry_eq_sum rK147 ⟨134, by decide⟩ e heK h T147_134_2 hfix147_134_2 hinj147_134_2 hcardT147_134_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨134, by decide⟩) (reps rK147) (T147_134_2 i) (hfix147_134_2 i) h)

/-! ### Cell (147, 135) twin -/

def T147_135_2 : Fin 1 → Coordinate 2 := fun i => T147_135list.getD i.val (0,0,0,0,0)

theorem hfix147_135_2 : ∀ i, ((T147_135_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨135, by decide⟩ T147_135_2 (by decide)

theorem hinj147_135_2 : Function.Injective
    (fun i => ((T147_135_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_135_2 (by decide)

theorem hcardT147_135_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨135, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 135) twin (q=2).** -/
theorem cell147_135_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨135, by decide⟩ : Fin 148))) :
    species (reps (⟨135, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_135_2 i :=
  species_entry_eq_sum rK147 ⟨135, by decide⟩ e heK h T147_135_2 hfix147_135_2 hinj147_135_2 hcardT147_135_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨135, by decide⟩) (reps rK147) (T147_135_2 i) (hfix147_135_2 i) h)

/-! ### Cell (147, 136) twin -/

def T147_136_2 : Fin 1 → Coordinate 2 := fun i => T147_136list.getD i.val (0,0,0,0,0)

theorem hfix147_136_2 : ∀ i, ((T147_136_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨136, by decide⟩ T147_136_2 (by decide)

theorem hinj147_136_2 : Function.Injective
    (fun i => ((T147_136_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_136_2 (by decide)

theorem hcardT147_136_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨136, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 136) twin (q=2).** -/
theorem cell147_136_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨136, by decide⟩ : Fin 148))) :
    species (reps (⟨136, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_136_2 i :=
  species_entry_eq_sum rK147 ⟨136, by decide⟩ e heK h T147_136_2 hfix147_136_2 hinj147_136_2 hcardT147_136_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨136, by decide⟩) (reps rK147) (T147_136_2 i) (hfix147_136_2 i) h)

/-! ### Cell (147, 137) twin -/

def T147_137_2 : Fin 1 → Coordinate 2 := fun i => T147_137list.getD i.val (0,0,0,0,0)

theorem hfix147_137_2 : ∀ i, ((T147_137_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨137, by decide⟩ T147_137_2 (by decide)

theorem hinj147_137_2 : Function.Injective
    (fun i => ((T147_137_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_137_2 (by decide)

theorem hcardT147_137_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨137, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 137) twin (q=2).** -/
theorem cell147_137_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨137, by decide⟩ : Fin 148))) :
    species (reps (⟨137, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_137_2 i :=
  species_entry_eq_sum rK147 ⟨137, by decide⟩ e heK h T147_137_2 hfix147_137_2 hinj147_137_2 hcardT147_137_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨137, by decide⟩) (reps rK147) (T147_137_2 i) (hfix147_137_2 i) h)

/-! ### Cell (147, 138) twin -/

def T147_138_2 : Fin 1 → Coordinate 2 := fun i => T147_138list.getD i.val (0,0,0,0,0)

theorem hfix147_138_2 : ∀ i, ((T147_138_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨138, by decide⟩ T147_138_2 (by decide)

theorem hinj147_138_2 : Function.Injective
    (fun i => ((T147_138_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_138_2 (by decide)

theorem hcardT147_138_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨138, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 138) twin (q=2).** -/
theorem cell147_138_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨138, by decide⟩ : Fin 148))) :
    species (reps (⟨138, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_138_2 i :=
  species_entry_eq_sum rK147 ⟨138, by decide⟩ e heK h T147_138_2 hfix147_138_2 hinj147_138_2 hcardT147_138_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨138, by decide⟩) (reps rK147) (T147_138_2 i) (hfix147_138_2 i) h)

/-! ### Cell (147, 139) twin -/

def T147_139_2 : Fin 1 → Coordinate 2 := fun i => T147_139list.getD i.val (0,0,0,0,0)

theorem hfix147_139_2 : ∀ i, ((T147_139_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨139, by decide⟩ T147_139_2 (by decide)

theorem hinj147_139_2 : Function.Injective
    (fun i => ((T147_139_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_139_2 (by decide)

theorem hcardT147_139_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨139, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 139) twin (q=2).** -/
theorem cell147_139_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨139, by decide⟩ : Fin 148))) :
    species (reps (⟨139, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_139_2 i :=
  species_entry_eq_sum rK147 ⟨139, by decide⟩ e heK h T147_139_2 hfix147_139_2 hinj147_139_2 hcardT147_139_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨139, by decide⟩) (reps rK147) (T147_139_2 i) (hfix147_139_2 i) h)

/-! ### Cell (147, 140) twin -/

def T147_140_2 : Fin 1 → Coordinate 2 := fun i => T147_140list.getD i.val (0,0,0,0,0)

theorem hfix147_140_2 : ∀ i, ((T147_140_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨140, by decide⟩ T147_140_2 (by decide)

theorem hinj147_140_2 : Function.Injective
    (fun i => ((T147_140_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_140_2 (by decide)

theorem hcardT147_140_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨140, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 140) twin (q=2).** -/
theorem cell147_140_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨140, by decide⟩ : Fin 148))) :
    species (reps (⟨140, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_140_2 i :=
  species_entry_eq_sum rK147 ⟨140, by decide⟩ e heK h T147_140_2 hfix147_140_2 hinj147_140_2 hcardT147_140_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨140, by decide⟩) (reps rK147) (T147_140_2 i) (hfix147_140_2 i) h)

/-! ### Cell (147, 141) twin -/

def T147_141_2 : Fin 1 → Coordinate 2 := fun i => T147_141list.getD i.val (0,0,0,0,0)

theorem hfix147_141_2 : ∀ i, ((T147_141_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨141, by decide⟩ T147_141_2 (by decide)

theorem hinj147_141_2 : Function.Injective
    (fun i => ((T147_141_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_141_2 (by decide)

theorem hcardT147_141_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨141, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 141) twin (q=2).** -/
theorem cell147_141_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨141, by decide⟩ : Fin 148))) :
    species (reps (⟨141, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_141_2 i :=
  species_entry_eq_sum rK147 ⟨141, by decide⟩ e heK h T147_141_2 hfix147_141_2 hinj147_141_2 hcardT147_141_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨141, by decide⟩) (reps rK147) (T147_141_2 i) (hfix147_141_2 i) h)

/-! ### Cell (147, 142) twin -/

def T147_142_2 : Fin 1 → Coordinate 2 := fun i => T147_142list.getD i.val (0,0,0,0,0)

theorem hfix147_142_2 : ∀ i, ((T147_142_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨142, by decide⟩ T147_142_2 (by decide)

theorem hinj147_142_2 : Function.Injective
    (fun i => ((T147_142_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_142_2 (by decide)

theorem hcardT147_142_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨142, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 142) twin (q=2).** -/
theorem cell147_142_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨142, by decide⟩ : Fin 148))) :
    species (reps (⟨142, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_142_2 i :=
  species_entry_eq_sum rK147 ⟨142, by decide⟩ e heK h T147_142_2 hfix147_142_2 hinj147_142_2 hcardT147_142_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨142, by decide⟩) (reps rK147) (T147_142_2 i) (hfix147_142_2 i) h)

/-! ### Cell (147, 143) twin -/

def T147_143_2 : Fin 1 → Coordinate 2 := fun i => T147_143list.getD i.val (0,0,0,0,0)

theorem hfix147_143_2 : ∀ i, ((T147_143_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨143, by decide⟩ T147_143_2 (by decide)

theorem hinj147_143_2 : Function.Injective
    (fun i => ((T147_143_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_143_2 (by decide)

theorem hcardT147_143_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨143, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 143) twin (q=2).** -/
theorem cell147_143_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨143, by decide⟩ : Fin 148))) :
    species (reps (⟨143, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_143_2 i :=
  species_entry_eq_sum rK147 ⟨143, by decide⟩ e heK h T147_143_2 hfix147_143_2 hinj147_143_2 hcardT147_143_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨143, by decide⟩) (reps rK147) (T147_143_2 i) (hfix147_143_2 i) h)

/-! ### Cell (147, 144) twin -/

def T147_144_2 : Fin 1 → Coordinate 2 := fun i => T147_144list.getD i.val (0,0,0,0,0)

theorem hfix147_144_2 : ∀ i, ((T147_144_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨144, by decide⟩ T147_144_2 (by decide)

theorem hinj147_144_2 : Function.Injective
    (fun i => ((T147_144_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_144_2 (by decide)

theorem hcardT147_144_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨144, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 144) twin (q=2).** -/
theorem cell147_144_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨144, by decide⟩ : Fin 148))) :
    species (reps (⟨144, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_144_2 i :=
  species_entry_eq_sum rK147 ⟨144, by decide⟩ e heK h T147_144_2 hfix147_144_2 hinj147_144_2 hcardT147_144_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨144, by decide⟩) (reps rK147) (T147_144_2 i) (hfix147_144_2 i) h)

/-! ### Cell (147, 145) twin -/

def T147_145_2 : Fin 1 → Coordinate 2 := fun i => T147_145list.getD i.val (0,0,0,0,0)

theorem hfix147_145_2 : ∀ i, ((T147_145_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨145, by decide⟩ T147_145_2 (by decide)

theorem hinj147_145_2 : Function.Injective
    (fun i => ((T147_145_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_145_2 (by decide)

theorem hcardT147_145_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨145, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 145) twin (q=2).** -/
theorem cell147_145_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨145, by decide⟩ : Fin 148))) :
    species (reps (⟨145, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_145_2 i :=
  species_entry_eq_sum rK147 ⟨145, by decide⟩ e heK h T147_145_2 hfix147_145_2 hinj147_145_2 hcardT147_145_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨145, by decide⟩) (reps rK147) (T147_145_2 i) (hfix147_145_2 i) h)

/-! ### Cell (147, 146) twin -/

def T147_146_2 : Fin 1 → Coordinate 2 := fun i => T147_146list.getD i.val (0,0,0,0,0)

theorem hfix147_146_2 : ∀ i, ((T147_146_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨146, by decide⟩ T147_146_2 (by decide)

theorem hinj147_146_2 : Function.Injective
    (fun i => ((T147_146_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_146_2 (by decide)

theorem hcardT147_146_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨146, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 146) twin (q=2).** -/
theorem cell147_146_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨146, by decide⟩ : Fin 148))) :
    species (reps (⟨146, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_146_2 i :=
  species_entry_eq_sum rK147 ⟨146, by decide⟩ e heK h T147_146_2 hfix147_146_2 hinj147_146_2 hcardT147_146_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨146, by decide⟩) (reps rK147) (T147_146_2 i) (hfix147_146_2 i) h)

/-! ### Cell (147, 147) twin -/

def T147_147_2 : Fin 1 → Coordinate 2 := fun i => T147_147list.getD i.val (0,0,0,0,0)

theorem hfix147_147_2 : ∀ i, ((T147_147_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)
    ∈ fixedPoints (reps (⟨147, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147) :=
  repsFix_of_siftB2 rK147 ⟨147, by decide⟩ T147_147_2 (by decide)

theorem hinj147_147_2 : Function.Injective
    (fun i => ((T147_147_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK147)) :=
  repsInj_of_reduceAux2 rK147 T147_147_2 (by decide)

theorem hcardT147_147_2 : Fintype.card (Fin 1)
    = Fintype.card (fixedPoints (reps (⟨147, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK147)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK147 ⟨147, by decide⟩ R147_2 hpxR147_2 hcardq147_2 (by decide)).symm

/-- **Cell (147, 147) twin (q=2).** -/
theorem cell147_147_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK147) e = true)
    (h : ↥(reps (⟨147, by decide⟩ : Fin 148))) :
    species (reps (⟨147, by decide⟩ : Fin 148)) h (basisElt (reps rK147) (charOfVec2 rK147 e heK))
      = ∑ i : Fin 1, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK147 e (h : Coordinate 2) T147_147_2 i :=
  species_entry_eq_sum rK147 ⟨147, by decide⟩ e heK h T147_147_2 hfix147_147_2 hinj147_147_2 hcardT147_147_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨147, by decide⟩) (reps rK147) (T147_147_2 i) (hfix147_147_2 i) h)

end Q2

end LeanDring.P5Presentation
