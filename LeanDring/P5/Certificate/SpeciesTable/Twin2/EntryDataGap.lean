/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryA.C001
import LeanDring.P5.Data.EntryA.C002
import LeanDring.P5.Data.EntryA.C003

/-!
# Species-table cells, gap-fill: the 19 on-support cells the A-block pilot missed

The true on-support set is 1,523 `(rK,rH)` class pairs (= the nonzero entries of
the certified table of marks, cross-checked against stage 0); the emitted species-table cell
layer covers all but 19 of them, all with `rK ∈ {13,14,15}`.  Each cell here is
built exactly like the emitted ones: the `H`-fixed sub-transversal is a sub-list
of the class's certified full transversal `R<rK>list`, re-verified by `decide`
through the `LeanDring/P5/Certificate/SpeciesTable/EntryTransA.lean` adapters, in both twins (the transversal data
coincides, as everywhere else).

Emitted by `python/p5_gapfill_emit.py`.
-/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! ## Cell (13, 6): |T| = 25 -/

def T13_6list : List Coordinates := [(0,0,0,0,4), (0,0,0,0,0), (0,0,0,0,1), (0,0,0,0,2), (0,0,0,0,3), (1,3,0,0,4), (1,3,0,0,0), (1,3,0,0,1), (1,3,0,0,2), (1,3,0,0,3), (2,1,0,0,4), (2,1,0,0,0), (2,1,0,0,1), (2,1,0,0,2), (2,1,0,0,3), (3,4,0,0,4), (3,4,0,0,0), (3,4,0,0,1), (3,4,0,0,2), (3,4,0,0,3), (4,2,0,0,4), (4,2,0,0,0), (4,2,0,0,1), (4,2,0,0,2), (4,2,0,0,3)]
def T13_6 : Fin 25 → Coordinate 1 := fun i => T13_6list.getD i.val (0,0,0,0,0)

theorem hfix13_6 : ∀ i, ((T13_6 i : Coordinate 1) : Coordinate 1 ⧸ reps rK13)
    ∈ fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13) :=
  repsFix_of_siftB rK13 ⟨6, by decide⟩ T13_6 (by decide)

theorem hinj13_6 : Function.Injective
    (fun i => ((T13_6 i : Coordinate 1) : Coordinate 1 ⧸ reps rK13)) :=
  repsInj_of_reduceAux rK13 T13_6 (by decide)

theorem hcardT13_6 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK13 ⟨6, by decide⟩ R13 hpxR13 hcardq13 (by decide)).symm

/-- **Cell (13, 6).** -/
theorem cell13_6 (e : List (ZMod 25)) (heK : charOK (basisAt rK13) e = true)
    (h : ↥(reps (⟨6, by decide⟩ : Fin 148))) :
    species (reps (⟨6, by decide⟩ : Fin 148)) h (basisElt (reps rK13) (charOfVec rK13 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK13 e (h : Coordinate 1) T13_6 i :=
  species_entry_eq_sum rK13 ⟨6, by decide⟩ e heK h T13_6 hfix13_6 hinj13_6 hcardT13_6
    (fun i => conj_mem_of_fixedPoints (reps ⟨6, by decide⟩) (reps rK13) (T13_6 i) (hfix13_6 i) h)

/-! ## Cell (13, 7): |T| = 25 -/

def T13_7list : List Coordinates := [(0,0,0,0,4), (0,0,0,0,0), (0,0,0,0,1), (0,0,0,0,2), (0,0,0,0,3), (1,2,0,0,4), (1,2,0,0,0), (1,2,0,0,1), (1,2,0,0,2), (1,2,0,0,3), (2,4,0,0,4), (2,4,0,0,0), (2,4,0,0,1), (2,4,0,0,2), (2,4,0,0,3), (3,1,0,0,4), (3,1,0,0,0), (3,1,0,0,1), (3,1,0,0,2), (3,1,0,0,3), (4,3,0,0,4), (4,3,0,0,0), (4,3,0,0,1), (4,3,0,0,2), (4,3,0,0,3)]
def T13_7 : Fin 25 → Coordinate 1 := fun i => T13_7list.getD i.val (0,0,0,0,0)

theorem hfix13_7 : ∀ i, ((T13_7 i : Coordinate 1) : Coordinate 1 ⧸ reps rK13)
    ∈ fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13) :=
  repsFix_of_siftB rK13 ⟨7, by decide⟩ T13_7 (by decide)

theorem hinj13_7 : Function.Injective
    (fun i => ((T13_7 i : Coordinate 1) : Coordinate 1 ⧸ reps rK13)) :=
  repsInj_of_reduceAux rK13 T13_7 (by decide)

theorem hcardT13_7 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK13 ⟨7, by decide⟩ R13 hpxR13 hcardq13 (by decide)).symm

/-- **Cell (13, 7).** -/
theorem cell13_7 (e : List (ZMod 25)) (heK : charOK (basisAt rK13) e = true)
    (h : ↥(reps (⟨7, by decide⟩ : Fin 148))) :
    species (reps (⟨7, by decide⟩ : Fin 148)) h (basisElt (reps rK13) (charOfVec rK13 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK13 e (h : Coordinate 1) T13_7 i :=
  species_entry_eq_sum rK13 ⟨7, by decide⟩ e heK h T13_7 hfix13_7 hinj13_7 hcardT13_7
    (fun i => conj_mem_of_fixedPoints (reps ⟨7, by decide⟩) (reps rK13) (T13_7 i) (hfix13_7 i) h)

/-! ## Cell (13, 8): |T| = 25 -/

def T13_8list : List Coordinates := [(0,0,0,0,4), (0,0,0,0,0), (0,0,0,0,1), (0,0,0,0,2), (0,0,0,0,3), (1,4,0,0,4), (1,4,0,0,0), (1,4,0,0,1), (1,4,0,0,2), (1,4,0,0,3), (2,3,0,0,4), (2,3,0,0,0), (2,3,0,0,1), (2,3,0,0,2), (2,3,0,0,3), (3,2,0,0,4), (3,2,0,0,0), (3,2,0,0,1), (3,2,0,0,2), (3,2,0,0,3), (4,1,0,0,4), (4,1,0,0,0), (4,1,0,0,1), (4,1,0,0,2), (4,1,0,0,3)]
def T13_8 : Fin 25 → Coordinate 1 := fun i => T13_8list.getD i.val (0,0,0,0,0)

theorem hfix13_8 : ∀ i, ((T13_8 i : Coordinate 1) : Coordinate 1 ⧸ reps rK13)
    ∈ fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13) :=
  repsFix_of_siftB rK13 ⟨8, by decide⟩ T13_8 (by decide)

theorem hinj13_8 : Function.Injective
    (fun i => ((T13_8 i : Coordinate 1) : Coordinate 1 ⧸ reps rK13)) :=
  repsInj_of_reduceAux rK13 T13_8 (by decide)

theorem hcardT13_8 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK13 ⟨8, by decide⟩ R13 hpxR13 hcardq13 (by decide)).symm

/-- **Cell (13, 8).** -/
theorem cell13_8 (e : List (ZMod 25)) (heK : charOK (basisAt rK13) e = true)
    (h : ↥(reps (⟨8, by decide⟩ : Fin 148))) :
    species (reps (⟨8, by decide⟩ : Fin 148)) h (basisElt (reps rK13) (charOfVec rK13 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK13 e (h : Coordinate 1) T13_8 i :=
  species_entry_eq_sum rK13 ⟨8, by decide⟩ e heK h T13_8 hfix13_8 hinj13_8 hcardT13_8
    (fun i => conj_mem_of_fixedPoints (reps ⟨8, by decide⟩) (reps rK13) (T13_8 i) (hfix13_8 i) h)

/-! ## Cell (13, 9): |T| = 25 -/

def T13_9list : List Coordinates := [(0,0,0,0,4), (0,0,0,0,0), (0,0,0,0,1), (0,0,0,0,2), (0,0,0,0,3), (1,0,0,0,4), (1,0,0,0,0), (1,0,0,0,1), (1,0,0,0,2), (1,0,0,0,3), (2,0,0,0,4), (2,0,0,0,0), (2,0,0,0,1), (2,0,0,0,2), (2,0,0,0,3), (3,0,0,0,4), (3,0,0,0,0), (3,0,0,0,1), (3,0,0,0,2), (3,0,0,0,3), (4,0,0,0,4), (4,0,0,0,0), (4,0,0,0,1), (4,0,0,0,2), (4,0,0,0,3)]
def T13_9 : Fin 25 → Coordinate 1 := fun i => T13_9list.getD i.val (0,0,0,0,0)

theorem hfix13_9 : ∀ i, ((T13_9 i : Coordinate 1) : Coordinate 1 ⧸ reps rK13)
    ∈ fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13) :=
  repsFix_of_siftB rK13 ⟨9, by decide⟩ T13_9 (by decide)

theorem hinj13_9 : Function.Injective
    (fun i => ((T13_9 i : Coordinate 1) : Coordinate 1 ⧸ reps rK13)) :=
  repsInj_of_reduceAux rK13 T13_9 (by decide)

theorem hcardT13_9 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK13 ⟨9, by decide⟩ R13 hpxR13 hcardq13 (by decide)).symm

/-- **Cell (13, 9).** -/
theorem cell13_9 (e : List (ZMod 25)) (heK : charOK (basisAt rK13) e = true)
    (h : ↥(reps (⟨9, by decide⟩ : Fin 148))) :
    species (reps (⟨9, by decide⟩ : Fin 148)) h (basisElt (reps rK13) (charOfVec rK13 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK13 e (h : Coordinate 1) T13_9 i :=
  species_entry_eq_sum rK13 ⟨9, by decide⟩ e heK h T13_9 hfix13_9 hinj13_9 hcardT13_9
    (fun i => conj_mem_of_fixedPoints (reps ⟨9, by decide⟩) (reps rK13) (T13_9 i) (hfix13_9 i) h)

/-! ## Cell (13, 10): |T| = 25 -/

def T13_10list : List Coordinates := [(1,0,0,0,4), (1,0,0,0,0), (1,0,0,0,1), (1,0,0,0,2), (1,0,0,0,3), (1,1,0,0,4), (1,1,0,0,0), (1,1,0,0,1), (1,1,0,0,2), (1,1,0,0,3), (1,2,0,0,4), (1,2,0,0,0), (1,2,0,0,1), (1,2,0,0,2), (1,2,0,0,3), (1,3,0,0,4), (1,3,0,0,0), (1,3,0,0,1), (1,3,0,0,2), (1,3,0,0,3), (1,4,0,0,4), (1,4,0,0,0), (1,4,0,0,1), (1,4,0,0,2), (1,4,0,0,3)]
def T13_10 : Fin 25 → Coordinate 1 := fun i => T13_10list.getD i.val (0,0,0,0,0)

theorem hfix13_10 : ∀ i, ((T13_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK13)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13) :=
  repsFix_of_siftB rK13 ⟨10, by decide⟩ T13_10 (by decide)

theorem hinj13_10 : Function.Injective
    (fun i => ((T13_10 i : Coordinate 1) : Coordinate 1 ⧸ reps rK13)) :=
  repsInj_of_reduceAux rK13 T13_10 (by decide)

theorem hcardT13_10 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK13 ⟨10, by decide⟩ R13 hpxR13 hcardq13 (by decide)).symm

/-- **Cell (13, 10).** -/
theorem cell13_10 (e : List (ZMod 25)) (heK : charOK (basisAt rK13) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK13) (charOfVec rK13 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK13 e (h : Coordinate 1) T13_10 i :=
  species_entry_eq_sum rK13 ⟨10, by decide⟩ e heK h T13_10 hfix13_10 hinj13_10 hcardT13_10
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK13) (T13_10 i) (hfix13_10 i) h)

/-! ## Cell (14, 2): |T| = 5 -/

def T14_2list : List Coordinates := [(0,2,0,0,2), (0,2,0,0,3), (0,2,0,0,4), (0,2,0,0,0), (0,2,0,0,1)]
def T14_2 : Fin 5 → Coordinate 1 := fun i => T14_2list.getD i.val (0,0,0,0,0)

theorem hfix14_2 : ∀ i, ((T14_2 i : Coordinate 1) : Coordinate 1 ⧸ reps rK14)
    ∈ fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14) :=
  repsFix_of_siftB rK14 ⟨2, by decide⟩ T14_2 (by decide)

theorem hinj14_2 : Function.Injective
    (fun i => ((T14_2 i : Coordinate 1) : Coordinate 1 ⧸ reps rK14)) :=
  repsInj_of_reduceAux rK14 T14_2 (by decide)

theorem hcardT14_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK14 ⟨2, by decide⟩ R14 hpxR14 hcardq14 (by decide)).symm

/-- **Cell (14, 2).** -/
theorem cell14_2 (e : List (ZMod 25)) (heK : charOK (basisAt rK14) e = true)
    (h : ↥(reps (⟨2, by decide⟩ : Fin 148))) :
    species (reps (⟨2, by decide⟩ : Fin 148)) h (basisElt (reps rK14) (charOfVec rK14 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK14 e (h : Coordinate 1) T14_2 i :=
  species_entry_eq_sum rK14 ⟨2, by decide⟩ e heK h T14_2 hfix14_2 hinj14_2 hcardT14_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨2, by decide⟩) (reps rK14) (T14_2 i) (hfix14_2 i) h)

/-! ## Cell (14, 3): |T| = 5 -/

def T14_3list : List Coordinates := [(0,4,0,1,1), (0,4,0,1,2), (0,4,0,1,3), (0,4,0,1,4), (0,4,0,1,0)]
def T14_3 : Fin 5 → Coordinate 1 := fun i => T14_3list.getD i.val (0,0,0,0,0)

theorem hfix14_3 : ∀ i, ((T14_3 i : Coordinate 1) : Coordinate 1 ⧸ reps rK14)
    ∈ fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14) :=
  repsFix_of_siftB rK14 ⟨3, by decide⟩ T14_3 (by decide)

theorem hinj14_3 : Function.Injective
    (fun i => ((T14_3 i : Coordinate 1) : Coordinate 1 ⧸ reps rK14)) :=
  repsInj_of_reduceAux rK14 T14_3 (by decide)

theorem hcardT14_3 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK14 ⟨3, by decide⟩ R14 hpxR14 hcardq14 (by decide)).symm

/-- **Cell (14, 3).** -/
theorem cell14_3 (e : List (ZMod 25)) (heK : charOK (basisAt rK14) e = true)
    (h : ↥(reps (⟨3, by decide⟩ : Fin 148))) :
    species (reps (⟨3, by decide⟩ : Fin 148)) h (basisElt (reps rK14) (charOfVec rK14 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK14 e (h : Coordinate 1) T14_3 i :=
  species_entry_eq_sum rK14 ⟨3, by decide⟩ e heK h T14_3 hfix14_3 hinj14_3 hcardT14_3
    (fun i => conj_mem_of_fixedPoints (reps ⟨3, by decide⟩) (reps rK14) (T14_3 i) (hfix14_3 i) h)

/-! ## Cell (14, 4): |T| = 5 -/

def T14_4list : List Coordinates := [(0,3,0,4,0), (0,3,0,4,1), (0,3,0,4,2), (0,3,0,4,3), (0,3,0,4,4)]
def T14_4 : Fin 5 → Coordinate 1 := fun i => T14_4list.getD i.val (0,0,0,0,0)

theorem hfix14_4 : ∀ i, ((T14_4 i : Coordinate 1) : Coordinate 1 ⧸ reps rK14)
    ∈ fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14) :=
  repsFix_of_siftB rK14 ⟨4, by decide⟩ T14_4 (by decide)

theorem hinj14_4 : Function.Injective
    (fun i => ((T14_4 i : Coordinate 1) : Coordinate 1 ⧸ reps rK14)) :=
  repsInj_of_reduceAux rK14 T14_4 (by decide)

theorem hcardT14_4 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK14 ⟨4, by decide⟩ R14 hpxR14 hcardq14 (by decide)).symm

/-- **Cell (14, 4).** -/
theorem cell14_4 (e : List (ZMod 25)) (heK : charOK (basisAt rK14) e = true)
    (h : ↥(reps (⟨4, by decide⟩ : Fin 148))) :
    species (reps (⟨4, by decide⟩ : Fin 148)) h (basisElt (reps rK14) (charOfVec rK14 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK14 e (h : Coordinate 1) T14_4 i :=
  species_entry_eq_sum rK14 ⟨4, by decide⟩ e heK h T14_4 hfix14_4 hinj14_4 hcardT14_4
    (fun i => conj_mem_of_fixedPoints (reps ⟨4, by decide⟩) (reps rK14) (T14_4 i) (hfix14_4 i) h)

/-! ## Cell (14, 5): |T| = 5 -/

def T14_5list : List Coordinates := [(0,0,0,1,0), (0,0,0,1,1), (0,0,0,1,2), (0,0,0,1,3), (0,0,0,1,4)]
def T14_5 : Fin 5 → Coordinate 1 := fun i => T14_5list.getD i.val (0,0,0,0,0)

theorem hfix14_5 : ∀ i, ((T14_5 i : Coordinate 1) : Coordinate 1 ⧸ reps rK14)
    ∈ fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14) :=
  repsFix_of_siftB rK14 ⟨5, by decide⟩ T14_5 (by decide)

theorem hinj14_5 : Function.Injective
    (fun i => ((T14_5 i : Coordinate 1) : Coordinate 1 ⧸ reps rK14)) :=
  repsInj_of_reduceAux rK14 T14_5 (by decide)

theorem hcardT14_5 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK14 ⟨5, by decide⟩ R14 hpxR14 hcardq14 (by decide)).symm

/-- **Cell (14, 5).** -/
theorem cell14_5 (e : List (ZMod 25)) (heK : charOK (basisAt rK14) e = true)
    (h : ↥(reps (⟨5, by decide⟩ : Fin 148))) :
    species (reps (⟨5, by decide⟩ : Fin 148)) h (basisElt (reps rK14) (charOfVec rK14 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK14 e (h : Coordinate 1) T14_5 i :=
  species_entry_eq_sum rK14 ⟨5, by decide⟩ e heK h T14_5 hfix14_5 hinj14_5 hcardT14_5
    (fun i => conj_mem_of_fixedPoints (reps ⟨5, by decide⟩) (reps rK14) (T14_5 i) (hfix14_5 i) h)

/-! ## Cell (14, 9): |T| = 25 -/

def T14_9list : List Coordinates := [(0,1,0,0,3), (0,1,0,0,4), (0,1,0,0,0), (0,1,0,0,1), (0,1,0,0,2), (0,1,0,1,4), (0,1,0,1,0), (0,1,0,1,1), (0,1,0,1,2), (0,1,0,1,3), (0,1,0,2,0), (0,1,0,2,1), (0,1,0,2,2), (0,1,0,2,3), (0,1,0,2,4), (0,1,0,3,1), (0,1,0,3,2), (0,1,0,3,3), (0,1,0,3,4), (0,1,0,3,0), (0,1,0,4,2), (0,1,0,4,3), (0,1,0,4,4), (0,1,0,4,0), (0,1,0,4,1)]
def T14_9 : Fin 25 → Coordinate 1 := fun i => T14_9list.getD i.val (0,0,0,0,0)

theorem hfix14_9 : ∀ i, ((T14_9 i : Coordinate 1) : Coordinate 1 ⧸ reps rK14)
    ∈ fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14) :=
  repsFix_of_siftB rK14 ⟨9, by decide⟩ T14_9 (by decide)

theorem hinj14_9 : Function.Injective
    (fun i => ((T14_9 i : Coordinate 1) : Coordinate 1 ⧸ reps rK14)) :=
  repsInj_of_reduceAux rK14 T14_9 (by decide)

theorem hcardT14_9 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK14 ⟨9, by decide⟩ R14 hpxR14 hcardq14 (by decide)).symm

/-- **Cell (14, 9).** -/
theorem cell14_9 (e : List (ZMod 25)) (heK : charOK (basisAt rK14) e = true)
    (h : ↥(reps (⟨9, by decide⟩ : Fin 148))) :
    species (reps (⟨9, by decide⟩ : Fin 148)) h (basisElt (reps rK14) (charOfVec rK14 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK14 e (h : Coordinate 1) T14_9 i :=
  species_entry_eq_sum rK14 ⟨9, by decide⟩ e heK h T14_9 hfix14_9 hinj14_9 hcardT14_9
    (fun i => conj_mem_of_fixedPoints (reps ⟨9, by decide⟩) (reps rK14) (T14_9 i) (hfix14_9 i) h)

/-! ## Cell (14, 11): |T| = 5 -/

def T14_11list : List Coordinates := [(0,0,0,0,4), (0,0,0,0,0), (0,0,0,0,1), (0,0,0,0,2), (0,0,0,0,3)]
def T14_11 : Fin 5 → Coordinate 1 := fun i => T14_11list.getD i.val (0,0,0,0,0)

theorem hfix14_11 : ∀ i, ((T14_11 i : Coordinate 1) : Coordinate 1 ⧸ reps rK14)
    ∈ fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14) :=
  repsFix_of_siftB rK14 ⟨11, by decide⟩ T14_11 (by decide)

theorem hinj14_11 : Function.Injective
    (fun i => ((T14_11 i : Coordinate 1) : Coordinate 1 ⧸ reps rK14)) :=
  repsInj_of_reduceAux rK14 T14_11 (by decide)

theorem hcardT14_11 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK14 ⟨11, by decide⟩ R14 hpxR14 hcardq14 (by decide)).symm

/-- **Cell (14, 11).** -/
theorem cell14_11 (e : List (ZMod 25)) (heK : charOK (basisAt rK14) e = true)
    (h : ↥(reps (⟨11, by decide⟩ : Fin 148))) :
    species (reps (⟨11, by decide⟩ : Fin 148)) h (basisElt (reps rK14) (charOfVec rK14 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK14 e (h : Coordinate 1) T14_11 i :=
  species_entry_eq_sum rK14 ⟨11, by decide⟩ e heK h T14_11 hfix14_11 hinj14_11 hcardT14_11
    (fun i => conj_mem_of_fixedPoints (reps ⟨11, by decide⟩) (reps rK14) (T14_11 i) (hfix14_11 i) h)

/-! ## Cell (14, 14): |T| = 5 -/

def T14_14list : List Coordinates := [(0,0,0,0,4), (0,0,0,0,0), (0,0,0,0,1), (0,0,0,0,2), (0,0,0,0,3)]
def T14_14 : Fin 5 → Coordinate 1 := fun i => T14_14list.getD i.val (0,0,0,0,0)

theorem hfix14_14 : ∀ i, ((T14_14 i : Coordinate 1) : Coordinate 1 ⧸ reps rK14)
    ∈ fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14) :=
  repsFix_of_siftB rK14 ⟨14, by decide⟩ T14_14 (by decide)

theorem hinj14_14 : Function.Injective
    (fun i => ((T14_14 i : Coordinate 1) : Coordinate 1 ⧸ reps rK14)) :=
  repsInj_of_reduceAux rK14 T14_14 (by decide)

theorem hcardT14_14 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK14 ⟨14, by decide⟩ R14 hpxR14 hcardq14 (by decide)).symm

/-- **Cell (14, 14).** -/
theorem cell14_14 (e : List (ZMod 25)) (heK : charOK (basisAt rK14) e = true)
    (h : ↥(reps (⟨14, by decide⟩ : Fin 148))) :
    species (reps (⟨14, by decide⟩ : Fin 148)) h (basisElt (reps rK14) (charOfVec rK14 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK14 e (h : Coordinate 1) T14_14 i :=
  species_entry_eq_sum rK14 ⟨14, by decide⟩ e heK h T14_14 hfix14_14 hinj14_14 hcardT14_14
    (fun i => conj_mem_of_fixedPoints (reps ⟨14, by decide⟩) (reps rK14) (T14_14 i) (hfix14_14 i) h)

/-! ## Cell (15, 2): |T| = 5 -/

def T15_2list : List Coordinates := [(0,2,0,4,0), (0,2,0,4,1), (0,2,0,4,2), (0,2,0,4,3), (0,2,0,4,4)]
def T15_2 : Fin 5 → Coordinate 1 := fun i => T15_2list.getD i.val (0,0,0,0,0)

theorem hfix15_2 : ∀ i, ((T15_2 i : Coordinate 1) : Coordinate 1 ⧸ reps rK15)
    ∈ fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15) :=
  repsFix_of_siftB rK15 ⟨2, by decide⟩ T15_2 (by decide)

theorem hinj15_2 : Function.Injective
    (fun i => ((T15_2 i : Coordinate 1) : Coordinate 1 ⧸ reps rK15)) :=
  repsInj_of_reduceAux rK15 T15_2 (by decide)

theorem hcardT15_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK15 ⟨2, by decide⟩ R15 hpxR15 hcardq15 (by decide)).symm

/-- **Cell (15, 2).** -/
theorem cell15_2 (e : List (ZMod 25)) (heK : charOK (basisAt rK15) e = true)
    (h : ↥(reps (⟨2, by decide⟩ : Fin 148))) :
    species (reps (⟨2, by decide⟩ : Fin 148)) h (basisElt (reps rK15) (charOfVec rK15 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK15 e (h : Coordinate 1) T15_2 i :=
  species_entry_eq_sum rK15 ⟨2, by decide⟩ e heK h T15_2 hfix15_2 hinj15_2 hcardT15_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨2, by decide⟩) (reps rK15) (T15_2 i) (hfix15_2 i) h)

/-! ## Cell (15, 3): |T| = 5 -/

def T15_3list : List Coordinates := [(0,4,0,3,2), (0,4,0,3,3), (0,4,0,3,4), (0,4,0,3,0), (0,4,0,3,1)]
def T15_3 : Fin 5 → Coordinate 1 := fun i => T15_3list.getD i.val (0,0,0,0,0)

theorem hfix15_3 : ∀ i, ((T15_3 i : Coordinate 1) : Coordinate 1 ⧸ reps rK15)
    ∈ fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15) :=
  repsFix_of_siftB rK15 ⟨3, by decide⟩ T15_3 (by decide)

theorem hinj15_3 : Function.Injective
    (fun i => ((T15_3 i : Coordinate 1) : Coordinate 1 ⧸ reps rK15)) :=
  repsInj_of_reduceAux rK15 T15_3 (by decide)

theorem hcardT15_3 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK15 ⟨3, by decide⟩ R15 hpxR15 hcardq15 (by decide)).symm

/-- **Cell (15, 3).** -/
theorem cell15_3 (e : List (ZMod 25)) (heK : charOK (basisAt rK15) e = true)
    (h : ↥(reps (⟨3, by decide⟩ : Fin 148))) :
    species (reps (⟨3, by decide⟩ : Fin 148)) h (basisElt (reps rK15) (charOfVec rK15 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK15 e (h : Coordinate 1) T15_3 i :=
  species_entry_eq_sum rK15 ⟨3, by decide⟩ e heK h T15_3 hfix15_3 hinj15_3 hcardT15_3
    (fun i => conj_mem_of_fixedPoints (reps ⟨3, by decide⟩) (reps rK15) (T15_3 i) (hfix15_3 i) h)

/-! ## Cell (15, 4): |T| = 5 -/

def T15_4list : List Coordinates := [(0,3,0,2,2), (0,3,0,2,3), (0,3,0,2,4), (0,3,0,2,0), (0,3,0,2,1)]
def T15_4 : Fin 5 → Coordinate 1 := fun i => T15_4list.getD i.val (0,0,0,0,0)

theorem hfix15_4 : ∀ i, ((T15_4 i : Coordinate 1) : Coordinate 1 ⧸ reps rK15)
    ∈ fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15) :=
  repsFix_of_siftB rK15 ⟨4, by decide⟩ T15_4 (by decide)

theorem hinj15_4 : Function.Injective
    (fun i => ((T15_4 i : Coordinate 1) : Coordinate 1 ⧸ reps rK15)) :=
  repsInj_of_reduceAux rK15 T15_4 (by decide)

theorem hcardT15_4 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK15 ⟨4, by decide⟩ R15 hpxR15 hcardq15 (by decide)).symm

/-- **Cell (15, 4).** -/
theorem cell15_4 (e : List (ZMod 25)) (heK : charOK (basisAt rK15) e = true)
    (h : ↥(reps (⟨4, by decide⟩ : Fin 148))) :
    species (reps (⟨4, by decide⟩ : Fin 148)) h (basisElt (reps rK15) (charOfVec rK15 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK15 e (h : Coordinate 1) T15_4 i :=
  species_entry_eq_sum rK15 ⟨4, by decide⟩ e heK h T15_4 hfix15_4 hinj15_4 hcardT15_4
    (fun i => conj_mem_of_fixedPoints (reps ⟨4, by decide⟩) (reps rK15) (T15_4 i) (hfix15_4 i) h)

/-! ## Cell (15, 5): |T| = 5 -/

def T15_5list : List Coordinates := [(0,0,0,2,0), (0,0,0,2,1), (0,0,0,2,2), (0,0,0,2,3), (0,0,0,2,4)]
def T15_5 : Fin 5 → Coordinate 1 := fun i => T15_5list.getD i.val (0,0,0,0,0)

theorem hfix15_5 : ∀ i, ((T15_5 i : Coordinate 1) : Coordinate 1 ⧸ reps rK15)
    ∈ fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15) :=
  repsFix_of_siftB rK15 ⟨5, by decide⟩ T15_5 (by decide)

theorem hinj15_5 : Function.Injective
    (fun i => ((T15_5 i : Coordinate 1) : Coordinate 1 ⧸ reps rK15)) :=
  repsInj_of_reduceAux rK15 T15_5 (by decide)

theorem hcardT15_5 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK15 ⟨5, by decide⟩ R15 hpxR15 hcardq15 (by decide)).symm

/-- **Cell (15, 5).** -/
theorem cell15_5 (e : List (ZMod 25)) (heK : charOK (basisAt rK15) e = true)
    (h : ↥(reps (⟨5, by decide⟩ : Fin 148))) :
    species (reps (⟨5, by decide⟩ : Fin 148)) h (basisElt (reps rK15) (charOfVec rK15 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK15 e (h : Coordinate 1) T15_5 i :=
  species_entry_eq_sum rK15 ⟨5, by decide⟩ e heK h T15_5 hfix15_5 hinj15_5 hcardT15_5
    (fun i => conj_mem_of_fixedPoints (reps ⟨5, by decide⟩) (reps rK15) (T15_5 i) (hfix15_5 i) h)

/-! ## Cell (15, 9): |T| = 25 -/

def T15_9list : List Coordinates := [(0,0,0,4,2), (0,0,0,4,3), (0,0,0,4,4), (0,0,0,4,0), (0,0,0,4,1), (0,0,0,0,3), (0,0,0,0,4), (0,0,0,0,0), (0,0,0,0,1), (0,0,0,0,2), (0,0,0,1,4), (0,0,0,1,0), (0,0,0,1,1), (0,0,0,1,2), (0,0,0,1,3), (0,0,0,2,0), (0,0,0,2,1), (0,0,0,2,2), (0,0,0,2,3), (0,0,0,2,4), (0,0,0,3,1), (0,0,0,3,2), (0,0,0,3,3), (0,0,0,3,4), (0,0,0,3,0)]
def T15_9 : Fin 25 → Coordinate 1 := fun i => T15_9list.getD i.val (0,0,0,0,0)

theorem hfix15_9 : ∀ i, ((T15_9 i : Coordinate 1) : Coordinate 1 ⧸ reps rK15)
    ∈ fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15) :=
  repsFix_of_siftB rK15 ⟨9, by decide⟩ T15_9 (by decide)

theorem hinj15_9 : Function.Injective
    (fun i => ((T15_9 i : Coordinate 1) : Coordinate 1 ⧸ reps rK15)) :=
  repsInj_of_reduceAux rK15 T15_9 (by decide)

theorem hcardT15_9 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK15 ⟨9, by decide⟩ R15 hpxR15 hcardq15 (by decide)).symm

/-- **Cell (15, 9).** -/
theorem cell15_9 (e : List (ZMod 25)) (heK : charOK (basisAt rK15) e = true)
    (h : ↥(reps (⟨9, by decide⟩ : Fin 148))) :
    species (reps (⟨9, by decide⟩ : Fin 148)) h (basisElt (reps rK15) (charOfVec rK15 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK15 e (h : Coordinate 1) T15_9 i :=
  species_entry_eq_sum rK15 ⟨9, by decide⟩ e heK h T15_9 hfix15_9 hinj15_9 hcardT15_9
    (fun i => conj_mem_of_fixedPoints (reps ⟨9, by decide⟩) (reps rK15) (T15_9 i) (hfix15_9 i) h)

/-! ## Cell (15, 11): |T| = 5 -/

def T15_11list : List Coordinates := [(0,0,0,0,3), (0,0,0,0,4), (0,0,0,0,0), (0,0,0,0,1), (0,0,0,0,2)]
def T15_11 : Fin 5 → Coordinate 1 := fun i => T15_11list.getD i.val (0,0,0,0,0)

theorem hfix15_11 : ∀ i, ((T15_11 i : Coordinate 1) : Coordinate 1 ⧸ reps rK15)
    ∈ fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15) :=
  repsFix_of_siftB rK15 ⟨11, by decide⟩ T15_11 (by decide)

theorem hinj15_11 : Function.Injective
    (fun i => ((T15_11 i : Coordinate 1) : Coordinate 1 ⧸ reps rK15)) :=
  repsInj_of_reduceAux rK15 T15_11 (by decide)

theorem hcardT15_11 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK15 ⟨11, by decide⟩ R15 hpxR15 hcardq15 (by decide)).symm

/-- **Cell (15, 11).** -/
theorem cell15_11 (e : List (ZMod 25)) (heK : charOK (basisAt rK15) e = true)
    (h : ↥(reps (⟨11, by decide⟩ : Fin 148))) :
    species (reps (⟨11, by decide⟩ : Fin 148)) h (basisElt (reps rK15) (charOfVec rK15 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK15 e (h : Coordinate 1) T15_11 i :=
  species_entry_eq_sum rK15 ⟨11, by decide⟩ e heK h T15_11 hfix15_11 hinj15_11 hcardT15_11
    (fun i => conj_mem_of_fixedPoints (reps ⟨11, by decide⟩) (reps rK15) (T15_11 i) (hfix15_11 i) h)

/-! ## Cell (15, 15): |T| = 5 -/

def T15_15list : List Coordinates := [(0,0,0,0,3), (0,0,0,0,4), (0,0,0,0,0), (0,0,0,0,1), (0,0,0,0,2)]
def T15_15 : Fin 5 → Coordinate 1 := fun i => T15_15list.getD i.val (0,0,0,0,0)

theorem hfix15_15 : ∀ i, ((T15_15 i : Coordinate 1) : Coordinate 1 ⧸ reps rK15)
    ∈ fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15) :=
  repsFix_of_siftB rK15 ⟨15, by decide⟩ T15_15 (by decide)

theorem hinj15_15 : Function.Injective
    (fun i => ((T15_15 i : Coordinate 1) : Coordinate 1 ⧸ reps rK15)) :=
  repsInj_of_reduceAux rK15 T15_15 (by decide)

theorem hcardT15_15 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK15 ⟨15, by decide⟩ R15 hpxR15 hcardq15 (by decide)).symm

/-- **Cell (15, 15).** -/
theorem cell15_15 (e : List (ZMod 25)) (heK : charOK (basisAt rK15) e = true)
    (h : ↥(reps (⟨15, by decide⟩ : Fin 148))) :
    species (reps (⟨15, by decide⟩ : Fin 148)) h (basisElt (reps rK15) (charOfVec rK15 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK15 e (h : Coordinate 1) T15_15 i :=
  species_entry_eq_sum rK15 ⟨15, by decide⟩ e heK h T15_15 hfix15_15 hinj15_15 hcardT15_15
    (fun i => conj_mem_of_fixedPoints (reps ⟨15, by decide⟩) (reps rK15) (T15_15 i) (hfix15_15 i) h)

namespace Q2

/-! ### Cell (13, 6) twin -/

def T13_6_2 : Fin 25 → Coordinate 2 := fun i => T13_6list.getD i.val (0,0,0,0,0)

theorem hfix13_6_2 : ∀ i, ((T13_6_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK13)
    ∈ fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK13) :=
  repsFix_of_siftB2 rK13 ⟨6, by decide⟩ T13_6_2 (by decide)

theorem hinj13_6_2 : Function.Injective
    (fun i => ((T13_6_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK13)) :=
  repsInj_of_reduceAux2 rK13 T13_6_2 (by decide)

theorem hcardT13_6_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK13)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK13 ⟨6, by decide⟩ R13_2 hpxR13_2 hcardq13_2 (by decide)).symm

/-- **Cell (13, 6) twin (q=2).** -/
theorem cell13_6_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK13) e = true)
    (h : ↥(reps (⟨6, by decide⟩ : Fin 148))) :
    species (reps (⟨6, by decide⟩ : Fin 148)) h (basisElt (reps rK13) (charOfVec2 rK13 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK13 e (h : Coordinate 2) T13_6_2 i :=
  species_entry_eq_sum rK13 ⟨6, by decide⟩ e heK h T13_6_2 hfix13_6_2 hinj13_6_2 hcardT13_6_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨6, by decide⟩) (reps rK13) (T13_6_2 i) (hfix13_6_2 i) h)

/-! ### Cell (13, 7) twin -/

def T13_7_2 : Fin 25 → Coordinate 2 := fun i => T13_7list.getD i.val (0,0,0,0,0)

theorem hfix13_7_2 : ∀ i, ((T13_7_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK13)
    ∈ fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK13) :=
  repsFix_of_siftB2 rK13 ⟨7, by decide⟩ T13_7_2 (by decide)

theorem hinj13_7_2 : Function.Injective
    (fun i => ((T13_7_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK13)) :=
  repsInj_of_reduceAux2 rK13 T13_7_2 (by decide)

theorem hcardT13_7_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK13)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK13 ⟨7, by decide⟩ R13_2 hpxR13_2 hcardq13_2 (by decide)).symm

/-- **Cell (13, 7) twin (q=2).** -/
theorem cell13_7_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK13) e = true)
    (h : ↥(reps (⟨7, by decide⟩ : Fin 148))) :
    species (reps (⟨7, by decide⟩ : Fin 148)) h (basisElt (reps rK13) (charOfVec2 rK13 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK13 e (h : Coordinate 2) T13_7_2 i :=
  species_entry_eq_sum rK13 ⟨7, by decide⟩ e heK h T13_7_2 hfix13_7_2 hinj13_7_2 hcardT13_7_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨7, by decide⟩) (reps rK13) (T13_7_2 i) (hfix13_7_2 i) h)

/-! ### Cell (13, 8) twin -/

def T13_8_2 : Fin 25 → Coordinate 2 := fun i => T13_8list.getD i.val (0,0,0,0,0)

theorem hfix13_8_2 : ∀ i, ((T13_8_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK13)
    ∈ fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK13) :=
  repsFix_of_siftB2 rK13 ⟨8, by decide⟩ T13_8_2 (by decide)

theorem hinj13_8_2 : Function.Injective
    (fun i => ((T13_8_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK13)) :=
  repsInj_of_reduceAux2 rK13 T13_8_2 (by decide)

theorem hcardT13_8_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK13)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK13 ⟨8, by decide⟩ R13_2 hpxR13_2 hcardq13_2 (by decide)).symm

/-- **Cell (13, 8) twin (q=2).** -/
theorem cell13_8_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK13) e = true)
    (h : ↥(reps (⟨8, by decide⟩ : Fin 148))) :
    species (reps (⟨8, by decide⟩ : Fin 148)) h (basisElt (reps rK13) (charOfVec2 rK13 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK13 e (h : Coordinate 2) T13_8_2 i :=
  species_entry_eq_sum rK13 ⟨8, by decide⟩ e heK h T13_8_2 hfix13_8_2 hinj13_8_2 hcardT13_8_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨8, by decide⟩) (reps rK13) (T13_8_2 i) (hfix13_8_2 i) h)

/-! ### Cell (13, 9) twin -/

def T13_9_2 : Fin 25 → Coordinate 2 := fun i => T13_9list.getD i.val (0,0,0,0,0)

theorem hfix13_9_2 : ∀ i, ((T13_9_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK13)
    ∈ fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK13) :=
  repsFix_of_siftB2 rK13 ⟨9, by decide⟩ T13_9_2 (by decide)

theorem hinj13_9_2 : Function.Injective
    (fun i => ((T13_9_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK13)) :=
  repsInj_of_reduceAux2 rK13 T13_9_2 (by decide)

theorem hcardT13_9_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK13)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK13 ⟨9, by decide⟩ R13_2 hpxR13_2 hcardq13_2 (by decide)).symm

/-- **Cell (13, 9) twin (q=2).** -/
theorem cell13_9_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK13) e = true)
    (h : ↥(reps (⟨9, by decide⟩ : Fin 148))) :
    species (reps (⟨9, by decide⟩ : Fin 148)) h (basisElt (reps rK13) (charOfVec2 rK13 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK13 e (h : Coordinate 2) T13_9_2 i :=
  species_entry_eq_sum rK13 ⟨9, by decide⟩ e heK h T13_9_2 hfix13_9_2 hinj13_9_2 hcardT13_9_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨9, by decide⟩) (reps rK13) (T13_9_2 i) (hfix13_9_2 i) h)

/-! ### Cell (13, 10) twin -/

def T13_10_2 : Fin 25 → Coordinate 2 := fun i => T13_10list.getD i.val (0,0,0,0,0)

theorem hfix13_10_2 : ∀ i, ((T13_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK13)
    ∈ fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK13) :=
  repsFix_of_siftB2 rK13 ⟨10, by decide⟩ T13_10_2 (by decide)

theorem hinj13_10_2 : Function.Injective
    (fun i => ((T13_10_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK13)) :=
  repsInj_of_reduceAux2 rK13 T13_10_2 (by decide)

theorem hcardT13_10_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK13)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK13 ⟨10, by decide⟩ R13_2 hpxR13_2 hcardq13_2 (by decide)).symm

/-- **Cell (13, 10) twin (q=2).** -/
theorem cell13_10_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK13) e = true)
    (h : ↥(reps (⟨10, by decide⟩ : Fin 148))) :
    species (reps (⟨10, by decide⟩ : Fin 148)) h (basisElt (reps rK13) (charOfVec2 rK13 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK13 e (h : Coordinate 2) T13_10_2 i :=
  species_entry_eq_sum rK13 ⟨10, by decide⟩ e heK h T13_10_2 hfix13_10_2 hinj13_10_2 hcardT13_10_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨10, by decide⟩) (reps rK13) (T13_10_2 i) (hfix13_10_2 i) h)

/-! ### Cell (14, 2) twin -/

def T14_2_2 : Fin 5 → Coordinate 2 := fun i => T14_2list.getD i.val (0,0,0,0,0)

theorem hfix14_2_2 : ∀ i, ((T14_2_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK14)
    ∈ fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK14) :=
  repsFix_of_siftB2 rK14 ⟨2, by decide⟩ T14_2_2 (by decide)

theorem hinj14_2_2 : Function.Injective
    (fun i => ((T14_2_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK14)) :=
  repsInj_of_reduceAux2 rK14 T14_2_2 (by decide)

theorem hcardT14_2_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK14)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK14 ⟨2, by decide⟩ R14_2 hpxR14_2 hcardq14_2 (by decide)).symm

/-- **Cell (14, 2) twin (q=2).** -/
theorem cell14_2_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK14) e = true)
    (h : ↥(reps (⟨2, by decide⟩ : Fin 148))) :
    species (reps (⟨2, by decide⟩ : Fin 148)) h (basisElt (reps rK14) (charOfVec2 rK14 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK14 e (h : Coordinate 2) T14_2_2 i :=
  species_entry_eq_sum rK14 ⟨2, by decide⟩ e heK h T14_2_2 hfix14_2_2 hinj14_2_2 hcardT14_2_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨2, by decide⟩) (reps rK14) (T14_2_2 i) (hfix14_2_2 i) h)

/-! ### Cell (14, 3) twin -/

def T14_3_2 : Fin 5 → Coordinate 2 := fun i => T14_3list.getD i.val (0,0,0,0,0)

theorem hfix14_3_2 : ∀ i, ((T14_3_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK14)
    ∈ fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK14) :=
  repsFix_of_siftB2 rK14 ⟨3, by decide⟩ T14_3_2 (by decide)

theorem hinj14_3_2 : Function.Injective
    (fun i => ((T14_3_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK14)) :=
  repsInj_of_reduceAux2 rK14 T14_3_2 (by decide)

theorem hcardT14_3_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK14)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK14 ⟨3, by decide⟩ R14_2 hpxR14_2 hcardq14_2 (by decide)).symm

/-- **Cell (14, 3) twin (q=2).** -/
theorem cell14_3_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK14) e = true)
    (h : ↥(reps (⟨3, by decide⟩ : Fin 148))) :
    species (reps (⟨3, by decide⟩ : Fin 148)) h (basisElt (reps rK14) (charOfVec2 rK14 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK14 e (h : Coordinate 2) T14_3_2 i :=
  species_entry_eq_sum rK14 ⟨3, by decide⟩ e heK h T14_3_2 hfix14_3_2 hinj14_3_2 hcardT14_3_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨3, by decide⟩) (reps rK14) (T14_3_2 i) (hfix14_3_2 i) h)

/-! ### Cell (14, 4) twin -/

def T14_4_2 : Fin 5 → Coordinate 2 := fun i => T14_4list.getD i.val (0,0,0,0,0)

theorem hfix14_4_2 : ∀ i, ((T14_4_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK14)
    ∈ fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK14) :=
  repsFix_of_siftB2 rK14 ⟨4, by decide⟩ T14_4_2 (by decide)

theorem hinj14_4_2 : Function.Injective
    (fun i => ((T14_4_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK14)) :=
  repsInj_of_reduceAux2 rK14 T14_4_2 (by decide)

theorem hcardT14_4_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK14)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK14 ⟨4, by decide⟩ R14_2 hpxR14_2 hcardq14_2 (by decide)).symm

/-- **Cell (14, 4) twin (q=2).** -/
theorem cell14_4_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK14) e = true)
    (h : ↥(reps (⟨4, by decide⟩ : Fin 148))) :
    species (reps (⟨4, by decide⟩ : Fin 148)) h (basisElt (reps rK14) (charOfVec2 rK14 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK14 e (h : Coordinate 2) T14_4_2 i :=
  species_entry_eq_sum rK14 ⟨4, by decide⟩ e heK h T14_4_2 hfix14_4_2 hinj14_4_2 hcardT14_4_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨4, by decide⟩) (reps rK14) (T14_4_2 i) (hfix14_4_2 i) h)

/-! ### Cell (14, 5) twin -/

def T14_5_2 : Fin 5 → Coordinate 2 := fun i => T14_5list.getD i.val (0,0,0,0,0)

theorem hfix14_5_2 : ∀ i, ((T14_5_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK14)
    ∈ fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK14) :=
  repsFix_of_siftB2 rK14 ⟨5, by decide⟩ T14_5_2 (by decide)

theorem hinj14_5_2 : Function.Injective
    (fun i => ((T14_5_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK14)) :=
  repsInj_of_reduceAux2 rK14 T14_5_2 (by decide)

theorem hcardT14_5_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK14)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK14 ⟨5, by decide⟩ R14_2 hpxR14_2 hcardq14_2 (by decide)).symm

/-- **Cell (14, 5) twin (q=2).** -/
theorem cell14_5_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK14) e = true)
    (h : ↥(reps (⟨5, by decide⟩ : Fin 148))) :
    species (reps (⟨5, by decide⟩ : Fin 148)) h (basisElt (reps rK14) (charOfVec2 rK14 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK14 e (h : Coordinate 2) T14_5_2 i :=
  species_entry_eq_sum rK14 ⟨5, by decide⟩ e heK h T14_5_2 hfix14_5_2 hinj14_5_2 hcardT14_5_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨5, by decide⟩) (reps rK14) (T14_5_2 i) (hfix14_5_2 i) h)

/-! ### Cell (14, 9) twin -/

def T14_9_2 : Fin 25 → Coordinate 2 := fun i => T14_9list.getD i.val (0,0,0,0,0)

theorem hfix14_9_2 : ∀ i, ((T14_9_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK14)
    ∈ fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK14) :=
  repsFix_of_siftB2 rK14 ⟨9, by decide⟩ T14_9_2 (by decide)

theorem hinj14_9_2 : Function.Injective
    (fun i => ((T14_9_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK14)) :=
  repsInj_of_reduceAux2 rK14 T14_9_2 (by decide)

theorem hcardT14_9_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK14)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK14 ⟨9, by decide⟩ R14_2 hpxR14_2 hcardq14_2 (by decide)).symm

/-- **Cell (14, 9) twin (q=2).** -/
theorem cell14_9_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK14) e = true)
    (h : ↥(reps (⟨9, by decide⟩ : Fin 148))) :
    species (reps (⟨9, by decide⟩ : Fin 148)) h (basisElt (reps rK14) (charOfVec2 rK14 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK14 e (h : Coordinate 2) T14_9_2 i :=
  species_entry_eq_sum rK14 ⟨9, by decide⟩ e heK h T14_9_2 hfix14_9_2 hinj14_9_2 hcardT14_9_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨9, by decide⟩) (reps rK14) (T14_9_2 i) (hfix14_9_2 i) h)

/-! ### Cell (14, 11) twin -/

def T14_11_2 : Fin 5 → Coordinate 2 := fun i => T14_11list.getD i.val (0,0,0,0,0)

theorem hfix14_11_2 : ∀ i, ((T14_11_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK14)
    ∈ fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK14) :=
  repsFix_of_siftB2 rK14 ⟨11, by decide⟩ T14_11_2 (by decide)

theorem hinj14_11_2 : Function.Injective
    (fun i => ((T14_11_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK14)) :=
  repsInj_of_reduceAux2 rK14 T14_11_2 (by decide)

theorem hcardT14_11_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK14)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK14 ⟨11, by decide⟩ R14_2 hpxR14_2 hcardq14_2 (by decide)).symm

/-- **Cell (14, 11) twin (q=2).** -/
theorem cell14_11_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK14) e = true)
    (h : ↥(reps (⟨11, by decide⟩ : Fin 148))) :
    species (reps (⟨11, by decide⟩ : Fin 148)) h (basisElt (reps rK14) (charOfVec2 rK14 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK14 e (h : Coordinate 2) T14_11_2 i :=
  species_entry_eq_sum rK14 ⟨11, by decide⟩ e heK h T14_11_2 hfix14_11_2 hinj14_11_2 hcardT14_11_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨11, by decide⟩) (reps rK14) (T14_11_2 i) (hfix14_11_2 i) h)

/-! ### Cell (14, 14) twin -/

def T14_14_2 : Fin 5 → Coordinate 2 := fun i => T14_14list.getD i.val (0,0,0,0,0)

theorem hfix14_14_2 : ∀ i, ((T14_14_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK14)
    ∈ fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK14) :=
  repsFix_of_siftB2 rK14 ⟨14, by decide⟩ T14_14_2 (by decide)

theorem hinj14_14_2 : Function.Injective
    (fun i => ((T14_14_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK14)) :=
  repsInj_of_reduceAux2 rK14 T14_14_2 (by decide)

theorem hcardT14_14_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK14)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK14 ⟨14, by decide⟩ R14_2 hpxR14_2 hcardq14_2 (by decide)).symm

/-- **Cell (14, 14) twin (q=2).** -/
theorem cell14_14_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK14) e = true)
    (h : ↥(reps (⟨14, by decide⟩ : Fin 148))) :
    species (reps (⟨14, by decide⟩ : Fin 148)) h (basisElt (reps rK14) (charOfVec2 rK14 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK14 e (h : Coordinate 2) T14_14_2 i :=
  species_entry_eq_sum rK14 ⟨14, by decide⟩ e heK h T14_14_2 hfix14_14_2 hinj14_14_2 hcardT14_14_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨14, by decide⟩) (reps rK14) (T14_14_2 i) (hfix14_14_2 i) h)

/-! ### Cell (15, 2) twin -/

def T15_2_2 : Fin 5 → Coordinate 2 := fun i => T15_2list.getD i.val (0,0,0,0,0)

theorem hfix15_2_2 : ∀ i, ((T15_2_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK15)
    ∈ fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK15) :=
  repsFix_of_siftB2 rK15 ⟨2, by decide⟩ T15_2_2 (by decide)

theorem hinj15_2_2 : Function.Injective
    (fun i => ((T15_2_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK15)) :=
  repsInj_of_reduceAux2 rK15 T15_2_2 (by decide)

theorem hcardT15_2_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK15)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK15 ⟨2, by decide⟩ R15_2 hpxR15_2 hcardq15_2 (by decide)).symm

/-- **Cell (15, 2) twin (q=2).** -/
theorem cell15_2_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK15) e = true)
    (h : ↥(reps (⟨2, by decide⟩ : Fin 148))) :
    species (reps (⟨2, by decide⟩ : Fin 148)) h (basisElt (reps rK15) (charOfVec2 rK15 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK15 e (h : Coordinate 2) T15_2_2 i :=
  species_entry_eq_sum rK15 ⟨2, by decide⟩ e heK h T15_2_2 hfix15_2_2 hinj15_2_2 hcardT15_2_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨2, by decide⟩) (reps rK15) (T15_2_2 i) (hfix15_2_2 i) h)

/-! ### Cell (15, 3) twin -/

def T15_3_2 : Fin 5 → Coordinate 2 := fun i => T15_3list.getD i.val (0,0,0,0,0)

theorem hfix15_3_2 : ∀ i, ((T15_3_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK15)
    ∈ fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK15) :=
  repsFix_of_siftB2 rK15 ⟨3, by decide⟩ T15_3_2 (by decide)

theorem hinj15_3_2 : Function.Injective
    (fun i => ((T15_3_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK15)) :=
  repsInj_of_reduceAux2 rK15 T15_3_2 (by decide)

theorem hcardT15_3_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK15)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK15 ⟨3, by decide⟩ R15_2 hpxR15_2 hcardq15_2 (by decide)).symm

/-- **Cell (15, 3) twin (q=2).** -/
theorem cell15_3_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK15) e = true)
    (h : ↥(reps (⟨3, by decide⟩ : Fin 148))) :
    species (reps (⟨3, by decide⟩ : Fin 148)) h (basisElt (reps rK15) (charOfVec2 rK15 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK15 e (h : Coordinate 2) T15_3_2 i :=
  species_entry_eq_sum rK15 ⟨3, by decide⟩ e heK h T15_3_2 hfix15_3_2 hinj15_3_2 hcardT15_3_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨3, by decide⟩) (reps rK15) (T15_3_2 i) (hfix15_3_2 i) h)

/-! ### Cell (15, 4) twin -/

def T15_4_2 : Fin 5 → Coordinate 2 := fun i => T15_4list.getD i.val (0,0,0,0,0)

theorem hfix15_4_2 : ∀ i, ((T15_4_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK15)
    ∈ fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK15) :=
  repsFix_of_siftB2 rK15 ⟨4, by decide⟩ T15_4_2 (by decide)

theorem hinj15_4_2 : Function.Injective
    (fun i => ((T15_4_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK15)) :=
  repsInj_of_reduceAux2 rK15 T15_4_2 (by decide)

theorem hcardT15_4_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK15)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK15 ⟨4, by decide⟩ R15_2 hpxR15_2 hcardq15_2 (by decide)).symm

/-- **Cell (15, 4) twin (q=2).** -/
theorem cell15_4_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK15) e = true)
    (h : ↥(reps (⟨4, by decide⟩ : Fin 148))) :
    species (reps (⟨4, by decide⟩ : Fin 148)) h (basisElt (reps rK15) (charOfVec2 rK15 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK15 e (h : Coordinate 2) T15_4_2 i :=
  species_entry_eq_sum rK15 ⟨4, by decide⟩ e heK h T15_4_2 hfix15_4_2 hinj15_4_2 hcardT15_4_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨4, by decide⟩) (reps rK15) (T15_4_2 i) (hfix15_4_2 i) h)

/-! ### Cell (15, 5) twin -/

def T15_5_2 : Fin 5 → Coordinate 2 := fun i => T15_5list.getD i.val (0,0,0,0,0)

theorem hfix15_5_2 : ∀ i, ((T15_5_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK15)
    ∈ fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK15) :=
  repsFix_of_siftB2 rK15 ⟨5, by decide⟩ T15_5_2 (by decide)

theorem hinj15_5_2 : Function.Injective
    (fun i => ((T15_5_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK15)) :=
  repsInj_of_reduceAux2 rK15 T15_5_2 (by decide)

theorem hcardT15_5_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK15)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK15 ⟨5, by decide⟩ R15_2 hpxR15_2 hcardq15_2 (by decide)).symm

/-- **Cell (15, 5) twin (q=2).** -/
theorem cell15_5_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK15) e = true)
    (h : ↥(reps (⟨5, by decide⟩ : Fin 148))) :
    species (reps (⟨5, by decide⟩ : Fin 148)) h (basisElt (reps rK15) (charOfVec2 rK15 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK15 e (h : Coordinate 2) T15_5_2 i :=
  species_entry_eq_sum rK15 ⟨5, by decide⟩ e heK h T15_5_2 hfix15_5_2 hinj15_5_2 hcardT15_5_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨5, by decide⟩) (reps rK15) (T15_5_2 i) (hfix15_5_2 i) h)

/-! ### Cell (15, 9) twin -/

def T15_9_2 : Fin 25 → Coordinate 2 := fun i => T15_9list.getD i.val (0,0,0,0,0)

theorem hfix15_9_2 : ∀ i, ((T15_9_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK15)
    ∈ fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK15) :=
  repsFix_of_siftB2 rK15 ⟨9, by decide⟩ T15_9_2 (by decide)

theorem hinj15_9_2 : Function.Injective
    (fun i => ((T15_9_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK15)) :=
  repsInj_of_reduceAux2 rK15 T15_9_2 (by decide)

theorem hcardT15_9_2 : Fintype.card (Fin 25)
    = Fintype.card (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK15)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK15 ⟨9, by decide⟩ R15_2 hpxR15_2 hcardq15_2 (by decide)).symm

/-- **Cell (15, 9) twin (q=2).** -/
theorem cell15_9_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK15) e = true)
    (h : ↥(reps (⟨9, by decide⟩ : Fin 148))) :
    species (reps (⟨9, by decide⟩ : Fin 148)) h (basisElt (reps rK15) (charOfVec2 rK15 e heK))
      = ∑ i : Fin 25, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK15 e (h : Coordinate 2) T15_9_2 i :=
  species_entry_eq_sum rK15 ⟨9, by decide⟩ e heK h T15_9_2 hfix15_9_2 hinj15_9_2 hcardT15_9_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨9, by decide⟩) (reps rK15) (T15_9_2 i) (hfix15_9_2 i) h)

/-! ### Cell (15, 11) twin -/

def T15_11_2 : Fin 5 → Coordinate 2 := fun i => T15_11list.getD i.val (0,0,0,0,0)

theorem hfix15_11_2 : ∀ i, ((T15_11_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK15)
    ∈ fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK15) :=
  repsFix_of_siftB2 rK15 ⟨11, by decide⟩ T15_11_2 (by decide)

theorem hinj15_11_2 : Function.Injective
    (fun i => ((T15_11_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK15)) :=
  repsInj_of_reduceAux2 rK15 T15_11_2 (by decide)

theorem hcardT15_11_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK15)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK15 ⟨11, by decide⟩ R15_2 hpxR15_2 hcardq15_2 (by decide)).symm

/-- **Cell (15, 11) twin (q=2).** -/
theorem cell15_11_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK15) e = true)
    (h : ↥(reps (⟨11, by decide⟩ : Fin 148))) :
    species (reps (⟨11, by decide⟩ : Fin 148)) h (basisElt (reps rK15) (charOfVec2 rK15 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK15 e (h : Coordinate 2) T15_11_2 i :=
  species_entry_eq_sum rK15 ⟨11, by decide⟩ e heK h T15_11_2 hfix15_11_2 hinj15_11_2 hcardT15_11_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨11, by decide⟩) (reps rK15) (T15_11_2 i) (hfix15_11_2 i) h)

/-! ### Cell (15, 15) twin -/

def T15_15_2 : Fin 5 → Coordinate 2 := fun i => T15_15list.getD i.val (0,0,0,0,0)

theorem hfix15_15_2 : ∀ i, ((T15_15_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK15)
    ∈ fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK15) :=
  repsFix_of_siftB2 rK15 ⟨15, by decide⟩ T15_15_2 (by decide)

theorem hinj15_15_2 : Function.Injective
    (fun i => ((T15_15_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK15)) :=
  repsInj_of_reduceAux2 rK15 T15_15_2 (by decide)

theorem hcardT15_15_2 : Fintype.card (Fin 5)
    = Fintype.card (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK15)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK15 ⟨15, by decide⟩ R15_2 hpxR15_2 hcardq15_2 (by decide)).symm

/-- **Cell (15, 15) twin (q=2).** -/
theorem cell15_15_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK15) e = true)
    (h : ↥(reps (⟨15, by decide⟩ : Fin 148))) :
    species (reps (⟨15, by decide⟩ : Fin 148)) h (basisElt (reps rK15) (charOfVec2 rK15 e heK))
      = ∑ i : Fin 5, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK15 e (h : Coordinate 2) T15_15_2 i :=
  species_entry_eq_sum rK15 ⟨15, by decide⟩ e heK h T15_15_2 hfix15_15_2 hinj15_15_2 hcardT15_15_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨15, by decide⟩) (reps rK15) (T15_15_2 i) (hfix15_15_2 i) h)

end Q2

end LeanDring.P5Presentation
