/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore

/-!
# Species-table cells, A-block data (rK = 26): certified per-cell species-entry instantiations, both twins.

Emit-embed-decide loop for order-25 A-block class `rK = 26` (`|G/K| = 125`).
All nonzero `H`-columns (`|gH| ≤ 2`, `t⁻¹Ht ⊆ K`).  Full 125-coset transversal
`R26` and each `H`-fixed sub-transversal `T26_rH` embedded as kernel data and
re-verified by `decide` through the `LeanDring/P5/Certificate/SpeciesTable/EntryTransA.lean` adapters.  Transversal data is
SHARED between the twins (`reduceAux` normal forms coincide; verified in the
emitter and re-checked by the `q=2` decides below).
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false
set_option linter.style.setOption false

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

def rK26 : Fin 148 := ⟨26, by decide⟩

def R26list : List Coordinates := [(0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,1,0,1,0), (1,1,0,2,0), (1,1,0,3,0), (1,1,0,4,0), (1,1,0,0,0), (1,2,0,1,0), (1,2,0,2,0), (1,2,0,3,0), (1,2,0,4,0), (1,2,0,0,0), (1,3,0,1,0), (1,3,0,2,0), (1,3,0,3,0), (1,3,0,4,0), (1,3,0,0,0), (1,4,0,1,0), (1,4,0,2,0), (1,4,0,3,0), (1,4,0,4,0), (1,4,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,1,0,1,0), (2,1,0,2,0), (2,1,0,3,0), (2,1,0,4,0), (2,1,0,0,0), (2,2,0,1,0), (2,2,0,2,0), (2,2,0,3,0), (2,2,0,4,0), (2,2,0,0,0), (2,3,0,1,0), (2,3,0,2,0), (2,3,0,3,0), (2,3,0,4,0), (2,3,0,0,0), (2,4,0,1,0), (2,4,0,2,0), (2,4,0,3,0), (2,4,0,4,0), (2,4,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,1,0,1,0), (3,1,0,2,0), (3,1,0,3,0), (3,1,0,4,0), (3,1,0,0,0), (3,2,0,1,0), (3,2,0,2,0), (3,2,0,3,0), (3,2,0,4,0), (3,2,0,0,0), (3,3,0,1,0), (3,3,0,2,0), (3,3,0,3,0), (3,3,0,4,0), (3,3,0,0,0), (3,4,0,1,0), (3,4,0,2,0), (3,4,0,3,0), (3,4,0,4,0), (3,4,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,1,0,1,0), (4,1,0,2,0), (4,1,0,3,0), (4,1,0,4,0), (4,1,0,0,0), (4,2,0,1,0), (4,2,0,2,0), (4,2,0,3,0), (4,2,0,4,0), (4,2,0,0,0), (4,3,0,1,0), (4,3,0,2,0), (4,3,0,3,0), (4,3,0,4,0), (4,3,0,0,0), (4,4,0,1,0), (4,4,0,2,0), (4,4,0,3,0), (4,4,0,4,0), (4,4,0,0,0)]
def R26 : Fin 125 → Coordinate 1 := fun i => R26list.getD i.val (0,0,0,0,0)

theorem hpxR26 : Function.Injective (fun i => reduceAux 1 (basisAt rK26) (R26 i)) := by decide
theorem hcardq26 : Nat.card (Coordinate 1 ⧸ reps rK26) = 125 := by
  rw [card_quotient_reps]; decide

/-! ## Cell (26, 0): |T| = 125 -/

def T26_0list : List Coordinates := [(0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,1,0,1,0), (1,1,0,2,0), (1,1,0,3,0), (1,1,0,4,0), (1,1,0,0,0), (1,2,0,1,0), (1,2,0,2,0), (1,2,0,3,0), (1,2,0,4,0), (1,2,0,0,0), (1,3,0,1,0), (1,3,0,2,0), (1,3,0,3,0), (1,3,0,4,0), (1,3,0,0,0), (1,4,0,1,0), (1,4,0,2,0), (1,4,0,3,0), (1,4,0,4,0), (1,4,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,1,0,1,0), (2,1,0,2,0), (2,1,0,3,0), (2,1,0,4,0), (2,1,0,0,0), (2,2,0,1,0), (2,2,0,2,0), (2,2,0,3,0), (2,2,0,4,0), (2,2,0,0,0), (2,3,0,1,0), (2,3,0,2,0), (2,3,0,3,0), (2,3,0,4,0), (2,3,0,0,0), (2,4,0,1,0), (2,4,0,2,0), (2,4,0,3,0), (2,4,0,4,0), (2,4,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,1,0,1,0), (3,1,0,2,0), (3,1,0,3,0), (3,1,0,4,0), (3,1,0,0,0), (3,2,0,1,0), (3,2,0,2,0), (3,2,0,3,0), (3,2,0,4,0), (3,2,0,0,0), (3,3,0,1,0), (3,3,0,2,0), (3,3,0,3,0), (3,3,0,4,0), (3,3,0,0,0), (3,4,0,1,0), (3,4,0,2,0), (3,4,0,3,0), (3,4,0,4,0), (3,4,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,1,0,1,0), (4,1,0,2,0), (4,1,0,3,0), (4,1,0,4,0), (4,1,0,0,0), (4,2,0,1,0), (4,2,0,2,0), (4,2,0,3,0), (4,2,0,4,0), (4,2,0,0,0), (4,3,0,1,0), (4,3,0,2,0), (4,3,0,3,0), (4,3,0,4,0), (4,3,0,0,0), (4,4,0,1,0), (4,4,0,2,0), (4,4,0,3,0), (4,4,0,4,0), (4,4,0,0,0)]
def T26_0 : Fin 125 → Coordinate 1 := fun i => T26_0list.getD i.val (0,0,0,0,0)

theorem hfix26_0 : ∀ i, ((T26_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK26)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26) :=
  repsFix_of_siftB rK26 ⟨0, by decide⟩ T26_0 (by decide)

theorem hinj26_0 : Function.Injective
    (fun i => ((T26_0 i : Coordinate 1) : Coordinate 1 ⧸ reps rK26)) :=
  repsInj_of_reduceAux rK26 T26_0 (by decide)

theorem hcardT26_0 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK26 ⟨0, by decide⟩ R26 hpxR26 hcardq26 (by decide)).symm

/-- **Cell (26, 0).** -/
theorem cell26_0 (e : List (ZMod 25)) (heK : charOK (basisAt rK26) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK26) (charOfVec rK26 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK26 e (h : Coordinate 1) T26_0 i :=
  species_entry_eq_sum rK26 ⟨0, by decide⟩ e heK h T26_0 hfix26_0 hinj26_0 hcardT26_0
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK26) (T26_0 i) (hfix26_0 i) h)

/-! ## Cell (26, 8): |T| = 125 -/

def T26_8list : List Coordinates := [(0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,1,0,1,0), (1,1,0,2,0), (1,1,0,3,0), (1,1,0,4,0), (1,1,0,0,0), (1,2,0,1,0), (1,2,0,2,0), (1,2,0,3,0), (1,2,0,4,0), (1,2,0,0,0), (1,3,0,1,0), (1,3,0,2,0), (1,3,0,3,0), (1,3,0,4,0), (1,3,0,0,0), (1,4,0,1,0), (1,4,0,2,0), (1,4,0,3,0), (1,4,0,4,0), (1,4,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,1,0,1,0), (2,1,0,2,0), (2,1,0,3,0), (2,1,0,4,0), (2,1,0,0,0), (2,2,0,1,0), (2,2,0,2,0), (2,2,0,3,0), (2,2,0,4,0), (2,2,0,0,0), (2,3,0,1,0), (2,3,0,2,0), (2,3,0,3,0), (2,3,0,4,0), (2,3,0,0,0), (2,4,0,1,0), (2,4,0,2,0), (2,4,0,3,0), (2,4,0,4,0), (2,4,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,1,0,1,0), (3,1,0,2,0), (3,1,0,3,0), (3,1,0,4,0), (3,1,0,0,0), (3,2,0,1,0), (3,2,0,2,0), (3,2,0,3,0), (3,2,0,4,0), (3,2,0,0,0), (3,3,0,1,0), (3,3,0,2,0), (3,3,0,3,0), (3,3,0,4,0), (3,3,0,0,0), (3,4,0,1,0), (3,4,0,2,0), (3,4,0,3,0), (3,4,0,4,0), (3,4,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,1,0,1,0), (4,1,0,2,0), (4,1,0,3,0), (4,1,0,4,0), (4,1,0,0,0), (4,2,0,1,0), (4,2,0,2,0), (4,2,0,3,0), (4,2,0,4,0), (4,2,0,0,0), (4,3,0,1,0), (4,3,0,2,0), (4,3,0,3,0), (4,3,0,4,0), (4,3,0,0,0), (4,4,0,1,0), (4,4,0,2,0), (4,4,0,3,0), (4,4,0,4,0), (4,4,0,0,0)]
def T26_8 : Fin 125 → Coordinate 1 := fun i => T26_8list.getD i.val (0,0,0,0,0)

theorem hfix26_8 : ∀ i, ((T26_8 i : Coordinate 1) : Coordinate 1 ⧸ reps rK26)
    ∈ fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26) :=
  repsFix_of_siftB rK26 ⟨8, by decide⟩ T26_8 (by decide)

theorem hinj26_8 : Function.Injective
    (fun i => ((T26_8 i : Coordinate 1) : Coordinate 1 ⧸ reps rK26)) :=
  repsInj_of_reduceAux rK26 T26_8 (by decide)

theorem hcardT26_8 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK26 ⟨8, by decide⟩ R26 hpxR26 hcardq26 (by decide)).symm

/-- **Cell (26, 8).** -/
theorem cell26_8 (e : List (ZMod 25)) (heK : charOK (basisAt rK26) e = true)
    (h : ↥(reps (⟨8, by decide⟩ : Fin 148))) :
    species (reps (⟨8, by decide⟩ : Fin 148)) h (basisElt (reps rK26) (charOfVec rK26 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK26 e (h : Coordinate 1) T26_8 i :=
  species_entry_eq_sum rK26 ⟨8, by decide⟩ e heK h T26_8 hfix26_8 hinj26_8 hcardT26_8
    (fun i => conj_mem_of_fixedPoints (reps ⟨8, by decide⟩) (reps rK26) (T26_8 i) (hfix26_8 i) h)

/-! ## Cell (26, 12): |T| = 125 -/

def T26_12list : List Coordinates := [(0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,1,0,1,0), (1,1,0,2,0), (1,1,0,3,0), (1,1,0,4,0), (1,1,0,0,0), (1,2,0,1,0), (1,2,0,2,0), (1,2,0,3,0), (1,2,0,4,0), (1,2,0,0,0), (1,3,0,1,0), (1,3,0,2,0), (1,3,0,3,0), (1,3,0,4,0), (1,3,0,0,0), (1,4,0,1,0), (1,4,0,2,0), (1,4,0,3,0), (1,4,0,4,0), (1,4,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,1,0,1,0), (2,1,0,2,0), (2,1,0,3,0), (2,1,0,4,0), (2,1,0,0,0), (2,2,0,1,0), (2,2,0,2,0), (2,2,0,3,0), (2,2,0,4,0), (2,2,0,0,0), (2,3,0,1,0), (2,3,0,2,0), (2,3,0,3,0), (2,3,0,4,0), (2,3,0,0,0), (2,4,0,1,0), (2,4,0,2,0), (2,4,0,3,0), (2,4,0,4,0), (2,4,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,1,0,1,0), (3,1,0,2,0), (3,1,0,3,0), (3,1,0,4,0), (3,1,0,0,0), (3,2,0,1,0), (3,2,0,2,0), (3,2,0,3,0), (3,2,0,4,0), (3,2,0,0,0), (3,3,0,1,0), (3,3,0,2,0), (3,3,0,3,0), (3,3,0,4,0), (3,3,0,0,0), (3,4,0,1,0), (3,4,0,2,0), (3,4,0,3,0), (3,4,0,4,0), (3,4,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,1,0,1,0), (4,1,0,2,0), (4,1,0,3,0), (4,1,0,4,0), (4,1,0,0,0), (4,2,0,1,0), (4,2,0,2,0), (4,2,0,3,0), (4,2,0,4,0), (4,2,0,0,0), (4,3,0,1,0), (4,3,0,2,0), (4,3,0,3,0), (4,3,0,4,0), (4,3,0,0,0), (4,4,0,1,0), (4,4,0,2,0), (4,4,0,3,0), (4,4,0,4,0), (4,4,0,0,0)]
def T26_12 : Fin 125 → Coordinate 1 := fun i => T26_12list.getD i.val (0,0,0,0,0)

theorem hfix26_12 : ∀ i, ((T26_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK26)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26) :=
  repsFix_of_siftB rK26 ⟨12, by decide⟩ T26_12 (by decide)

theorem hinj26_12 : Function.Injective
    (fun i => ((T26_12 i : Coordinate 1) : Coordinate 1 ⧸ reps rK26)) :=
  repsInj_of_reduceAux rK26 T26_12 (by decide)

theorem hcardT26_12 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK26 ⟨12, by decide⟩ R26 hpxR26 hcardq26 (by decide)).symm

/-- **Cell (26, 12).** -/
theorem cell26_12 (e : List (ZMod 25)) (heK : charOK (basisAt rK26) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK26) (charOfVec rK26 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK26 e (h : Coordinate 1) T26_12 i :=
  species_entry_eq_sum rK26 ⟨12, by decide⟩ e heK h T26_12 hfix26_12 hinj26_12 hcardT26_12
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK26) (T26_12 i) (hfix26_12 i) h)

/-! ## Cell (26, 26): |T| = 125 -/

def T26_26list : List Coordinates := [(0,0,0,1,0), (0,0,0,2,0), (0,0,0,3,0), (0,0,0,4,0), (0,0,0,0,0), (0,1,0,1,0), (0,1,0,2,0), (0,1,0,3,0), (0,1,0,4,0), (0,1,0,0,0), (0,2,0,1,0), (0,2,0,2,0), (0,2,0,3,0), (0,2,0,4,0), (0,2,0,0,0), (0,3,0,1,0), (0,3,0,2,0), (0,3,0,3,0), (0,3,0,4,0), (0,3,0,0,0), (0,4,0,1,0), (0,4,0,2,0), (0,4,0,3,0), (0,4,0,4,0), (0,4,0,0,0), (1,0,0,1,0), (1,0,0,2,0), (1,0,0,3,0), (1,0,0,4,0), (1,0,0,0,0), (1,1,0,1,0), (1,1,0,2,0), (1,1,0,3,0), (1,1,0,4,0), (1,1,0,0,0), (1,2,0,1,0), (1,2,0,2,0), (1,2,0,3,0), (1,2,0,4,0), (1,2,0,0,0), (1,3,0,1,0), (1,3,0,2,0), (1,3,0,3,0), (1,3,0,4,0), (1,3,0,0,0), (1,4,0,1,0), (1,4,0,2,0), (1,4,0,3,0), (1,4,0,4,0), (1,4,0,0,0), (2,0,0,1,0), (2,0,0,2,0), (2,0,0,3,0), (2,0,0,4,0), (2,0,0,0,0), (2,1,0,1,0), (2,1,0,2,0), (2,1,0,3,0), (2,1,0,4,0), (2,1,0,0,0), (2,2,0,1,0), (2,2,0,2,0), (2,2,0,3,0), (2,2,0,4,0), (2,2,0,0,0), (2,3,0,1,0), (2,3,0,2,0), (2,3,0,3,0), (2,3,0,4,0), (2,3,0,0,0), (2,4,0,1,0), (2,4,0,2,0), (2,4,0,3,0), (2,4,0,4,0), (2,4,0,0,0), (3,0,0,1,0), (3,0,0,2,0), (3,0,0,3,0), (3,0,0,4,0), (3,0,0,0,0), (3,1,0,1,0), (3,1,0,2,0), (3,1,0,3,0), (3,1,0,4,0), (3,1,0,0,0), (3,2,0,1,0), (3,2,0,2,0), (3,2,0,3,0), (3,2,0,4,0), (3,2,0,0,0), (3,3,0,1,0), (3,3,0,2,0), (3,3,0,3,0), (3,3,0,4,0), (3,3,0,0,0), (3,4,0,1,0), (3,4,0,2,0), (3,4,0,3,0), (3,4,0,4,0), (3,4,0,0,0), (4,0,0,1,0), (4,0,0,2,0), (4,0,0,3,0), (4,0,0,4,0), (4,0,0,0,0), (4,1,0,1,0), (4,1,0,2,0), (4,1,0,3,0), (4,1,0,4,0), (4,1,0,0,0), (4,2,0,1,0), (4,2,0,2,0), (4,2,0,3,0), (4,2,0,4,0), (4,2,0,0,0), (4,3,0,1,0), (4,3,0,2,0), (4,3,0,3,0), (4,3,0,4,0), (4,3,0,0,0), (4,4,0,1,0), (4,4,0,2,0), (4,4,0,3,0), (4,4,0,4,0), (4,4,0,0,0)]
def T26_26 : Fin 125 → Coordinate 1 := fun i => T26_26list.getD i.val (0,0,0,0,0)

theorem hfix26_26 : ∀ i, ((T26_26 i : Coordinate 1) : Coordinate 1 ⧸ reps rK26)
    ∈ fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26) :=
  repsFix_of_siftB rK26 ⟨26, by decide⟩ T26_26 (by decide)

theorem hinj26_26 : Function.Injective
    (fun i => ((T26_26 i : Coordinate 1) : Coordinate 1 ⧸ reps rK26)) :=
  repsInj_of_reduceAux rK26 T26_26 (by decide)

theorem hcardT26_26 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard rK26 ⟨26, by decide⟩ R26 hpxR26 hcardq26 (by decide)).symm

/-- **Cell (26, 26).** -/
theorem cell26_26 (e : List (ZMod 25)) (heK : charOK (basisAt rK26) e = true)
    (h : ↥(reps (⟨26, by decide⟩ : Fin 148))) :
    species (reps (⟨26, by decide⟩ : Fin 148)) h (basisElt (reps rK26) (charOfVec rK26 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp rK26 e (h : Coordinate 1) T26_26 i :=
  species_entry_eq_sum rK26 ⟨26, by decide⟩ e heK h T26_26 hfix26_26 hinj26_26 hcardT26_26
    (fun i => conj_mem_of_fixedPoints (reps ⟨26, by decide⟩) (reps rK26) (T26_26 i) (hfix26_26 i) h)

namespace Q2

def R26_2 : Fin 125 → Coordinate 2 := fun i => R26list.getD i.val (0,0,0,0,0)
theorem hpxR26_2 : Function.Injective (fun i => reduceAux 2 (basisAt2 rK26) (R26_2 i)) := by decide
theorem hcardq26_2 : Nat.card (Coordinate 2 ⧸ reps rK26) = 125 := by
  rw [card_quotient_reps2]; decide

/-! ### Cell (26, 0) twin -/

def T26_0_2 : Fin 125 → Coordinate 2 := fun i => T26_0list.getD i.val (0,0,0,0,0)

theorem hfix26_0_2 : ∀ i, ((T26_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK26)
    ∈ fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK26) :=
  repsFix_of_siftB2 rK26 ⟨0, by decide⟩ T26_0_2 (by decide)

theorem hinj26_0_2 : Function.Injective
    (fun i => ((T26_0_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK26)) :=
  repsInj_of_reduceAux2 rK26 T26_0_2 (by decide)

theorem hcardT26_0_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨0, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK26)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK26 ⟨0, by decide⟩ R26_2 hpxR26_2 hcardq26_2 (by decide)).symm

/-- **Cell (26, 0) twin (q=2).** -/
theorem cell26_0_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK26) e = true)
    (h : ↥(reps (⟨0, by decide⟩ : Fin 148))) :
    species (reps (⟨0, by decide⟩ : Fin 148)) h (basisElt (reps rK26) (charOfVec2 rK26 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK26 e (h : Coordinate 2) T26_0_2 i :=
  species_entry_eq_sum rK26 ⟨0, by decide⟩ e heK h T26_0_2 hfix26_0_2 hinj26_0_2 hcardT26_0_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨0, by decide⟩) (reps rK26) (T26_0_2 i) (hfix26_0_2 i) h)

/-! ### Cell (26, 8) twin -/

def T26_8_2 : Fin 125 → Coordinate 2 := fun i => T26_8list.getD i.val (0,0,0,0,0)

theorem hfix26_8_2 : ∀ i, ((T26_8_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK26)
    ∈ fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK26) :=
  repsFix_of_siftB2 rK26 ⟨8, by decide⟩ T26_8_2 (by decide)

theorem hinj26_8_2 : Function.Injective
    (fun i => ((T26_8_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK26)) :=
  repsInj_of_reduceAux2 rK26 T26_8_2 (by decide)

theorem hcardT26_8_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK26)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK26 ⟨8, by decide⟩ R26_2 hpxR26_2 hcardq26_2 (by decide)).symm

/-- **Cell (26, 8) twin (q=2).** -/
theorem cell26_8_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK26) e = true)
    (h : ↥(reps (⟨8, by decide⟩ : Fin 148))) :
    species (reps (⟨8, by decide⟩ : Fin 148)) h (basisElt (reps rK26) (charOfVec2 rK26 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK26 e (h : Coordinate 2) T26_8_2 i :=
  species_entry_eq_sum rK26 ⟨8, by decide⟩ e heK h T26_8_2 hfix26_8_2 hinj26_8_2 hcardT26_8_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨8, by decide⟩) (reps rK26) (T26_8_2 i) (hfix26_8_2 i) h)

/-! ### Cell (26, 12) twin -/

def T26_12_2 : Fin 125 → Coordinate 2 := fun i => T26_12list.getD i.val (0,0,0,0,0)

theorem hfix26_12_2 : ∀ i, ((T26_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK26)
    ∈ fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK26) :=
  repsFix_of_siftB2 rK26 ⟨12, by decide⟩ T26_12_2 (by decide)

theorem hinj26_12_2 : Function.Injective
    (fun i => ((T26_12_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK26)) :=
  repsInj_of_reduceAux2 rK26 T26_12_2 (by decide)

theorem hcardT26_12_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK26)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK26 ⟨12, by decide⟩ R26_2 hpxR26_2 hcardq26_2 (by decide)).symm

/-- **Cell (26, 12) twin (q=2).** -/
theorem cell26_12_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK26) e = true)
    (h : ↥(reps (⟨12, by decide⟩ : Fin 148))) :
    species (reps (⟨12, by decide⟩ : Fin 148)) h (basisElt (reps rK26) (charOfVec2 rK26 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK26 e (h : Coordinate 2) T26_12_2 i :=
  species_entry_eq_sum rK26 ⟨12, by decide⟩ e heK h T26_12_2 hfix26_12_2 hinj26_12_2 hcardT26_12_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨12, by decide⟩) (reps rK26) (T26_12_2 i) (hfix26_12_2 i) h)

/-! ### Cell (26, 26) twin -/

def T26_26_2 : Fin 125 → Coordinate 2 := fun i => T26_26list.getD i.val (0,0,0,0,0)

theorem hfix26_26_2 : ∀ i, ((T26_26_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK26)
    ∈ fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK26) :=
  repsFix_of_siftB2 rK26 ⟨26, by decide⟩ T26_26_2 (by decide)

theorem hinj26_26_2 : Function.Injective
    (fun i => ((T26_26_2 i : Coordinate 2) : Coordinate 2 ⧸ reps rK26)) :=
  repsInj_of_reduceAux2 rK26 T26_26_2 (by decide)

theorem hcardT26_26_2 : Fintype.card (Fin 125)
    = Fintype.card (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ reps rK26)) := by
  rw [Fintype.card_fin]
  exact (repsFixedCard2 rK26 ⟨26, by decide⟩ R26_2 hpxR26_2 hcardq26_2 (by decide)).symm

/-- **Cell (26, 26) twin (q=2).** -/
theorem cell26_26_2 (e : List (ZMod 25)) (heK : charOK2 (basisAt2 rK26) e = true)
    (h : ↥(reps (⟨26, by decide⟩ : Fin 148))) :
    species (reps (⟨26, by decide⟩ : Fin 148)) h (basisElt (reps rK26) (charOfVec2 rK26 e heK))
      = ∑ i : Fin 125, ((zeta25 : ℂˣ) : ℂ) ^ entryExp2 rK26 e (h : Coordinate 2) T26_26_2 i :=
  species_entry_eq_sum rK26 ⟨26, by decide⟩ e heK h T26_26_2 hfix26_26_2 hinj26_26_2 hcardT26_26_2
    (fun i => conj_mem_of_fixedPoints (reps ⟨26, by decide⟩) (reps rK26) (T26_26_2 i) (hfix26_26_2 i) h)

end Q2

end LeanDring.P5Presentation
