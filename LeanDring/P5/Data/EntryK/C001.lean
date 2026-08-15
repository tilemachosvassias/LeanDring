/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryCore
import LeanDring.Theory.DRing.BridgeEntries
import LeanDring.Theory.DRing.BridgeRecognition

/-!
# Species-table cells, K-stratum data (rK = 0): the abstract K = ⊥ column, both twins.

The `K = ⊥` basis class `[⊥, 1]` is the augmentation basis element (`⊥` carries
only the trivial character).  Its species column is proven **abstractly** — no
`3125`-coset transversal is emitted — by reusing the two generic bridge lemmas:

* `LeanDring.DRing.species_basisElt_bot` — for `H ≠ ⊥`, `φ_{H,h}[⊥,λ] = 0`
  (the `G`-action on `G/⊥ ≅ G` is free, so `(G/⊥)^H = ∅` unless `H = ⊥`);
* `LeanDring.DRing.species_bot_one_basisElt` — the augmentation entry
  `φ_{⊥,1}[⊥,1] = |G/⊥| = |G| = 3125`.

So the whole `rK = 0` column is `0` off the augmentation row and `3125` on it,
uniformly for both twins.  `reps_zero_eq_bot` / `reps_zero_eq_bot2` identify the
class representative `reps 0` with `⊥`, tying these to the presentation's row 0.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

def rK0 : Fin 148 := ⟨0, by decide⟩

/-! ## `reps 0 = ⊥` (both twins) -/

/-- The `rK = 0` class representative is the trivial subgroup (`basisAt 0 = []`,
`⟨∅⟩ = ⊥`). -/
theorem reps_zero_eq_bot : reps rK0 = (⊥ : Subgroup (Coordinate 1)) := by
  rw [reps_eq_ofList rK0, show basisAt rK0 = [] from by decide]
  simp only [ofList]
  rw [Subgroup.closure_eq_bot_iff]
  intro y hy
  exact absurd hy List.not_mem_nil

/-- Twin: `reps 0 = ⊥` in `Coordinate 2`. -/
theorem reps_zero_eq_bot2 : Q2.reps rK0 = (⊥ : Subgroup (Coordinate 2)) := by
  rw [Q2.reps_eq_ofList2 rK0, show Q2.basisAt2 rK0 = [] from by decide]
  simp only [ofList]
  rw [Subgroup.closure_eq_bot_iff]
  intro y hy
  exact absurd hy List.not_mem_nil

/-! ## The augmentation entry `φ_{⊥,1}[⊥,1] = 3125` -/

/-- **Cell (0, 0).** The augmentation entry of the `K = ⊥` column: `|G/⊥| = |G| = 3125`. -/
theorem cell0_aug :
    species (⊥ : Subgroup (Coordinate 1)) 1
        (basisElt (⊥ : Subgroup (Coordinate 1)) (1 : (⊥ : Subgroup (Coordinate 1)) →* ℂˣ))
      = (3125 : ℂ) := by
  rw [species_bot_one_basisElt]
  have : Nat.card (Coordinate 1 ⧸ (⊥ : Subgroup (Coordinate 1))) = 3125 := by
    rw [Nat.card_congr (QuotientGroup.quotientBot (G := Coordinate 1)).toEquiv,
      Nat.card_eq_fintype_card]
    exact card_coordinates
  rw [this]; norm_num

/-- **Cell (0, 0) twin (q=2).** -/
theorem cell0_aug2 :
    species (⊥ : Subgroup (Coordinate 2)) 1
        (basisElt (⊥ : Subgroup (Coordinate 2)) (1 : (⊥ : Subgroup (Coordinate 2)) →* ℂˣ))
      = (3125 : ℂ) := by
  rw [species_bot_one_basisElt]
  have : Nat.card (Coordinate 2 ⧸ (⊥ : Subgroup (Coordinate 2))) = 3125 := by
    rw [Nat.card_congr (QuotientGroup.quotientBot (G := Coordinate 2)).toEquiv,
      Nat.card_eq_fintype_card]
    exact card_coordinates
  rw [this]; norm_num

/-! ## The zero pattern `φ_{H,h}[⊥,λ] = 0` for `H ≠ ⊥` -/

/-- **Cells (0, rH), rH ≠ 0.** Every off-augmentation entry of the `K = ⊥`
column vanishes: for `H ≠ ⊥` and any `h ∈ H`, `φ_{H,h}[⊥,λ] = 0`.  This one
generic statement covers all 147 nonzero `H`-classes at once. -/
theorem cell0_zero {H : Subgroup (Coordinate 1)} (hH : H ≠ ⊥) (h : H)
    (l : (⊥ : Subgroup (Coordinate 1)) →* ℂˣ) :
    species H h (basisElt (⊥ : Subgroup (Coordinate 1)) l) = 0 :=
  species_basisElt_bot hH h l

/-- **Cells (0, rH), rH ≠ 0 — twin (q=2).** -/
theorem cell0_zero2 {H : Subgroup (Coordinate 2)} (hH : H ≠ ⊥) (h : H)
    (l : (⊥ : Subgroup (Coordinate 2)) →* ℂˣ) :
    species H h (basisElt (⊥ : Subgroup (Coordinate 2)) l) = 0 :=
  species_basisElt_bot hH h l

end LeanDring.P5Presentation
