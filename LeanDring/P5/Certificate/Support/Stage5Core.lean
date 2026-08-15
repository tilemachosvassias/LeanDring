/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA
import LeanDring.P5.Data.EntryK.C001

/-!
# The off-support and `⊥`-column discharges

Three generic lemmas that close every *non*-certificate case of the master cell
theorem, uniformly in the class indices:

* `species_zero_of_fixCard_zero` (+ `Q2` twin) — if the certified fixed-point
  count of `H = reps rH` on `G/reps rK` is `0` then the whole `(rK, rH)` block of
  the species table vanishes.  This is the discharge for the **12,725** class
  pairs that are off support without being caught by the order bound; the
  hypothesis is produced by `repsFixedCard`(`2`) with `m = 0`.
* `species_zero_of_len_lt` (+ twin) — the order bound `|K| < |H|`, restated on
  the certified echelon-basis lengths so the hypothesis is a `decide` on two
  list lengths.
* `species_bot_column` (+ twin) — the `rH = 0` column (`H = ⊥`, `h = 1`) is
  `|G/K| = 5 ^ (5 - |basisAt rK|)` on *every* row, with no transversal data at
  all; this covers all 148 `rH = 0` triples, including those for which no
  per-cell certificate was emitted.
-/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- file-level maxHeartbeats: dozens of decide-heavy declarations below need it
set_option linter.style.setOption false
set_option maxHeartbeats 4000000

/-! ## Empty fixed-point set ⟹ the block vanishes -/

theorem species_zero_of_fixCard_zero (rK rH : Fin 148) (h : ↥(reps rH))
    (l : ↥(reps rK) →* ℂˣ)
    (hz : Fintype.card (fixedPoints (reps rH) (Coordinate 1 ⧸ reps rK)) = 0) :
    species (reps rH) h (basisElt (reps rK) l) = 0 := by
  classical
  rw [species_basisElt]
  haveI : IsEmpty (MulAction.fixedPoints (reps rH)
      (induced (reps rK) l : MonGSet (Coordinate 1) ℂˣ).carrier) := by
    constructor
    rintro ⟨q, hq⟩
    have hne : Nat.card (MulAction.fixedPoints (reps rH) (Coordinate 1 ⧸ reps rK)) ≠ 0 :=
      Nat.card_ne_zero.mpr ⟨⟨⟨q, hq⟩⟩, Subtype.finite⟩
    rw [Nat.card_eq_fintype_card, hz] at hne
    exact hne rfl
  rw [Finset.univ_eq_empty, Finset.sum_empty]

theorem Q2.species_zero_of_fixCard_zero (rK rH : Fin 148) (h : ↥(Q2.reps rH))
    (l : ↥(Q2.reps rK) →* ℂˣ)
    (hz : Fintype.card (fixedPoints (Q2.reps rH) (Coordinate 2 ⧸ Q2.reps rK)) = 0) :
    species (Q2.reps rH) h (basisElt (Q2.reps rK) l) = 0 := by
  classical
  rw [species_basisElt]
  haveI : IsEmpty (MulAction.fixedPoints (Q2.reps rH)
      (induced (Q2.reps rK) l : MonGSet (Coordinate 2) ℂˣ).carrier) := by
    constructor
    rintro ⟨q, hq⟩
    have hne : Nat.card (MulAction.fixedPoints (Q2.reps rH) (Coordinate 2 ⧸ Q2.reps rK)) ≠ 0 :=
      Nat.card_ne_zero.mpr ⟨⟨⟨q, hq⟩⟩, Subtype.finite⟩
    rw [Nat.card_eq_fintype_card, hz] at hne
    exact hne rfl
  rw [Finset.univ_eq_empty, Finset.sum_empty]

/-! ## The order bound, on certified basis lengths -/

theorem card_reps_eq (r : Fin 148) : Nat.card (reps r) = 5 ^ (basisAt r).length := by
  have h : Nat.card (subAt (classRepsData.getD r.val 0))
      = 5 ^ (getB (classRepsData.getD r.val 0)).length :=
    card_subAt (classReps_lt r.val r.isLt)
  rw [basisAt_eq r]
  exact h

theorem Q2.card_reps_eq (r : Fin 148) : Nat.card (Q2.reps r) = 5 ^ (Q2.basisAt2 r).length := by
  have h : Nat.card (Q2.subAt (classRepsData.getD r.val 0))
      = 5 ^ (Q2.getB (classRepsData.getD r.val 0)).length :=
    Q2.card_subAt (classReps_lt r.val r.isLt)
  rw [Q2.basisAt2_eq r]
  exact h

theorem species_zero_of_len_lt (rK rH : Fin 148) (h : ↥(reps rH)) (l : ↥(reps rK) →* ℂˣ)
    (hlt : (basisAt rK).length < (basisAt rH).length) :
    species (reps rH) h (basisElt (reps rK) l) = 0 := by
  refine species_basisElt_eq_zero_of_card_lt ?_ h l
  rw [card_reps_eq, card_reps_eq]
  exact Nat.pow_lt_pow_right (by norm_num) hlt

theorem Q2.species_zero_of_len_lt (rK rH : Fin 148) (h : ↥(Q2.reps rH))
    (l : ↥(Q2.reps rK) →* ℂˣ)
    (hlt : (Q2.basisAt2 rK).length < (Q2.basisAt2 rH).length) :
    species (Q2.reps rH) h (basisElt (Q2.reps rK) l) = 0 := by
  refine species_basisElt_eq_zero_of_card_lt ?_ h l
  rw [Q2.card_reps_eq, Q2.card_reps_eq]
  exact Nat.pow_lt_pow_right (by norm_num) hlt

/-! ## The `⊥` column (`rH = 0`) -/

/-- Generic: a species column at a trivial subgroup is the index of the row
subgroup, on every row. -/
theorem species_eq_of_bot {GG : Type} [_root_.Group GG] [Fintype GG] {H : Subgroup GG} (hH : H = ⊥)
    (h : H) (K : Subgroup GG) (l : K →* ℂˣ) :
    species H h (basisElt K l) = (Nat.card (GG ⧸ K) : ℂ) := by
  subst hH
  have h1 : h = 1 := Subtype.ext (Subgroup.mem_bot.mp h.2)
  subst h1
  exact species_bot_one_basisElt' K l

theorem species_bot_column (rK : Fin 148) (h : ↥(reps rK0))
    (l : ↥(reps rK) →* ℂˣ) :
    species (reps rK0) h (basisElt (reps rK) l)
      = ((5 ^ (5 - (basisAt rK).length) : ℕ) : ℂ) := by
  rw [species_eq_of_bot reps_zero_eq_bot h (reps rK) l, card_quotient_reps rK]

theorem Q2.species_bot_column (rK : Fin 148) (h : ↥(Q2.reps rK0))
    (l : ↥(Q2.reps rK) →* ℂˣ) :
    species (Q2.reps rK0) h (basisElt (Q2.reps rK) l)
      = ((5 ^ (5 - (Q2.basisAt2 rK).length) : ℕ) : ℂ) := by
  rw [species_eq_of_bot reps_zero_eq_bot2 h (Q2.reps rK) l, Q2.card_quotient_reps2 rK]

/-- The two twins' basis lengths agree class by class — one data-level `decide`. -/
theorem basisLen_eq : (List.range 148).all
    (fun r => Nat.beq (repBases.getD r []).length (Q2.repBases2.getD r []).length) = true := by
  decide

theorem basisAt_length_eq (r : Fin 148) : (basisAt r).length = (Q2.basisAt2 r).length := by
  have h := (List.all_eq_true.mp basisLen_eq) r.val (List.mem_range.mpr r.isLt)
  exact Nat.eq_of_beq_eq_true h

end LeanDring.P5Presentation
