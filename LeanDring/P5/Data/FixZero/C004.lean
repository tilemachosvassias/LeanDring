/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryK.C005

/-!
# Species-table cells, off-support emptiness certificates, chunk 3

For each `(rK, rH)` in this chunk the `H`-fixed part of `G/K` is EMPTY (while
`|H| <= |K|`, so the order bound does not apply): one batched kernel `decide` per
class scans the certified full transversal `R<rK>`, and the per-pair theorems
reflect it through `repsFixedCard` into the fixed-point count.  Feeds
`species_zero_of_fixCard_zero` (`LeanDring/P5/Certificate/Support/Stage5Core.lean`).
Auto-emitted by `python/p5_fixzero_emit.py`.
-/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem fixz1_4 : ([1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 625 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK4) (retConj 1 (R4 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_4_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK4)) = 0 :=
  repsFixedCard rK4 ⟨1, by decide⟩ R4 hpxR4 hcardq4
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_4) 1 (by decide)))

theorem fz1_4_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK4)) = 0 :=
  repsFixedCard rK4 ⟨2, by decide⟩ R4 hpxR4 hcardq4
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_4) 2 (by decide)))

theorem fz1_4_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK4)) = 0 :=
  repsFixedCard rK4 ⟨3, by decide⟩ R4 hpxR4 hcardq4
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_4) 3 (by decide)))

theorem fz1_4_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK4)) = 0 :=
  repsFixedCard rK4 ⟨5, by decide⟩ R4 hpxR4 hcardq4
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_4) 5 (by decide)))

theorem fz1_4_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK4)) = 0 :=
  repsFixedCard rK4 ⟨6, by decide⟩ R4 hpxR4 hcardq4
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_4) 6 (by decide)))

theorem fz1_4_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK4)) = 0 :=
  repsFixedCard rK4 ⟨7, by decide⟩ R4 hpxR4 hcardq4
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_4) 7 (by decide)))

theorem fz1_4_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK4)) = 0 :=
  repsFixedCard rK4 ⟨8, by decide⟩ R4 hpxR4 hcardq4
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_4) 8 (by decide)))

theorem fz1_4_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK4)) = 0 :=
  repsFixedCard rK4 ⟨9, by decide⟩ R4 hpxR4 hcardq4
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_4) 9 (by decide)))

theorem fz1_4_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK4)) = 0 :=
  repsFixedCard rK4 ⟨10, by decide⟩ R4 hpxR4 hcardq4
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_4) 10 (by decide)))

theorem fz1_4_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK4)) = 0 :=
  repsFixedCard rK4 ⟨11, by decide⟩ R4 hpxR4 hcardq4
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_4) 11 (by decide)))

theorem fz1_4_12 : Fintype.card
    (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK4)) = 0 :=
  repsFixedCard rK4 ⟨12, by decide⟩ R4 hpxR4 hcardq4
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_4) 12 (by decide)))

theorem fixz2_4 : ([1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 625 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK4) (retConj 2 (Q2.R4_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_4_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK4)) = 0 :=
  Q2.repsFixedCard2 rK4 ⟨1, by decide⟩ Q2.R4_2 Q2.hpxR4_2 Q2.hcardq4_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_4) 1 (by decide)))

theorem fz2_4_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK4)) = 0 :=
  Q2.repsFixedCard2 rK4 ⟨2, by decide⟩ Q2.R4_2 Q2.hpxR4_2 Q2.hcardq4_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_4) 2 (by decide)))

theorem fz2_4_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK4)) = 0 :=
  Q2.repsFixedCard2 rK4 ⟨3, by decide⟩ Q2.R4_2 Q2.hpxR4_2 Q2.hcardq4_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_4) 3 (by decide)))

theorem fz2_4_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK4)) = 0 :=
  Q2.repsFixedCard2 rK4 ⟨5, by decide⟩ Q2.R4_2 Q2.hpxR4_2 Q2.hcardq4_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_4) 5 (by decide)))

theorem fz2_4_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK4)) = 0 :=
  Q2.repsFixedCard2 rK4 ⟨6, by decide⟩ Q2.R4_2 Q2.hpxR4_2 Q2.hcardq4_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_4) 6 (by decide)))

theorem fz2_4_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK4)) = 0 :=
  Q2.repsFixedCard2 rK4 ⟨7, by decide⟩ Q2.R4_2 Q2.hpxR4_2 Q2.hcardq4_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_4) 7 (by decide)))

theorem fz2_4_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK4)) = 0 :=
  Q2.repsFixedCard2 rK4 ⟨8, by decide⟩ Q2.R4_2 Q2.hpxR4_2 Q2.hcardq4_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_4) 8 (by decide)))

theorem fz2_4_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK4)) = 0 :=
  Q2.repsFixedCard2 rK4 ⟨9, by decide⟩ Q2.R4_2 Q2.hpxR4_2 Q2.hcardq4_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_4) 9 (by decide)))

theorem fz2_4_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK4)) = 0 :=
  Q2.repsFixedCard2 rK4 ⟨10, by decide⟩ Q2.R4_2 Q2.hpxR4_2 Q2.hcardq4_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_4) 10 (by decide)))

theorem fz2_4_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK4)) = 0 :=
  Q2.repsFixedCard2 rK4 ⟨11, by decide⟩ Q2.R4_2 Q2.hpxR4_2 Q2.hcardq4_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_4) 11 (by decide)))

theorem fz2_4_12 : Fintype.card
    (fixedPoints (Q2.reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK4)) = 0 :=
  Q2.repsFixedCard2 rK4 ⟨12, by decide⟩ Q2.R4_2 Q2.hpxR4_2 Q2.hcardq4_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_4) 12 (by decide)))

end LeanDring.P5Presentation
