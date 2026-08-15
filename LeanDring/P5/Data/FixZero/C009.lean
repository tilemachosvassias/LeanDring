/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryK.C010

/-!
# Species-table cells, off-support emptiness certificates, chunk 8

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

theorem fixz1_9 : ([1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 625 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK9) (retConj 1 (R9 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_9_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK9)) = 0 :=
  repsFixedCard rK9 ⟨1, by decide⟩ R9 hpxR9 hcardq9
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_9) 1 (by decide)))

theorem fz1_9_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK9)) = 0 :=
  repsFixedCard rK9 ⟨2, by decide⟩ R9 hpxR9 hcardq9
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_9) 2 (by decide)))

theorem fz1_9_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK9)) = 0 :=
  repsFixedCard rK9 ⟨3, by decide⟩ R9 hpxR9 hcardq9
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_9) 3 (by decide)))

theorem fz1_9_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK9)) = 0 :=
  repsFixedCard rK9 ⟨4, by decide⟩ R9 hpxR9 hcardq9
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_9) 4 (by decide)))

theorem fz1_9_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK9)) = 0 :=
  repsFixedCard rK9 ⟨5, by decide⟩ R9 hpxR9 hcardq9
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_9) 5 (by decide)))

theorem fz1_9_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK9)) = 0 :=
  repsFixedCard rK9 ⟨6, by decide⟩ R9 hpxR9 hcardq9
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_9) 6 (by decide)))

theorem fz1_9_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK9)) = 0 :=
  repsFixedCard rK9 ⟨7, by decide⟩ R9 hpxR9 hcardq9
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_9) 7 (by decide)))

theorem fz1_9_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK9)) = 0 :=
  repsFixedCard rK9 ⟨8, by decide⟩ R9 hpxR9 hcardq9
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_9) 8 (by decide)))

theorem fz1_9_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK9)) = 0 :=
  repsFixedCard rK9 ⟨10, by decide⟩ R9 hpxR9 hcardq9
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_9) 10 (by decide)))

theorem fz1_9_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK9)) = 0 :=
  repsFixedCard rK9 ⟨11, by decide⟩ R9 hpxR9 hcardq9
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_9) 11 (by decide)))

theorem fz1_9_12 : Fintype.card
    (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK9)) = 0 :=
  repsFixedCard rK9 ⟨12, by decide⟩ R9 hpxR9 hcardq9
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_9) 12 (by decide)))

theorem fixz2_9 : ([1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 625 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK9) (retConj 2 (Q2.R9_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_9_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK9)) = 0 :=
  Q2.repsFixedCard2 rK9 ⟨1, by decide⟩ Q2.R9_2 Q2.hpxR9_2 Q2.hcardq9_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_9) 1 (by decide)))

theorem fz2_9_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK9)) = 0 :=
  Q2.repsFixedCard2 rK9 ⟨2, by decide⟩ Q2.R9_2 Q2.hpxR9_2 Q2.hcardq9_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_9) 2 (by decide)))

theorem fz2_9_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK9)) = 0 :=
  Q2.repsFixedCard2 rK9 ⟨3, by decide⟩ Q2.R9_2 Q2.hpxR9_2 Q2.hcardq9_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_9) 3 (by decide)))

theorem fz2_9_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK9)) = 0 :=
  Q2.repsFixedCard2 rK9 ⟨4, by decide⟩ Q2.R9_2 Q2.hpxR9_2 Q2.hcardq9_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_9) 4 (by decide)))

theorem fz2_9_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK9)) = 0 :=
  Q2.repsFixedCard2 rK9 ⟨5, by decide⟩ Q2.R9_2 Q2.hpxR9_2 Q2.hcardq9_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_9) 5 (by decide)))

theorem fz2_9_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK9)) = 0 :=
  Q2.repsFixedCard2 rK9 ⟨6, by decide⟩ Q2.R9_2 Q2.hpxR9_2 Q2.hcardq9_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_9) 6 (by decide)))

theorem fz2_9_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK9)) = 0 :=
  Q2.repsFixedCard2 rK9 ⟨7, by decide⟩ Q2.R9_2 Q2.hpxR9_2 Q2.hcardq9_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_9) 7 (by decide)))

theorem fz2_9_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK9)) = 0 :=
  Q2.repsFixedCard2 rK9 ⟨8, by decide⟩ Q2.R9_2 Q2.hpxR9_2 Q2.hcardq9_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_9) 8 (by decide)))

theorem fz2_9_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK9)) = 0 :=
  Q2.repsFixedCard2 rK9 ⟨10, by decide⟩ Q2.R9_2 Q2.hpxR9_2 Q2.hcardq9_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_9) 10 (by decide)))

theorem fz2_9_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK9)) = 0 :=
  Q2.repsFixedCard2 rK9 ⟨11, by decide⟩ Q2.R9_2 Q2.hpxR9_2 Q2.hcardq9_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_9) 11 (by decide)))

theorem fz2_9_12 : Fintype.card
    (fixedPoints (Q2.reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK9)) = 0 :=
  Q2.repsFixedCard2 rK9 ⟨12, by decide⟩ Q2.R9_2 Q2.hpxR9_2 Q2.hcardq9_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_9) 12 (by decide)))

end LeanDring.P5Presentation
