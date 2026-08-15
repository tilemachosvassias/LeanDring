/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryK.C002

/-!
# Species-table cells, off-support emptiness certificates, chunk 0

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

theorem fixz1_1 : ([2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 625 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK1) (retConj 1 (R1 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_1_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK1)) = 0 :=
  repsFixedCard rK1 ⟨2, by decide⟩ R1 hpxR1 hcardq1
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_1) 2 (by decide)))

theorem fz1_1_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK1)) = 0 :=
  repsFixedCard rK1 ⟨3, by decide⟩ R1 hpxR1 hcardq1
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_1) 3 (by decide)))

theorem fz1_1_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK1)) = 0 :=
  repsFixedCard rK1 ⟨4, by decide⟩ R1 hpxR1 hcardq1
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_1) 4 (by decide)))

theorem fz1_1_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK1)) = 0 :=
  repsFixedCard rK1 ⟨5, by decide⟩ R1 hpxR1 hcardq1
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_1) 5 (by decide)))

theorem fz1_1_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK1)) = 0 :=
  repsFixedCard rK1 ⟨6, by decide⟩ R1 hpxR1 hcardq1
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_1) 6 (by decide)))

theorem fz1_1_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK1)) = 0 :=
  repsFixedCard rK1 ⟨7, by decide⟩ R1 hpxR1 hcardq1
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_1) 7 (by decide)))

theorem fz1_1_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK1)) = 0 :=
  repsFixedCard rK1 ⟨8, by decide⟩ R1 hpxR1 hcardq1
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_1) 8 (by decide)))

theorem fz1_1_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK1)) = 0 :=
  repsFixedCard rK1 ⟨9, by decide⟩ R1 hpxR1 hcardq1
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_1) 9 (by decide)))

theorem fz1_1_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK1)) = 0 :=
  repsFixedCard rK1 ⟨10, by decide⟩ R1 hpxR1 hcardq1
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_1) 10 (by decide)))

theorem fz1_1_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK1)) = 0 :=
  repsFixedCard rK1 ⟨11, by decide⟩ R1 hpxR1 hcardq1
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_1) 11 (by decide)))

theorem fz1_1_12 : Fintype.card
    (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK1)) = 0 :=
  repsFixedCard rK1 ⟨12, by decide⟩ R1 hpxR1 hcardq1
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_1) 12 (by decide)))

theorem fixz2_1 : ([2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 625 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK1) (retConj 2 (Q2.R1_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_1_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK1)) = 0 :=
  Q2.repsFixedCard2 rK1 ⟨2, by decide⟩ Q2.R1_2 Q2.hpxR1_2 Q2.hcardq1_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_1) 2 (by decide)))

theorem fz2_1_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK1)) = 0 :=
  Q2.repsFixedCard2 rK1 ⟨3, by decide⟩ Q2.R1_2 Q2.hpxR1_2 Q2.hcardq1_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_1) 3 (by decide)))

theorem fz2_1_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK1)) = 0 :=
  Q2.repsFixedCard2 rK1 ⟨4, by decide⟩ Q2.R1_2 Q2.hpxR1_2 Q2.hcardq1_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_1) 4 (by decide)))

theorem fz2_1_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK1)) = 0 :=
  Q2.repsFixedCard2 rK1 ⟨5, by decide⟩ Q2.R1_2 Q2.hpxR1_2 Q2.hcardq1_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_1) 5 (by decide)))

theorem fz2_1_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK1)) = 0 :=
  Q2.repsFixedCard2 rK1 ⟨6, by decide⟩ Q2.R1_2 Q2.hpxR1_2 Q2.hcardq1_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_1) 6 (by decide)))

theorem fz2_1_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK1)) = 0 :=
  Q2.repsFixedCard2 rK1 ⟨7, by decide⟩ Q2.R1_2 Q2.hpxR1_2 Q2.hcardq1_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_1) 7 (by decide)))

theorem fz2_1_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK1)) = 0 :=
  Q2.repsFixedCard2 rK1 ⟨8, by decide⟩ Q2.R1_2 Q2.hpxR1_2 Q2.hcardq1_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_1) 8 (by decide)))

theorem fz2_1_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK1)) = 0 :=
  Q2.repsFixedCard2 rK1 ⟨9, by decide⟩ Q2.R1_2 Q2.hpxR1_2 Q2.hcardq1_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_1) 9 (by decide)))

theorem fz2_1_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK1)) = 0 :=
  Q2.repsFixedCard2 rK1 ⟨10, by decide⟩ Q2.R1_2 Q2.hpxR1_2 Q2.hcardq1_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_1) 10 (by decide)))

theorem fz2_1_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK1)) = 0 :=
  Q2.repsFixedCard2 rK1 ⟨11, by decide⟩ Q2.R1_2 Q2.hpxR1_2 Q2.hcardq1_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_1) 11 (by decide)))

theorem fz2_1_12 : Fintype.card
    (fixedPoints (Q2.reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK1)) = 0 :=
  Q2.repsFixedCard2 rK1 ⟨12, by decide⟩ Q2.R1_2 Q2.hpxR1_2 Q2.hcardq1_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_1) 12 (by decide)))

end LeanDring.P5Presentation
