/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryK.C008

/-!
# Species-table cells, off-support emptiness certificates, chunk 6

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

theorem fixz1_7 : ([1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 625 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK7) (retConj 1 (R7 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_7_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK7)) = 0 :=
  repsFixedCard rK7 ⟨1, by decide⟩ R7 hpxR7 hcardq7
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_7) 1 (by decide)))

theorem fz1_7_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK7)) = 0 :=
  repsFixedCard rK7 ⟨2, by decide⟩ R7 hpxR7 hcardq7
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_7) 2 (by decide)))

theorem fz1_7_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK7)) = 0 :=
  repsFixedCard rK7 ⟨3, by decide⟩ R7 hpxR7 hcardq7
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_7) 3 (by decide)))

theorem fz1_7_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK7)) = 0 :=
  repsFixedCard rK7 ⟨4, by decide⟩ R7 hpxR7 hcardq7
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_7) 4 (by decide)))

theorem fz1_7_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK7)) = 0 :=
  repsFixedCard rK7 ⟨5, by decide⟩ R7 hpxR7 hcardq7
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_7) 5 (by decide)))

theorem fz1_7_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK7)) = 0 :=
  repsFixedCard rK7 ⟨6, by decide⟩ R7 hpxR7 hcardq7
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_7) 6 (by decide)))

theorem fz1_7_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK7)) = 0 :=
  repsFixedCard rK7 ⟨8, by decide⟩ R7 hpxR7 hcardq7
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_7) 8 (by decide)))

theorem fz1_7_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK7)) = 0 :=
  repsFixedCard rK7 ⟨9, by decide⟩ R7 hpxR7 hcardq7
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_7) 9 (by decide)))

theorem fz1_7_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK7)) = 0 :=
  repsFixedCard rK7 ⟨10, by decide⟩ R7 hpxR7 hcardq7
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_7) 10 (by decide)))

theorem fz1_7_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK7)) = 0 :=
  repsFixedCard rK7 ⟨11, by decide⟩ R7 hpxR7 hcardq7
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_7) 11 (by decide)))

theorem fz1_7_12 : Fintype.card
    (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK7)) = 0 :=
  repsFixedCard rK7 ⟨12, by decide⟩ R7 hpxR7 hcardq7
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_7) 12 (by decide)))

theorem fixz2_7 : ([1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 625 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK7) (retConj 2 (Q2.R7_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_7_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK7)) = 0 :=
  Q2.repsFixedCard2 rK7 ⟨1, by decide⟩ Q2.R7_2 Q2.hpxR7_2 Q2.hcardq7_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_7) 1 (by decide)))

theorem fz2_7_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK7)) = 0 :=
  Q2.repsFixedCard2 rK7 ⟨2, by decide⟩ Q2.R7_2 Q2.hpxR7_2 Q2.hcardq7_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_7) 2 (by decide)))

theorem fz2_7_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK7)) = 0 :=
  Q2.repsFixedCard2 rK7 ⟨3, by decide⟩ Q2.R7_2 Q2.hpxR7_2 Q2.hcardq7_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_7) 3 (by decide)))

theorem fz2_7_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK7)) = 0 :=
  Q2.repsFixedCard2 rK7 ⟨4, by decide⟩ Q2.R7_2 Q2.hpxR7_2 Q2.hcardq7_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_7) 4 (by decide)))

theorem fz2_7_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK7)) = 0 :=
  Q2.repsFixedCard2 rK7 ⟨5, by decide⟩ Q2.R7_2 Q2.hpxR7_2 Q2.hcardq7_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_7) 5 (by decide)))

theorem fz2_7_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK7)) = 0 :=
  Q2.repsFixedCard2 rK7 ⟨6, by decide⟩ Q2.R7_2 Q2.hpxR7_2 Q2.hcardq7_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_7) 6 (by decide)))

theorem fz2_7_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK7)) = 0 :=
  Q2.repsFixedCard2 rK7 ⟨8, by decide⟩ Q2.R7_2 Q2.hpxR7_2 Q2.hcardq7_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_7) 8 (by decide)))

theorem fz2_7_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK7)) = 0 :=
  Q2.repsFixedCard2 rK7 ⟨9, by decide⟩ Q2.R7_2 Q2.hpxR7_2 Q2.hcardq7_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_7) 9 (by decide)))

theorem fz2_7_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK7)) = 0 :=
  Q2.repsFixedCard2 rK7 ⟨10, by decide⟩ Q2.R7_2 Q2.hpxR7_2 Q2.hcardq7_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_7) 10 (by decide)))

theorem fz2_7_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK7)) = 0 :=
  Q2.repsFixedCard2 rK7 ⟨11, by decide⟩ Q2.R7_2 Q2.hpxR7_2 Q2.hcardq7_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_7) 11 (by decide)))

theorem fz2_7_12 : Fintype.card
    (fixedPoints (Q2.reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK7)) = 0 :=
  Q2.repsFixedCard2 rK7 ⟨12, by decide⟩ Q2.R7_2 Q2.hpxR7_2 Q2.hcardq7_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_7) 12 (by decide)))

end LeanDring.P5Presentation
