/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryK.C006

/-!
# Species-table cells, off-support emptiness certificates, chunk 4

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

theorem fixz1_5 : ([1, 2, 3, 4, 6, 7, 8, 9, 10, 11, 12] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 625 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK5) (retConj 1 (R5 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_5_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK5)) = 0 :=
  repsFixedCard rK5 ⟨1, by decide⟩ R5 hpxR5 hcardq5
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_5) 1 (by decide)))

theorem fz1_5_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK5)) = 0 :=
  repsFixedCard rK5 ⟨2, by decide⟩ R5 hpxR5 hcardq5
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_5) 2 (by decide)))

theorem fz1_5_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK5)) = 0 :=
  repsFixedCard rK5 ⟨3, by decide⟩ R5 hpxR5 hcardq5
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_5) 3 (by decide)))

theorem fz1_5_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK5)) = 0 :=
  repsFixedCard rK5 ⟨4, by decide⟩ R5 hpxR5 hcardq5
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_5) 4 (by decide)))

theorem fz1_5_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK5)) = 0 :=
  repsFixedCard rK5 ⟨6, by decide⟩ R5 hpxR5 hcardq5
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_5) 6 (by decide)))

theorem fz1_5_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK5)) = 0 :=
  repsFixedCard rK5 ⟨7, by decide⟩ R5 hpxR5 hcardq5
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_5) 7 (by decide)))

theorem fz1_5_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK5)) = 0 :=
  repsFixedCard rK5 ⟨8, by decide⟩ R5 hpxR5 hcardq5
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_5) 8 (by decide)))

theorem fz1_5_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK5)) = 0 :=
  repsFixedCard rK5 ⟨9, by decide⟩ R5 hpxR5 hcardq5
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_5) 9 (by decide)))

theorem fz1_5_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK5)) = 0 :=
  repsFixedCard rK5 ⟨10, by decide⟩ R5 hpxR5 hcardq5
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_5) 10 (by decide)))

theorem fz1_5_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK5)) = 0 :=
  repsFixedCard rK5 ⟨11, by decide⟩ R5 hpxR5 hcardq5
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_5) 11 (by decide)))

theorem fz1_5_12 : Fintype.card
    (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK5)) = 0 :=
  repsFixedCard rK5 ⟨12, by decide⟩ R5 hpxR5 hcardq5
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_5) 12 (by decide)))

theorem fixz2_5 : ([1, 2, 3, 4, 6, 7, 8, 9, 10, 11, 12] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 625 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK5) (retConj 2 (Q2.R5_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_5_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK5)) = 0 :=
  Q2.repsFixedCard2 rK5 ⟨1, by decide⟩ Q2.R5_2 Q2.hpxR5_2 Q2.hcardq5_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_5) 1 (by decide)))

theorem fz2_5_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK5)) = 0 :=
  Q2.repsFixedCard2 rK5 ⟨2, by decide⟩ Q2.R5_2 Q2.hpxR5_2 Q2.hcardq5_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_5) 2 (by decide)))

theorem fz2_5_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK5)) = 0 :=
  Q2.repsFixedCard2 rK5 ⟨3, by decide⟩ Q2.R5_2 Q2.hpxR5_2 Q2.hcardq5_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_5) 3 (by decide)))

theorem fz2_5_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK5)) = 0 :=
  Q2.repsFixedCard2 rK5 ⟨4, by decide⟩ Q2.R5_2 Q2.hpxR5_2 Q2.hcardq5_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_5) 4 (by decide)))

theorem fz2_5_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK5)) = 0 :=
  Q2.repsFixedCard2 rK5 ⟨6, by decide⟩ Q2.R5_2 Q2.hpxR5_2 Q2.hcardq5_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_5) 6 (by decide)))

theorem fz2_5_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK5)) = 0 :=
  Q2.repsFixedCard2 rK5 ⟨7, by decide⟩ Q2.R5_2 Q2.hpxR5_2 Q2.hcardq5_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_5) 7 (by decide)))

theorem fz2_5_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK5)) = 0 :=
  Q2.repsFixedCard2 rK5 ⟨8, by decide⟩ Q2.R5_2 Q2.hpxR5_2 Q2.hcardq5_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_5) 8 (by decide)))

theorem fz2_5_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK5)) = 0 :=
  Q2.repsFixedCard2 rK5 ⟨9, by decide⟩ Q2.R5_2 Q2.hpxR5_2 Q2.hcardq5_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_5) 9 (by decide)))

theorem fz2_5_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK5)) = 0 :=
  Q2.repsFixedCard2 rK5 ⟨10, by decide⟩ Q2.R5_2 Q2.hpxR5_2 Q2.hcardq5_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_5) 10 (by decide)))

theorem fz2_5_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK5)) = 0 :=
  Q2.repsFixedCard2 rK5 ⟨11, by decide⟩ Q2.R5_2 Q2.hpxR5_2 Q2.hcardq5_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_5) 11 (by decide)))

theorem fz2_5_12 : Fintype.card
    (fixedPoints (Q2.reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK5)) = 0 :=
  Q2.repsFixedCard2 rK5 ⟨12, by decide⟩ Q2.R5_2 Q2.hpxR5_2 Q2.hcardq5_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_5) 12 (by decide)))

end LeanDring.P5Presentation
