/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryK.C011

/-!
# Species-table cells, off-support emptiness certificates, chunk 9

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

theorem fixz1_10 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 625 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK10) (retConj 1 (R10 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_10_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK10)) = 0 :=
  repsFixedCard rK10 ⟨1, by decide⟩ R10 hpxR10 hcardq10
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_10) 1 (by decide)))

theorem fz1_10_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK10)) = 0 :=
  repsFixedCard rK10 ⟨2, by decide⟩ R10 hpxR10 hcardq10
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_10) 2 (by decide)))

theorem fz1_10_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK10)) = 0 :=
  repsFixedCard rK10 ⟨3, by decide⟩ R10 hpxR10 hcardq10
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_10) 3 (by decide)))

theorem fz1_10_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK10)) = 0 :=
  repsFixedCard rK10 ⟨4, by decide⟩ R10 hpxR10 hcardq10
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_10) 4 (by decide)))

theorem fz1_10_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK10)) = 0 :=
  repsFixedCard rK10 ⟨5, by decide⟩ R10 hpxR10 hcardq10
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_10) 5 (by decide)))

theorem fz1_10_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK10)) = 0 :=
  repsFixedCard rK10 ⟨6, by decide⟩ R10 hpxR10 hcardq10
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_10) 6 (by decide)))

theorem fz1_10_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK10)) = 0 :=
  repsFixedCard rK10 ⟨7, by decide⟩ R10 hpxR10 hcardq10
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_10) 7 (by decide)))

theorem fz1_10_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK10)) = 0 :=
  repsFixedCard rK10 ⟨8, by decide⟩ R10 hpxR10 hcardq10
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_10) 8 (by decide)))

theorem fz1_10_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK10)) = 0 :=
  repsFixedCard rK10 ⟨9, by decide⟩ R10 hpxR10 hcardq10
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_10) 9 (by decide)))

theorem fz1_10_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK10)) = 0 :=
  repsFixedCard rK10 ⟨11, by decide⟩ R10 hpxR10 hcardq10
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_10) 11 (by decide)))

theorem fz1_10_12 : Fintype.card
    (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK10)) = 0 :=
  repsFixedCard rK10 ⟨12, by decide⟩ R10 hpxR10 hcardq10
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_10) 12 (by decide)))

theorem fixz2_10 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 625 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK10) (retConj 2 (Q2.R10_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_10_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK10)) = 0 :=
  Q2.repsFixedCard2 rK10 ⟨1, by decide⟩ Q2.R10_2 Q2.hpxR10_2 Q2.hcardq10_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_10) 1 (by decide)))

theorem fz2_10_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK10)) = 0 :=
  Q2.repsFixedCard2 rK10 ⟨2, by decide⟩ Q2.R10_2 Q2.hpxR10_2 Q2.hcardq10_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_10) 2 (by decide)))

theorem fz2_10_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK10)) = 0 :=
  Q2.repsFixedCard2 rK10 ⟨3, by decide⟩ Q2.R10_2 Q2.hpxR10_2 Q2.hcardq10_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_10) 3 (by decide)))

theorem fz2_10_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK10)) = 0 :=
  Q2.repsFixedCard2 rK10 ⟨4, by decide⟩ Q2.R10_2 Q2.hpxR10_2 Q2.hcardq10_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_10) 4 (by decide)))

theorem fz2_10_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK10)) = 0 :=
  Q2.repsFixedCard2 rK10 ⟨5, by decide⟩ Q2.R10_2 Q2.hpxR10_2 Q2.hcardq10_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_10) 5 (by decide)))

theorem fz2_10_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK10)) = 0 :=
  Q2.repsFixedCard2 rK10 ⟨6, by decide⟩ Q2.R10_2 Q2.hpxR10_2 Q2.hcardq10_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_10) 6 (by decide)))

theorem fz2_10_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK10)) = 0 :=
  Q2.repsFixedCard2 rK10 ⟨7, by decide⟩ Q2.R10_2 Q2.hpxR10_2 Q2.hcardq10_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_10) 7 (by decide)))

theorem fz2_10_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK10)) = 0 :=
  Q2.repsFixedCard2 rK10 ⟨8, by decide⟩ Q2.R10_2 Q2.hpxR10_2 Q2.hcardq10_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_10) 8 (by decide)))

theorem fz2_10_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK10)) = 0 :=
  Q2.repsFixedCard2 rK10 ⟨9, by decide⟩ Q2.R10_2 Q2.hpxR10_2 Q2.hcardq10_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_10) 9 (by decide)))

theorem fz2_10_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK10)) = 0 :=
  Q2.repsFixedCard2 rK10 ⟨11, by decide⟩ Q2.R10_2 Q2.hpxR10_2 Q2.hcardq10_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_10) 11 (by decide)))

theorem fz2_10_12 : Fintype.card
    (fixedPoints (Q2.reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK10)) = 0 :=
  Q2.repsFixedCard2 rK10 ⟨12, by decide⟩ Q2.R10_2 Q2.hpxR10_2 Q2.hcardq10_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_10) 12 (by decide)))

end LeanDring.P5Presentation
