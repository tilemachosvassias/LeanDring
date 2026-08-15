/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryA.C029

/-!
# Species-table cells, off-support emptiness certificates, chunk 40

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

theorem fixz1_41 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK41) (retConj 1 (R41 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_41_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨1, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 1 (by decide)))

theorem fz1_41_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨2, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 2 (by decide)))

theorem fz1_41_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨3, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 3 (by decide)))

theorem fz1_41_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨4, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 4 (by decide)))

theorem fz1_41_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨5, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 5 (by decide)))

theorem fz1_41_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨6, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 6 (by decide)))

theorem fz1_41_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨7, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 7 (by decide)))

theorem fz1_41_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨8, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 8 (by decide)))

theorem fz1_41_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨9, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 9 (by decide)))

theorem fz1_41_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨10, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 10 (by decide)))

theorem fz1_41_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨11, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 11 (by decide)))

theorem fz1_41_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨13, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 13 (by decide)))

theorem fz1_41_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨14, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 14 (by decide)))

theorem fz1_41_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨15, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 15 (by decide)))

theorem fz1_41_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨16, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 16 (by decide)))

theorem fz1_41_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨17, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 17 (by decide)))

theorem fz1_41_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨18, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 18 (by decide)))

theorem fz1_41_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨19, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 19 (by decide)))

theorem fz1_41_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨20, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 20 (by decide)))

theorem fz1_41_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨21, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 21 (by decide)))

theorem fz1_41_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨22, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 22 (by decide)))

theorem fz1_41_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨23, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 23 (by decide)))

theorem fz1_41_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨24, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 24 (by decide)))

theorem fz1_41_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨25, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 25 (by decide)))

theorem fz1_41_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨26, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 26 (by decide)))

theorem fz1_41_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨27, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 27 (by decide)))

theorem fz1_41_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨28, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 28 (by decide)))

theorem fz1_41_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨29, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 29 (by decide)))

theorem fz1_41_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨30, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 30 (by decide)))

theorem fz1_41_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨31, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 31 (by decide)))

theorem fz1_41_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨32, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 32 (by decide)))

theorem fz1_41_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨33, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 33 (by decide)))

theorem fz1_41_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨34, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 34 (by decide)))

theorem fz1_41_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨35, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 35 (by decide)))

theorem fz1_41_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨36, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 36 (by decide)))

theorem fz1_41_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨37, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 37 (by decide)))

theorem fz1_41_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨38, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 38 (by decide)))

theorem fz1_41_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨39, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 39 (by decide)))

theorem fz1_41_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨40, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 40 (by decide)))

theorem fz1_41_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨42, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 42 (by decide)))

theorem fz1_41_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨43, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 43 (by decide)))

theorem fz1_41_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨44, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 44 (by decide)))

theorem fz1_41_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨45, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 45 (by decide)))

theorem fz1_41_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨46, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 46 (by decide)))

theorem fz1_41_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨47, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 47 (by decide)))

theorem fz1_41_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨48, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 48 (by decide)))

theorem fz1_41_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨49, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 49 (by decide)))

theorem fz1_41_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨50, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 50 (by decide)))

theorem fz1_41_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨51, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 51 (by decide)))

theorem fz1_41_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨52, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 52 (by decide)))

theorem fz1_41_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨53, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 53 (by decide)))

theorem fz1_41_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK41)) = 0 :=
  repsFixedCard rK41 ⟨54, by decide⟩ R41 hpxR41 hcardq41
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_41) 54 (by decide)))

theorem fixz2_41 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK41) (retConj 2 (Q2.R41_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_41_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨1, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 1 (by decide)))

theorem fz2_41_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨2, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 2 (by decide)))

theorem fz2_41_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨3, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 3 (by decide)))

theorem fz2_41_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨4, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 4 (by decide)))

theorem fz2_41_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨5, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 5 (by decide)))

theorem fz2_41_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨6, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 6 (by decide)))

theorem fz2_41_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨7, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 7 (by decide)))

theorem fz2_41_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨8, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 8 (by decide)))

theorem fz2_41_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨9, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 9 (by decide)))

theorem fz2_41_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨10, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 10 (by decide)))

theorem fz2_41_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨11, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 11 (by decide)))

theorem fz2_41_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨13, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 13 (by decide)))

theorem fz2_41_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨14, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 14 (by decide)))

theorem fz2_41_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨15, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 15 (by decide)))

theorem fz2_41_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨16, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 16 (by decide)))

theorem fz2_41_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨17, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 17 (by decide)))

theorem fz2_41_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨18, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 18 (by decide)))

theorem fz2_41_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨19, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 19 (by decide)))

theorem fz2_41_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨20, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 20 (by decide)))

theorem fz2_41_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨21, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 21 (by decide)))

theorem fz2_41_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨22, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 22 (by decide)))

theorem fz2_41_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨23, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 23 (by decide)))

theorem fz2_41_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨24, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 24 (by decide)))

theorem fz2_41_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨25, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 25 (by decide)))

theorem fz2_41_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨26, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 26 (by decide)))

theorem fz2_41_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨27, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 27 (by decide)))

theorem fz2_41_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨28, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 28 (by decide)))

theorem fz2_41_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨29, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 29 (by decide)))

theorem fz2_41_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨30, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 30 (by decide)))

theorem fz2_41_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨31, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 31 (by decide)))

theorem fz2_41_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨32, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 32 (by decide)))

theorem fz2_41_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨33, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 33 (by decide)))

theorem fz2_41_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨34, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 34 (by decide)))

theorem fz2_41_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨35, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 35 (by decide)))

theorem fz2_41_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨36, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 36 (by decide)))

theorem fz2_41_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨37, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 37 (by decide)))

theorem fz2_41_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨38, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 38 (by decide)))

theorem fz2_41_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨39, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 39 (by decide)))

theorem fz2_41_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨40, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 40 (by decide)))

theorem fz2_41_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨42, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 42 (by decide)))

theorem fz2_41_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨43, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 43 (by decide)))

theorem fz2_41_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨44, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 44 (by decide)))

theorem fz2_41_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨45, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 45 (by decide)))

theorem fz2_41_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨46, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 46 (by decide)))

theorem fz2_41_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨47, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 47 (by decide)))

theorem fz2_41_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨48, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 48 (by decide)))

theorem fz2_41_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨49, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 49 (by decide)))

theorem fz2_41_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨50, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 50 (by decide)))

theorem fz2_41_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨51, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 51 (by decide)))

theorem fz2_41_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨52, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 52 (by decide)))

theorem fz2_41_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨53, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 53 (by decide)))

theorem fz2_41_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK41)) = 0 :=
  Q2.repsFixedCard2 rK41 ⟨54, by decide⟩ Q2.R41_2 Q2.hpxR41_2 Q2.hcardq41_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_41) 54 (by decide)))

end LeanDring.P5Presentation
