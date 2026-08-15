/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryA.C008

/-!
# Species-table cells, off-support emptiness certificates, chunk 19

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

theorem fixz1_20 : ([1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK20) (retConj 1 (R20 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_20_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨1, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 1 (by decide)))

theorem fz1_20_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨3, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 3 (by decide)))

theorem fz1_20_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨4, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 4 (by decide)))

theorem fz1_20_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨5, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 5 (by decide)))

theorem fz1_20_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨6, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 6 (by decide)))

theorem fz1_20_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨7, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 7 (by decide)))

theorem fz1_20_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨8, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 8 (by decide)))

theorem fz1_20_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨9, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 9 (by decide)))

theorem fz1_20_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨10, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 10 (by decide)))

theorem fz1_20_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨11, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 11 (by decide)))

theorem fz1_20_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨13, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 13 (by decide)))

theorem fz1_20_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨14, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 14 (by decide)))

theorem fz1_20_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨15, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 15 (by decide)))

theorem fz1_20_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨16, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 16 (by decide)))

theorem fz1_20_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨17, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 17 (by decide)))

theorem fz1_20_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨18, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 18 (by decide)))

theorem fz1_20_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨19, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 19 (by decide)))

theorem fz1_20_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨21, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 21 (by decide)))

theorem fz1_20_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨22, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 22 (by decide)))

theorem fz1_20_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨23, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 23 (by decide)))

theorem fz1_20_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨24, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 24 (by decide)))

theorem fz1_20_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨25, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 25 (by decide)))

theorem fz1_20_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨26, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 26 (by decide)))

theorem fz1_20_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨27, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 27 (by decide)))

theorem fz1_20_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨28, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 28 (by decide)))

theorem fz1_20_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨29, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 29 (by decide)))

theorem fz1_20_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨30, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 30 (by decide)))

theorem fz1_20_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨31, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 31 (by decide)))

theorem fz1_20_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨32, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 32 (by decide)))

theorem fz1_20_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨33, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 33 (by decide)))

theorem fz1_20_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨34, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 34 (by decide)))

theorem fz1_20_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨35, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 35 (by decide)))

theorem fz1_20_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨36, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 36 (by decide)))

theorem fz1_20_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨37, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 37 (by decide)))

theorem fz1_20_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨38, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 38 (by decide)))

theorem fz1_20_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨39, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 39 (by decide)))

theorem fz1_20_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨40, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 40 (by decide)))

theorem fz1_20_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨41, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 41 (by decide)))

theorem fz1_20_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨42, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 42 (by decide)))

theorem fz1_20_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨43, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 43 (by decide)))

theorem fz1_20_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨44, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 44 (by decide)))

theorem fz1_20_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨45, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 45 (by decide)))

theorem fz1_20_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨46, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 46 (by decide)))

theorem fz1_20_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨47, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 47 (by decide)))

theorem fz1_20_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨48, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 48 (by decide)))

theorem fz1_20_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨49, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 49 (by decide)))

theorem fz1_20_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨50, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 50 (by decide)))

theorem fz1_20_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨51, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 51 (by decide)))

theorem fz1_20_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨52, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 52 (by decide)))

theorem fz1_20_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨53, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 53 (by decide)))

theorem fz1_20_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK20)) = 0 :=
  repsFixedCard rK20 ⟨54, by decide⟩ R20 hpxR20 hcardq20
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_20) 54 (by decide)))

theorem fixz2_20 : ([1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK20) (retConj 2 (Q2.R20_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_20_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨1, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 1 (by decide)))

theorem fz2_20_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨3, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 3 (by decide)))

theorem fz2_20_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨4, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 4 (by decide)))

theorem fz2_20_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨5, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 5 (by decide)))

theorem fz2_20_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨6, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 6 (by decide)))

theorem fz2_20_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨7, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 7 (by decide)))

theorem fz2_20_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨8, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 8 (by decide)))

theorem fz2_20_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨9, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 9 (by decide)))

theorem fz2_20_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨10, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 10 (by decide)))

theorem fz2_20_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨11, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 11 (by decide)))

theorem fz2_20_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨13, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 13 (by decide)))

theorem fz2_20_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨14, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 14 (by decide)))

theorem fz2_20_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨15, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 15 (by decide)))

theorem fz2_20_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨16, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 16 (by decide)))

theorem fz2_20_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨17, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 17 (by decide)))

theorem fz2_20_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨18, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 18 (by decide)))

theorem fz2_20_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨19, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 19 (by decide)))

theorem fz2_20_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨21, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 21 (by decide)))

theorem fz2_20_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨22, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 22 (by decide)))

theorem fz2_20_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨23, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 23 (by decide)))

theorem fz2_20_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨24, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 24 (by decide)))

theorem fz2_20_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨25, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 25 (by decide)))

theorem fz2_20_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨26, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 26 (by decide)))

theorem fz2_20_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨27, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 27 (by decide)))

theorem fz2_20_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨28, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 28 (by decide)))

theorem fz2_20_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨29, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 29 (by decide)))

theorem fz2_20_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨30, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 30 (by decide)))

theorem fz2_20_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨31, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 31 (by decide)))

theorem fz2_20_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨32, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 32 (by decide)))

theorem fz2_20_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨33, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 33 (by decide)))

theorem fz2_20_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨34, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 34 (by decide)))

theorem fz2_20_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨35, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 35 (by decide)))

theorem fz2_20_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨36, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 36 (by decide)))

theorem fz2_20_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨37, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 37 (by decide)))

theorem fz2_20_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨38, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 38 (by decide)))

theorem fz2_20_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨39, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 39 (by decide)))

theorem fz2_20_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨40, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 40 (by decide)))

theorem fz2_20_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨41, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 41 (by decide)))

theorem fz2_20_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨42, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 42 (by decide)))

theorem fz2_20_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨43, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 43 (by decide)))

theorem fz2_20_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨44, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 44 (by decide)))

theorem fz2_20_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨45, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 45 (by decide)))

theorem fz2_20_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨46, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 46 (by decide)))

theorem fz2_20_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨47, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 47 (by decide)))

theorem fz2_20_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨48, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 48 (by decide)))

theorem fz2_20_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨49, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 49 (by decide)))

theorem fz2_20_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨50, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 50 (by decide)))

theorem fz2_20_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨51, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 51 (by decide)))

theorem fz2_20_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨52, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 52 (by decide)))

theorem fz2_20_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨53, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 53 (by decide)))

theorem fz2_20_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK20)) = 0 :=
  Q2.repsFixedCard2 rK20 ⟨54, by decide⟩ Q2.R20_2 Q2.hpxR20_2 Q2.hcardq20_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_20) 54 (by decide)))

end LeanDring.P5Presentation
