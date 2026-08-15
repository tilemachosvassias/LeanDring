/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryA.C041

/-!
# Species-table cells, off-support emptiness certificates, chunk 52

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

theorem fixz1_53 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK53) (retConj 1 (R53 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_53_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨1, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 1 (by decide)))

theorem fz1_53_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨2, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 2 (by decide)))

theorem fz1_53_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨3, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 3 (by decide)))

theorem fz1_53_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨4, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 4 (by decide)))

theorem fz1_53_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨5, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 5 (by decide)))

theorem fz1_53_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨6, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 6 (by decide)))

theorem fz1_53_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨7, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 7 (by decide)))

theorem fz1_53_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨8, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 8 (by decide)))

theorem fz1_53_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨9, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 9 (by decide)))

theorem fz1_53_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨11, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 11 (by decide)))

theorem fz1_53_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨13, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 13 (by decide)))

theorem fz1_53_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨14, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 14 (by decide)))

theorem fz1_53_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨15, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 15 (by decide)))

theorem fz1_53_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨16, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 16 (by decide)))

theorem fz1_53_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨17, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 17 (by decide)))

theorem fz1_53_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨18, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 18 (by decide)))

theorem fz1_53_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨19, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 19 (by decide)))

theorem fz1_53_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨20, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 20 (by decide)))

theorem fz1_53_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨21, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 21 (by decide)))

theorem fz1_53_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨22, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 22 (by decide)))

theorem fz1_53_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨23, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 23 (by decide)))

theorem fz1_53_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨24, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 24 (by decide)))

theorem fz1_53_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨25, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 25 (by decide)))

theorem fz1_53_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨26, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 26 (by decide)))

theorem fz1_53_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨27, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 27 (by decide)))

theorem fz1_53_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨28, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 28 (by decide)))

theorem fz1_53_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨29, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 29 (by decide)))

theorem fz1_53_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨30, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 30 (by decide)))

theorem fz1_53_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨31, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 31 (by decide)))

theorem fz1_53_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨32, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 32 (by decide)))

theorem fz1_53_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨33, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 33 (by decide)))

theorem fz1_53_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨34, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 34 (by decide)))

theorem fz1_53_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨35, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 35 (by decide)))

theorem fz1_53_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨36, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 36 (by decide)))

theorem fz1_53_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨37, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 37 (by decide)))

theorem fz1_53_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨38, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 38 (by decide)))

theorem fz1_53_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨39, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 39 (by decide)))

theorem fz1_53_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨40, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 40 (by decide)))

theorem fz1_53_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨41, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 41 (by decide)))

theorem fz1_53_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨42, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 42 (by decide)))

theorem fz1_53_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨43, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 43 (by decide)))

theorem fz1_53_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨44, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 44 (by decide)))

theorem fz1_53_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨45, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 45 (by decide)))

theorem fz1_53_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨46, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 46 (by decide)))

theorem fz1_53_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨47, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 47 (by decide)))

theorem fz1_53_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨48, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 48 (by decide)))

theorem fz1_53_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨49, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 49 (by decide)))

theorem fz1_53_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨50, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 50 (by decide)))

theorem fz1_53_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨51, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 51 (by decide)))

theorem fz1_53_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨52, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 52 (by decide)))

theorem fz1_53_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK53)) = 0 :=
  repsFixedCard rK53 ⟨54, by decide⟩ R53 hpxR53 hcardq53
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_53) 54 (by decide)))

theorem fixz2_53 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK53) (retConj 2 (Q2.R53_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_53_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨1, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 1 (by decide)))

theorem fz2_53_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨2, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 2 (by decide)))

theorem fz2_53_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨3, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 3 (by decide)))

theorem fz2_53_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨4, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 4 (by decide)))

theorem fz2_53_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨5, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 5 (by decide)))

theorem fz2_53_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨6, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 6 (by decide)))

theorem fz2_53_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨7, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 7 (by decide)))

theorem fz2_53_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨8, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 8 (by decide)))

theorem fz2_53_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨9, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 9 (by decide)))

theorem fz2_53_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨11, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 11 (by decide)))

theorem fz2_53_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨13, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 13 (by decide)))

theorem fz2_53_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨14, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 14 (by decide)))

theorem fz2_53_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨15, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 15 (by decide)))

theorem fz2_53_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨16, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 16 (by decide)))

theorem fz2_53_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨17, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 17 (by decide)))

theorem fz2_53_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨18, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 18 (by decide)))

theorem fz2_53_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨19, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 19 (by decide)))

theorem fz2_53_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨20, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 20 (by decide)))

theorem fz2_53_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨21, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 21 (by decide)))

theorem fz2_53_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨22, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 22 (by decide)))

theorem fz2_53_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨23, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 23 (by decide)))

theorem fz2_53_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨24, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 24 (by decide)))

theorem fz2_53_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨25, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 25 (by decide)))

theorem fz2_53_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨26, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 26 (by decide)))

theorem fz2_53_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨27, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 27 (by decide)))

theorem fz2_53_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨28, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 28 (by decide)))

theorem fz2_53_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨29, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 29 (by decide)))

theorem fz2_53_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨30, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 30 (by decide)))

theorem fz2_53_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨31, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 31 (by decide)))

theorem fz2_53_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨32, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 32 (by decide)))

theorem fz2_53_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨33, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 33 (by decide)))

theorem fz2_53_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨34, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 34 (by decide)))

theorem fz2_53_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨35, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 35 (by decide)))

theorem fz2_53_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨36, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 36 (by decide)))

theorem fz2_53_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨37, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 37 (by decide)))

theorem fz2_53_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨38, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 38 (by decide)))

theorem fz2_53_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨39, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 39 (by decide)))

theorem fz2_53_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨40, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 40 (by decide)))

theorem fz2_53_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨41, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 41 (by decide)))

theorem fz2_53_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨42, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 42 (by decide)))

theorem fz2_53_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨43, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 43 (by decide)))

theorem fz2_53_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨44, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 44 (by decide)))

theorem fz2_53_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨45, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 45 (by decide)))

theorem fz2_53_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨46, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 46 (by decide)))

theorem fz2_53_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨47, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 47 (by decide)))

theorem fz2_53_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨48, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 48 (by decide)))

theorem fz2_53_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨49, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 49 (by decide)))

theorem fz2_53_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨50, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 50 (by decide)))

theorem fz2_53_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨51, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 51 (by decide)))

theorem fz2_53_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨52, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 52 (by decide)))

theorem fz2_53_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK53)) = 0 :=
  Q2.repsFixedCard2 rK53 ⟨54, by decide⟩ Q2.R53_2 Q2.hpxR53_2 Q2.hcardq53_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_53) 54 (by decide)))

end LeanDring.P5Presentation
