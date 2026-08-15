/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryA.C031

/-!
# Species-table cells, off-support emptiness certificates, chunk 42

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

theorem fixz1_43 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK43) (retConj 1 (R43 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_43_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨1, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 1 (by decide)))

theorem fz1_43_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨2, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 2 (by decide)))

theorem fz1_43_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨3, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 3 (by decide)))

theorem fz1_43_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨4, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 4 (by decide)))

theorem fz1_43_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨5, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 5 (by decide)))

theorem fz1_43_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨6, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 6 (by decide)))

theorem fz1_43_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨7, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 7 (by decide)))

theorem fz1_43_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨8, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 8 (by decide)))

theorem fz1_43_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨9, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 9 (by decide)))

theorem fz1_43_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨10, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 10 (by decide)))

theorem fz1_43_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨11, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 11 (by decide)))

theorem fz1_43_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨13, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 13 (by decide)))

theorem fz1_43_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨14, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 14 (by decide)))

theorem fz1_43_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨15, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 15 (by decide)))

theorem fz1_43_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨16, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 16 (by decide)))

theorem fz1_43_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨17, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 17 (by decide)))

theorem fz1_43_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨18, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 18 (by decide)))

theorem fz1_43_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨19, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 19 (by decide)))

theorem fz1_43_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨20, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 20 (by decide)))

theorem fz1_43_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨21, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 21 (by decide)))

theorem fz1_43_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨22, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 22 (by decide)))

theorem fz1_43_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨23, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 23 (by decide)))

theorem fz1_43_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨24, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 24 (by decide)))

theorem fz1_43_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨25, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 25 (by decide)))

theorem fz1_43_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨26, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 26 (by decide)))

theorem fz1_43_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨27, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 27 (by decide)))

theorem fz1_43_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨28, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 28 (by decide)))

theorem fz1_43_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨29, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 29 (by decide)))

theorem fz1_43_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨30, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 30 (by decide)))

theorem fz1_43_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨31, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 31 (by decide)))

theorem fz1_43_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨32, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 32 (by decide)))

theorem fz1_43_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨33, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 33 (by decide)))

theorem fz1_43_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨34, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 34 (by decide)))

theorem fz1_43_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨35, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 35 (by decide)))

theorem fz1_43_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨36, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 36 (by decide)))

theorem fz1_43_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨37, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 37 (by decide)))

theorem fz1_43_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨38, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 38 (by decide)))

theorem fz1_43_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨39, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 39 (by decide)))

theorem fz1_43_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨40, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 40 (by decide)))

theorem fz1_43_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨41, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 41 (by decide)))

theorem fz1_43_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨42, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 42 (by decide)))

theorem fz1_43_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨44, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 44 (by decide)))

theorem fz1_43_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨45, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 45 (by decide)))

theorem fz1_43_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨46, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 46 (by decide)))

theorem fz1_43_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨47, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 47 (by decide)))

theorem fz1_43_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨48, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 48 (by decide)))

theorem fz1_43_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨49, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 49 (by decide)))

theorem fz1_43_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨50, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 50 (by decide)))

theorem fz1_43_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨51, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 51 (by decide)))

theorem fz1_43_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨52, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 52 (by decide)))

theorem fz1_43_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨53, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 53 (by decide)))

theorem fz1_43_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK43)) = 0 :=
  repsFixedCard rK43 ⟨54, by decide⟩ R43 hpxR43 hcardq43
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_43) 54 (by decide)))

theorem fixz2_43 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK43) (retConj 2 (Q2.R43_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_43_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨1, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 1 (by decide)))

theorem fz2_43_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨2, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 2 (by decide)))

theorem fz2_43_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨3, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 3 (by decide)))

theorem fz2_43_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨4, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 4 (by decide)))

theorem fz2_43_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨5, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 5 (by decide)))

theorem fz2_43_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨6, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 6 (by decide)))

theorem fz2_43_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨7, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 7 (by decide)))

theorem fz2_43_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨8, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 8 (by decide)))

theorem fz2_43_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨9, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 9 (by decide)))

theorem fz2_43_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨10, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 10 (by decide)))

theorem fz2_43_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨11, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 11 (by decide)))

theorem fz2_43_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨13, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 13 (by decide)))

theorem fz2_43_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨14, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 14 (by decide)))

theorem fz2_43_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨15, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 15 (by decide)))

theorem fz2_43_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨16, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 16 (by decide)))

theorem fz2_43_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨17, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 17 (by decide)))

theorem fz2_43_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨18, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 18 (by decide)))

theorem fz2_43_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨19, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 19 (by decide)))

theorem fz2_43_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨20, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 20 (by decide)))

theorem fz2_43_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨21, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 21 (by decide)))

theorem fz2_43_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨22, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 22 (by decide)))

theorem fz2_43_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨23, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 23 (by decide)))

theorem fz2_43_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨24, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 24 (by decide)))

theorem fz2_43_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨25, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 25 (by decide)))

theorem fz2_43_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨26, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 26 (by decide)))

theorem fz2_43_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨27, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 27 (by decide)))

theorem fz2_43_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨28, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 28 (by decide)))

theorem fz2_43_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨29, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 29 (by decide)))

theorem fz2_43_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨30, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 30 (by decide)))

theorem fz2_43_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨31, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 31 (by decide)))

theorem fz2_43_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨32, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 32 (by decide)))

theorem fz2_43_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨33, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 33 (by decide)))

theorem fz2_43_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨34, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 34 (by decide)))

theorem fz2_43_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨35, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 35 (by decide)))

theorem fz2_43_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨36, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 36 (by decide)))

theorem fz2_43_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨37, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 37 (by decide)))

theorem fz2_43_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨38, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 38 (by decide)))

theorem fz2_43_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨39, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 39 (by decide)))

theorem fz2_43_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨40, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 40 (by decide)))

theorem fz2_43_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨41, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 41 (by decide)))

theorem fz2_43_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨42, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 42 (by decide)))

theorem fz2_43_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨44, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 44 (by decide)))

theorem fz2_43_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨45, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 45 (by decide)))

theorem fz2_43_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨46, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 46 (by decide)))

theorem fz2_43_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨47, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 47 (by decide)))

theorem fz2_43_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨48, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 48 (by decide)))

theorem fz2_43_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨49, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 49 (by decide)))

theorem fz2_43_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨50, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 50 (by decide)))

theorem fz2_43_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨51, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 51 (by decide)))

theorem fz2_43_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨52, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 52 (by decide)))

theorem fz2_43_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨53, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 53 (by decide)))

theorem fz2_43_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK43)) = 0 :=
  Q2.repsFixedCard2 rK43 ⟨54, by decide⟩ Q2.R43_2 Q2.hpxR43_2 Q2.hcardq43_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_43) 54 (by decide)))

end LeanDring.P5Presentation
