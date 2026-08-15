/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryA.C022

/-!
# Species-table cells, off-support emptiness certificates, chunk 33

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

theorem fixz1_34 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK34) (retConj 1 (R34 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_34_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨1, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 1 (by decide)))

theorem fz1_34_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨2, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 2 (by decide)))

theorem fz1_34_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨3, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 3 (by decide)))

theorem fz1_34_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨4, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 4 (by decide)))

theorem fz1_34_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨5, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 5 (by decide)))

theorem fz1_34_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨6, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 6 (by decide)))

theorem fz1_34_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨7, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 7 (by decide)))

theorem fz1_34_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨8, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 8 (by decide)))

theorem fz1_34_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨9, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 9 (by decide)))

theorem fz1_34_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨10, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 10 (by decide)))

theorem fz1_34_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨11, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 11 (by decide)))

theorem fz1_34_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨13, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 13 (by decide)))

theorem fz1_34_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨14, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 14 (by decide)))

theorem fz1_34_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨15, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 15 (by decide)))

theorem fz1_34_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨16, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 16 (by decide)))

theorem fz1_34_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨17, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 17 (by decide)))

theorem fz1_34_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨18, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 18 (by decide)))

theorem fz1_34_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨19, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 19 (by decide)))

theorem fz1_34_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨20, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 20 (by decide)))

theorem fz1_34_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨21, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 21 (by decide)))

theorem fz1_34_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨22, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 22 (by decide)))

theorem fz1_34_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨23, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 23 (by decide)))

theorem fz1_34_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨24, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 24 (by decide)))

theorem fz1_34_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨25, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 25 (by decide)))

theorem fz1_34_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨26, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 26 (by decide)))

theorem fz1_34_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨27, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 27 (by decide)))

theorem fz1_34_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨28, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 28 (by decide)))

theorem fz1_34_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨29, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 29 (by decide)))

theorem fz1_34_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨30, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 30 (by decide)))

theorem fz1_34_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨31, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 31 (by decide)))

theorem fz1_34_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨32, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 32 (by decide)))

theorem fz1_34_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨33, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 33 (by decide)))

theorem fz1_34_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨35, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 35 (by decide)))

theorem fz1_34_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨36, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 36 (by decide)))

theorem fz1_34_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨37, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 37 (by decide)))

theorem fz1_34_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨38, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 38 (by decide)))

theorem fz1_34_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨39, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 39 (by decide)))

theorem fz1_34_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨40, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 40 (by decide)))

theorem fz1_34_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨41, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 41 (by decide)))

theorem fz1_34_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨42, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 42 (by decide)))

theorem fz1_34_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨43, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 43 (by decide)))

theorem fz1_34_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨44, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 44 (by decide)))

theorem fz1_34_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨45, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 45 (by decide)))

theorem fz1_34_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨46, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 46 (by decide)))

theorem fz1_34_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨47, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 47 (by decide)))

theorem fz1_34_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨48, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 48 (by decide)))

theorem fz1_34_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨49, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 49 (by decide)))

theorem fz1_34_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨50, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 50 (by decide)))

theorem fz1_34_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨51, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 51 (by decide)))

theorem fz1_34_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨52, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 52 (by decide)))

theorem fz1_34_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨53, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 53 (by decide)))

theorem fz1_34_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK34)) = 0 :=
  repsFixedCard rK34 ⟨54, by decide⟩ R34 hpxR34 hcardq34
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_34) 54 (by decide)))

theorem fixz2_34 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK34) (retConj 2 (Q2.R34_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_34_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨1, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 1 (by decide)))

theorem fz2_34_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨2, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 2 (by decide)))

theorem fz2_34_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨3, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 3 (by decide)))

theorem fz2_34_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨4, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 4 (by decide)))

theorem fz2_34_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨5, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 5 (by decide)))

theorem fz2_34_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨6, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 6 (by decide)))

theorem fz2_34_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨7, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 7 (by decide)))

theorem fz2_34_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨8, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 8 (by decide)))

theorem fz2_34_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨9, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 9 (by decide)))

theorem fz2_34_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨10, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 10 (by decide)))

theorem fz2_34_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨11, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 11 (by decide)))

theorem fz2_34_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨13, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 13 (by decide)))

theorem fz2_34_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨14, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 14 (by decide)))

theorem fz2_34_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨15, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 15 (by decide)))

theorem fz2_34_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨16, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 16 (by decide)))

theorem fz2_34_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨17, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 17 (by decide)))

theorem fz2_34_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨18, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 18 (by decide)))

theorem fz2_34_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨19, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 19 (by decide)))

theorem fz2_34_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨20, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 20 (by decide)))

theorem fz2_34_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨21, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 21 (by decide)))

theorem fz2_34_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨22, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 22 (by decide)))

theorem fz2_34_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨23, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 23 (by decide)))

theorem fz2_34_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨24, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 24 (by decide)))

theorem fz2_34_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨25, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 25 (by decide)))

theorem fz2_34_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨26, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 26 (by decide)))

theorem fz2_34_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨27, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 27 (by decide)))

theorem fz2_34_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨28, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 28 (by decide)))

theorem fz2_34_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨29, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 29 (by decide)))

theorem fz2_34_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨30, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 30 (by decide)))

theorem fz2_34_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨31, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 31 (by decide)))

theorem fz2_34_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨32, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 32 (by decide)))

theorem fz2_34_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨33, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 33 (by decide)))

theorem fz2_34_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨35, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 35 (by decide)))

theorem fz2_34_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨36, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 36 (by decide)))

theorem fz2_34_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨37, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 37 (by decide)))

theorem fz2_34_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨38, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 38 (by decide)))

theorem fz2_34_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨39, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 39 (by decide)))

theorem fz2_34_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨40, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 40 (by decide)))

theorem fz2_34_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨41, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 41 (by decide)))

theorem fz2_34_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨42, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 42 (by decide)))

theorem fz2_34_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨43, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 43 (by decide)))

theorem fz2_34_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨44, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 44 (by decide)))

theorem fz2_34_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨45, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 45 (by decide)))

theorem fz2_34_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨46, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 46 (by decide)))

theorem fz2_34_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨47, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 47 (by decide)))

theorem fz2_34_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨48, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 48 (by decide)))

theorem fz2_34_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨49, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 49 (by decide)))

theorem fz2_34_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨50, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 50 (by decide)))

theorem fz2_34_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨51, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 51 (by decide)))

theorem fz2_34_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨52, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 52 (by decide)))

theorem fz2_34_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨53, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 53 (by decide)))

theorem fz2_34_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK34)) = 0 :=
  Q2.repsFixedCard2 rK34 ⟨54, by decide⟩ Q2.R34_2 Q2.hpxR34_2 Q2.hcardq34_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_34) 54 (by decide)))

end LeanDring.P5Presentation
