/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryA.C028

/-!
# Species-table cells, off-support emptiness certificates, chunk 39

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

theorem fixz1_40 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK40) (retConj 1 (R40 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_40_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨1, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 1 (by decide)))

theorem fz1_40_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨2, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 2 (by decide)))

theorem fz1_40_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨3, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 3 (by decide)))

theorem fz1_40_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨4, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 4 (by decide)))

theorem fz1_40_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨5, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 5 (by decide)))

theorem fz1_40_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨6, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 6 (by decide)))

theorem fz1_40_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨7, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 7 (by decide)))

theorem fz1_40_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨8, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 8 (by decide)))

theorem fz1_40_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨9, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 9 (by decide)))

theorem fz1_40_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨10, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 10 (by decide)))

theorem fz1_40_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨11, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 11 (by decide)))

theorem fz1_40_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨13, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 13 (by decide)))

theorem fz1_40_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨14, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 14 (by decide)))

theorem fz1_40_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨15, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 15 (by decide)))

theorem fz1_40_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨16, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 16 (by decide)))

theorem fz1_40_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨17, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 17 (by decide)))

theorem fz1_40_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨18, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 18 (by decide)))

theorem fz1_40_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨19, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 19 (by decide)))

theorem fz1_40_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨20, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 20 (by decide)))

theorem fz1_40_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨21, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 21 (by decide)))

theorem fz1_40_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨22, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 22 (by decide)))

theorem fz1_40_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨23, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 23 (by decide)))

theorem fz1_40_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨24, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 24 (by decide)))

theorem fz1_40_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨25, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 25 (by decide)))

theorem fz1_40_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨26, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 26 (by decide)))

theorem fz1_40_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨27, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 27 (by decide)))

theorem fz1_40_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨28, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 28 (by decide)))

theorem fz1_40_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨29, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 29 (by decide)))

theorem fz1_40_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨30, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 30 (by decide)))

theorem fz1_40_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨31, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 31 (by decide)))

theorem fz1_40_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨32, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 32 (by decide)))

theorem fz1_40_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨33, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 33 (by decide)))

theorem fz1_40_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨34, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 34 (by decide)))

theorem fz1_40_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨35, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 35 (by decide)))

theorem fz1_40_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨36, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 36 (by decide)))

theorem fz1_40_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨37, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 37 (by decide)))

theorem fz1_40_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨38, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 38 (by decide)))

theorem fz1_40_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨39, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 39 (by decide)))

theorem fz1_40_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨41, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 41 (by decide)))

theorem fz1_40_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨42, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 42 (by decide)))

theorem fz1_40_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨43, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 43 (by decide)))

theorem fz1_40_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨44, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 44 (by decide)))

theorem fz1_40_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨45, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 45 (by decide)))

theorem fz1_40_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨46, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 46 (by decide)))

theorem fz1_40_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨47, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 47 (by decide)))

theorem fz1_40_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨48, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 48 (by decide)))

theorem fz1_40_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨49, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 49 (by decide)))

theorem fz1_40_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨50, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 50 (by decide)))

theorem fz1_40_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨51, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 51 (by decide)))

theorem fz1_40_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨52, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 52 (by decide)))

theorem fz1_40_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨53, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 53 (by decide)))

theorem fz1_40_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK40)) = 0 :=
  repsFixedCard rK40 ⟨54, by decide⟩ R40 hpxR40 hcardq40
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_40) 54 (by decide)))

theorem fixz2_40 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK40) (retConj 2 (Q2.R40_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_40_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨1, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 1 (by decide)))

theorem fz2_40_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨2, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 2 (by decide)))

theorem fz2_40_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨3, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 3 (by decide)))

theorem fz2_40_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨4, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 4 (by decide)))

theorem fz2_40_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨5, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 5 (by decide)))

theorem fz2_40_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨6, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 6 (by decide)))

theorem fz2_40_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨7, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 7 (by decide)))

theorem fz2_40_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨8, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 8 (by decide)))

theorem fz2_40_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨9, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 9 (by decide)))

theorem fz2_40_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨10, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 10 (by decide)))

theorem fz2_40_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨11, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 11 (by decide)))

theorem fz2_40_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨13, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 13 (by decide)))

theorem fz2_40_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨14, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 14 (by decide)))

theorem fz2_40_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨15, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 15 (by decide)))

theorem fz2_40_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨16, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 16 (by decide)))

theorem fz2_40_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨17, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 17 (by decide)))

theorem fz2_40_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨18, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 18 (by decide)))

theorem fz2_40_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨19, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 19 (by decide)))

theorem fz2_40_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨20, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 20 (by decide)))

theorem fz2_40_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨21, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 21 (by decide)))

theorem fz2_40_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨22, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 22 (by decide)))

theorem fz2_40_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨23, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 23 (by decide)))

theorem fz2_40_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨24, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 24 (by decide)))

theorem fz2_40_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨25, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 25 (by decide)))

theorem fz2_40_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨26, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 26 (by decide)))

theorem fz2_40_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨27, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 27 (by decide)))

theorem fz2_40_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨28, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 28 (by decide)))

theorem fz2_40_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨29, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 29 (by decide)))

theorem fz2_40_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨30, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 30 (by decide)))

theorem fz2_40_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨31, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 31 (by decide)))

theorem fz2_40_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨32, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 32 (by decide)))

theorem fz2_40_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨33, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 33 (by decide)))

theorem fz2_40_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨34, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 34 (by decide)))

theorem fz2_40_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨35, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 35 (by decide)))

theorem fz2_40_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨36, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 36 (by decide)))

theorem fz2_40_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨37, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 37 (by decide)))

theorem fz2_40_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨38, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 38 (by decide)))

theorem fz2_40_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨39, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 39 (by decide)))

theorem fz2_40_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨41, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 41 (by decide)))

theorem fz2_40_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨42, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 42 (by decide)))

theorem fz2_40_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨43, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 43 (by decide)))

theorem fz2_40_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨44, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 44 (by decide)))

theorem fz2_40_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨45, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 45 (by decide)))

theorem fz2_40_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨46, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 46 (by decide)))

theorem fz2_40_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨47, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 47 (by decide)))

theorem fz2_40_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨48, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 48 (by decide)))

theorem fz2_40_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨49, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 49 (by decide)))

theorem fz2_40_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨50, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 50 (by decide)))

theorem fz2_40_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨51, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 51 (by decide)))

theorem fz2_40_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨52, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 52 (by decide)))

theorem fz2_40_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨53, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 53 (by decide)))

theorem fz2_40_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK40)) = 0 :=
  Q2.repsFixedCard2 rK40 ⟨54, by decide⟩ Q2.R40_2 Q2.hpxR40_2 Q2.hcardq40_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_40) 54 (by decide)))

end LeanDring.P5Presentation
