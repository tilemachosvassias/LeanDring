/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryA.C032

/-!
# Species-table cells, off-support emptiness certificates, chunk 43

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

theorem fixz1_44 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK44) (retConj 1 (R44 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_44_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨1, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 1 (by decide)))

theorem fz1_44_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨2, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 2 (by decide)))

theorem fz1_44_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨3, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 3 (by decide)))

theorem fz1_44_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨4, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 4 (by decide)))

theorem fz1_44_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨5, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 5 (by decide)))

theorem fz1_44_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨6, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 6 (by decide)))

theorem fz1_44_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨7, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 7 (by decide)))

theorem fz1_44_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨8, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 8 (by decide)))

theorem fz1_44_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨9, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 9 (by decide)))

theorem fz1_44_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨10, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 10 (by decide)))

theorem fz1_44_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨11, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 11 (by decide)))

theorem fz1_44_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨13, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 13 (by decide)))

theorem fz1_44_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨14, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 14 (by decide)))

theorem fz1_44_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨15, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 15 (by decide)))

theorem fz1_44_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨16, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 16 (by decide)))

theorem fz1_44_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨17, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 17 (by decide)))

theorem fz1_44_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨18, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 18 (by decide)))

theorem fz1_44_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨19, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 19 (by decide)))

theorem fz1_44_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨20, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 20 (by decide)))

theorem fz1_44_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨21, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 21 (by decide)))

theorem fz1_44_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨22, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 22 (by decide)))

theorem fz1_44_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨23, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 23 (by decide)))

theorem fz1_44_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨24, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 24 (by decide)))

theorem fz1_44_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨25, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 25 (by decide)))

theorem fz1_44_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨26, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 26 (by decide)))

theorem fz1_44_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨27, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 27 (by decide)))

theorem fz1_44_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨28, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 28 (by decide)))

theorem fz1_44_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨29, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 29 (by decide)))

theorem fz1_44_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨30, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 30 (by decide)))

theorem fz1_44_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨31, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 31 (by decide)))

theorem fz1_44_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨32, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 32 (by decide)))

theorem fz1_44_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨33, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 33 (by decide)))

theorem fz1_44_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨34, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 34 (by decide)))

theorem fz1_44_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨35, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 35 (by decide)))

theorem fz1_44_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨36, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 36 (by decide)))

theorem fz1_44_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨37, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 37 (by decide)))

theorem fz1_44_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨38, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 38 (by decide)))

theorem fz1_44_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨39, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 39 (by decide)))

theorem fz1_44_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨40, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 40 (by decide)))

theorem fz1_44_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨41, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 41 (by decide)))

theorem fz1_44_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨42, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 42 (by decide)))

theorem fz1_44_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨43, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 43 (by decide)))

theorem fz1_44_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨45, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 45 (by decide)))

theorem fz1_44_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨46, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 46 (by decide)))

theorem fz1_44_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨47, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 47 (by decide)))

theorem fz1_44_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨48, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 48 (by decide)))

theorem fz1_44_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨49, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 49 (by decide)))

theorem fz1_44_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨50, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 50 (by decide)))

theorem fz1_44_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨51, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 51 (by decide)))

theorem fz1_44_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨52, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 52 (by decide)))

theorem fz1_44_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨53, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 53 (by decide)))

theorem fz1_44_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK44)) = 0 :=
  repsFixedCard rK44 ⟨54, by decide⟩ R44 hpxR44 hcardq44
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_44) 54 (by decide)))

theorem fixz2_44 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK44) (retConj 2 (Q2.R44_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_44_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨1, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 1 (by decide)))

theorem fz2_44_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨2, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 2 (by decide)))

theorem fz2_44_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨3, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 3 (by decide)))

theorem fz2_44_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨4, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 4 (by decide)))

theorem fz2_44_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨5, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 5 (by decide)))

theorem fz2_44_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨6, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 6 (by decide)))

theorem fz2_44_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨7, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 7 (by decide)))

theorem fz2_44_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨8, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 8 (by decide)))

theorem fz2_44_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨9, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 9 (by decide)))

theorem fz2_44_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨10, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 10 (by decide)))

theorem fz2_44_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨11, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 11 (by decide)))

theorem fz2_44_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨13, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 13 (by decide)))

theorem fz2_44_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨14, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 14 (by decide)))

theorem fz2_44_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨15, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 15 (by decide)))

theorem fz2_44_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨16, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 16 (by decide)))

theorem fz2_44_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨17, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 17 (by decide)))

theorem fz2_44_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨18, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 18 (by decide)))

theorem fz2_44_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨19, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 19 (by decide)))

theorem fz2_44_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨20, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 20 (by decide)))

theorem fz2_44_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨21, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 21 (by decide)))

theorem fz2_44_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨22, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 22 (by decide)))

theorem fz2_44_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨23, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 23 (by decide)))

theorem fz2_44_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨24, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 24 (by decide)))

theorem fz2_44_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨25, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 25 (by decide)))

theorem fz2_44_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨26, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 26 (by decide)))

theorem fz2_44_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨27, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 27 (by decide)))

theorem fz2_44_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨28, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 28 (by decide)))

theorem fz2_44_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨29, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 29 (by decide)))

theorem fz2_44_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨30, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 30 (by decide)))

theorem fz2_44_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨31, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 31 (by decide)))

theorem fz2_44_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨32, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 32 (by decide)))

theorem fz2_44_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨33, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 33 (by decide)))

theorem fz2_44_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨34, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 34 (by decide)))

theorem fz2_44_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨35, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 35 (by decide)))

theorem fz2_44_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨36, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 36 (by decide)))

theorem fz2_44_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨37, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 37 (by decide)))

theorem fz2_44_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨38, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 38 (by decide)))

theorem fz2_44_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨39, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 39 (by decide)))

theorem fz2_44_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨40, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 40 (by decide)))

theorem fz2_44_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨41, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 41 (by decide)))

theorem fz2_44_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨42, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 42 (by decide)))

theorem fz2_44_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨43, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 43 (by decide)))

theorem fz2_44_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨45, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 45 (by decide)))

theorem fz2_44_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨46, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 46 (by decide)))

theorem fz2_44_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨47, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 47 (by decide)))

theorem fz2_44_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨48, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 48 (by decide)))

theorem fz2_44_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨49, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 49 (by decide)))

theorem fz2_44_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨50, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 50 (by decide)))

theorem fz2_44_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨51, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 51 (by decide)))

theorem fz2_44_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨52, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 52 (by decide)))

theorem fz2_44_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨53, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 53 (by decide)))

theorem fz2_44_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK44)) = 0 :=
  Q2.repsFixedCard2 rK44 ⟨54, by decide⟩ Q2.R44_2 Q2.hpxR44_2 Q2.hcardq44_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_44) 54 (by decide)))

end LeanDring.P5Presentation
