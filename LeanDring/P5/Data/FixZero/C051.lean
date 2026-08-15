/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryA.C039

/-!
# Species-table cells, off-support emptiness certificates, chunk 50

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

theorem fixz1_51 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK51) (retConj 1 (R51 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_51_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨1, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 1 (by decide)))

theorem fz1_51_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨2, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 2 (by decide)))

theorem fz1_51_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨3, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 3 (by decide)))

theorem fz1_51_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨4, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 4 (by decide)))

theorem fz1_51_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨5, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 5 (by decide)))

theorem fz1_51_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨6, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 6 (by decide)))

theorem fz1_51_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨7, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 7 (by decide)))

theorem fz1_51_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨8, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 8 (by decide)))

theorem fz1_51_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨9, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 9 (by decide)))

theorem fz1_51_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨10, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 10 (by decide)))

theorem fz1_51_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨11, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 11 (by decide)))

theorem fz1_51_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨13, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 13 (by decide)))

theorem fz1_51_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨14, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 14 (by decide)))

theorem fz1_51_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨15, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 15 (by decide)))

theorem fz1_51_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨16, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 16 (by decide)))

theorem fz1_51_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨17, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 17 (by decide)))

theorem fz1_51_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨18, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 18 (by decide)))

theorem fz1_51_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨19, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 19 (by decide)))

theorem fz1_51_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨20, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 20 (by decide)))

theorem fz1_51_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨21, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 21 (by decide)))

theorem fz1_51_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨22, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 22 (by decide)))

theorem fz1_51_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨23, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 23 (by decide)))

theorem fz1_51_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨24, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 24 (by decide)))

theorem fz1_51_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨25, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 25 (by decide)))

theorem fz1_51_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨26, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 26 (by decide)))

theorem fz1_51_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨27, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 27 (by decide)))

theorem fz1_51_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨28, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 28 (by decide)))

theorem fz1_51_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨29, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 29 (by decide)))

theorem fz1_51_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨30, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 30 (by decide)))

theorem fz1_51_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨31, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 31 (by decide)))

theorem fz1_51_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨32, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 32 (by decide)))

theorem fz1_51_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨33, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 33 (by decide)))

theorem fz1_51_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨34, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 34 (by decide)))

theorem fz1_51_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨35, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 35 (by decide)))

theorem fz1_51_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨36, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 36 (by decide)))

theorem fz1_51_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨37, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 37 (by decide)))

theorem fz1_51_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨38, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 38 (by decide)))

theorem fz1_51_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨39, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 39 (by decide)))

theorem fz1_51_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨40, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 40 (by decide)))

theorem fz1_51_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨41, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 41 (by decide)))

theorem fz1_51_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨42, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 42 (by decide)))

theorem fz1_51_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨43, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 43 (by decide)))

theorem fz1_51_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨44, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 44 (by decide)))

theorem fz1_51_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨45, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 45 (by decide)))

theorem fz1_51_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨46, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 46 (by decide)))

theorem fz1_51_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨47, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 47 (by decide)))

theorem fz1_51_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨48, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 48 (by decide)))

theorem fz1_51_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨49, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 49 (by decide)))

theorem fz1_51_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨50, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 50 (by decide)))

theorem fz1_51_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨52, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 52 (by decide)))

theorem fz1_51_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨53, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 53 (by decide)))

theorem fz1_51_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK51)) = 0 :=
  repsFixedCard rK51 ⟨54, by decide⟩ R51 hpxR51 hcardq51
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_51) 54 (by decide)))

theorem fixz2_51 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK51) (retConj 2 (Q2.R51_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_51_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨1, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 1 (by decide)))

theorem fz2_51_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨2, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 2 (by decide)))

theorem fz2_51_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨3, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 3 (by decide)))

theorem fz2_51_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨4, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 4 (by decide)))

theorem fz2_51_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨5, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 5 (by decide)))

theorem fz2_51_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨6, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 6 (by decide)))

theorem fz2_51_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨7, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 7 (by decide)))

theorem fz2_51_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨8, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 8 (by decide)))

theorem fz2_51_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨9, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 9 (by decide)))

theorem fz2_51_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨10, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 10 (by decide)))

theorem fz2_51_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨11, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 11 (by decide)))

theorem fz2_51_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨13, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 13 (by decide)))

theorem fz2_51_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨14, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 14 (by decide)))

theorem fz2_51_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨15, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 15 (by decide)))

theorem fz2_51_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨16, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 16 (by decide)))

theorem fz2_51_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨17, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 17 (by decide)))

theorem fz2_51_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨18, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 18 (by decide)))

theorem fz2_51_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨19, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 19 (by decide)))

theorem fz2_51_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨20, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 20 (by decide)))

theorem fz2_51_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨21, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 21 (by decide)))

theorem fz2_51_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨22, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 22 (by decide)))

theorem fz2_51_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨23, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 23 (by decide)))

theorem fz2_51_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨24, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 24 (by decide)))

theorem fz2_51_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨25, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 25 (by decide)))

theorem fz2_51_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨26, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 26 (by decide)))

theorem fz2_51_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨27, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 27 (by decide)))

theorem fz2_51_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨28, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 28 (by decide)))

theorem fz2_51_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨29, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 29 (by decide)))

theorem fz2_51_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨30, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 30 (by decide)))

theorem fz2_51_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨31, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 31 (by decide)))

theorem fz2_51_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨32, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 32 (by decide)))

theorem fz2_51_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨33, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 33 (by decide)))

theorem fz2_51_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨34, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 34 (by decide)))

theorem fz2_51_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨35, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 35 (by decide)))

theorem fz2_51_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨36, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 36 (by decide)))

theorem fz2_51_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨37, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 37 (by decide)))

theorem fz2_51_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨38, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 38 (by decide)))

theorem fz2_51_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨39, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 39 (by decide)))

theorem fz2_51_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨40, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 40 (by decide)))

theorem fz2_51_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨41, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 41 (by decide)))

theorem fz2_51_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨42, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 42 (by decide)))

theorem fz2_51_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨43, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 43 (by decide)))

theorem fz2_51_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨44, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 44 (by decide)))

theorem fz2_51_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨45, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 45 (by decide)))

theorem fz2_51_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨46, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 46 (by decide)))

theorem fz2_51_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨47, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 47 (by decide)))

theorem fz2_51_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨48, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 48 (by decide)))

theorem fz2_51_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨49, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 49 (by decide)))

theorem fz2_51_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨50, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 50 (by decide)))

theorem fz2_51_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨52, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 52 (by decide)))

theorem fz2_51_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨53, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 53 (by decide)))

theorem fz2_51_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK51)) = 0 :=
  Q2.repsFixedCard2 rK51 ⟨54, by decide⟩ Q2.R51_2 Q2.hpxR51_2 Q2.hcardq51_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_51) 54 (by decide)))

end LeanDring.P5Presentation
