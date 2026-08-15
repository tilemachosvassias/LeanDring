/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryA.C025

/-!
# Species-table cells, off-support emptiness certificates, chunk 36

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

theorem fixz1_37 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK37) (retConj 1 (R37 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_37_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨1, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 1 (by decide)))

theorem fz1_37_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨2, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 2 (by decide)))

theorem fz1_37_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨3, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 3 (by decide)))

theorem fz1_37_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨4, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 4 (by decide)))

theorem fz1_37_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨5, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 5 (by decide)))

theorem fz1_37_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨6, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 6 (by decide)))

theorem fz1_37_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨7, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 7 (by decide)))

theorem fz1_37_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨8, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 8 (by decide)))

theorem fz1_37_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨9, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 9 (by decide)))

theorem fz1_37_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨10, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 10 (by decide)))

theorem fz1_37_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨11, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 11 (by decide)))

theorem fz1_37_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨13, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 13 (by decide)))

theorem fz1_37_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨14, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 14 (by decide)))

theorem fz1_37_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨15, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 15 (by decide)))

theorem fz1_37_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨16, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 16 (by decide)))

theorem fz1_37_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨17, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 17 (by decide)))

theorem fz1_37_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨18, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 18 (by decide)))

theorem fz1_37_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨19, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 19 (by decide)))

theorem fz1_37_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨20, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 20 (by decide)))

theorem fz1_37_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨21, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 21 (by decide)))

theorem fz1_37_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨22, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 22 (by decide)))

theorem fz1_37_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨23, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 23 (by decide)))

theorem fz1_37_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨24, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 24 (by decide)))

theorem fz1_37_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨25, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 25 (by decide)))

theorem fz1_37_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨26, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 26 (by decide)))

theorem fz1_37_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨27, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 27 (by decide)))

theorem fz1_37_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨28, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 28 (by decide)))

theorem fz1_37_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨29, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 29 (by decide)))

theorem fz1_37_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨30, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 30 (by decide)))

theorem fz1_37_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨31, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 31 (by decide)))

theorem fz1_37_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨32, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 32 (by decide)))

theorem fz1_37_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨33, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 33 (by decide)))

theorem fz1_37_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨34, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 34 (by decide)))

theorem fz1_37_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨35, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 35 (by decide)))

theorem fz1_37_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨36, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 36 (by decide)))

theorem fz1_37_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨38, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 38 (by decide)))

theorem fz1_37_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨39, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 39 (by decide)))

theorem fz1_37_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨40, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 40 (by decide)))

theorem fz1_37_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨41, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 41 (by decide)))

theorem fz1_37_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨42, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 42 (by decide)))

theorem fz1_37_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨43, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 43 (by decide)))

theorem fz1_37_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨44, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 44 (by decide)))

theorem fz1_37_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨45, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 45 (by decide)))

theorem fz1_37_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨46, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 46 (by decide)))

theorem fz1_37_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨47, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 47 (by decide)))

theorem fz1_37_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨48, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 48 (by decide)))

theorem fz1_37_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨49, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 49 (by decide)))

theorem fz1_37_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨50, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 50 (by decide)))

theorem fz1_37_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨51, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 51 (by decide)))

theorem fz1_37_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨52, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 52 (by decide)))

theorem fz1_37_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨53, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 53 (by decide)))

theorem fz1_37_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK37)) = 0 :=
  repsFixedCard rK37 ⟨54, by decide⟩ R37 hpxR37 hcardq37
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_37) 54 (by decide)))

theorem fixz2_37 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK37) (retConj 2 (Q2.R37_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_37_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨1, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 1 (by decide)))

theorem fz2_37_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨2, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 2 (by decide)))

theorem fz2_37_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨3, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 3 (by decide)))

theorem fz2_37_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨4, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 4 (by decide)))

theorem fz2_37_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨5, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 5 (by decide)))

theorem fz2_37_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨6, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 6 (by decide)))

theorem fz2_37_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨7, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 7 (by decide)))

theorem fz2_37_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨8, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 8 (by decide)))

theorem fz2_37_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨9, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 9 (by decide)))

theorem fz2_37_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨10, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 10 (by decide)))

theorem fz2_37_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨11, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 11 (by decide)))

theorem fz2_37_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨13, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 13 (by decide)))

theorem fz2_37_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨14, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 14 (by decide)))

theorem fz2_37_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨15, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 15 (by decide)))

theorem fz2_37_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨16, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 16 (by decide)))

theorem fz2_37_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨17, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 17 (by decide)))

theorem fz2_37_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨18, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 18 (by decide)))

theorem fz2_37_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨19, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 19 (by decide)))

theorem fz2_37_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨20, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 20 (by decide)))

theorem fz2_37_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨21, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 21 (by decide)))

theorem fz2_37_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨22, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 22 (by decide)))

theorem fz2_37_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨23, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 23 (by decide)))

theorem fz2_37_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨24, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 24 (by decide)))

theorem fz2_37_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨25, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 25 (by decide)))

theorem fz2_37_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨26, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 26 (by decide)))

theorem fz2_37_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨27, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 27 (by decide)))

theorem fz2_37_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨28, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 28 (by decide)))

theorem fz2_37_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨29, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 29 (by decide)))

theorem fz2_37_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨30, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 30 (by decide)))

theorem fz2_37_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨31, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 31 (by decide)))

theorem fz2_37_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨32, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 32 (by decide)))

theorem fz2_37_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨33, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 33 (by decide)))

theorem fz2_37_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨34, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 34 (by decide)))

theorem fz2_37_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨35, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 35 (by decide)))

theorem fz2_37_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨36, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 36 (by decide)))

theorem fz2_37_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨38, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 38 (by decide)))

theorem fz2_37_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨39, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 39 (by decide)))

theorem fz2_37_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨40, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 40 (by decide)))

theorem fz2_37_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨41, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 41 (by decide)))

theorem fz2_37_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨42, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 42 (by decide)))

theorem fz2_37_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨43, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 43 (by decide)))

theorem fz2_37_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨44, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 44 (by decide)))

theorem fz2_37_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨45, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 45 (by decide)))

theorem fz2_37_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨46, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 46 (by decide)))

theorem fz2_37_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨47, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 47 (by decide)))

theorem fz2_37_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨48, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 48 (by decide)))

theorem fz2_37_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨49, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 49 (by decide)))

theorem fz2_37_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨50, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 50 (by decide)))

theorem fz2_37_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨51, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 51 (by decide)))

theorem fz2_37_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨52, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 52 (by decide)))

theorem fz2_37_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨53, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 53 (by decide)))

theorem fz2_37_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK37)) = 0 :=
  Q2.repsFixedCard2 rK37 ⟨54, by decide⟩ Q2.R37_2 Q2.hpxR37_2 Q2.hcardq37_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_37) 54 (by decide)))

end LeanDring.P5Presentation
