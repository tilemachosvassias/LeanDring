/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryA.C034

/-!
# Species-table cells, off-support emptiness certificates, chunk 45

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

theorem fixz1_46 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK46) (retConj 1 (R46 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_46_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨1, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 1 (by decide)))

theorem fz1_46_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨2, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 2 (by decide)))

theorem fz1_46_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨3, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 3 (by decide)))

theorem fz1_46_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨4, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 4 (by decide)))

theorem fz1_46_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨5, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 5 (by decide)))

theorem fz1_46_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨6, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 6 (by decide)))

theorem fz1_46_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨7, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 7 (by decide)))

theorem fz1_46_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨8, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 8 (by decide)))

theorem fz1_46_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨9, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 9 (by decide)))

theorem fz1_46_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨10, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 10 (by decide)))

theorem fz1_46_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨11, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 11 (by decide)))

theorem fz1_46_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨13, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 13 (by decide)))

theorem fz1_46_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨14, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 14 (by decide)))

theorem fz1_46_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨15, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 15 (by decide)))

theorem fz1_46_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨16, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 16 (by decide)))

theorem fz1_46_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨17, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 17 (by decide)))

theorem fz1_46_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨18, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 18 (by decide)))

theorem fz1_46_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨19, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 19 (by decide)))

theorem fz1_46_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨20, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 20 (by decide)))

theorem fz1_46_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨21, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 21 (by decide)))

theorem fz1_46_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨22, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 22 (by decide)))

theorem fz1_46_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨23, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 23 (by decide)))

theorem fz1_46_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨24, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 24 (by decide)))

theorem fz1_46_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨25, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 25 (by decide)))

theorem fz1_46_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨26, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 26 (by decide)))

theorem fz1_46_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨27, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 27 (by decide)))

theorem fz1_46_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨28, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 28 (by decide)))

theorem fz1_46_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨29, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 29 (by decide)))

theorem fz1_46_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨30, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 30 (by decide)))

theorem fz1_46_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨31, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 31 (by decide)))

theorem fz1_46_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨32, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 32 (by decide)))

theorem fz1_46_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨33, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 33 (by decide)))

theorem fz1_46_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨34, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 34 (by decide)))

theorem fz1_46_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨35, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 35 (by decide)))

theorem fz1_46_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨36, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 36 (by decide)))

theorem fz1_46_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨37, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 37 (by decide)))

theorem fz1_46_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨38, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 38 (by decide)))

theorem fz1_46_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨39, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 39 (by decide)))

theorem fz1_46_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨40, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 40 (by decide)))

theorem fz1_46_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨41, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 41 (by decide)))

theorem fz1_46_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨42, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 42 (by decide)))

theorem fz1_46_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨43, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 43 (by decide)))

theorem fz1_46_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨44, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 44 (by decide)))

theorem fz1_46_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨45, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 45 (by decide)))

theorem fz1_46_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨47, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 47 (by decide)))

theorem fz1_46_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨48, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 48 (by decide)))

theorem fz1_46_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨49, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 49 (by decide)))

theorem fz1_46_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨50, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 50 (by decide)))

theorem fz1_46_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨51, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 51 (by decide)))

theorem fz1_46_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨52, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 52 (by decide)))

theorem fz1_46_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨53, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 53 (by decide)))

theorem fz1_46_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK46)) = 0 :=
  repsFixedCard rK46 ⟨54, by decide⟩ R46 hpxR46 hcardq46
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_46) 54 (by decide)))

theorem fixz2_46 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK46) (retConj 2 (Q2.R46_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_46_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨1, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 1 (by decide)))

theorem fz2_46_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨2, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 2 (by decide)))

theorem fz2_46_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨3, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 3 (by decide)))

theorem fz2_46_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨4, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 4 (by decide)))

theorem fz2_46_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨5, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 5 (by decide)))

theorem fz2_46_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨6, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 6 (by decide)))

theorem fz2_46_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨7, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 7 (by decide)))

theorem fz2_46_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨8, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 8 (by decide)))

theorem fz2_46_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨9, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 9 (by decide)))

theorem fz2_46_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨10, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 10 (by decide)))

theorem fz2_46_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨11, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 11 (by decide)))

theorem fz2_46_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨13, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 13 (by decide)))

theorem fz2_46_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨14, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 14 (by decide)))

theorem fz2_46_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨15, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 15 (by decide)))

theorem fz2_46_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨16, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 16 (by decide)))

theorem fz2_46_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨17, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 17 (by decide)))

theorem fz2_46_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨18, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 18 (by decide)))

theorem fz2_46_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨19, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 19 (by decide)))

theorem fz2_46_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨20, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 20 (by decide)))

theorem fz2_46_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨21, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 21 (by decide)))

theorem fz2_46_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨22, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 22 (by decide)))

theorem fz2_46_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨23, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 23 (by decide)))

theorem fz2_46_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨24, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 24 (by decide)))

theorem fz2_46_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨25, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 25 (by decide)))

theorem fz2_46_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨26, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 26 (by decide)))

theorem fz2_46_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨27, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 27 (by decide)))

theorem fz2_46_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨28, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 28 (by decide)))

theorem fz2_46_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨29, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 29 (by decide)))

theorem fz2_46_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨30, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 30 (by decide)))

theorem fz2_46_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨31, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 31 (by decide)))

theorem fz2_46_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨32, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 32 (by decide)))

theorem fz2_46_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨33, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 33 (by decide)))

theorem fz2_46_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨34, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 34 (by decide)))

theorem fz2_46_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨35, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 35 (by decide)))

theorem fz2_46_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨36, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 36 (by decide)))

theorem fz2_46_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨37, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 37 (by decide)))

theorem fz2_46_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨38, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 38 (by decide)))

theorem fz2_46_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨39, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 39 (by decide)))

theorem fz2_46_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨40, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 40 (by decide)))

theorem fz2_46_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨41, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 41 (by decide)))

theorem fz2_46_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨42, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 42 (by decide)))

theorem fz2_46_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨43, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 43 (by decide)))

theorem fz2_46_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨44, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 44 (by decide)))

theorem fz2_46_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨45, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 45 (by decide)))

theorem fz2_46_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨47, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 47 (by decide)))

theorem fz2_46_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨48, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 48 (by decide)))

theorem fz2_46_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨49, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 49 (by decide)))

theorem fz2_46_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨50, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 50 (by decide)))

theorem fz2_46_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨51, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 51 (by decide)))

theorem fz2_46_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨52, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 52 (by decide)))

theorem fz2_46_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨53, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 53 (by decide)))

theorem fz2_46_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK46)) = 0 :=
  Q2.repsFixedCard2 rK46 ⟨54, by decide⟩ Q2.R46_2 Q2.hpxR46_2 Q2.hcardq46_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_46) 54 (by decide)))

end LeanDring.P5Presentation
