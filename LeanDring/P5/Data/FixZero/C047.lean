/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryA.C035

/-!
# Species-table cells, off-support emptiness certificates, chunk 46

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

theorem fixz1_47 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK47) (retConj 1 (R47 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_47_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨1, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 1 (by decide)))

theorem fz1_47_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨2, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 2 (by decide)))

theorem fz1_47_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨3, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 3 (by decide)))

theorem fz1_47_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨4, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 4 (by decide)))

theorem fz1_47_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨5, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 5 (by decide)))

theorem fz1_47_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨6, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 6 (by decide)))

theorem fz1_47_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨7, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 7 (by decide)))

theorem fz1_47_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨8, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 8 (by decide)))

theorem fz1_47_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨9, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 9 (by decide)))

theorem fz1_47_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨10, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 10 (by decide)))

theorem fz1_47_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨11, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 11 (by decide)))

theorem fz1_47_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨13, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 13 (by decide)))

theorem fz1_47_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨14, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 14 (by decide)))

theorem fz1_47_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨15, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 15 (by decide)))

theorem fz1_47_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨16, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 16 (by decide)))

theorem fz1_47_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨17, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 17 (by decide)))

theorem fz1_47_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨18, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 18 (by decide)))

theorem fz1_47_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨19, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 19 (by decide)))

theorem fz1_47_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨20, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 20 (by decide)))

theorem fz1_47_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨21, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 21 (by decide)))

theorem fz1_47_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨22, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 22 (by decide)))

theorem fz1_47_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨23, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 23 (by decide)))

theorem fz1_47_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨24, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 24 (by decide)))

theorem fz1_47_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨25, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 25 (by decide)))

theorem fz1_47_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨26, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 26 (by decide)))

theorem fz1_47_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨27, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 27 (by decide)))

theorem fz1_47_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨28, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 28 (by decide)))

theorem fz1_47_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨29, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 29 (by decide)))

theorem fz1_47_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨30, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 30 (by decide)))

theorem fz1_47_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨31, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 31 (by decide)))

theorem fz1_47_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨32, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 32 (by decide)))

theorem fz1_47_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨33, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 33 (by decide)))

theorem fz1_47_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨34, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 34 (by decide)))

theorem fz1_47_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨35, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 35 (by decide)))

theorem fz1_47_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨36, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 36 (by decide)))

theorem fz1_47_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨37, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 37 (by decide)))

theorem fz1_47_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨38, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 38 (by decide)))

theorem fz1_47_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨39, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 39 (by decide)))

theorem fz1_47_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨40, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 40 (by decide)))

theorem fz1_47_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨41, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 41 (by decide)))

theorem fz1_47_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨42, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 42 (by decide)))

theorem fz1_47_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨43, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 43 (by decide)))

theorem fz1_47_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨44, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 44 (by decide)))

theorem fz1_47_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨45, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 45 (by decide)))

theorem fz1_47_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨46, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 46 (by decide)))

theorem fz1_47_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨48, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 48 (by decide)))

theorem fz1_47_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨49, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 49 (by decide)))

theorem fz1_47_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨50, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 50 (by decide)))

theorem fz1_47_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨51, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 51 (by decide)))

theorem fz1_47_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨52, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 52 (by decide)))

theorem fz1_47_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨53, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 53 (by decide)))

theorem fz1_47_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK47)) = 0 :=
  repsFixedCard rK47 ⟨54, by decide⟩ R47 hpxR47 hcardq47
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_47) 54 (by decide)))

theorem fixz2_47 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK47) (retConj 2 (Q2.R47_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_47_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨1, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 1 (by decide)))

theorem fz2_47_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨2, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 2 (by decide)))

theorem fz2_47_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨3, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 3 (by decide)))

theorem fz2_47_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨4, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 4 (by decide)))

theorem fz2_47_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨5, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 5 (by decide)))

theorem fz2_47_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨6, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 6 (by decide)))

theorem fz2_47_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨7, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 7 (by decide)))

theorem fz2_47_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨8, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 8 (by decide)))

theorem fz2_47_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨9, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 9 (by decide)))

theorem fz2_47_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨10, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 10 (by decide)))

theorem fz2_47_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨11, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 11 (by decide)))

theorem fz2_47_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨13, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 13 (by decide)))

theorem fz2_47_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨14, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 14 (by decide)))

theorem fz2_47_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨15, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 15 (by decide)))

theorem fz2_47_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨16, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 16 (by decide)))

theorem fz2_47_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨17, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 17 (by decide)))

theorem fz2_47_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨18, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 18 (by decide)))

theorem fz2_47_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨19, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 19 (by decide)))

theorem fz2_47_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨20, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 20 (by decide)))

theorem fz2_47_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨21, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 21 (by decide)))

theorem fz2_47_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨22, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 22 (by decide)))

theorem fz2_47_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨23, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 23 (by decide)))

theorem fz2_47_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨24, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 24 (by decide)))

theorem fz2_47_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨25, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 25 (by decide)))

theorem fz2_47_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨26, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 26 (by decide)))

theorem fz2_47_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨27, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 27 (by decide)))

theorem fz2_47_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨28, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 28 (by decide)))

theorem fz2_47_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨29, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 29 (by decide)))

theorem fz2_47_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨30, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 30 (by decide)))

theorem fz2_47_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨31, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 31 (by decide)))

theorem fz2_47_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨32, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 32 (by decide)))

theorem fz2_47_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨33, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 33 (by decide)))

theorem fz2_47_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨34, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 34 (by decide)))

theorem fz2_47_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨35, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 35 (by decide)))

theorem fz2_47_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨36, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 36 (by decide)))

theorem fz2_47_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨37, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 37 (by decide)))

theorem fz2_47_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨38, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 38 (by decide)))

theorem fz2_47_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨39, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 39 (by decide)))

theorem fz2_47_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨40, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 40 (by decide)))

theorem fz2_47_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨41, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 41 (by decide)))

theorem fz2_47_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨42, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 42 (by decide)))

theorem fz2_47_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨43, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 43 (by decide)))

theorem fz2_47_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨44, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 44 (by decide)))

theorem fz2_47_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨45, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 45 (by decide)))

theorem fz2_47_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨46, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 46 (by decide)))

theorem fz2_47_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨48, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 48 (by decide)))

theorem fz2_47_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨49, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 49 (by decide)))

theorem fz2_47_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨50, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 50 (by decide)))

theorem fz2_47_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨51, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 51 (by decide)))

theorem fz2_47_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨52, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 52 (by decide)))

theorem fz2_47_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨53, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 53 (by decide)))

theorem fz2_47_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK47)) = 0 :=
  Q2.repsFixedCard2 rK47 ⟨54, by decide⟩ Q2.R47_2 Q2.hpxR47_2 Q2.hcardq47_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_47) 54 (by decide)))

end LeanDring.P5Presentation
