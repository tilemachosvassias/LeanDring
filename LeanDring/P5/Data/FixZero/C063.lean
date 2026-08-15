/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryK.C017

/-!
# Species-table cells, off-support emptiness certificates, chunk 62

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

theorem fixz1_71 : ([2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34, 35, 37, 38, 39, 40, 42, 43, 44, 45, 47, 48, 49, 50, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK71) (retConj 1 (R71 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_71_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨2, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 2 (by decide)))

theorem fz1_71_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨3, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 3 (by decide)))

theorem fz1_71_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨4, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 4 (by decide)))

theorem fz1_71_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨5, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 5 (by decide)))

theorem fz1_71_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨6, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 6 (by decide)))

theorem fz1_71_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨7, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 7 (by decide)))

theorem fz1_71_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨8, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 8 (by decide)))

theorem fz1_71_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨9, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 9 (by decide)))

theorem fz1_71_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨10, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 10 (by decide)))

theorem fz1_71_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨11, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 11 (by decide)))

theorem fz1_71_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨13, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 13 (by decide)))

theorem fz1_71_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨14, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 14 (by decide)))

theorem fz1_71_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨15, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 15 (by decide)))

theorem fz1_71_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨16, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 16 (by decide)))

theorem fz1_71_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨17, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 17 (by decide)))

theorem fz1_71_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨18, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 18 (by decide)))

theorem fz1_71_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨20, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 20 (by decide)))

theorem fz1_71_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨21, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 21 (by decide)))

theorem fz1_71_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨22, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 22 (by decide)))

theorem fz1_71_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨23, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 23 (by decide)))

theorem fz1_71_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨24, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 24 (by decide)))

theorem fz1_71_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨25, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 25 (by decide)))

theorem fz1_71_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨26, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 26 (by decide)))

theorem fz1_71_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨27, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 27 (by decide)))

theorem fz1_71_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨28, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 28 (by decide)))

theorem fz1_71_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨29, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 29 (by decide)))

theorem fz1_71_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨30, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 30 (by decide)))

theorem fz1_71_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨32, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 32 (by decide)))

theorem fz1_71_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨33, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 33 (by decide)))

theorem fz1_71_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨34, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 34 (by decide)))

theorem fz1_71_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨35, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 35 (by decide)))

theorem fz1_71_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨37, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 37 (by decide)))

theorem fz1_71_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨38, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 38 (by decide)))

theorem fz1_71_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨39, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 39 (by decide)))

theorem fz1_71_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨40, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 40 (by decide)))

theorem fz1_71_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨42, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 42 (by decide)))

theorem fz1_71_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨43, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 43 (by decide)))

theorem fz1_71_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨44, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 44 (by decide)))

theorem fz1_71_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨45, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 45 (by decide)))

theorem fz1_71_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨47, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 47 (by decide)))

theorem fz1_71_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨48, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 48 (by decide)))

theorem fz1_71_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨49, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 49 (by decide)))

theorem fz1_71_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨50, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 50 (by decide)))

theorem fz1_71_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨52, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 52 (by decide)))

theorem fz1_71_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨53, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 53 (by decide)))

theorem fz1_71_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨54, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 54 (by decide)))

theorem fz1_71_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨55, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 55 (by decide)))

theorem fz1_71_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨56, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 56 (by decide)))

theorem fz1_71_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨57, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 57 (by decide)))

theorem fz1_71_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨58, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 58 (by decide)))

theorem fz1_71_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨59, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 59 (by decide)))

theorem fz1_71_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨60, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 60 (by decide)))

theorem fz1_71_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨61, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 61 (by decide)))

theorem fz1_71_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨62, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 62 (by decide)))

theorem fz1_71_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨63, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 63 (by decide)))

theorem fz1_71_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨64, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 64 (by decide)))

theorem fz1_71_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨65, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 65 (by decide)))

theorem fz1_71_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨66, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 66 (by decide)))

theorem fz1_71_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨67, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 67 (by decide)))

theorem fz1_71_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨68, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 68 (by decide)))

theorem fz1_71_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨69, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 69 (by decide)))

theorem fz1_71_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨70, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 70 (by decide)))

theorem fz1_71_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨72, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 72 (by decide)))

theorem fz1_71_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨73, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 73 (by decide)))

theorem fz1_71_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨74, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 74 (by decide)))

theorem fz1_71_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨75, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 75 (by decide)))

theorem fz1_71_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨76, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 76 (by decide)))

theorem fz1_71_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨77, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 77 (by decide)))

theorem fz1_71_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨78, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 78 (by decide)))

theorem fz1_71_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨79, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 79 (by decide)))

theorem fz1_71_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨80, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 80 (by decide)))

theorem fz1_71_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨81, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 81 (by decide)))

theorem fz1_71_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨82, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 82 (by decide)))

theorem fz1_71_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨83, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 83 (by decide)))

theorem fz1_71_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨84, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 84 (by decide)))

theorem fz1_71_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨85, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 85 (by decide)))

theorem fz1_71_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨86, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 86 (by decide)))

theorem fz1_71_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨87, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 87 (by decide)))

theorem fz1_71_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨88, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 88 (by decide)))

theorem fz1_71_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨89, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 89 (by decide)))

theorem fz1_71_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨90, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 90 (by decide)))

theorem fz1_71_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨91, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 91 (by decide)))

theorem fz1_71_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨92, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 92 (by decide)))

theorem fz1_71_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨93, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 93 (by decide)))

theorem fz1_71_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨94, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 94 (by decide)))

theorem fz1_71_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨95, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 95 (by decide)))

theorem fz1_71_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨96, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 96 (by decide)))

theorem fz1_71_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨97, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 97 (by decide)))

theorem fz1_71_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨98, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 98 (by decide)))

theorem fz1_71_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨99, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 99 (by decide)))

theorem fz1_71_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨100, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 100 (by decide)))

theorem fz1_71_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨101, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 101 (by decide)))

theorem fz1_71_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨102, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 102 (by decide)))

theorem fz1_71_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨103, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 103 (by decide)))

theorem fz1_71_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨104, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 104 (by decide)))

theorem fz1_71_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨105, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 105 (by decide)))

theorem fz1_71_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨106, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 106 (by decide)))

theorem fz1_71_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨107, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 107 (by decide)))

theorem fz1_71_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨108, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 108 (by decide)))

theorem fz1_71_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨109, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 109 (by decide)))

theorem fz1_71_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨110, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 110 (by decide)))

theorem fz1_71_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨111, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 111 (by decide)))

theorem fz1_71_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨112, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 112 (by decide)))

theorem fz1_71_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨113, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 113 (by decide)))

theorem fz1_71_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨114, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 114 (by decide)))

theorem fz1_71_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK71)) = 0 :=
  repsFixedCard rK71 ⟨115, by decide⟩ R71 hpxR71 hcardq71
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_71) 115 (by decide)))

theorem fixz2_71 : ([2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34, 35, 37, 38, 39, 40, 42, 43, 44, 45, 47, 48, 49, 50, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK71) (retConj 2 (Q2.R71_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_71_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨2, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 2 (by decide)))

theorem fz2_71_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨3, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 3 (by decide)))

theorem fz2_71_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨4, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 4 (by decide)))

theorem fz2_71_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨5, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 5 (by decide)))

theorem fz2_71_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨6, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 6 (by decide)))

theorem fz2_71_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨7, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 7 (by decide)))

theorem fz2_71_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨8, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 8 (by decide)))

theorem fz2_71_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨9, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 9 (by decide)))

theorem fz2_71_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨10, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 10 (by decide)))

theorem fz2_71_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨11, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 11 (by decide)))

theorem fz2_71_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨13, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 13 (by decide)))

theorem fz2_71_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨14, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 14 (by decide)))

theorem fz2_71_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨15, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 15 (by decide)))

theorem fz2_71_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨16, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 16 (by decide)))

theorem fz2_71_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨17, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 17 (by decide)))

theorem fz2_71_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨18, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 18 (by decide)))

theorem fz2_71_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨20, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 20 (by decide)))

theorem fz2_71_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨21, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 21 (by decide)))

theorem fz2_71_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨22, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 22 (by decide)))

theorem fz2_71_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨23, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 23 (by decide)))

theorem fz2_71_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨24, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 24 (by decide)))

theorem fz2_71_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨25, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 25 (by decide)))

theorem fz2_71_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨26, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 26 (by decide)))

theorem fz2_71_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨27, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 27 (by decide)))

theorem fz2_71_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨28, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 28 (by decide)))

theorem fz2_71_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨29, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 29 (by decide)))

theorem fz2_71_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨30, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 30 (by decide)))

theorem fz2_71_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨32, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 32 (by decide)))

theorem fz2_71_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨33, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 33 (by decide)))

theorem fz2_71_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨34, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 34 (by decide)))

theorem fz2_71_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨35, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 35 (by decide)))

theorem fz2_71_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨37, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 37 (by decide)))

theorem fz2_71_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨38, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 38 (by decide)))

theorem fz2_71_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨39, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 39 (by decide)))

theorem fz2_71_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨40, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 40 (by decide)))

theorem fz2_71_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨42, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 42 (by decide)))

theorem fz2_71_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨43, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 43 (by decide)))

theorem fz2_71_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨44, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 44 (by decide)))

theorem fz2_71_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨45, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 45 (by decide)))

theorem fz2_71_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨47, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 47 (by decide)))

theorem fz2_71_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨48, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 48 (by decide)))

theorem fz2_71_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨49, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 49 (by decide)))

theorem fz2_71_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨50, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 50 (by decide)))

theorem fz2_71_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨52, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 52 (by decide)))

theorem fz2_71_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨53, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 53 (by decide)))

theorem fz2_71_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨54, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 54 (by decide)))

theorem fz2_71_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨55, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 55 (by decide)))

theorem fz2_71_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨56, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 56 (by decide)))

theorem fz2_71_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨57, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 57 (by decide)))

theorem fz2_71_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨58, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 58 (by decide)))

theorem fz2_71_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨59, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 59 (by decide)))

theorem fz2_71_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨60, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 60 (by decide)))

theorem fz2_71_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨61, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 61 (by decide)))

theorem fz2_71_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨62, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 62 (by decide)))

theorem fz2_71_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨63, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 63 (by decide)))

theorem fz2_71_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨64, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 64 (by decide)))

theorem fz2_71_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨65, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 65 (by decide)))

theorem fz2_71_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨66, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 66 (by decide)))

theorem fz2_71_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨67, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 67 (by decide)))

theorem fz2_71_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨68, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 68 (by decide)))

theorem fz2_71_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨69, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 69 (by decide)))

theorem fz2_71_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨70, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 70 (by decide)))

theorem fz2_71_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨72, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 72 (by decide)))

theorem fz2_71_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨73, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 73 (by decide)))

theorem fz2_71_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨74, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 74 (by decide)))

theorem fz2_71_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨75, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 75 (by decide)))

theorem fz2_71_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨76, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 76 (by decide)))

theorem fz2_71_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨77, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 77 (by decide)))

theorem fz2_71_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨78, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 78 (by decide)))

theorem fz2_71_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨79, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 79 (by decide)))

theorem fz2_71_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨80, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 80 (by decide)))

theorem fz2_71_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨81, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 81 (by decide)))

theorem fz2_71_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨82, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 82 (by decide)))

theorem fz2_71_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨83, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 83 (by decide)))

theorem fz2_71_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨84, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 84 (by decide)))

theorem fz2_71_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨85, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 85 (by decide)))

theorem fz2_71_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨86, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 86 (by decide)))

theorem fz2_71_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨87, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 87 (by decide)))

theorem fz2_71_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨88, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 88 (by decide)))

theorem fz2_71_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨89, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 89 (by decide)))

theorem fz2_71_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨90, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 90 (by decide)))

theorem fz2_71_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨91, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 91 (by decide)))

theorem fz2_71_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨92, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 92 (by decide)))

theorem fz2_71_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨93, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 93 (by decide)))

theorem fz2_71_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨94, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 94 (by decide)))

theorem fz2_71_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨95, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 95 (by decide)))

theorem fz2_71_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨96, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 96 (by decide)))

theorem fz2_71_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨97, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 97 (by decide)))

theorem fz2_71_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨98, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 98 (by decide)))

theorem fz2_71_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨99, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 99 (by decide)))

theorem fz2_71_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨100, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 100 (by decide)))

theorem fz2_71_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨101, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 101 (by decide)))

theorem fz2_71_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨102, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 102 (by decide)))

theorem fz2_71_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨103, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 103 (by decide)))

theorem fz2_71_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨104, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 104 (by decide)))

theorem fz2_71_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨105, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 105 (by decide)))

theorem fz2_71_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨106, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 106 (by decide)))

theorem fz2_71_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨107, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 107 (by decide)))

theorem fz2_71_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨108, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 108 (by decide)))

theorem fz2_71_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨109, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 109 (by decide)))

theorem fz2_71_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨110, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 110 (by decide)))

theorem fz2_71_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨111, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 111 (by decide)))

theorem fz2_71_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨112, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 112 (by decide)))

theorem fz2_71_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨113, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 113 (by decide)))

theorem fz2_71_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨114, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 114 (by decide)))

theorem fz2_71_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK71)) = 0 :=
  Q2.repsFixedCard2 rK71 ⟨115, by decide⟩ Q2.R71_2 Q2.hpxR71_2 Q2.hcardq71_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_71) 115 (by decide)))

theorem fixz1_72 : ([1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28, 29, 30, 32, 33, 34, 35, 37, 38, 39, 40, 42, 43, 44, 45, 47, 48, 49, 50, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK72) (retConj 1 (R72 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_72_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨1, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 1 (by decide)))

theorem fz1_72_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨2, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 2 (by decide)))

theorem fz1_72_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨3, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 3 (by decide)))

theorem fz1_72_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨4, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 4 (by decide)))

theorem fz1_72_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨5, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 5 (by decide)))

theorem fz1_72_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨6, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 6 (by decide)))

theorem fz1_72_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨8, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 8 (by decide)))

theorem fz1_72_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨9, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 9 (by decide)))

theorem fz1_72_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨10, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 10 (by decide)))

theorem fz1_72_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨11, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 11 (by decide)))

theorem fz1_72_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨13, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 13 (by decide)))

theorem fz1_72_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨14, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 14 (by decide)))

theorem fz1_72_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨15, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 15 (by decide)))

theorem fz1_72_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨16, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 16 (by decide)))

theorem fz1_72_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨17, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 17 (by decide)))

theorem fz1_72_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨18, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 18 (by decide)))

theorem fz1_72_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨19, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 19 (by decide)))

theorem fz1_72_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨20, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 20 (by decide)))

theorem fz1_72_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨21, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 21 (by decide)))

theorem fz1_72_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨22, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 22 (by decide)))

theorem fz1_72_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨23, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 23 (by decide)))

theorem fz1_72_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨24, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 24 (by decide)))

theorem fz1_72_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨26, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 26 (by decide)))

theorem fz1_72_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨27, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 27 (by decide)))

theorem fz1_72_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨28, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 28 (by decide)))

theorem fz1_72_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨29, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 29 (by decide)))

theorem fz1_72_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨30, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 30 (by decide)))

theorem fz1_72_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨32, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 32 (by decide)))

theorem fz1_72_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨33, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 33 (by decide)))

theorem fz1_72_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨34, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 34 (by decide)))

theorem fz1_72_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨35, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 35 (by decide)))

theorem fz1_72_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨37, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 37 (by decide)))

theorem fz1_72_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨38, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 38 (by decide)))

theorem fz1_72_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨39, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 39 (by decide)))

theorem fz1_72_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨40, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 40 (by decide)))

theorem fz1_72_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨42, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 42 (by decide)))

theorem fz1_72_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨43, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 43 (by decide)))

theorem fz1_72_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨44, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 44 (by decide)))

theorem fz1_72_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨45, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 45 (by decide)))

theorem fz1_72_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨47, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 47 (by decide)))

theorem fz1_72_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨48, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 48 (by decide)))

theorem fz1_72_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨49, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 49 (by decide)))

theorem fz1_72_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨50, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 50 (by decide)))

theorem fz1_72_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨52, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 52 (by decide)))

theorem fz1_72_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨53, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 53 (by decide)))

theorem fz1_72_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨54, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 54 (by decide)))

theorem fz1_72_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨55, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 55 (by decide)))

theorem fz1_72_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨56, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 56 (by decide)))

theorem fz1_72_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨57, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 57 (by decide)))

theorem fz1_72_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨58, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 58 (by decide)))

theorem fz1_72_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨59, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 59 (by decide)))

theorem fz1_72_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨60, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 60 (by decide)))

theorem fz1_72_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨61, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 61 (by decide)))

theorem fz1_72_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨62, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 62 (by decide)))

theorem fz1_72_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨63, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 63 (by decide)))

theorem fz1_72_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨64, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 64 (by decide)))

theorem fz1_72_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨65, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 65 (by decide)))

theorem fz1_72_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨66, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 66 (by decide)))

theorem fz1_72_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨67, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 67 (by decide)))

theorem fz1_72_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨68, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 68 (by decide)))

theorem fz1_72_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨69, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 69 (by decide)))

theorem fz1_72_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨70, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 70 (by decide)))

theorem fz1_72_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨71, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 71 (by decide)))

theorem fz1_72_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨73, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 73 (by decide)))

theorem fz1_72_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨74, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 74 (by decide)))

theorem fz1_72_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨75, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 75 (by decide)))

theorem fz1_72_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨76, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 76 (by decide)))

theorem fz1_72_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨77, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 77 (by decide)))

theorem fz1_72_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨78, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 78 (by decide)))

theorem fz1_72_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨79, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 79 (by decide)))

theorem fz1_72_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨80, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 80 (by decide)))

theorem fz1_72_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨81, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 81 (by decide)))

theorem fz1_72_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨82, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 82 (by decide)))

theorem fz1_72_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨83, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 83 (by decide)))

theorem fz1_72_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨84, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 84 (by decide)))

theorem fz1_72_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨85, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 85 (by decide)))

theorem fz1_72_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨86, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 86 (by decide)))

theorem fz1_72_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨87, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 87 (by decide)))

theorem fz1_72_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨88, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 88 (by decide)))

theorem fz1_72_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨89, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 89 (by decide)))

theorem fz1_72_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨90, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 90 (by decide)))

theorem fz1_72_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨91, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 91 (by decide)))

theorem fz1_72_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨92, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 92 (by decide)))

theorem fz1_72_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨93, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 93 (by decide)))

theorem fz1_72_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨94, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 94 (by decide)))

theorem fz1_72_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨95, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 95 (by decide)))

theorem fz1_72_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨96, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 96 (by decide)))

theorem fz1_72_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨97, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 97 (by decide)))

theorem fz1_72_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨98, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 98 (by decide)))

theorem fz1_72_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨99, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 99 (by decide)))

theorem fz1_72_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨100, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 100 (by decide)))

theorem fz1_72_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨101, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 101 (by decide)))

theorem fz1_72_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨102, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 102 (by decide)))

theorem fz1_72_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨103, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 103 (by decide)))

theorem fz1_72_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨104, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 104 (by decide)))

theorem fz1_72_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨105, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 105 (by decide)))

theorem fz1_72_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨106, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 106 (by decide)))

theorem fz1_72_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨107, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 107 (by decide)))

theorem fz1_72_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨108, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 108 (by decide)))

theorem fz1_72_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨109, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 109 (by decide)))

theorem fz1_72_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨110, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 110 (by decide)))

theorem fz1_72_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨111, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 111 (by decide)))

theorem fz1_72_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨112, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 112 (by decide)))

theorem fz1_72_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨113, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 113 (by decide)))

theorem fz1_72_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨114, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 114 (by decide)))

theorem fz1_72_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK72)) = 0 :=
  repsFixedCard rK72 ⟨115, by decide⟩ R72 hpxR72 hcardq72
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_72) 115 (by decide)))

theorem fixz2_72 : ([1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28, 29, 30, 32, 33, 34, 35, 37, 38, 39, 40, 42, 43, 44, 45, 47, 48, 49, 50, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK72) (retConj 2 (Q2.R72_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_72_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨1, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 1 (by decide)))

theorem fz2_72_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨2, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 2 (by decide)))

theorem fz2_72_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨3, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 3 (by decide)))

theorem fz2_72_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨4, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 4 (by decide)))

theorem fz2_72_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨5, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 5 (by decide)))

theorem fz2_72_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨6, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 6 (by decide)))

theorem fz2_72_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨8, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 8 (by decide)))

theorem fz2_72_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨9, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 9 (by decide)))

theorem fz2_72_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨10, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 10 (by decide)))

theorem fz2_72_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨11, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 11 (by decide)))

theorem fz2_72_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨13, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 13 (by decide)))

theorem fz2_72_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨14, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 14 (by decide)))

theorem fz2_72_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨15, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 15 (by decide)))

theorem fz2_72_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨16, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 16 (by decide)))

theorem fz2_72_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨17, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 17 (by decide)))

theorem fz2_72_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨18, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 18 (by decide)))

theorem fz2_72_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨19, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 19 (by decide)))

theorem fz2_72_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨20, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 20 (by decide)))

theorem fz2_72_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨21, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 21 (by decide)))

theorem fz2_72_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨22, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 22 (by decide)))

theorem fz2_72_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨23, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 23 (by decide)))

theorem fz2_72_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨24, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 24 (by decide)))

theorem fz2_72_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨26, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 26 (by decide)))

theorem fz2_72_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨27, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 27 (by decide)))

theorem fz2_72_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨28, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 28 (by decide)))

theorem fz2_72_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨29, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 29 (by decide)))

theorem fz2_72_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨30, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 30 (by decide)))

theorem fz2_72_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨32, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 32 (by decide)))

theorem fz2_72_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨33, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 33 (by decide)))

theorem fz2_72_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨34, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 34 (by decide)))

theorem fz2_72_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨35, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 35 (by decide)))

theorem fz2_72_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨37, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 37 (by decide)))

theorem fz2_72_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨38, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 38 (by decide)))

theorem fz2_72_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨39, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 39 (by decide)))

theorem fz2_72_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨40, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 40 (by decide)))

theorem fz2_72_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨42, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 42 (by decide)))

theorem fz2_72_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨43, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 43 (by decide)))

theorem fz2_72_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨44, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 44 (by decide)))

theorem fz2_72_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨45, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 45 (by decide)))

theorem fz2_72_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨47, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 47 (by decide)))

theorem fz2_72_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨48, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 48 (by decide)))

theorem fz2_72_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨49, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 49 (by decide)))

theorem fz2_72_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨50, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 50 (by decide)))

theorem fz2_72_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨52, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 52 (by decide)))

theorem fz2_72_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨53, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 53 (by decide)))

theorem fz2_72_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨54, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 54 (by decide)))

theorem fz2_72_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨55, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 55 (by decide)))

theorem fz2_72_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨56, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 56 (by decide)))

theorem fz2_72_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨57, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 57 (by decide)))

theorem fz2_72_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨58, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 58 (by decide)))

theorem fz2_72_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨59, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 59 (by decide)))

theorem fz2_72_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨60, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 60 (by decide)))

theorem fz2_72_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨61, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 61 (by decide)))

theorem fz2_72_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨62, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 62 (by decide)))

theorem fz2_72_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨63, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 63 (by decide)))

theorem fz2_72_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨64, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 64 (by decide)))

theorem fz2_72_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨65, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 65 (by decide)))

theorem fz2_72_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨66, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 66 (by decide)))

theorem fz2_72_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨67, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 67 (by decide)))

theorem fz2_72_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨68, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 68 (by decide)))

theorem fz2_72_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨69, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 69 (by decide)))

theorem fz2_72_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨70, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 70 (by decide)))

theorem fz2_72_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨71, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 71 (by decide)))

theorem fz2_72_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨73, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 73 (by decide)))

theorem fz2_72_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨74, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 74 (by decide)))

theorem fz2_72_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨75, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 75 (by decide)))

theorem fz2_72_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨76, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 76 (by decide)))

theorem fz2_72_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨77, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 77 (by decide)))

theorem fz2_72_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨78, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 78 (by decide)))

theorem fz2_72_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨79, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 79 (by decide)))

theorem fz2_72_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨80, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 80 (by decide)))

theorem fz2_72_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨81, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 81 (by decide)))

theorem fz2_72_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨82, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 82 (by decide)))

theorem fz2_72_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨83, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 83 (by decide)))

theorem fz2_72_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨84, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 84 (by decide)))

theorem fz2_72_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨85, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 85 (by decide)))

theorem fz2_72_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨86, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 86 (by decide)))

theorem fz2_72_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨87, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 87 (by decide)))

theorem fz2_72_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨88, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 88 (by decide)))

theorem fz2_72_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨89, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 89 (by decide)))

theorem fz2_72_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨90, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 90 (by decide)))

theorem fz2_72_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨91, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 91 (by decide)))

theorem fz2_72_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨92, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 92 (by decide)))

theorem fz2_72_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨93, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 93 (by decide)))

theorem fz2_72_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨94, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 94 (by decide)))

theorem fz2_72_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨95, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 95 (by decide)))

theorem fz2_72_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨96, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 96 (by decide)))

theorem fz2_72_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨97, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 97 (by decide)))

theorem fz2_72_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨98, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 98 (by decide)))

theorem fz2_72_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨99, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 99 (by decide)))

theorem fz2_72_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨100, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 100 (by decide)))

theorem fz2_72_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨101, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 101 (by decide)))

theorem fz2_72_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨102, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 102 (by decide)))

theorem fz2_72_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨103, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 103 (by decide)))

theorem fz2_72_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨104, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 104 (by decide)))

theorem fz2_72_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨105, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 105 (by decide)))

theorem fz2_72_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨106, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 106 (by decide)))

theorem fz2_72_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨107, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 107 (by decide)))

theorem fz2_72_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨108, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 108 (by decide)))

theorem fz2_72_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨109, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 109 (by decide)))

theorem fz2_72_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨110, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 110 (by decide)))

theorem fz2_72_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨111, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 111 (by decide)))

theorem fz2_72_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨112, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 112 (by decide)))

theorem fz2_72_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨113, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 113 (by decide)))

theorem fz2_72_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨114, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 114 (by decide)))

theorem fz2_72_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK72)) = 0 :=
  Q2.repsFixedCard2 rK72 ⟨115, by decide⟩ Q2.R72_2 Q2.hpxR72_2 Q2.hcardq72_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_72) 115 (by decide)))

end LeanDring.P5Presentation
