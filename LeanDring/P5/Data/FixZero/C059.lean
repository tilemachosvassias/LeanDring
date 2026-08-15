/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryK.C015

/-!
# Species-table cells, off-support emptiness certificates, chunk 58

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

theorem fixz1_63 : ([1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 28, 30, 31, 32, 33, 35, 36, 37, 38, 40, 41, 42, 43, 45, 46, 47, 48, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK63) (retConj 1 (R63 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_63_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨1, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 1 (by decide)))

theorem fz1_63_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨2, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 2 (by decide)))

theorem fz1_63_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨3, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 3 (by decide)))

theorem fz1_63_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨4, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 4 (by decide)))

theorem fz1_63_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨5, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 5 (by decide)))

theorem fz1_63_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨7, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 7 (by decide)))

theorem fz1_63_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨8, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 8 (by decide)))

theorem fz1_63_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨9, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 9 (by decide)))

theorem fz1_63_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨10, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 10 (by decide)))

theorem fz1_63_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨11, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 11 (by decide)))

theorem fz1_63_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨13, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 13 (by decide)))

theorem fz1_63_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨14, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 14 (by decide)))

theorem fz1_63_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨15, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 15 (by decide)))

theorem fz1_63_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨16, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 16 (by decide)))

theorem fz1_63_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨17, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 17 (by decide)))

theorem fz1_63_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨18, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 18 (by decide)))

theorem fz1_63_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨19, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 19 (by decide)))

theorem fz1_63_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨20, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 20 (by decide)))

theorem fz1_63_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨21, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 21 (by decide)))

theorem fz1_63_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨22, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 22 (by decide)))

theorem fz1_63_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨23, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 23 (by decide)))

theorem fz1_63_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨25, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 25 (by decide)))

theorem fz1_63_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨26, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 26 (by decide)))

theorem fz1_63_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨27, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 27 (by decide)))

theorem fz1_63_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨28, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 28 (by decide)))

theorem fz1_63_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨30, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 30 (by decide)))

theorem fz1_63_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨31, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 31 (by decide)))

theorem fz1_63_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨32, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 32 (by decide)))

theorem fz1_63_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨33, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 33 (by decide)))

theorem fz1_63_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨35, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 35 (by decide)))

theorem fz1_63_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨36, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 36 (by decide)))

theorem fz1_63_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨37, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 37 (by decide)))

theorem fz1_63_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨38, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 38 (by decide)))

theorem fz1_63_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨40, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 40 (by decide)))

theorem fz1_63_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨41, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 41 (by decide)))

theorem fz1_63_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨42, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 42 (by decide)))

theorem fz1_63_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨43, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 43 (by decide)))

theorem fz1_63_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨45, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 45 (by decide)))

theorem fz1_63_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨46, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 46 (by decide)))

theorem fz1_63_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨47, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 47 (by decide)))

theorem fz1_63_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨48, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 48 (by decide)))

theorem fz1_63_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨50, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 50 (by decide)))

theorem fz1_63_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨51, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 51 (by decide)))

theorem fz1_63_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨52, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 52 (by decide)))

theorem fz1_63_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨53, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 53 (by decide)))

theorem fz1_63_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨54, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 54 (by decide)))

theorem fz1_63_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨55, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 55 (by decide)))

theorem fz1_63_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨56, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 56 (by decide)))

theorem fz1_63_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨57, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 57 (by decide)))

theorem fz1_63_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨58, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 58 (by decide)))

theorem fz1_63_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨59, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 59 (by decide)))

theorem fz1_63_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨60, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 60 (by decide)))

theorem fz1_63_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨61, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 61 (by decide)))

theorem fz1_63_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨62, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 62 (by decide)))

theorem fz1_63_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨64, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 64 (by decide)))

theorem fz1_63_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨65, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 65 (by decide)))

theorem fz1_63_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨66, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 66 (by decide)))

theorem fz1_63_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨67, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 67 (by decide)))

theorem fz1_63_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨68, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 68 (by decide)))

theorem fz1_63_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨69, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 69 (by decide)))

theorem fz1_63_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨70, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 70 (by decide)))

theorem fz1_63_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨71, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 71 (by decide)))

theorem fz1_63_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨72, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 72 (by decide)))

theorem fz1_63_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨73, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 73 (by decide)))

theorem fz1_63_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨74, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 74 (by decide)))

theorem fz1_63_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨75, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 75 (by decide)))

theorem fz1_63_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨76, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 76 (by decide)))

theorem fz1_63_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨77, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 77 (by decide)))

theorem fz1_63_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨78, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 78 (by decide)))

theorem fz1_63_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨79, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 79 (by decide)))

theorem fz1_63_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨80, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 80 (by decide)))

theorem fz1_63_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨81, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 81 (by decide)))

theorem fz1_63_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨82, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 82 (by decide)))

theorem fz1_63_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨83, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 83 (by decide)))

theorem fz1_63_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨84, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 84 (by decide)))

theorem fz1_63_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨85, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 85 (by decide)))

theorem fz1_63_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨86, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 86 (by decide)))

theorem fz1_63_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨87, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 87 (by decide)))

theorem fz1_63_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨88, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 88 (by decide)))

theorem fz1_63_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨89, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 89 (by decide)))

theorem fz1_63_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨90, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 90 (by decide)))

theorem fz1_63_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨91, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 91 (by decide)))

theorem fz1_63_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨92, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 92 (by decide)))

theorem fz1_63_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨93, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 93 (by decide)))

theorem fz1_63_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨94, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 94 (by decide)))

theorem fz1_63_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨95, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 95 (by decide)))

theorem fz1_63_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨96, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 96 (by decide)))

theorem fz1_63_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨97, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 97 (by decide)))

theorem fz1_63_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨98, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 98 (by decide)))

theorem fz1_63_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨99, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 99 (by decide)))

theorem fz1_63_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨100, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 100 (by decide)))

theorem fz1_63_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨101, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 101 (by decide)))

theorem fz1_63_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨102, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 102 (by decide)))

theorem fz1_63_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨103, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 103 (by decide)))

theorem fz1_63_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨104, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 104 (by decide)))

theorem fz1_63_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨105, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 105 (by decide)))

theorem fz1_63_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨106, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 106 (by decide)))

theorem fz1_63_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨107, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 107 (by decide)))

theorem fz1_63_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨108, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 108 (by decide)))

theorem fz1_63_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨109, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 109 (by decide)))

theorem fz1_63_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨110, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 110 (by decide)))

theorem fz1_63_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨111, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 111 (by decide)))

theorem fz1_63_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨112, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 112 (by decide)))

theorem fz1_63_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨113, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 113 (by decide)))

theorem fz1_63_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨114, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 114 (by decide)))

theorem fz1_63_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK63)) = 0 :=
  repsFixedCard rK63 ⟨115, by decide⟩ R63 hpxR63 hcardq63
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_63) 115 (by decide)))

theorem fixz2_63 : ([1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 28, 30, 31, 32, 33, 35, 36, 37, 38, 40, 41, 42, 43, 45, 46, 47, 48, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK63) (retConj 2 (Q2.R63_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_63_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨1, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 1 (by decide)))

theorem fz2_63_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨2, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 2 (by decide)))

theorem fz2_63_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨3, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 3 (by decide)))

theorem fz2_63_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨4, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 4 (by decide)))

theorem fz2_63_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨5, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 5 (by decide)))

theorem fz2_63_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨7, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 7 (by decide)))

theorem fz2_63_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨8, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 8 (by decide)))

theorem fz2_63_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨9, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 9 (by decide)))

theorem fz2_63_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨10, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 10 (by decide)))

theorem fz2_63_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨11, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 11 (by decide)))

theorem fz2_63_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨13, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 13 (by decide)))

theorem fz2_63_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨14, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 14 (by decide)))

theorem fz2_63_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨15, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 15 (by decide)))

theorem fz2_63_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨16, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 16 (by decide)))

theorem fz2_63_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨17, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 17 (by decide)))

theorem fz2_63_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨18, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 18 (by decide)))

theorem fz2_63_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨19, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 19 (by decide)))

theorem fz2_63_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨20, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 20 (by decide)))

theorem fz2_63_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨21, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 21 (by decide)))

theorem fz2_63_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨22, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 22 (by decide)))

theorem fz2_63_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨23, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 23 (by decide)))

theorem fz2_63_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨25, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 25 (by decide)))

theorem fz2_63_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨26, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 26 (by decide)))

theorem fz2_63_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨27, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 27 (by decide)))

theorem fz2_63_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨28, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 28 (by decide)))

theorem fz2_63_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨30, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 30 (by decide)))

theorem fz2_63_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨31, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 31 (by decide)))

theorem fz2_63_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨32, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 32 (by decide)))

theorem fz2_63_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨33, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 33 (by decide)))

theorem fz2_63_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨35, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 35 (by decide)))

theorem fz2_63_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨36, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 36 (by decide)))

theorem fz2_63_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨37, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 37 (by decide)))

theorem fz2_63_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨38, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 38 (by decide)))

theorem fz2_63_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨40, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 40 (by decide)))

theorem fz2_63_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨41, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 41 (by decide)))

theorem fz2_63_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨42, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 42 (by decide)))

theorem fz2_63_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨43, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 43 (by decide)))

theorem fz2_63_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨45, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 45 (by decide)))

theorem fz2_63_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨46, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 46 (by decide)))

theorem fz2_63_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨47, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 47 (by decide)))

theorem fz2_63_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨48, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 48 (by decide)))

theorem fz2_63_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨50, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 50 (by decide)))

theorem fz2_63_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨51, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 51 (by decide)))

theorem fz2_63_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨52, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 52 (by decide)))

theorem fz2_63_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨53, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 53 (by decide)))

theorem fz2_63_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨54, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 54 (by decide)))

theorem fz2_63_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨55, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 55 (by decide)))

theorem fz2_63_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨56, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 56 (by decide)))

theorem fz2_63_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨57, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 57 (by decide)))

theorem fz2_63_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨58, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 58 (by decide)))

theorem fz2_63_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨59, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 59 (by decide)))

theorem fz2_63_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨60, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 60 (by decide)))

theorem fz2_63_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨61, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 61 (by decide)))

theorem fz2_63_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨62, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 62 (by decide)))

theorem fz2_63_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨64, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 64 (by decide)))

theorem fz2_63_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨65, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 65 (by decide)))

theorem fz2_63_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨66, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 66 (by decide)))

theorem fz2_63_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨67, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 67 (by decide)))

theorem fz2_63_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨68, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 68 (by decide)))

theorem fz2_63_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨69, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 69 (by decide)))

theorem fz2_63_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨70, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 70 (by decide)))

theorem fz2_63_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨71, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 71 (by decide)))

theorem fz2_63_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨72, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 72 (by decide)))

theorem fz2_63_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨73, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 73 (by decide)))

theorem fz2_63_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨74, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 74 (by decide)))

theorem fz2_63_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨75, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 75 (by decide)))

theorem fz2_63_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨76, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 76 (by decide)))

theorem fz2_63_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨77, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 77 (by decide)))

theorem fz2_63_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨78, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 78 (by decide)))

theorem fz2_63_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨79, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 79 (by decide)))

theorem fz2_63_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨80, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 80 (by decide)))

theorem fz2_63_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨81, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 81 (by decide)))

theorem fz2_63_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨82, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 82 (by decide)))

theorem fz2_63_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨83, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 83 (by decide)))

theorem fz2_63_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨84, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 84 (by decide)))

theorem fz2_63_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨85, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 85 (by decide)))

theorem fz2_63_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨86, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 86 (by decide)))

theorem fz2_63_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨87, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 87 (by decide)))

theorem fz2_63_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨88, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 88 (by decide)))

theorem fz2_63_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨89, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 89 (by decide)))

theorem fz2_63_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨90, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 90 (by decide)))

theorem fz2_63_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨91, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 91 (by decide)))

theorem fz2_63_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨92, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 92 (by decide)))

theorem fz2_63_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨93, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 93 (by decide)))

theorem fz2_63_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨94, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 94 (by decide)))

theorem fz2_63_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨95, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 95 (by decide)))

theorem fz2_63_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨96, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 96 (by decide)))

theorem fz2_63_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨97, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 97 (by decide)))

theorem fz2_63_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨98, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 98 (by decide)))

theorem fz2_63_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨99, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 99 (by decide)))

theorem fz2_63_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨100, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 100 (by decide)))

theorem fz2_63_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨101, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 101 (by decide)))

theorem fz2_63_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨102, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 102 (by decide)))

theorem fz2_63_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨103, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 103 (by decide)))

theorem fz2_63_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨104, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 104 (by decide)))

theorem fz2_63_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨105, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 105 (by decide)))

theorem fz2_63_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨106, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 106 (by decide)))

theorem fz2_63_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨107, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 107 (by decide)))

theorem fz2_63_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨108, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 108 (by decide)))

theorem fz2_63_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨109, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 109 (by decide)))

theorem fz2_63_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨110, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 110 (by decide)))

theorem fz2_63_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨111, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 111 (by decide)))

theorem fz2_63_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨112, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 112 (by decide)))

theorem fz2_63_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨113, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 113 (by decide)))

theorem fz2_63_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨114, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 114 (by decide)))

theorem fz2_63_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK63)) = 0 :=
  Q2.repsFixedCard2 rK63 ⟨115, by decide⟩ Q2.R63_2 Q2.hpxR63_2 Q2.hcardq63_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_63) 115 (by decide)))

theorem fixz1_64 : ([1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 27, 28, 30, 31, 32, 33, 35, 36, 37, 38, 40, 41, 42, 43, 45, 46, 47, 48, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK64) (retConj 1 (R64 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_64_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨1, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 1 (by decide)))

theorem fz1_64_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨2, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 2 (by decide)))

theorem fz1_64_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨3, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 3 (by decide)))

theorem fz1_64_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨4, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 4 (by decide)))

theorem fz1_64_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨5, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 5 (by decide)))

theorem fz1_64_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨6, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 6 (by decide)))

theorem fz1_64_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨7, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 7 (by decide)))

theorem fz1_64_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨9, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 9 (by decide)))

theorem fz1_64_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨10, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 10 (by decide)))

theorem fz1_64_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨11, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 11 (by decide)))

theorem fz1_64_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨13, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 13 (by decide)))

theorem fz1_64_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨14, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 14 (by decide)))

theorem fz1_64_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨15, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 15 (by decide)))

theorem fz1_64_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨16, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 16 (by decide)))

theorem fz1_64_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨17, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 17 (by decide)))

theorem fz1_64_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨18, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 18 (by decide)))

theorem fz1_64_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨19, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 19 (by decide)))

theorem fz1_64_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨20, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 20 (by decide)))

theorem fz1_64_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨21, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 21 (by decide)))

theorem fz1_64_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨22, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 22 (by decide)))

theorem fz1_64_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨23, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 23 (by decide)))

theorem fz1_64_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨24, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 24 (by decide)))

theorem fz1_64_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨25, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 25 (by decide)))

theorem fz1_64_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨27, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 27 (by decide)))

theorem fz1_64_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨28, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 28 (by decide)))

theorem fz1_64_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨30, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 30 (by decide)))

theorem fz1_64_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨31, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 31 (by decide)))

theorem fz1_64_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨32, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 32 (by decide)))

theorem fz1_64_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨33, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 33 (by decide)))

theorem fz1_64_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨35, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 35 (by decide)))

theorem fz1_64_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨36, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 36 (by decide)))

theorem fz1_64_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨37, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 37 (by decide)))

theorem fz1_64_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨38, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 38 (by decide)))

theorem fz1_64_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨40, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 40 (by decide)))

theorem fz1_64_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨41, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 41 (by decide)))

theorem fz1_64_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨42, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 42 (by decide)))

theorem fz1_64_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨43, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 43 (by decide)))

theorem fz1_64_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨45, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 45 (by decide)))

theorem fz1_64_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨46, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 46 (by decide)))

theorem fz1_64_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨47, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 47 (by decide)))

theorem fz1_64_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨48, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 48 (by decide)))

theorem fz1_64_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨50, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 50 (by decide)))

theorem fz1_64_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨51, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 51 (by decide)))

theorem fz1_64_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨52, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 52 (by decide)))

theorem fz1_64_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨53, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 53 (by decide)))

theorem fz1_64_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨54, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 54 (by decide)))

theorem fz1_64_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨55, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 55 (by decide)))

theorem fz1_64_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨56, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 56 (by decide)))

theorem fz1_64_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨57, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 57 (by decide)))

theorem fz1_64_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨58, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 58 (by decide)))

theorem fz1_64_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨59, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 59 (by decide)))

theorem fz1_64_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨60, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 60 (by decide)))

theorem fz1_64_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨61, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 61 (by decide)))

theorem fz1_64_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨62, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 62 (by decide)))

theorem fz1_64_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨63, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 63 (by decide)))

theorem fz1_64_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨65, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 65 (by decide)))

theorem fz1_64_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨66, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 66 (by decide)))

theorem fz1_64_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨67, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 67 (by decide)))

theorem fz1_64_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨68, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 68 (by decide)))

theorem fz1_64_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨69, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 69 (by decide)))

theorem fz1_64_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨70, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 70 (by decide)))

theorem fz1_64_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨71, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 71 (by decide)))

theorem fz1_64_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨72, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 72 (by decide)))

theorem fz1_64_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨73, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 73 (by decide)))

theorem fz1_64_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨74, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 74 (by decide)))

theorem fz1_64_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨75, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 75 (by decide)))

theorem fz1_64_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨76, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 76 (by decide)))

theorem fz1_64_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨77, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 77 (by decide)))

theorem fz1_64_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨78, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 78 (by decide)))

theorem fz1_64_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨79, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 79 (by decide)))

theorem fz1_64_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨80, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 80 (by decide)))

theorem fz1_64_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨81, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 81 (by decide)))

theorem fz1_64_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨82, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 82 (by decide)))

theorem fz1_64_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨83, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 83 (by decide)))

theorem fz1_64_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨84, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 84 (by decide)))

theorem fz1_64_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨85, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 85 (by decide)))

theorem fz1_64_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨86, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 86 (by decide)))

theorem fz1_64_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨87, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 87 (by decide)))

theorem fz1_64_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨88, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 88 (by decide)))

theorem fz1_64_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨89, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 89 (by decide)))

theorem fz1_64_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨90, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 90 (by decide)))

theorem fz1_64_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨91, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 91 (by decide)))

theorem fz1_64_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨92, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 92 (by decide)))

theorem fz1_64_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨93, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 93 (by decide)))

theorem fz1_64_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨94, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 94 (by decide)))

theorem fz1_64_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨95, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 95 (by decide)))

theorem fz1_64_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨96, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 96 (by decide)))

theorem fz1_64_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨97, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 97 (by decide)))

theorem fz1_64_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨98, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 98 (by decide)))

theorem fz1_64_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨99, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 99 (by decide)))

theorem fz1_64_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨100, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 100 (by decide)))

theorem fz1_64_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨101, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 101 (by decide)))

theorem fz1_64_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨102, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 102 (by decide)))

theorem fz1_64_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨103, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 103 (by decide)))

theorem fz1_64_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨104, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 104 (by decide)))

theorem fz1_64_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨105, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 105 (by decide)))

theorem fz1_64_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨106, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 106 (by decide)))

theorem fz1_64_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨107, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 107 (by decide)))

theorem fz1_64_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨108, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 108 (by decide)))

theorem fz1_64_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨109, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 109 (by decide)))

theorem fz1_64_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨110, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 110 (by decide)))

theorem fz1_64_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨111, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 111 (by decide)))

theorem fz1_64_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨112, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 112 (by decide)))

theorem fz1_64_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨113, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 113 (by decide)))

theorem fz1_64_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨114, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 114 (by decide)))

theorem fz1_64_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK64)) = 0 :=
  repsFixedCard rK64 ⟨115, by decide⟩ R64 hpxR64 hcardq64
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_64) 115 (by decide)))

theorem fixz2_64 : ([1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 27, 28, 30, 31, 32, 33, 35, 36, 37, 38, 40, 41, 42, 43, 45, 46, 47, 48, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK64) (retConj 2 (Q2.R64_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_64_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨1, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 1 (by decide)))

theorem fz2_64_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨2, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 2 (by decide)))

theorem fz2_64_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨3, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 3 (by decide)))

theorem fz2_64_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨4, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 4 (by decide)))

theorem fz2_64_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨5, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 5 (by decide)))

theorem fz2_64_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨6, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 6 (by decide)))

theorem fz2_64_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨7, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 7 (by decide)))

theorem fz2_64_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨9, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 9 (by decide)))

theorem fz2_64_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨10, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 10 (by decide)))

theorem fz2_64_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨11, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 11 (by decide)))

theorem fz2_64_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨13, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 13 (by decide)))

theorem fz2_64_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨14, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 14 (by decide)))

theorem fz2_64_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨15, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 15 (by decide)))

theorem fz2_64_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨16, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 16 (by decide)))

theorem fz2_64_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨17, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 17 (by decide)))

theorem fz2_64_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨18, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 18 (by decide)))

theorem fz2_64_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨19, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 19 (by decide)))

theorem fz2_64_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨20, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 20 (by decide)))

theorem fz2_64_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨21, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 21 (by decide)))

theorem fz2_64_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨22, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 22 (by decide)))

theorem fz2_64_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨23, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 23 (by decide)))

theorem fz2_64_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨24, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 24 (by decide)))

theorem fz2_64_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨25, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 25 (by decide)))

theorem fz2_64_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨27, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 27 (by decide)))

theorem fz2_64_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨28, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 28 (by decide)))

theorem fz2_64_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨30, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 30 (by decide)))

theorem fz2_64_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨31, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 31 (by decide)))

theorem fz2_64_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨32, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 32 (by decide)))

theorem fz2_64_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨33, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 33 (by decide)))

theorem fz2_64_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨35, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 35 (by decide)))

theorem fz2_64_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨36, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 36 (by decide)))

theorem fz2_64_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨37, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 37 (by decide)))

theorem fz2_64_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨38, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 38 (by decide)))

theorem fz2_64_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨40, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 40 (by decide)))

theorem fz2_64_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨41, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 41 (by decide)))

theorem fz2_64_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨42, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 42 (by decide)))

theorem fz2_64_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨43, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 43 (by decide)))

theorem fz2_64_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨45, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 45 (by decide)))

theorem fz2_64_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨46, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 46 (by decide)))

theorem fz2_64_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨47, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 47 (by decide)))

theorem fz2_64_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨48, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 48 (by decide)))

theorem fz2_64_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨50, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 50 (by decide)))

theorem fz2_64_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨51, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 51 (by decide)))

theorem fz2_64_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨52, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 52 (by decide)))

theorem fz2_64_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨53, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 53 (by decide)))

theorem fz2_64_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨54, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 54 (by decide)))

theorem fz2_64_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨55, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 55 (by decide)))

theorem fz2_64_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨56, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 56 (by decide)))

theorem fz2_64_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨57, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 57 (by decide)))

theorem fz2_64_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨58, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 58 (by decide)))

theorem fz2_64_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨59, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 59 (by decide)))

theorem fz2_64_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨60, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 60 (by decide)))

theorem fz2_64_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨61, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 61 (by decide)))

theorem fz2_64_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨62, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 62 (by decide)))

theorem fz2_64_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨63, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 63 (by decide)))

theorem fz2_64_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨65, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 65 (by decide)))

theorem fz2_64_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨66, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 66 (by decide)))

theorem fz2_64_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨67, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 67 (by decide)))

theorem fz2_64_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨68, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 68 (by decide)))

theorem fz2_64_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨69, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 69 (by decide)))

theorem fz2_64_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨70, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 70 (by decide)))

theorem fz2_64_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨71, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 71 (by decide)))

theorem fz2_64_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨72, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 72 (by decide)))

theorem fz2_64_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨73, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 73 (by decide)))

theorem fz2_64_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨74, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 74 (by decide)))

theorem fz2_64_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨75, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 75 (by decide)))

theorem fz2_64_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨76, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 76 (by decide)))

theorem fz2_64_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨77, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 77 (by decide)))

theorem fz2_64_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨78, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 78 (by decide)))

theorem fz2_64_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨79, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 79 (by decide)))

theorem fz2_64_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨80, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 80 (by decide)))

theorem fz2_64_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨81, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 81 (by decide)))

theorem fz2_64_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨82, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 82 (by decide)))

theorem fz2_64_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨83, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 83 (by decide)))

theorem fz2_64_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨84, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 84 (by decide)))

theorem fz2_64_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨85, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 85 (by decide)))

theorem fz2_64_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨86, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 86 (by decide)))

theorem fz2_64_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨87, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 87 (by decide)))

theorem fz2_64_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨88, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 88 (by decide)))

theorem fz2_64_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨89, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 89 (by decide)))

theorem fz2_64_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨90, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 90 (by decide)))

theorem fz2_64_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨91, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 91 (by decide)))

theorem fz2_64_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨92, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 92 (by decide)))

theorem fz2_64_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨93, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 93 (by decide)))

theorem fz2_64_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨94, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 94 (by decide)))

theorem fz2_64_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨95, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 95 (by decide)))

theorem fz2_64_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨96, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 96 (by decide)))

theorem fz2_64_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨97, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 97 (by decide)))

theorem fz2_64_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨98, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 98 (by decide)))

theorem fz2_64_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨99, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 99 (by decide)))

theorem fz2_64_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨100, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 100 (by decide)))

theorem fz2_64_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨101, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 101 (by decide)))

theorem fz2_64_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨102, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 102 (by decide)))

theorem fz2_64_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨103, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 103 (by decide)))

theorem fz2_64_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨104, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 104 (by decide)))

theorem fz2_64_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨105, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 105 (by decide)))

theorem fz2_64_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨106, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 106 (by decide)))

theorem fz2_64_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨107, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 107 (by decide)))

theorem fz2_64_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨108, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 108 (by decide)))

theorem fz2_64_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨109, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 109 (by decide)))

theorem fz2_64_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨110, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 110 (by decide)))

theorem fz2_64_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨111, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 111 (by decide)))

theorem fz2_64_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨112, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 112 (by decide)))

theorem fz2_64_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨113, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 113 (by decide)))

theorem fz2_64_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨114, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 114 (by decide)))

theorem fz2_64_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK64)) = 0 :=
  Q2.repsFixedCard2 rK64 ⟨115, by decide⟩ Q2.R64_2 Q2.hpxR64_2 Q2.hcardq64_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_64) 115 (by decide)))

end LeanDring.P5Presentation
