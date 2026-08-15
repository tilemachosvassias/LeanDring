/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryK.C021

/-!
# Species-table cells, off-support emptiness certificates, chunk 71

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

theorem fixz1_89 : ([1, 6, 7, 9, 10, 13, 14, 15, 16, 17, 18, 19, 24, 25, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK89) (retConj 1 (R89 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_89_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨1, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 1 (by decide)))

theorem fz1_89_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨6, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 6 (by decide)))

theorem fz1_89_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨7, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 7 (by decide)))

theorem fz1_89_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨9, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 9 (by decide)))

theorem fz1_89_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨10, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 10 (by decide)))

theorem fz1_89_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨13, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 13 (by decide)))

theorem fz1_89_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨14, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 14 (by decide)))

theorem fz1_89_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨15, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 15 (by decide)))

theorem fz1_89_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨16, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 16 (by decide)))

theorem fz1_89_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨17, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 17 (by decide)))

theorem fz1_89_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨18, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 18 (by decide)))

theorem fz1_89_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨19, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 19 (by decide)))

theorem fz1_89_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨24, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 24 (by decide)))

theorem fz1_89_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨25, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 25 (by decide)))

theorem fz1_89_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨27, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 27 (by decide)))

theorem fz1_89_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨28, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 28 (by decide)))

theorem fz1_89_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨29, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 29 (by decide)))

theorem fz1_89_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨30, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 30 (by decide)))

theorem fz1_89_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨31, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 31 (by decide)))

theorem fz1_89_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨32, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 32 (by decide)))

theorem fz1_89_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨33, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 33 (by decide)))

theorem fz1_89_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨34, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 34 (by decide)))

theorem fz1_89_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨35, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 35 (by decide)))

theorem fz1_89_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨36, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 36 (by decide)))

theorem fz1_89_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨37, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 37 (by decide)))

theorem fz1_89_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨38, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 38 (by decide)))

theorem fz1_89_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨39, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 39 (by decide)))

theorem fz1_89_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨40, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 40 (by decide)))

theorem fz1_89_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨41, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 41 (by decide)))

theorem fz1_89_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨42, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 42 (by decide)))

theorem fz1_89_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨43, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 43 (by decide)))

theorem fz1_89_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨44, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 44 (by decide)))

theorem fz1_89_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨45, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 45 (by decide)))

theorem fz1_89_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨46, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 46 (by decide)))

theorem fz1_89_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨47, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 47 (by decide)))

theorem fz1_89_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨48, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 48 (by decide)))

theorem fz1_89_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨49, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 49 (by decide)))

theorem fz1_89_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨50, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 50 (by decide)))

theorem fz1_89_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨51, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 51 (by decide)))

theorem fz1_89_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨52, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 52 (by decide)))

theorem fz1_89_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨53, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 53 (by decide)))

theorem fz1_89_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨55, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 55 (by decide)))

theorem fz1_89_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨56, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 56 (by decide)))

theorem fz1_89_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨57, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 57 (by decide)))

theorem fz1_89_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨58, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 58 (by decide)))

theorem fz1_89_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨59, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 59 (by decide)))

theorem fz1_89_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨60, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 60 (by decide)))

theorem fz1_89_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨61, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 61 (by decide)))

theorem fz1_89_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨62, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 62 (by decide)))

theorem fz1_89_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨63, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 63 (by decide)))

theorem fz1_89_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨64, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 64 (by decide)))

theorem fz1_89_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨65, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 65 (by decide)))

theorem fz1_89_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨66, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 66 (by decide)))

theorem fz1_89_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨67, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 67 (by decide)))

theorem fz1_89_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨68, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 68 (by decide)))

theorem fz1_89_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨69, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 69 (by decide)))

theorem fz1_89_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨70, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 70 (by decide)))

theorem fz1_89_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨71, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 71 (by decide)))

theorem fz1_89_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨72, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 72 (by decide)))

theorem fz1_89_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨73, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 73 (by decide)))

theorem fz1_89_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨74, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 74 (by decide)))

theorem fz1_89_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨75, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 75 (by decide)))

theorem fz1_89_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨76, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 76 (by decide)))

theorem fz1_89_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨77, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 77 (by decide)))

theorem fz1_89_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨78, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 78 (by decide)))

theorem fz1_89_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨79, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 79 (by decide)))

theorem fz1_89_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨80, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 80 (by decide)))

theorem fz1_89_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨81, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 81 (by decide)))

theorem fz1_89_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨82, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 82 (by decide)))

theorem fz1_89_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨83, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 83 (by decide)))

theorem fz1_89_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨84, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 84 (by decide)))

theorem fz1_89_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨85, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 85 (by decide)))

theorem fz1_89_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨86, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 86 (by decide)))

theorem fz1_89_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨87, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 87 (by decide)))

theorem fz1_89_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨88, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 88 (by decide)))

theorem fz1_89_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨90, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 90 (by decide)))

theorem fz1_89_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨91, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 91 (by decide)))

theorem fz1_89_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨92, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 92 (by decide)))

theorem fz1_89_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨93, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 93 (by decide)))

theorem fz1_89_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨94, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 94 (by decide)))

theorem fz1_89_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨95, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 95 (by decide)))

theorem fz1_89_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨96, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 96 (by decide)))

theorem fz1_89_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨97, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 97 (by decide)))

theorem fz1_89_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨98, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 98 (by decide)))

theorem fz1_89_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨99, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 99 (by decide)))

theorem fz1_89_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨100, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 100 (by decide)))

theorem fz1_89_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨101, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 101 (by decide)))

theorem fz1_89_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨102, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 102 (by decide)))

theorem fz1_89_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨103, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 103 (by decide)))

theorem fz1_89_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨104, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 104 (by decide)))

theorem fz1_89_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨105, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 105 (by decide)))

theorem fz1_89_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨106, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 106 (by decide)))

theorem fz1_89_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨107, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 107 (by decide)))

theorem fz1_89_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨108, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 108 (by decide)))

theorem fz1_89_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨109, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 109 (by decide)))

theorem fz1_89_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨110, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 110 (by decide)))

theorem fz1_89_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨111, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 111 (by decide)))

theorem fz1_89_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨112, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 112 (by decide)))

theorem fz1_89_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨113, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 113 (by decide)))

theorem fz1_89_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨114, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 114 (by decide)))

theorem fz1_89_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK89)) = 0 :=
  repsFixedCard rK89 ⟨115, by decide⟩ R89 hpxR89 hcardq89
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_89) 115 (by decide)))

theorem fixz2_89 : ([1, 6, 7, 9, 10, 13, 14, 15, 16, 17, 18, 19, 24, 25, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK89) (retConj 2 (Q2.R89_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_89_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨1, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 1 (by decide)))

theorem fz2_89_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨6, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 6 (by decide)))

theorem fz2_89_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨7, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 7 (by decide)))

theorem fz2_89_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨9, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 9 (by decide)))

theorem fz2_89_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨10, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 10 (by decide)))

theorem fz2_89_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨13, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 13 (by decide)))

theorem fz2_89_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨14, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 14 (by decide)))

theorem fz2_89_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨15, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 15 (by decide)))

theorem fz2_89_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨16, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 16 (by decide)))

theorem fz2_89_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨17, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 17 (by decide)))

theorem fz2_89_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨18, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 18 (by decide)))

theorem fz2_89_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨19, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 19 (by decide)))

theorem fz2_89_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨24, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 24 (by decide)))

theorem fz2_89_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨25, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 25 (by decide)))

theorem fz2_89_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨27, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 27 (by decide)))

theorem fz2_89_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨28, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 28 (by decide)))

theorem fz2_89_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨29, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 29 (by decide)))

theorem fz2_89_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨30, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 30 (by decide)))

theorem fz2_89_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨31, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 31 (by decide)))

theorem fz2_89_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨32, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 32 (by decide)))

theorem fz2_89_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨33, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 33 (by decide)))

theorem fz2_89_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨34, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 34 (by decide)))

theorem fz2_89_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨35, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 35 (by decide)))

theorem fz2_89_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨36, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 36 (by decide)))

theorem fz2_89_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨37, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 37 (by decide)))

theorem fz2_89_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨38, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 38 (by decide)))

theorem fz2_89_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨39, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 39 (by decide)))

theorem fz2_89_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨40, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 40 (by decide)))

theorem fz2_89_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨41, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 41 (by decide)))

theorem fz2_89_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨42, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 42 (by decide)))

theorem fz2_89_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨43, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 43 (by decide)))

theorem fz2_89_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨44, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 44 (by decide)))

theorem fz2_89_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨45, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 45 (by decide)))

theorem fz2_89_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨46, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 46 (by decide)))

theorem fz2_89_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨47, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 47 (by decide)))

theorem fz2_89_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨48, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 48 (by decide)))

theorem fz2_89_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨49, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 49 (by decide)))

theorem fz2_89_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨50, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 50 (by decide)))

theorem fz2_89_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨51, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 51 (by decide)))

theorem fz2_89_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨52, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 52 (by decide)))

theorem fz2_89_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨53, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 53 (by decide)))

theorem fz2_89_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨55, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 55 (by decide)))

theorem fz2_89_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨56, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 56 (by decide)))

theorem fz2_89_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨57, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 57 (by decide)))

theorem fz2_89_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨58, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 58 (by decide)))

theorem fz2_89_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨59, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 59 (by decide)))

theorem fz2_89_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨60, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 60 (by decide)))

theorem fz2_89_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨61, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 61 (by decide)))

theorem fz2_89_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨62, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 62 (by decide)))

theorem fz2_89_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨63, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 63 (by decide)))

theorem fz2_89_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨64, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 64 (by decide)))

theorem fz2_89_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨65, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 65 (by decide)))

theorem fz2_89_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨66, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 66 (by decide)))

theorem fz2_89_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨67, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 67 (by decide)))

theorem fz2_89_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨68, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 68 (by decide)))

theorem fz2_89_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨69, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 69 (by decide)))

theorem fz2_89_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨70, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 70 (by decide)))

theorem fz2_89_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨71, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 71 (by decide)))

theorem fz2_89_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨72, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 72 (by decide)))

theorem fz2_89_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨73, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 73 (by decide)))

theorem fz2_89_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨74, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 74 (by decide)))

theorem fz2_89_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨75, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 75 (by decide)))

theorem fz2_89_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨76, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 76 (by decide)))

theorem fz2_89_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨77, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 77 (by decide)))

theorem fz2_89_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨78, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 78 (by decide)))

theorem fz2_89_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨79, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 79 (by decide)))

theorem fz2_89_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨80, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 80 (by decide)))

theorem fz2_89_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨81, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 81 (by decide)))

theorem fz2_89_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨82, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 82 (by decide)))

theorem fz2_89_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨83, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 83 (by decide)))

theorem fz2_89_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨84, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 84 (by decide)))

theorem fz2_89_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨85, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 85 (by decide)))

theorem fz2_89_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨86, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 86 (by decide)))

theorem fz2_89_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨87, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 87 (by decide)))

theorem fz2_89_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨88, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 88 (by decide)))

theorem fz2_89_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨90, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 90 (by decide)))

theorem fz2_89_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨91, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 91 (by decide)))

theorem fz2_89_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨92, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 92 (by decide)))

theorem fz2_89_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨93, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 93 (by decide)))

theorem fz2_89_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨94, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 94 (by decide)))

theorem fz2_89_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨95, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 95 (by decide)))

theorem fz2_89_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨96, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 96 (by decide)))

theorem fz2_89_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨97, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 97 (by decide)))

theorem fz2_89_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨98, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 98 (by decide)))

theorem fz2_89_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨99, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 99 (by decide)))

theorem fz2_89_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨100, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 100 (by decide)))

theorem fz2_89_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨101, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 101 (by decide)))

theorem fz2_89_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨102, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 102 (by decide)))

theorem fz2_89_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨103, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 103 (by decide)))

theorem fz2_89_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨104, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 104 (by decide)))

theorem fz2_89_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨105, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 105 (by decide)))

theorem fz2_89_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨106, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 106 (by decide)))

theorem fz2_89_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨107, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 107 (by decide)))

theorem fz2_89_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨108, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 108 (by decide)))

theorem fz2_89_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨109, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 109 (by decide)))

theorem fz2_89_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨110, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 110 (by decide)))

theorem fz2_89_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨111, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 111 (by decide)))

theorem fz2_89_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨112, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 112 (by decide)))

theorem fz2_89_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨113, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 113 (by decide)))

theorem fz2_89_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨114, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 114 (by decide)))

theorem fz2_89_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK89)) = 0 :=
  Q2.repsFixedCard2 rK89 ⟨115, by decide⟩ Q2.R89_2 Q2.hpxR89_2 Q2.hcardq89_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_89) 115 (by decide)))

theorem fixz1_90 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK90) (retConj 1 (R90 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_90_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨1, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 1 (by decide)))

theorem fz1_90_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨2, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 2 (by decide)))

theorem fz1_90_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨3, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 3 (by decide)))

theorem fz1_90_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨4, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 4 (by decide)))

theorem fz1_90_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨5, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 5 (by decide)))

theorem fz1_90_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨6, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 6 (by decide)))

theorem fz1_90_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨7, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 7 (by decide)))

theorem fz1_90_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨8, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 8 (by decide)))

theorem fz1_90_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨9, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 9 (by decide)))

theorem fz1_90_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨11, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 11 (by decide)))

theorem fz1_90_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨13, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 13 (by decide)))

theorem fz1_90_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨14, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 14 (by decide)))

theorem fz1_90_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨15, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 15 (by decide)))

theorem fz1_90_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨16, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 16 (by decide)))

theorem fz1_90_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨17, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 17 (by decide)))

theorem fz1_90_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨18, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 18 (by decide)))

theorem fz1_90_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨19, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 19 (by decide)))

theorem fz1_90_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨20, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 20 (by decide)))

theorem fz1_90_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨21, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 21 (by decide)))

theorem fz1_90_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨22, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 22 (by decide)))

theorem fz1_90_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨23, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 23 (by decide)))

theorem fz1_90_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨24, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 24 (by decide)))

theorem fz1_90_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨25, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 25 (by decide)))

theorem fz1_90_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨26, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 26 (by decide)))

theorem fz1_90_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨27, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 27 (by decide)))

theorem fz1_90_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨29, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 29 (by decide)))

theorem fz1_90_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨30, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 30 (by decide)))

theorem fz1_90_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨31, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 31 (by decide)))

theorem fz1_90_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨32, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 32 (by decide)))

theorem fz1_90_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨33, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 33 (by decide)))

theorem fz1_90_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨34, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 34 (by decide)))

theorem fz1_90_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨35, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 35 (by decide)))

theorem fz1_90_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨36, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 36 (by decide)))

theorem fz1_90_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨37, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 37 (by decide)))

theorem fz1_90_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨38, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 38 (by decide)))

theorem fz1_90_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨39, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 39 (by decide)))

theorem fz1_90_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨40, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 40 (by decide)))

theorem fz1_90_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨41, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 41 (by decide)))

theorem fz1_90_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨42, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 42 (by decide)))

theorem fz1_90_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨43, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 43 (by decide)))

theorem fz1_90_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨44, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 44 (by decide)))

theorem fz1_90_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨45, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 45 (by decide)))

theorem fz1_90_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨46, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 46 (by decide)))

theorem fz1_90_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨47, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 47 (by decide)))

theorem fz1_90_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨48, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 48 (by decide)))

theorem fz1_90_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨49, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 49 (by decide)))

theorem fz1_90_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨50, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 50 (by decide)))

theorem fz1_90_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨51, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 51 (by decide)))

theorem fz1_90_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨52, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 52 (by decide)))

theorem fz1_90_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨54, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 54 (by decide)))

theorem fz1_90_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨55, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 55 (by decide)))

theorem fz1_90_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨56, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 56 (by decide)))

theorem fz1_90_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨57, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 57 (by decide)))

theorem fz1_90_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨58, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 58 (by decide)))

theorem fz1_90_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨59, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 59 (by decide)))

theorem fz1_90_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨60, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 60 (by decide)))

theorem fz1_90_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨61, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 61 (by decide)))

theorem fz1_90_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨62, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 62 (by decide)))

theorem fz1_90_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨63, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 63 (by decide)))

theorem fz1_90_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨64, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 64 (by decide)))

theorem fz1_90_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨65, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 65 (by decide)))

theorem fz1_90_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨66, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 66 (by decide)))

theorem fz1_90_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨67, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 67 (by decide)))

theorem fz1_90_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨68, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 68 (by decide)))

theorem fz1_90_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨69, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 69 (by decide)))

theorem fz1_90_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨70, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 70 (by decide)))

theorem fz1_90_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨71, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 71 (by decide)))

theorem fz1_90_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨72, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 72 (by decide)))

theorem fz1_90_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨73, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 73 (by decide)))

theorem fz1_90_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨74, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 74 (by decide)))

theorem fz1_90_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨75, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 75 (by decide)))

theorem fz1_90_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨76, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 76 (by decide)))

theorem fz1_90_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨77, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 77 (by decide)))

theorem fz1_90_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨78, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 78 (by decide)))

theorem fz1_90_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨79, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 79 (by decide)))

theorem fz1_90_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨80, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 80 (by decide)))

theorem fz1_90_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨81, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 81 (by decide)))

theorem fz1_90_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨82, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 82 (by decide)))

theorem fz1_90_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨83, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 83 (by decide)))

theorem fz1_90_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨84, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 84 (by decide)))

theorem fz1_90_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨85, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 85 (by decide)))

theorem fz1_90_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨86, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 86 (by decide)))

theorem fz1_90_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨87, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 87 (by decide)))

theorem fz1_90_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨88, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 88 (by decide)))

theorem fz1_90_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨89, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 89 (by decide)))

theorem fz1_90_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨91, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 91 (by decide)))

theorem fz1_90_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨92, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 92 (by decide)))

theorem fz1_90_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨93, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 93 (by decide)))

theorem fz1_90_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨94, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 94 (by decide)))

theorem fz1_90_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨95, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 95 (by decide)))

theorem fz1_90_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨96, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 96 (by decide)))

theorem fz1_90_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨97, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 97 (by decide)))

theorem fz1_90_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨98, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 98 (by decide)))

theorem fz1_90_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨99, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 99 (by decide)))

theorem fz1_90_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨100, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 100 (by decide)))

theorem fz1_90_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨101, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 101 (by decide)))

theorem fz1_90_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨102, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 102 (by decide)))

theorem fz1_90_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨103, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 103 (by decide)))

theorem fz1_90_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨104, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 104 (by decide)))

theorem fz1_90_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨105, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 105 (by decide)))

theorem fz1_90_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨106, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 106 (by decide)))

theorem fz1_90_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨107, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 107 (by decide)))

theorem fz1_90_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨108, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 108 (by decide)))

theorem fz1_90_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨109, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 109 (by decide)))

theorem fz1_90_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨110, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 110 (by decide)))

theorem fz1_90_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨111, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 111 (by decide)))

theorem fz1_90_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨112, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 112 (by decide)))

theorem fz1_90_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨113, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 113 (by decide)))

theorem fz1_90_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨114, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 114 (by decide)))

theorem fz1_90_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK90)) = 0 :=
  repsFixedCard rK90 ⟨115, by decide⟩ R90 hpxR90 hcardq90
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_90) 115 (by decide)))

theorem fixz2_90 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK90) (retConj 2 (Q2.R90_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_90_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨1, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 1 (by decide)))

theorem fz2_90_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨2, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 2 (by decide)))

theorem fz2_90_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨3, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 3 (by decide)))

theorem fz2_90_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨4, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 4 (by decide)))

theorem fz2_90_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨5, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 5 (by decide)))

theorem fz2_90_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨6, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 6 (by decide)))

theorem fz2_90_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨7, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 7 (by decide)))

theorem fz2_90_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨8, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 8 (by decide)))

theorem fz2_90_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨9, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 9 (by decide)))

theorem fz2_90_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨11, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 11 (by decide)))

theorem fz2_90_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨13, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 13 (by decide)))

theorem fz2_90_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨14, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 14 (by decide)))

theorem fz2_90_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨15, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 15 (by decide)))

theorem fz2_90_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨16, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 16 (by decide)))

theorem fz2_90_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨17, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 17 (by decide)))

theorem fz2_90_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨18, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 18 (by decide)))

theorem fz2_90_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨19, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 19 (by decide)))

theorem fz2_90_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨20, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 20 (by decide)))

theorem fz2_90_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨21, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 21 (by decide)))

theorem fz2_90_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨22, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 22 (by decide)))

theorem fz2_90_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨23, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 23 (by decide)))

theorem fz2_90_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨24, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 24 (by decide)))

theorem fz2_90_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨25, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 25 (by decide)))

theorem fz2_90_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨26, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 26 (by decide)))

theorem fz2_90_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨27, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 27 (by decide)))

theorem fz2_90_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨29, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 29 (by decide)))

theorem fz2_90_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨30, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 30 (by decide)))

theorem fz2_90_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨31, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 31 (by decide)))

theorem fz2_90_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨32, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 32 (by decide)))

theorem fz2_90_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨33, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 33 (by decide)))

theorem fz2_90_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨34, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 34 (by decide)))

theorem fz2_90_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨35, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 35 (by decide)))

theorem fz2_90_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨36, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 36 (by decide)))

theorem fz2_90_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨37, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 37 (by decide)))

theorem fz2_90_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨38, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 38 (by decide)))

theorem fz2_90_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨39, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 39 (by decide)))

theorem fz2_90_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨40, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 40 (by decide)))

theorem fz2_90_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨41, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 41 (by decide)))

theorem fz2_90_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨42, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 42 (by decide)))

theorem fz2_90_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨43, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 43 (by decide)))

theorem fz2_90_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨44, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 44 (by decide)))

theorem fz2_90_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨45, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 45 (by decide)))

theorem fz2_90_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨46, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 46 (by decide)))

theorem fz2_90_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨47, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 47 (by decide)))

theorem fz2_90_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨48, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 48 (by decide)))

theorem fz2_90_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨49, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 49 (by decide)))

theorem fz2_90_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨50, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 50 (by decide)))

theorem fz2_90_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨51, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 51 (by decide)))

theorem fz2_90_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨52, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 52 (by decide)))

theorem fz2_90_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨54, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 54 (by decide)))

theorem fz2_90_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨55, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 55 (by decide)))

theorem fz2_90_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨56, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 56 (by decide)))

theorem fz2_90_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨57, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 57 (by decide)))

theorem fz2_90_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨58, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 58 (by decide)))

theorem fz2_90_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨59, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 59 (by decide)))

theorem fz2_90_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨60, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 60 (by decide)))

theorem fz2_90_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨61, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 61 (by decide)))

theorem fz2_90_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨62, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 62 (by decide)))

theorem fz2_90_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨63, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 63 (by decide)))

theorem fz2_90_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨64, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 64 (by decide)))

theorem fz2_90_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨65, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 65 (by decide)))

theorem fz2_90_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨66, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 66 (by decide)))

theorem fz2_90_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨67, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 67 (by decide)))

theorem fz2_90_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨68, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 68 (by decide)))

theorem fz2_90_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨69, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 69 (by decide)))

theorem fz2_90_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨70, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 70 (by decide)))

theorem fz2_90_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨71, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 71 (by decide)))

theorem fz2_90_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨72, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 72 (by decide)))

theorem fz2_90_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨73, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 73 (by decide)))

theorem fz2_90_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨74, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 74 (by decide)))

theorem fz2_90_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨75, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 75 (by decide)))

theorem fz2_90_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨76, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 76 (by decide)))

theorem fz2_90_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨77, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 77 (by decide)))

theorem fz2_90_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨78, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 78 (by decide)))

theorem fz2_90_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨79, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 79 (by decide)))

theorem fz2_90_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨80, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 80 (by decide)))

theorem fz2_90_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨81, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 81 (by decide)))

theorem fz2_90_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨82, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 82 (by decide)))

theorem fz2_90_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨83, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 83 (by decide)))

theorem fz2_90_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨84, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 84 (by decide)))

theorem fz2_90_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨85, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 85 (by decide)))

theorem fz2_90_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨86, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 86 (by decide)))

theorem fz2_90_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨87, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 87 (by decide)))

theorem fz2_90_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨88, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 88 (by decide)))

theorem fz2_90_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨89, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 89 (by decide)))

theorem fz2_90_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨91, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 91 (by decide)))

theorem fz2_90_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨92, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 92 (by decide)))

theorem fz2_90_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨93, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 93 (by decide)))

theorem fz2_90_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨94, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 94 (by decide)))

theorem fz2_90_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨95, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 95 (by decide)))

theorem fz2_90_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨96, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 96 (by decide)))

theorem fz2_90_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨97, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 97 (by decide)))

theorem fz2_90_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨98, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 98 (by decide)))

theorem fz2_90_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨99, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 99 (by decide)))

theorem fz2_90_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨100, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 100 (by decide)))

theorem fz2_90_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨101, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 101 (by decide)))

theorem fz2_90_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨102, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 102 (by decide)))

theorem fz2_90_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨103, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 103 (by decide)))

theorem fz2_90_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨104, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 104 (by decide)))

theorem fz2_90_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨105, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 105 (by decide)))

theorem fz2_90_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨106, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 106 (by decide)))

theorem fz2_90_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨107, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 107 (by decide)))

theorem fz2_90_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨108, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 108 (by decide)))

theorem fz2_90_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨109, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 109 (by decide)))

theorem fz2_90_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨110, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 110 (by decide)))

theorem fz2_90_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨111, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 111 (by decide)))

theorem fz2_90_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨112, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 112 (by decide)))

theorem fz2_90_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨113, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 113 (by decide)))

theorem fz2_90_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨114, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 114 (by decide)))

theorem fz2_90_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK90)) = 0 :=
  Q2.repsFixedCard2 rK90 ⟨115, by decide⟩ Q2.R90_2 Q2.hpxR90_2 Q2.hcardq90_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_90) 115 (by decide)))

end LeanDring.P5Presentation
