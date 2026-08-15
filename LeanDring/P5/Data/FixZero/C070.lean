/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryK.C020

/-!
# Species-table cells, off-support emptiness certificates, chunk 69

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

theorem fixz1_85 : ([1, 6, 7, 8, 10, 13, 19, 24, 25, 26, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK85) (retConj 1 (R85 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_85_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨1, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 1 (by decide)))

theorem fz1_85_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨6, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 6 (by decide)))

theorem fz1_85_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨7, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 7 (by decide)))

theorem fz1_85_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨8, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 8 (by decide)))

theorem fz1_85_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨10, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 10 (by decide)))

theorem fz1_85_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨13, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 13 (by decide)))

theorem fz1_85_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨19, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 19 (by decide)))

theorem fz1_85_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨24, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 24 (by decide)))

theorem fz1_85_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨25, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 25 (by decide)))

theorem fz1_85_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨26, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 26 (by decide)))

theorem fz1_85_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨28, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 28 (by decide)))

theorem fz1_85_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨29, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 29 (by decide)))

theorem fz1_85_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨30, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 30 (by decide)))

theorem fz1_85_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨31, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 31 (by decide)))

theorem fz1_85_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨32, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 32 (by decide)))

theorem fz1_85_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨33, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 33 (by decide)))

theorem fz1_85_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨34, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 34 (by decide)))

theorem fz1_85_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨35, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 35 (by decide)))

theorem fz1_85_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨36, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 36 (by decide)))

theorem fz1_85_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨37, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 37 (by decide)))

theorem fz1_85_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨38, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 38 (by decide)))

theorem fz1_85_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨39, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 39 (by decide)))

theorem fz1_85_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨40, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 40 (by decide)))

theorem fz1_85_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨41, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 41 (by decide)))

theorem fz1_85_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨42, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 42 (by decide)))

theorem fz1_85_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨43, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 43 (by decide)))

theorem fz1_85_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨44, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 44 (by decide)))

theorem fz1_85_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨45, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 45 (by decide)))

theorem fz1_85_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨46, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 46 (by decide)))

theorem fz1_85_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨47, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 47 (by decide)))

theorem fz1_85_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨48, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 48 (by decide)))

theorem fz1_85_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨49, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 49 (by decide)))

theorem fz1_85_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨50, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 50 (by decide)))

theorem fz1_85_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨51, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 51 (by decide)))

theorem fz1_85_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨52, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 52 (by decide)))

theorem fz1_85_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨53, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 53 (by decide)))

theorem fz1_85_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨55, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 55 (by decide)))

theorem fz1_85_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨56, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 56 (by decide)))

theorem fz1_85_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨57, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 57 (by decide)))

theorem fz1_85_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨58, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 58 (by decide)))

theorem fz1_85_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨59, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 59 (by decide)))

theorem fz1_85_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨60, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 60 (by decide)))

theorem fz1_85_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨61, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 61 (by decide)))

theorem fz1_85_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨62, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 62 (by decide)))

theorem fz1_85_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨63, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 63 (by decide)))

theorem fz1_85_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨64, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 64 (by decide)))

theorem fz1_85_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨65, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 65 (by decide)))

theorem fz1_85_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨66, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 66 (by decide)))

theorem fz1_85_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨67, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 67 (by decide)))

theorem fz1_85_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨68, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 68 (by decide)))

theorem fz1_85_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨69, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 69 (by decide)))

theorem fz1_85_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨70, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 70 (by decide)))

theorem fz1_85_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨71, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 71 (by decide)))

theorem fz1_85_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨72, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 72 (by decide)))

theorem fz1_85_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨73, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 73 (by decide)))

theorem fz1_85_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨74, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 74 (by decide)))

theorem fz1_85_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨75, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 75 (by decide)))

theorem fz1_85_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨76, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 76 (by decide)))

theorem fz1_85_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨77, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 77 (by decide)))

theorem fz1_85_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨78, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 78 (by decide)))

theorem fz1_85_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨79, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 79 (by decide)))

theorem fz1_85_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨80, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 80 (by decide)))

theorem fz1_85_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨81, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 81 (by decide)))

theorem fz1_85_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨82, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 82 (by decide)))

theorem fz1_85_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨83, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 83 (by decide)))

theorem fz1_85_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨84, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 84 (by decide)))

theorem fz1_85_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨86, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 86 (by decide)))

theorem fz1_85_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨87, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 87 (by decide)))

theorem fz1_85_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨88, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 88 (by decide)))

theorem fz1_85_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨89, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 89 (by decide)))

theorem fz1_85_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨90, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 90 (by decide)))

theorem fz1_85_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨91, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 91 (by decide)))

theorem fz1_85_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨92, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 92 (by decide)))

theorem fz1_85_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨93, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 93 (by decide)))

theorem fz1_85_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨94, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 94 (by decide)))

theorem fz1_85_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨95, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 95 (by decide)))

theorem fz1_85_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨96, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 96 (by decide)))

theorem fz1_85_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨97, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 97 (by decide)))

theorem fz1_85_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨98, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 98 (by decide)))

theorem fz1_85_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨99, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 99 (by decide)))

theorem fz1_85_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨100, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 100 (by decide)))

theorem fz1_85_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨101, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 101 (by decide)))

theorem fz1_85_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨102, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 102 (by decide)))

theorem fz1_85_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨103, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 103 (by decide)))

theorem fz1_85_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨104, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 104 (by decide)))

theorem fz1_85_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨105, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 105 (by decide)))

theorem fz1_85_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨106, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 106 (by decide)))

theorem fz1_85_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨107, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 107 (by decide)))

theorem fz1_85_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨108, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 108 (by decide)))

theorem fz1_85_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨109, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 109 (by decide)))

theorem fz1_85_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨110, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 110 (by decide)))

theorem fz1_85_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨111, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 111 (by decide)))

theorem fz1_85_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨112, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 112 (by decide)))

theorem fz1_85_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨113, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 113 (by decide)))

theorem fz1_85_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨114, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 114 (by decide)))

theorem fz1_85_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK85)) = 0 :=
  repsFixedCard rK85 ⟨115, by decide⟩ R85 hpxR85 hcardq85
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_85) 115 (by decide)))

theorem fixz2_85 : ([1, 6, 7, 8, 10, 13, 19, 24, 25, 26, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK85) (retConj 2 (Q2.R85_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_85_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨1, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 1 (by decide)))

theorem fz2_85_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨6, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 6 (by decide)))

theorem fz2_85_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨7, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 7 (by decide)))

theorem fz2_85_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨8, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 8 (by decide)))

theorem fz2_85_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨10, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 10 (by decide)))

theorem fz2_85_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨13, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 13 (by decide)))

theorem fz2_85_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨19, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 19 (by decide)))

theorem fz2_85_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨24, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 24 (by decide)))

theorem fz2_85_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨25, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 25 (by decide)))

theorem fz2_85_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨26, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 26 (by decide)))

theorem fz2_85_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨28, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 28 (by decide)))

theorem fz2_85_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨29, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 29 (by decide)))

theorem fz2_85_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨30, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 30 (by decide)))

theorem fz2_85_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨31, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 31 (by decide)))

theorem fz2_85_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨32, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 32 (by decide)))

theorem fz2_85_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨33, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 33 (by decide)))

theorem fz2_85_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨34, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 34 (by decide)))

theorem fz2_85_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨35, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 35 (by decide)))

theorem fz2_85_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨36, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 36 (by decide)))

theorem fz2_85_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨37, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 37 (by decide)))

theorem fz2_85_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨38, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 38 (by decide)))

theorem fz2_85_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨39, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 39 (by decide)))

theorem fz2_85_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨40, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 40 (by decide)))

theorem fz2_85_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨41, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 41 (by decide)))

theorem fz2_85_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨42, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 42 (by decide)))

theorem fz2_85_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨43, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 43 (by decide)))

theorem fz2_85_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨44, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 44 (by decide)))

theorem fz2_85_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨45, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 45 (by decide)))

theorem fz2_85_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨46, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 46 (by decide)))

theorem fz2_85_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨47, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 47 (by decide)))

theorem fz2_85_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨48, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 48 (by decide)))

theorem fz2_85_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨49, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 49 (by decide)))

theorem fz2_85_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨50, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 50 (by decide)))

theorem fz2_85_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨51, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 51 (by decide)))

theorem fz2_85_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨52, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 52 (by decide)))

theorem fz2_85_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨53, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 53 (by decide)))

theorem fz2_85_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨55, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 55 (by decide)))

theorem fz2_85_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨56, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 56 (by decide)))

theorem fz2_85_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨57, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 57 (by decide)))

theorem fz2_85_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨58, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 58 (by decide)))

theorem fz2_85_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨59, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 59 (by decide)))

theorem fz2_85_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨60, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 60 (by decide)))

theorem fz2_85_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨61, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 61 (by decide)))

theorem fz2_85_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨62, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 62 (by decide)))

theorem fz2_85_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨63, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 63 (by decide)))

theorem fz2_85_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨64, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 64 (by decide)))

theorem fz2_85_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨65, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 65 (by decide)))

theorem fz2_85_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨66, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 66 (by decide)))

theorem fz2_85_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨67, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 67 (by decide)))

theorem fz2_85_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨68, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 68 (by decide)))

theorem fz2_85_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨69, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 69 (by decide)))

theorem fz2_85_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨70, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 70 (by decide)))

theorem fz2_85_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨71, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 71 (by decide)))

theorem fz2_85_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨72, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 72 (by decide)))

theorem fz2_85_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨73, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 73 (by decide)))

theorem fz2_85_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨74, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 74 (by decide)))

theorem fz2_85_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨75, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 75 (by decide)))

theorem fz2_85_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨76, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 76 (by decide)))

theorem fz2_85_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨77, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 77 (by decide)))

theorem fz2_85_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨78, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 78 (by decide)))

theorem fz2_85_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨79, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 79 (by decide)))

theorem fz2_85_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨80, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 80 (by decide)))

theorem fz2_85_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨81, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 81 (by decide)))

theorem fz2_85_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨82, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 82 (by decide)))

theorem fz2_85_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨83, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 83 (by decide)))

theorem fz2_85_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨84, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 84 (by decide)))

theorem fz2_85_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨86, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 86 (by decide)))

theorem fz2_85_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨87, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 87 (by decide)))

theorem fz2_85_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨88, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 88 (by decide)))

theorem fz2_85_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨89, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 89 (by decide)))

theorem fz2_85_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨90, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 90 (by decide)))

theorem fz2_85_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨91, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 91 (by decide)))

theorem fz2_85_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨92, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 92 (by decide)))

theorem fz2_85_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨93, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 93 (by decide)))

theorem fz2_85_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨94, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 94 (by decide)))

theorem fz2_85_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨95, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 95 (by decide)))

theorem fz2_85_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨96, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 96 (by decide)))

theorem fz2_85_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨97, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 97 (by decide)))

theorem fz2_85_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨98, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 98 (by decide)))

theorem fz2_85_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨99, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 99 (by decide)))

theorem fz2_85_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨100, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 100 (by decide)))

theorem fz2_85_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨101, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 101 (by decide)))

theorem fz2_85_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨102, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 102 (by decide)))

theorem fz2_85_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨103, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 103 (by decide)))

theorem fz2_85_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨104, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 104 (by decide)))

theorem fz2_85_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨105, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 105 (by decide)))

theorem fz2_85_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨106, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 106 (by decide)))

theorem fz2_85_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨107, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 107 (by decide)))

theorem fz2_85_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨108, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 108 (by decide)))

theorem fz2_85_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨109, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 109 (by decide)))

theorem fz2_85_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨110, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 110 (by decide)))

theorem fz2_85_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨111, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 111 (by decide)))

theorem fz2_85_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨112, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 112 (by decide)))

theorem fz2_85_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨113, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 113 (by decide)))

theorem fz2_85_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨114, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 114 (by decide)))

theorem fz2_85_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK85)) = 0 :=
  Q2.repsFixedCard2 rK85 ⟨115, by decide⟩ Q2.R85_2 Q2.hpxR85_2 Q2.hcardq85_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_85) 115 (by decide)))

theorem fixz1_86 : ([6, 7, 8, 9, 10, 13, 14, 15, 16, 17, 18, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK86) (retConj 1 (R86 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_86_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨6, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 6 (by decide)))

theorem fz1_86_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨7, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 7 (by decide)))

theorem fz1_86_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨8, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 8 (by decide)))

theorem fz1_86_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨9, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 9 (by decide)))

theorem fz1_86_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨10, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 10 (by decide)))

theorem fz1_86_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨13, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 13 (by decide)))

theorem fz1_86_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨14, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 14 (by decide)))

theorem fz1_86_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨15, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 15 (by decide)))

theorem fz1_86_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨16, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 16 (by decide)))

theorem fz1_86_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨17, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 17 (by decide)))

theorem fz1_86_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨18, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 18 (by decide)))

theorem fz1_86_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨24, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 24 (by decide)))

theorem fz1_86_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨25, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 25 (by decide)))

theorem fz1_86_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨26, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 26 (by decide)))

theorem fz1_86_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨27, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 27 (by decide)))

theorem fz1_86_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨28, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 28 (by decide)))

theorem fz1_86_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨29, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 29 (by decide)))

theorem fz1_86_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨30, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 30 (by decide)))

theorem fz1_86_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨31, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 31 (by decide)))

theorem fz1_86_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨32, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 32 (by decide)))

theorem fz1_86_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨33, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 33 (by decide)))

theorem fz1_86_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨34, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 34 (by decide)))

theorem fz1_86_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨35, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 35 (by decide)))

theorem fz1_86_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨36, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 36 (by decide)))

theorem fz1_86_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨37, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 37 (by decide)))

theorem fz1_86_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨38, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 38 (by decide)))

theorem fz1_86_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨39, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 39 (by decide)))

theorem fz1_86_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨40, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 40 (by decide)))

theorem fz1_86_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨41, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 41 (by decide)))

theorem fz1_86_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨42, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 42 (by decide)))

theorem fz1_86_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨43, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 43 (by decide)))

theorem fz1_86_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨44, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 44 (by decide)))

theorem fz1_86_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨45, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 45 (by decide)))

theorem fz1_86_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨46, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 46 (by decide)))

theorem fz1_86_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨47, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 47 (by decide)))

theorem fz1_86_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨48, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 48 (by decide)))

theorem fz1_86_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨49, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 49 (by decide)))

theorem fz1_86_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨50, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 50 (by decide)))

theorem fz1_86_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨51, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 51 (by decide)))

theorem fz1_86_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨52, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 52 (by decide)))

theorem fz1_86_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨53, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 53 (by decide)))

theorem fz1_86_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨55, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 55 (by decide)))

theorem fz1_86_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨56, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 56 (by decide)))

theorem fz1_86_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨57, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 57 (by decide)))

theorem fz1_86_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨58, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 58 (by decide)))

theorem fz1_86_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨59, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 59 (by decide)))

theorem fz1_86_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨60, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 60 (by decide)))

theorem fz1_86_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨61, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 61 (by decide)))

theorem fz1_86_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨62, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 62 (by decide)))

theorem fz1_86_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨63, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 63 (by decide)))

theorem fz1_86_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨64, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 64 (by decide)))

theorem fz1_86_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨65, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 65 (by decide)))

theorem fz1_86_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨66, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 66 (by decide)))

theorem fz1_86_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨67, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 67 (by decide)))

theorem fz1_86_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨68, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 68 (by decide)))

theorem fz1_86_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨69, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 69 (by decide)))

theorem fz1_86_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨70, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 70 (by decide)))

theorem fz1_86_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨71, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 71 (by decide)))

theorem fz1_86_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨72, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 72 (by decide)))

theorem fz1_86_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨73, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 73 (by decide)))

theorem fz1_86_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨74, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 74 (by decide)))

theorem fz1_86_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨75, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 75 (by decide)))

theorem fz1_86_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨76, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 76 (by decide)))

theorem fz1_86_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨77, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 77 (by decide)))

theorem fz1_86_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨78, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 78 (by decide)))

theorem fz1_86_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨79, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 79 (by decide)))

theorem fz1_86_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨80, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 80 (by decide)))

theorem fz1_86_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨81, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 81 (by decide)))

theorem fz1_86_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨82, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 82 (by decide)))

theorem fz1_86_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨83, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 83 (by decide)))

theorem fz1_86_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨84, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 84 (by decide)))

theorem fz1_86_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨85, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 85 (by decide)))

theorem fz1_86_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨87, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 87 (by decide)))

theorem fz1_86_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨88, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 88 (by decide)))

theorem fz1_86_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨89, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 89 (by decide)))

theorem fz1_86_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨90, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 90 (by decide)))

theorem fz1_86_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨91, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 91 (by decide)))

theorem fz1_86_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨92, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 92 (by decide)))

theorem fz1_86_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨93, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 93 (by decide)))

theorem fz1_86_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨94, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 94 (by decide)))

theorem fz1_86_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨95, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 95 (by decide)))

theorem fz1_86_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨96, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 96 (by decide)))

theorem fz1_86_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨97, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 97 (by decide)))

theorem fz1_86_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨98, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 98 (by decide)))

theorem fz1_86_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨99, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 99 (by decide)))

theorem fz1_86_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨100, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 100 (by decide)))

theorem fz1_86_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨101, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 101 (by decide)))

theorem fz1_86_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨102, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 102 (by decide)))

theorem fz1_86_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨103, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 103 (by decide)))

theorem fz1_86_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨104, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 104 (by decide)))

theorem fz1_86_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨105, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 105 (by decide)))

theorem fz1_86_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨106, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 106 (by decide)))

theorem fz1_86_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨107, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 107 (by decide)))

theorem fz1_86_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨108, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 108 (by decide)))

theorem fz1_86_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨109, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 109 (by decide)))

theorem fz1_86_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨110, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 110 (by decide)))

theorem fz1_86_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨111, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 111 (by decide)))

theorem fz1_86_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨112, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 112 (by decide)))

theorem fz1_86_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨113, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 113 (by decide)))

theorem fz1_86_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨114, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 114 (by decide)))

theorem fz1_86_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK86)) = 0 :=
  repsFixedCard rK86 ⟨115, by decide⟩ R86 hpxR86 hcardq86
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_86) 115 (by decide)))

theorem fixz2_86 : ([6, 7, 8, 9, 10, 13, 14, 15, 16, 17, 18, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK86) (retConj 2 (Q2.R86_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_86_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨6, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 6 (by decide)))

theorem fz2_86_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨7, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 7 (by decide)))

theorem fz2_86_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨8, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 8 (by decide)))

theorem fz2_86_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨9, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 9 (by decide)))

theorem fz2_86_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨10, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 10 (by decide)))

theorem fz2_86_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨13, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 13 (by decide)))

theorem fz2_86_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨14, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 14 (by decide)))

theorem fz2_86_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨15, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 15 (by decide)))

theorem fz2_86_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨16, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 16 (by decide)))

theorem fz2_86_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨17, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 17 (by decide)))

theorem fz2_86_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨18, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 18 (by decide)))

theorem fz2_86_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨24, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 24 (by decide)))

theorem fz2_86_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨25, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 25 (by decide)))

theorem fz2_86_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨26, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 26 (by decide)))

theorem fz2_86_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨27, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 27 (by decide)))

theorem fz2_86_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨28, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 28 (by decide)))

theorem fz2_86_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨29, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 29 (by decide)))

theorem fz2_86_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨30, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 30 (by decide)))

theorem fz2_86_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨31, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 31 (by decide)))

theorem fz2_86_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨32, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 32 (by decide)))

theorem fz2_86_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨33, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 33 (by decide)))

theorem fz2_86_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨34, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 34 (by decide)))

theorem fz2_86_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨35, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 35 (by decide)))

theorem fz2_86_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨36, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 36 (by decide)))

theorem fz2_86_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨37, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 37 (by decide)))

theorem fz2_86_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨38, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 38 (by decide)))

theorem fz2_86_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨39, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 39 (by decide)))

theorem fz2_86_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨40, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 40 (by decide)))

theorem fz2_86_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨41, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 41 (by decide)))

theorem fz2_86_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨42, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 42 (by decide)))

theorem fz2_86_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨43, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 43 (by decide)))

theorem fz2_86_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨44, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 44 (by decide)))

theorem fz2_86_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨45, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 45 (by decide)))

theorem fz2_86_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨46, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 46 (by decide)))

theorem fz2_86_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨47, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 47 (by decide)))

theorem fz2_86_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨48, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 48 (by decide)))

theorem fz2_86_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨49, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 49 (by decide)))

theorem fz2_86_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨50, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 50 (by decide)))

theorem fz2_86_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨51, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 51 (by decide)))

theorem fz2_86_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨52, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 52 (by decide)))

theorem fz2_86_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨53, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 53 (by decide)))

theorem fz2_86_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨55, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 55 (by decide)))

theorem fz2_86_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨56, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 56 (by decide)))

theorem fz2_86_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨57, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 57 (by decide)))

theorem fz2_86_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨58, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 58 (by decide)))

theorem fz2_86_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨59, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 59 (by decide)))

theorem fz2_86_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨60, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 60 (by decide)))

theorem fz2_86_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨61, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 61 (by decide)))

theorem fz2_86_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨62, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 62 (by decide)))

theorem fz2_86_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨63, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 63 (by decide)))

theorem fz2_86_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨64, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 64 (by decide)))

theorem fz2_86_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨65, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 65 (by decide)))

theorem fz2_86_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨66, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 66 (by decide)))

theorem fz2_86_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨67, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 67 (by decide)))

theorem fz2_86_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨68, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 68 (by decide)))

theorem fz2_86_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨69, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 69 (by decide)))

theorem fz2_86_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨70, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 70 (by decide)))

theorem fz2_86_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨71, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 71 (by decide)))

theorem fz2_86_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨72, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 72 (by decide)))

theorem fz2_86_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨73, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 73 (by decide)))

theorem fz2_86_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨74, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 74 (by decide)))

theorem fz2_86_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨75, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 75 (by decide)))

theorem fz2_86_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨76, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 76 (by decide)))

theorem fz2_86_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨77, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 77 (by decide)))

theorem fz2_86_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨78, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 78 (by decide)))

theorem fz2_86_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨79, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 79 (by decide)))

theorem fz2_86_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨80, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 80 (by decide)))

theorem fz2_86_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨81, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 81 (by decide)))

theorem fz2_86_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨82, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 82 (by decide)))

theorem fz2_86_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨83, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 83 (by decide)))

theorem fz2_86_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨84, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 84 (by decide)))

theorem fz2_86_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨85, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 85 (by decide)))

theorem fz2_86_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨87, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 87 (by decide)))

theorem fz2_86_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨88, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 88 (by decide)))

theorem fz2_86_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨89, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 89 (by decide)))

theorem fz2_86_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨90, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 90 (by decide)))

theorem fz2_86_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨91, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 91 (by decide)))

theorem fz2_86_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨92, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 92 (by decide)))

theorem fz2_86_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨93, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 93 (by decide)))

theorem fz2_86_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨94, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 94 (by decide)))

theorem fz2_86_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨95, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 95 (by decide)))

theorem fz2_86_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨96, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 96 (by decide)))

theorem fz2_86_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨97, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 97 (by decide)))

theorem fz2_86_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨98, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 98 (by decide)))

theorem fz2_86_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨99, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 99 (by decide)))

theorem fz2_86_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨100, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 100 (by decide)))

theorem fz2_86_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨101, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 101 (by decide)))

theorem fz2_86_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨102, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 102 (by decide)))

theorem fz2_86_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨103, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 103 (by decide)))

theorem fz2_86_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨104, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 104 (by decide)))

theorem fz2_86_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨105, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 105 (by decide)))

theorem fz2_86_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨106, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 106 (by decide)))

theorem fz2_86_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨107, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 107 (by decide)))

theorem fz2_86_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨108, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 108 (by decide)))

theorem fz2_86_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨109, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 109 (by decide)))

theorem fz2_86_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨110, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 110 (by decide)))

theorem fz2_86_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨111, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 111 (by decide)))

theorem fz2_86_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨112, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 112 (by decide)))

theorem fz2_86_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨113, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 113 (by decide)))

theorem fz2_86_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨114, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 114 (by decide)))

theorem fz2_86_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK86)) = 0 :=
  Q2.repsFixedCard2 rK86 ⟨115, by decide⟩ Q2.R86_2 Q2.hpxR86_2 Q2.hcardq86_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_86) 115 (by decide)))

end LeanDring.P5Presentation
