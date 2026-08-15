/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryK.C014

/-!
# Species-table cells, off-support emptiness certificates, chunk 54

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

theorem fixz1_55 : ([1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 29, 30, 31, 32, 34, 35, 36, 37, 39, 40, 41, 42, 44, 45, 46, 47, 49, 50, 51, 52, 53, 54, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK55) (retConj 1 (R55 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_55_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨1, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 1 (by decide)))

theorem fz1_55_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨2, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 2 (by decide)))

theorem fz1_55_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨3, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 3 (by decide)))

theorem fz1_55_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨4, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 4 (by decide)))

theorem fz1_55_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨5, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 5 (by decide)))

theorem fz1_55_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨6, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 6 (by decide)))

theorem fz1_55_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨7, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 7 (by decide)))

theorem fz1_55_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨8, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 8 (by decide)))

theorem fz1_55_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨10, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 10 (by decide)))

theorem fz1_55_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨11, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 11 (by decide)))

theorem fz1_55_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨13, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 13 (by decide)))

theorem fz1_55_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨14, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 14 (by decide)))

theorem fz1_55_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨15, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 15 (by decide)))

theorem fz1_55_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨16, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 16 (by decide)))

theorem fz1_55_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨17, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 17 (by decide)))

theorem fz1_55_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨18, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 18 (by decide)))

theorem fz1_55_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨19, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 19 (by decide)))

theorem fz1_55_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨20, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 20 (by decide)))

theorem fz1_55_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨21, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 21 (by decide)))

theorem fz1_55_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨22, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 22 (by decide)))

theorem fz1_55_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨23, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 23 (by decide)))

theorem fz1_55_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨24, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 24 (by decide)))

theorem fz1_55_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨25, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 25 (by decide)))

theorem fz1_55_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨26, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 26 (by decide)))

theorem fz1_55_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨29, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 29 (by decide)))

theorem fz1_55_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨30, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 30 (by decide)))

theorem fz1_55_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨31, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 31 (by decide)))

theorem fz1_55_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨32, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 32 (by decide)))

theorem fz1_55_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨34, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 34 (by decide)))

theorem fz1_55_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨35, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 35 (by decide)))

theorem fz1_55_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨36, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 36 (by decide)))

theorem fz1_55_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨37, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 37 (by decide)))

theorem fz1_55_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨39, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 39 (by decide)))

theorem fz1_55_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨40, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 40 (by decide)))

theorem fz1_55_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨41, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 41 (by decide)))

theorem fz1_55_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨42, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 42 (by decide)))

theorem fz1_55_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨44, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 44 (by decide)))

theorem fz1_55_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨45, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 45 (by decide)))

theorem fz1_55_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨46, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 46 (by decide)))

theorem fz1_55_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨47, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 47 (by decide)))

theorem fz1_55_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨49, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 49 (by decide)))

theorem fz1_55_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨50, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 50 (by decide)))

theorem fz1_55_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨51, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 51 (by decide)))

theorem fz1_55_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨52, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 52 (by decide)))

theorem fz1_55_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨53, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 53 (by decide)))

theorem fz1_55_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨54, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 54 (by decide)))

theorem fz1_55_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨56, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 56 (by decide)))

theorem fz1_55_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨57, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 57 (by decide)))

theorem fz1_55_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨58, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 58 (by decide)))

theorem fz1_55_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨59, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 59 (by decide)))

theorem fz1_55_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨60, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 60 (by decide)))

theorem fz1_55_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨61, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 61 (by decide)))

theorem fz1_55_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨62, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 62 (by decide)))

theorem fz1_55_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨63, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 63 (by decide)))

theorem fz1_55_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨64, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 64 (by decide)))

theorem fz1_55_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨65, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 65 (by decide)))

theorem fz1_55_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨66, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 66 (by decide)))

theorem fz1_55_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨67, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 67 (by decide)))

theorem fz1_55_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨68, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 68 (by decide)))

theorem fz1_55_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨69, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 69 (by decide)))

theorem fz1_55_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨70, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 70 (by decide)))

theorem fz1_55_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨71, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 71 (by decide)))

theorem fz1_55_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨72, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 72 (by decide)))

theorem fz1_55_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨73, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 73 (by decide)))

theorem fz1_55_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨74, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 74 (by decide)))

theorem fz1_55_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨75, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 75 (by decide)))

theorem fz1_55_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨76, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 76 (by decide)))

theorem fz1_55_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨77, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 77 (by decide)))

theorem fz1_55_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨78, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 78 (by decide)))

theorem fz1_55_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨79, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 79 (by decide)))

theorem fz1_55_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨80, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 80 (by decide)))

theorem fz1_55_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨81, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 81 (by decide)))

theorem fz1_55_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨82, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 82 (by decide)))

theorem fz1_55_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨83, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 83 (by decide)))

theorem fz1_55_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨84, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 84 (by decide)))

theorem fz1_55_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨85, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 85 (by decide)))

theorem fz1_55_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨86, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 86 (by decide)))

theorem fz1_55_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨87, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 87 (by decide)))

theorem fz1_55_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨88, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 88 (by decide)))

theorem fz1_55_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨89, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 89 (by decide)))

theorem fz1_55_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨90, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 90 (by decide)))

theorem fz1_55_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨91, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 91 (by decide)))

theorem fz1_55_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨92, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 92 (by decide)))

theorem fz1_55_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨93, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 93 (by decide)))

theorem fz1_55_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨94, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 94 (by decide)))

theorem fz1_55_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨95, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 95 (by decide)))

theorem fz1_55_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨96, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 96 (by decide)))

theorem fz1_55_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨97, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 97 (by decide)))

theorem fz1_55_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨98, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 98 (by decide)))

theorem fz1_55_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨99, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 99 (by decide)))

theorem fz1_55_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨100, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 100 (by decide)))

theorem fz1_55_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨101, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 101 (by decide)))

theorem fz1_55_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨102, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 102 (by decide)))

theorem fz1_55_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨103, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 103 (by decide)))

theorem fz1_55_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨104, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 104 (by decide)))

theorem fz1_55_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨105, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 105 (by decide)))

theorem fz1_55_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨106, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 106 (by decide)))

theorem fz1_55_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨107, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 107 (by decide)))

theorem fz1_55_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨108, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 108 (by decide)))

theorem fz1_55_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨109, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 109 (by decide)))

theorem fz1_55_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨110, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 110 (by decide)))

theorem fz1_55_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨111, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 111 (by decide)))

theorem fz1_55_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨112, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 112 (by decide)))

theorem fz1_55_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨113, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 113 (by decide)))

theorem fz1_55_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨114, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 114 (by decide)))

theorem fz1_55_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK55)) = 0 :=
  repsFixedCard rK55 ⟨115, by decide⟩ R55 hpxR55 hcardq55
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_55) 115 (by decide)))

theorem fixz2_55 : ([1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 29, 30, 31, 32, 34, 35, 36, 37, 39, 40, 41, 42, 44, 45, 46, 47, 49, 50, 51, 52, 53, 54, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK55) (retConj 2 (Q2.R55_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_55_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨1, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 1 (by decide)))

theorem fz2_55_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨2, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 2 (by decide)))

theorem fz2_55_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨3, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 3 (by decide)))

theorem fz2_55_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨4, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 4 (by decide)))

theorem fz2_55_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨5, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 5 (by decide)))

theorem fz2_55_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨6, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 6 (by decide)))

theorem fz2_55_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨7, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 7 (by decide)))

theorem fz2_55_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨8, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 8 (by decide)))

theorem fz2_55_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨10, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 10 (by decide)))

theorem fz2_55_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨11, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 11 (by decide)))

theorem fz2_55_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨13, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 13 (by decide)))

theorem fz2_55_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨14, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 14 (by decide)))

theorem fz2_55_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨15, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 15 (by decide)))

theorem fz2_55_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨16, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 16 (by decide)))

theorem fz2_55_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨17, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 17 (by decide)))

theorem fz2_55_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨18, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 18 (by decide)))

theorem fz2_55_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨19, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 19 (by decide)))

theorem fz2_55_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨20, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 20 (by decide)))

theorem fz2_55_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨21, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 21 (by decide)))

theorem fz2_55_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨22, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 22 (by decide)))

theorem fz2_55_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨23, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 23 (by decide)))

theorem fz2_55_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨24, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 24 (by decide)))

theorem fz2_55_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨25, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 25 (by decide)))

theorem fz2_55_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨26, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 26 (by decide)))

theorem fz2_55_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨29, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 29 (by decide)))

theorem fz2_55_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨30, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 30 (by decide)))

theorem fz2_55_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨31, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 31 (by decide)))

theorem fz2_55_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨32, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 32 (by decide)))

theorem fz2_55_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨34, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 34 (by decide)))

theorem fz2_55_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨35, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 35 (by decide)))

theorem fz2_55_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨36, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 36 (by decide)))

theorem fz2_55_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨37, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 37 (by decide)))

theorem fz2_55_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨39, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 39 (by decide)))

theorem fz2_55_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨40, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 40 (by decide)))

theorem fz2_55_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨41, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 41 (by decide)))

theorem fz2_55_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨42, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 42 (by decide)))

theorem fz2_55_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨44, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 44 (by decide)))

theorem fz2_55_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨45, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 45 (by decide)))

theorem fz2_55_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨46, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 46 (by decide)))

theorem fz2_55_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨47, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 47 (by decide)))

theorem fz2_55_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨49, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 49 (by decide)))

theorem fz2_55_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨50, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 50 (by decide)))

theorem fz2_55_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨51, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 51 (by decide)))

theorem fz2_55_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨52, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 52 (by decide)))

theorem fz2_55_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨53, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 53 (by decide)))

theorem fz2_55_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨54, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 54 (by decide)))

theorem fz2_55_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨56, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 56 (by decide)))

theorem fz2_55_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨57, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 57 (by decide)))

theorem fz2_55_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨58, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 58 (by decide)))

theorem fz2_55_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨59, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 59 (by decide)))

theorem fz2_55_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨60, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 60 (by decide)))

theorem fz2_55_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨61, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 61 (by decide)))

theorem fz2_55_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨62, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 62 (by decide)))

theorem fz2_55_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨63, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 63 (by decide)))

theorem fz2_55_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨64, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 64 (by decide)))

theorem fz2_55_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨65, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 65 (by decide)))

theorem fz2_55_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨66, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 66 (by decide)))

theorem fz2_55_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨67, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 67 (by decide)))

theorem fz2_55_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨68, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 68 (by decide)))

theorem fz2_55_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨69, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 69 (by decide)))

theorem fz2_55_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨70, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 70 (by decide)))

theorem fz2_55_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨71, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 71 (by decide)))

theorem fz2_55_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨72, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 72 (by decide)))

theorem fz2_55_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨73, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 73 (by decide)))

theorem fz2_55_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨74, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 74 (by decide)))

theorem fz2_55_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨75, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 75 (by decide)))

theorem fz2_55_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨76, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 76 (by decide)))

theorem fz2_55_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨77, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 77 (by decide)))

theorem fz2_55_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨78, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 78 (by decide)))

theorem fz2_55_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨79, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 79 (by decide)))

theorem fz2_55_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨80, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 80 (by decide)))

theorem fz2_55_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨81, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 81 (by decide)))

theorem fz2_55_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨82, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 82 (by decide)))

theorem fz2_55_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨83, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 83 (by decide)))

theorem fz2_55_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨84, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 84 (by decide)))

theorem fz2_55_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨85, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 85 (by decide)))

theorem fz2_55_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨86, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 86 (by decide)))

theorem fz2_55_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨87, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 87 (by decide)))

theorem fz2_55_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨88, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 88 (by decide)))

theorem fz2_55_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨89, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 89 (by decide)))

theorem fz2_55_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨90, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 90 (by decide)))

theorem fz2_55_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨91, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 91 (by decide)))

theorem fz2_55_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨92, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 92 (by decide)))

theorem fz2_55_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨93, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 93 (by decide)))

theorem fz2_55_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨94, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 94 (by decide)))

theorem fz2_55_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨95, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 95 (by decide)))

theorem fz2_55_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨96, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 96 (by decide)))

theorem fz2_55_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨97, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 97 (by decide)))

theorem fz2_55_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨98, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 98 (by decide)))

theorem fz2_55_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨99, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 99 (by decide)))

theorem fz2_55_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨100, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 100 (by decide)))

theorem fz2_55_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨101, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 101 (by decide)))

theorem fz2_55_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨102, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 102 (by decide)))

theorem fz2_55_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨103, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 103 (by decide)))

theorem fz2_55_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨104, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 104 (by decide)))

theorem fz2_55_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨105, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 105 (by decide)))

theorem fz2_55_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨106, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 106 (by decide)))

theorem fz2_55_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨107, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 107 (by decide)))

theorem fz2_55_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨108, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 108 (by decide)))

theorem fz2_55_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨109, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 109 (by decide)))

theorem fz2_55_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨110, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 110 (by decide)))

theorem fz2_55_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨111, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 111 (by decide)))

theorem fz2_55_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨112, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 112 (by decide)))

theorem fz2_55_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨113, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 113 (by decide)))

theorem fz2_55_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨114, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 114 (by decide)))

theorem fz2_55_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK55)) = 0 :=
  Q2.repsFixedCard2 rK55 ⟨115, by decide⟩ Q2.R55_2 Q2.hpxR55_2 Q2.hcardq55_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_55) 115 (by decide)))

theorem fixz1_56 : ([2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 20, 21, 22, 23, 24, 25, 26, 27, 29, 30, 31, 32, 34, 35, 36, 37, 39, 40, 41, 42, 44, 45, 46, 47, 49, 50, 51, 52, 53, 54, 55, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK56) (retConj 1 (R56 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_56_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨2, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 2 (by decide)))

theorem fz1_56_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨3, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 3 (by decide)))

theorem fz1_56_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨4, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 4 (by decide)))

theorem fz1_56_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨5, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 5 (by decide)))

theorem fz1_56_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨6, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 6 (by decide)))

theorem fz1_56_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨7, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 7 (by decide)))

theorem fz1_56_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨8, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 8 (by decide)))

theorem fz1_56_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨9, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 9 (by decide)))

theorem fz1_56_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨10, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 10 (by decide)))

theorem fz1_56_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨11, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 11 (by decide)))

theorem fz1_56_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨13, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 13 (by decide)))

theorem fz1_56_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨14, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 14 (by decide)))

theorem fz1_56_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨15, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 15 (by decide)))

theorem fz1_56_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨16, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 16 (by decide)))

theorem fz1_56_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨17, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 17 (by decide)))

theorem fz1_56_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨18, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 18 (by decide)))

theorem fz1_56_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨20, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 20 (by decide)))

theorem fz1_56_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨21, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 21 (by decide)))

theorem fz1_56_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨22, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 22 (by decide)))

theorem fz1_56_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨23, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 23 (by decide)))

theorem fz1_56_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨24, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 24 (by decide)))

theorem fz1_56_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨25, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 25 (by decide)))

theorem fz1_56_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨26, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 26 (by decide)))

theorem fz1_56_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨27, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 27 (by decide)))

theorem fz1_56_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨29, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 29 (by decide)))

theorem fz1_56_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨30, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 30 (by decide)))

theorem fz1_56_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨31, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 31 (by decide)))

theorem fz1_56_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨32, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 32 (by decide)))

theorem fz1_56_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨34, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 34 (by decide)))

theorem fz1_56_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨35, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 35 (by decide)))

theorem fz1_56_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨36, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 36 (by decide)))

theorem fz1_56_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨37, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 37 (by decide)))

theorem fz1_56_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨39, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 39 (by decide)))

theorem fz1_56_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨40, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 40 (by decide)))

theorem fz1_56_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨41, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 41 (by decide)))

theorem fz1_56_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨42, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 42 (by decide)))

theorem fz1_56_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨44, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 44 (by decide)))

theorem fz1_56_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨45, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 45 (by decide)))

theorem fz1_56_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨46, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 46 (by decide)))

theorem fz1_56_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨47, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 47 (by decide)))

theorem fz1_56_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨49, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 49 (by decide)))

theorem fz1_56_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨50, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 50 (by decide)))

theorem fz1_56_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨51, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 51 (by decide)))

theorem fz1_56_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨52, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 52 (by decide)))

theorem fz1_56_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨53, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 53 (by decide)))

theorem fz1_56_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨54, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 54 (by decide)))

theorem fz1_56_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨55, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 55 (by decide)))

theorem fz1_56_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨57, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 57 (by decide)))

theorem fz1_56_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨58, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 58 (by decide)))

theorem fz1_56_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨59, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 59 (by decide)))

theorem fz1_56_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨60, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 60 (by decide)))

theorem fz1_56_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨61, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 61 (by decide)))

theorem fz1_56_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨62, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 62 (by decide)))

theorem fz1_56_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨63, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 63 (by decide)))

theorem fz1_56_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨64, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 64 (by decide)))

theorem fz1_56_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨65, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 65 (by decide)))

theorem fz1_56_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨66, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 66 (by decide)))

theorem fz1_56_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨67, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 67 (by decide)))

theorem fz1_56_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨68, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 68 (by decide)))

theorem fz1_56_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨69, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 69 (by decide)))

theorem fz1_56_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨70, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 70 (by decide)))

theorem fz1_56_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨71, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 71 (by decide)))

theorem fz1_56_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨72, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 72 (by decide)))

theorem fz1_56_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨73, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 73 (by decide)))

theorem fz1_56_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨74, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 74 (by decide)))

theorem fz1_56_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨75, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 75 (by decide)))

theorem fz1_56_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨76, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 76 (by decide)))

theorem fz1_56_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨77, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 77 (by decide)))

theorem fz1_56_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨78, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 78 (by decide)))

theorem fz1_56_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨79, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 79 (by decide)))

theorem fz1_56_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨80, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 80 (by decide)))

theorem fz1_56_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨81, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 81 (by decide)))

theorem fz1_56_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨82, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 82 (by decide)))

theorem fz1_56_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨83, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 83 (by decide)))

theorem fz1_56_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨84, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 84 (by decide)))

theorem fz1_56_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨85, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 85 (by decide)))

theorem fz1_56_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨86, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 86 (by decide)))

theorem fz1_56_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨87, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 87 (by decide)))

theorem fz1_56_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨88, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 88 (by decide)))

theorem fz1_56_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨89, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 89 (by decide)))

theorem fz1_56_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨90, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 90 (by decide)))

theorem fz1_56_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨91, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 91 (by decide)))

theorem fz1_56_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨92, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 92 (by decide)))

theorem fz1_56_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨93, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 93 (by decide)))

theorem fz1_56_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨94, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 94 (by decide)))

theorem fz1_56_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨95, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 95 (by decide)))

theorem fz1_56_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨96, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 96 (by decide)))

theorem fz1_56_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨97, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 97 (by decide)))

theorem fz1_56_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨98, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 98 (by decide)))

theorem fz1_56_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨99, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 99 (by decide)))

theorem fz1_56_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨100, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 100 (by decide)))

theorem fz1_56_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨101, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 101 (by decide)))

theorem fz1_56_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨102, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 102 (by decide)))

theorem fz1_56_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨103, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 103 (by decide)))

theorem fz1_56_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨104, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 104 (by decide)))

theorem fz1_56_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨105, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 105 (by decide)))

theorem fz1_56_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨106, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 106 (by decide)))

theorem fz1_56_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨107, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 107 (by decide)))

theorem fz1_56_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨108, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 108 (by decide)))

theorem fz1_56_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨109, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 109 (by decide)))

theorem fz1_56_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨110, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 110 (by decide)))

theorem fz1_56_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨111, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 111 (by decide)))

theorem fz1_56_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨112, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 112 (by decide)))

theorem fz1_56_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨113, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 113 (by decide)))

theorem fz1_56_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨114, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 114 (by decide)))

theorem fz1_56_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK56)) = 0 :=
  repsFixedCard rK56 ⟨115, by decide⟩ R56 hpxR56 hcardq56
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_56) 115 (by decide)))

theorem fixz2_56 : ([2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 20, 21, 22, 23, 24, 25, 26, 27, 29, 30, 31, 32, 34, 35, 36, 37, 39, 40, 41, 42, 44, 45, 46, 47, 49, 50, 51, 52, 53, 54, 55, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK56) (retConj 2 (Q2.R56_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_56_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨2, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 2 (by decide)))

theorem fz2_56_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨3, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 3 (by decide)))

theorem fz2_56_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨4, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 4 (by decide)))

theorem fz2_56_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨5, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 5 (by decide)))

theorem fz2_56_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨6, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 6 (by decide)))

theorem fz2_56_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨7, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 7 (by decide)))

theorem fz2_56_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨8, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 8 (by decide)))

theorem fz2_56_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨9, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 9 (by decide)))

theorem fz2_56_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨10, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 10 (by decide)))

theorem fz2_56_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨11, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 11 (by decide)))

theorem fz2_56_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨13, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 13 (by decide)))

theorem fz2_56_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨14, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 14 (by decide)))

theorem fz2_56_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨15, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 15 (by decide)))

theorem fz2_56_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨16, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 16 (by decide)))

theorem fz2_56_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨17, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 17 (by decide)))

theorem fz2_56_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨18, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 18 (by decide)))

theorem fz2_56_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨20, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 20 (by decide)))

theorem fz2_56_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨21, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 21 (by decide)))

theorem fz2_56_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨22, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 22 (by decide)))

theorem fz2_56_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨23, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 23 (by decide)))

theorem fz2_56_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨24, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 24 (by decide)))

theorem fz2_56_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨25, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 25 (by decide)))

theorem fz2_56_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨26, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 26 (by decide)))

theorem fz2_56_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨27, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 27 (by decide)))

theorem fz2_56_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨29, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 29 (by decide)))

theorem fz2_56_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨30, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 30 (by decide)))

theorem fz2_56_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨31, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 31 (by decide)))

theorem fz2_56_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨32, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 32 (by decide)))

theorem fz2_56_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨34, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 34 (by decide)))

theorem fz2_56_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨35, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 35 (by decide)))

theorem fz2_56_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨36, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 36 (by decide)))

theorem fz2_56_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨37, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 37 (by decide)))

theorem fz2_56_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨39, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 39 (by decide)))

theorem fz2_56_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨40, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 40 (by decide)))

theorem fz2_56_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨41, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 41 (by decide)))

theorem fz2_56_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨42, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 42 (by decide)))

theorem fz2_56_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨44, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 44 (by decide)))

theorem fz2_56_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨45, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 45 (by decide)))

theorem fz2_56_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨46, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 46 (by decide)))

theorem fz2_56_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨47, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 47 (by decide)))

theorem fz2_56_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨49, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 49 (by decide)))

theorem fz2_56_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨50, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 50 (by decide)))

theorem fz2_56_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨51, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 51 (by decide)))

theorem fz2_56_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨52, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 52 (by decide)))

theorem fz2_56_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨53, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 53 (by decide)))

theorem fz2_56_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨54, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 54 (by decide)))

theorem fz2_56_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨55, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 55 (by decide)))

theorem fz2_56_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨57, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 57 (by decide)))

theorem fz2_56_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨58, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 58 (by decide)))

theorem fz2_56_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨59, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 59 (by decide)))

theorem fz2_56_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨60, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 60 (by decide)))

theorem fz2_56_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨61, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 61 (by decide)))

theorem fz2_56_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨62, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 62 (by decide)))

theorem fz2_56_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨63, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 63 (by decide)))

theorem fz2_56_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨64, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 64 (by decide)))

theorem fz2_56_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨65, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 65 (by decide)))

theorem fz2_56_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨66, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 66 (by decide)))

theorem fz2_56_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨67, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 67 (by decide)))

theorem fz2_56_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨68, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 68 (by decide)))

theorem fz2_56_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨69, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 69 (by decide)))

theorem fz2_56_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨70, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 70 (by decide)))

theorem fz2_56_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨71, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 71 (by decide)))

theorem fz2_56_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨72, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 72 (by decide)))

theorem fz2_56_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨73, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 73 (by decide)))

theorem fz2_56_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨74, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 74 (by decide)))

theorem fz2_56_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨75, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 75 (by decide)))

theorem fz2_56_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨76, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 76 (by decide)))

theorem fz2_56_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨77, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 77 (by decide)))

theorem fz2_56_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨78, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 78 (by decide)))

theorem fz2_56_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨79, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 79 (by decide)))

theorem fz2_56_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨80, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 80 (by decide)))

theorem fz2_56_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨81, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 81 (by decide)))

theorem fz2_56_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨82, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 82 (by decide)))

theorem fz2_56_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨83, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 83 (by decide)))

theorem fz2_56_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨84, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 84 (by decide)))

theorem fz2_56_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨85, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 85 (by decide)))

theorem fz2_56_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨86, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 86 (by decide)))

theorem fz2_56_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨87, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 87 (by decide)))

theorem fz2_56_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨88, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 88 (by decide)))

theorem fz2_56_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨89, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 89 (by decide)))

theorem fz2_56_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨90, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 90 (by decide)))

theorem fz2_56_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨91, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 91 (by decide)))

theorem fz2_56_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨92, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 92 (by decide)))

theorem fz2_56_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨93, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 93 (by decide)))

theorem fz2_56_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨94, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 94 (by decide)))

theorem fz2_56_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨95, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 95 (by decide)))

theorem fz2_56_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨96, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 96 (by decide)))

theorem fz2_56_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨97, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 97 (by decide)))

theorem fz2_56_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨98, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 98 (by decide)))

theorem fz2_56_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨99, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 99 (by decide)))

theorem fz2_56_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨100, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 100 (by decide)))

theorem fz2_56_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨101, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 101 (by decide)))

theorem fz2_56_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨102, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 102 (by decide)))

theorem fz2_56_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨103, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 103 (by decide)))

theorem fz2_56_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨104, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 104 (by decide)))

theorem fz2_56_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨105, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 105 (by decide)))

theorem fz2_56_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨106, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 106 (by decide)))

theorem fz2_56_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨107, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 107 (by decide)))

theorem fz2_56_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨108, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 108 (by decide)))

theorem fz2_56_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨109, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 109 (by decide)))

theorem fz2_56_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨110, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 110 (by decide)))

theorem fz2_56_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨111, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 111 (by decide)))

theorem fz2_56_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨112, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 112 (by decide)))

theorem fz2_56_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨113, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 113 (by decide)))

theorem fz2_56_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨114, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 114 (by decide)))

theorem fz2_56_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK56)) = 0 :=
  Q2.repsFixedCard2 rK56 ⟨115, by decide⟩ Q2.R56_2 Q2.hpxR56_2 Q2.hcardq56_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_56) 115 (by decide)))

end LeanDring.P5Presentation
