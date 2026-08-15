/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryK.C012

/-!
# Species-table cells, off-support emptiness certificates, chunk 10

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

theorem fixz1_11 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 625 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK11) (retConj 1 (R11 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_11_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK11)) = 0 :=
  repsFixedCard rK11 ⟨1, by decide⟩ R11 hpxR11 hcardq11
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_11) 1 (by decide)))

theorem fz1_11_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK11)) = 0 :=
  repsFixedCard rK11 ⟨2, by decide⟩ R11 hpxR11 hcardq11
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_11) 2 (by decide)))

theorem fz1_11_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK11)) = 0 :=
  repsFixedCard rK11 ⟨3, by decide⟩ R11 hpxR11 hcardq11
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_11) 3 (by decide)))

theorem fz1_11_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK11)) = 0 :=
  repsFixedCard rK11 ⟨4, by decide⟩ R11 hpxR11 hcardq11
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_11) 4 (by decide)))

theorem fz1_11_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK11)) = 0 :=
  repsFixedCard rK11 ⟨5, by decide⟩ R11 hpxR11 hcardq11
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_11) 5 (by decide)))

theorem fz1_11_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK11)) = 0 :=
  repsFixedCard rK11 ⟨6, by decide⟩ R11 hpxR11 hcardq11
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_11) 6 (by decide)))

theorem fz1_11_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK11)) = 0 :=
  repsFixedCard rK11 ⟨7, by decide⟩ R11 hpxR11 hcardq11
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_11) 7 (by decide)))

theorem fz1_11_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK11)) = 0 :=
  repsFixedCard rK11 ⟨8, by decide⟩ R11 hpxR11 hcardq11
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_11) 8 (by decide)))

theorem fz1_11_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK11)) = 0 :=
  repsFixedCard rK11 ⟨9, by decide⟩ R11 hpxR11 hcardq11
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_11) 9 (by decide)))

theorem fz1_11_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK11)) = 0 :=
  repsFixedCard rK11 ⟨10, by decide⟩ R11 hpxR11 hcardq11
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_11) 10 (by decide)))

theorem fz1_11_12 : Fintype.card
    (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK11)) = 0 :=
  repsFixedCard rK11 ⟨12, by decide⟩ R11 hpxR11 hcardq11
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_11) 12 (by decide)))

theorem fixz2_11 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 625 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK11) (retConj 2 (Q2.R11_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_11_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK11)) = 0 :=
  Q2.repsFixedCard2 rK11 ⟨1, by decide⟩ Q2.R11_2 Q2.hpxR11_2 Q2.hcardq11_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_11) 1 (by decide)))

theorem fz2_11_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK11)) = 0 :=
  Q2.repsFixedCard2 rK11 ⟨2, by decide⟩ Q2.R11_2 Q2.hpxR11_2 Q2.hcardq11_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_11) 2 (by decide)))

theorem fz2_11_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK11)) = 0 :=
  Q2.repsFixedCard2 rK11 ⟨3, by decide⟩ Q2.R11_2 Q2.hpxR11_2 Q2.hcardq11_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_11) 3 (by decide)))

theorem fz2_11_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK11)) = 0 :=
  Q2.repsFixedCard2 rK11 ⟨4, by decide⟩ Q2.R11_2 Q2.hpxR11_2 Q2.hcardq11_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_11) 4 (by decide)))

theorem fz2_11_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK11)) = 0 :=
  Q2.repsFixedCard2 rK11 ⟨5, by decide⟩ Q2.R11_2 Q2.hpxR11_2 Q2.hcardq11_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_11) 5 (by decide)))

theorem fz2_11_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK11)) = 0 :=
  Q2.repsFixedCard2 rK11 ⟨6, by decide⟩ Q2.R11_2 Q2.hpxR11_2 Q2.hcardq11_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_11) 6 (by decide)))

theorem fz2_11_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK11)) = 0 :=
  Q2.repsFixedCard2 rK11 ⟨7, by decide⟩ Q2.R11_2 Q2.hpxR11_2 Q2.hcardq11_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_11) 7 (by decide)))

theorem fz2_11_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK11)) = 0 :=
  Q2.repsFixedCard2 rK11 ⟨8, by decide⟩ Q2.R11_2 Q2.hpxR11_2 Q2.hcardq11_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_11) 8 (by decide)))

theorem fz2_11_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK11)) = 0 :=
  Q2.repsFixedCard2 rK11 ⟨9, by decide⟩ Q2.R11_2 Q2.hpxR11_2 Q2.hcardq11_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_11) 9 (by decide)))

theorem fz2_11_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK11)) = 0 :=
  Q2.repsFixedCard2 rK11 ⟨10, by decide⟩ Q2.R11_2 Q2.hpxR11_2 Q2.hcardq11_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_11) 10 (by decide)))

theorem fz2_11_12 : Fintype.card
    (fixedPoints (Q2.reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK11)) = 0 :=
  Q2.repsFixedCard2 rK11 ⟨12, by decide⟩ Q2.R11_2 Q2.hpxR11_2 Q2.hcardq11_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_11) 12 (by decide)))

end LeanDring.P5Presentation
