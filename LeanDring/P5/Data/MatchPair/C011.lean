/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.MatchLeaf.C047
import LeanDring.P5.Data.MatchLeaf.C048
import LeanDring.P5.Data.MatchLeaf.C049
import LeanDring.P5.Data.MatchLeaf.C050
import LeanDring.P5.Data.MatchLeaf.C051
import LeanDring.P5.Data.MatchLeaf.C052
import LeanDring.P5.Data.MatchLeaf.C053
import LeanDring.P5.Data.MatchLeaf.C054

/-! # Stage-5 per-pair theorems, chunk 10 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem pair_145_46 (p : Nat) (hp : p < (Q2.transData.getD 46 []).length)
    (hrep : (Q2.cosetIsRep.getD 46 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ p hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ p (transLenTr ⟨46, by decide⟩ p hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_46 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_46_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_46_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_46_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_46_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_46_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_46_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_46_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_46_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_46_20 hp j hj hq
  simp at hm

theorem pair_145_47 (p : Nat) (hp : p < (Q2.transData.getD 47 []).length)
    (hrep : (Q2.cosetIsRep.getD 47 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ p hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ p (transLenTr ⟨47, by decide⟩ p hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_47 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_47_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_47_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_47_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_47_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_47_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_47_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_47_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_47_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_47_20 hp j hj hq
  simp at hm

theorem pair_145_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_53_20 hp j hj hq
  simp at hm

theorem pair_145_54 (p : Nat) (hp : p < (Q2.transData.getD 54 []).length)
    (hrep : (Q2.cosetIsRep.getD 54 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ p hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ p (transLenTr ⟨54, by decide⟩ p hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_54 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_54_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_54_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_54_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_54_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_54_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_54_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_54_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_54_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_54_20 hp j hj hq
  simp at hm

theorem pair_145_105 (p : Nat) (hp : p < (Q2.transData.getD 105 []).length)
    (hrep : (Q2.cosetIsRep.getD 105 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ p hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ p (transLenTr ⟨105, by decide⟩ p hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_105 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_105_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_105_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_105_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_105_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_105_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_105_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_105_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_105_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_105_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_105_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_105_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_105_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_105_100 hp j hj hq
  simp at hm

theorem pair_145_106 (p : Nat) (hp : p < (Q2.transData.getD 106 []).length)
    (hrep : (Q2.cosetIsRep.getD 106 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ p hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ p (transLenTr ⟨106, by decide⟩ p hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_106 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_106_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_106_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_106_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_106_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_106_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_106_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_106_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_106_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_106_20 hp j hj hq
  simp at hm

theorem pair_145_107 (p : Nat) (hp : p < (Q2.transData.getD 107 []).length)
    (hrep : (Q2.cosetIsRep.getD 107 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ p hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ p (transLenTr ⟨107, by decide⟩ p hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_107 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_107_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_107_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_107_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_107_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_107_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_107_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_107_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_107_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_107_20 hp j hj hq
  simp at hm

theorem pair_145_108 (p : Nat) (hp : p < (Q2.transData.getD 108 []).length)
    (hrep : (Q2.cosetIsRep.getD 108 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ p hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ p (transLenTr ⟨108, by decide⟩ p hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_108 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_108_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_108_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_108_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_108_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_108_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_108_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_108_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_108_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_108_20 hp j hj hq
  simp at hm

theorem pair_145_109 (p : Nat) (hp : p < (Q2.transData.getD 109 []).length)
    (hrep : (Q2.cosetIsRep.getD 109 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ p hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ p (transLenTr ⟨109, by decide⟩ p hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_109 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_109_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_109_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_109_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_109_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_109_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_109_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_109_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_109_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_109_20 hp j hj hq
  simp at hm

theorem pair_145_115 (p : Nat) (hp : p < (Q2.transData.getD 115 []).length)
    (hrep : (Q2.cosetIsRep.getD 115 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ p hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ p (transLenTr ⟨115, by decide⟩ p hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_115 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_115_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_115_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_115_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_115_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_115_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_115_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_115_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_115_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_115_20 hp j hj hq
  simp at hm

theorem pair_145_145 (p : Nat) (hp : p < (Q2.transData.getD 145 []).length)
    (hrep : (Q2.cosetIsRep.getD 145 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ p hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ p (transLenTr ⟨145, by decide⟩ p hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_145 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_145_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_145_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_145_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_145_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_145_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_145_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_145_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_145_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_145_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_145_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_145_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_145_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_145_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_145_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_145_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_145_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_145_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_145_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_145_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_145_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_145_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_145_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_145_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_145_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_145_24 hp j hj hq
  simp at hm

theorem pair_146_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_10_4 hp j hj hq
  simp at hm

theorem pair_146_11 (p : Nat) (hp : p < (Q2.transData.getD 11 []).length)
    (hrep : (Q2.cosetIsRep.getD 11 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ p hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ p (transLenTr ⟨11, by decide⟩ p hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_11 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_11_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_11_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_11_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_11_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_11_4 hp j hj hq
  simp at hm

theorem pair_146_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_12_4 hp j hj hq
  simp at hm

theorem pair_146_48 (p : Nat) (hp : p < (Q2.transData.getD 48 []).length)
    (hrep : (Q2.cosetIsRep.getD 48 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ p hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ p (transLenTr ⟨48, by decide⟩ p hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_48 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_48_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_48_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_48_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_48_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_48_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_48_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_48_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_48_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_48_20 hp j hj hq
  simp at hm

theorem pair_146_49 (p : Nat) (hp : p < (Q2.transData.getD 49 []).length)
    (hrep : (Q2.cosetIsRep.getD 49 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ p hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ p (transLenTr ⟨49, by decide⟩ p hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_49 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_49_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_49_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_49_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_49_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_49_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_49_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_49_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_49_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_49_20 hp j hj hq
  simp at hm

theorem pair_146_50 (p : Nat) (hp : p < (Q2.transData.getD 50 []).length)
    (hrep : (Q2.cosetIsRep.getD 50 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ p hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ p (transLenTr ⟨50, by decide⟩ p hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_50 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_50_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_50_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_50_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_50_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_50_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_50_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_50_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_50_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_50_20 hp j hj hq
  simp at hm

theorem pair_146_51 (p : Nat) (hp : p < (Q2.transData.getD 51 []).length)
    (hrep : (Q2.cosetIsRep.getD 51 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ p hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ p (transLenTr ⟨51, by decide⟩ p hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_51 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_51_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_51_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_51_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_51_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_51_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_51_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_51_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_51_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_51_20 hp j hj hq
  simp at hm

theorem pair_146_52 (p : Nat) (hp : p < (Q2.transData.getD 52 []).length)
    (hrep : (Q2.cosetIsRep.getD 52 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ p hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ p (transLenTr ⟨52, by decide⟩ p hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_52 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_52_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_52_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_52_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_52_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_52_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_52_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_52_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_52_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_52_20 hp j hj hq
  simp at hm

theorem pair_146_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_53_20 hp j hj hq
  simp at hm

theorem pair_146_54 (p : Nat) (hp : p < (Q2.transData.getD 54 []).length)
    (hrep : (Q2.cosetIsRep.getD 54 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ p hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ p (transLenTr ⟨54, by decide⟩ p hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_54 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_54_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_54_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_54_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_54_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_54_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_54_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_54_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_54_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_54_20 hp j hj hq
  simp at hm

theorem pair_146_110 (p : Nat) (hp : p < (Q2.transData.getD 110 []).length)
    (hrep : (Q2.cosetIsRep.getD 110 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ p hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ p (transLenTr ⟨110, by decide⟩ p hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_110 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_110_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_110_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_110_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_110_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_110_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_110_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_110_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_110_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_110_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_110_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_110_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_110_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_110_100 hp j hj hq
  simp at hm

theorem pair_146_111 (p : Nat) (hp : p < (Q2.transData.getD 111 []).length)
    (hrep : (Q2.cosetIsRep.getD 111 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ p hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ p (transLenTr ⟨111, by decide⟩ p hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_111 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_111_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_111_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_111_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_111_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_111_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_111_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_111_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_111_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_111_20 hp j hj hq
  simp at hm

theorem pair_146_112 (p : Nat) (hp : p < (Q2.transData.getD 112 []).length)
    (hrep : (Q2.cosetIsRep.getD 112 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ p hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ p (transLenTr ⟨112, by decide⟩ p hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_112 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_112_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_112_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_112_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_112_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_112_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_112_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_112_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_112_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_112_20 hp j hj hq
  simp at hm

theorem pair_146_113 (p : Nat) (hp : p < (Q2.transData.getD 113 []).length)
    (hrep : (Q2.cosetIsRep.getD 113 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ p hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ p (transLenTr ⟨113, by decide⟩ p hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_113 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_113_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_113_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_113_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_113_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_113_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_113_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_113_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_113_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_113_20 hp j hj hq
  simp at hm

theorem pair_146_114 (p : Nat) (hp : p < (Q2.transData.getD 114 []).length)
    (hrep : (Q2.cosetIsRep.getD 114 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ p hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ p (transLenTr ⟨114, by decide⟩ p hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_114 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_114_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_114_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_114_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_114_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_114_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_114_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_114_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_114_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_114_20 hp j hj hq
  simp at hm

theorem pair_146_115 (p : Nat) (hp : p < (Q2.transData.getD 115 []).length)
    (hrep : (Q2.cosetIsRep.getD 115 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ p hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ p (transLenTr ⟨115, by decide⟩ p hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_115 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_115_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_115_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_115_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_115_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_115_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_115_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_115_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_115_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_115_20 hp j hj hq
  simp at hm

theorem pair_146_146 (p : Nat) (hp : p < (Q2.transData.getD 146 []).length)
    (hrep : (Q2.cosetIsRep.getD 146 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ p hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ p (transLenTr ⟨146, by decide⟩ p hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_146 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_146_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_146_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_146_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_146_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_146_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_146_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_146_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_146_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_146_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_146_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_146_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_146_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_146_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_146_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_146_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_146_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_146_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_146_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_146_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_146_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_146_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_146_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_146_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_146_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_146_146_24 hp j hj hq
  simp at hm

theorem pair_147_1 (p : Nat) (hp : p < (Q2.transData.getD 1 []).length)
    (hrep : (Q2.cosetIsRep.getD 1 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ p (transLenTr ⟨1, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_1 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_1_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_1_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_1_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_1_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_1_4 hp j hj hq
  simp at hm

theorem pair_147_2 (p : Nat) (hp : p < (Q2.transData.getD 2 []).length)
    (hrep : (Q2.cosetIsRep.getD 2 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ p (transLenTr ⟨2, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_2 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_2_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_2_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_2_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_2_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_2_4 hp j hj hq
  simp at hm

theorem pair_147_3 (p : Nat) (hp : p < (Q2.transData.getD 3 []).length)
    (hrep : (Q2.cosetIsRep.getD 3 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ p (transLenTr ⟨3, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_3 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_3_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_3_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_3_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_3_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_3_4 hp j hj hq
  simp at hm

theorem pair_147_4 (p : Nat) (hp : p < (Q2.transData.getD 4 []).length)
    (hrep : (Q2.cosetIsRep.getD 4 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ p (transLenTr ⟨4, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_4 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_4_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_4_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_4_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_4_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_4_4 hp j hj hq
  simp at hm

theorem pair_147_5 (p : Nat) (hp : p < (Q2.transData.getD 5 []).length)
    (hrep : (Q2.cosetIsRep.getD 5 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ p (transLenTr ⟨5, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_5 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_5_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_5_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_5_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_5_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_5_4 hp j hj hq
  simp at hm

theorem pair_147_6 (p : Nat) (hp : p < (Q2.transData.getD 6 []).length)
    (hrep : (Q2.cosetIsRep.getD 6 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ p (transLenTr ⟨6, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_6 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_6_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_6_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_6_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_6_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_6_4 hp j hj hq
  simp at hm

theorem pair_147_7 (p : Nat) (hp : p < (Q2.transData.getD 7 []).length)
    (hrep : (Q2.cosetIsRep.getD 7 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ p (transLenTr ⟨7, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_7 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_7_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_7_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_7_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_7_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_7_4 hp j hj hq
  simp at hm

theorem pair_147_8 (p : Nat) (hp : p < (Q2.transData.getD 8 []).length)
    (hrep : (Q2.cosetIsRep.getD 8 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ p (transLenTr ⟨8, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_8 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_8_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_8_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_8_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_8_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_8_4 hp j hj hq
  simp at hm

theorem pair_147_9 (p : Nat) (hp : p < (Q2.transData.getD 9 []).length)
    (hrep : (Q2.cosetIsRep.getD 9 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ p (transLenTr ⟨9, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_9 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_9_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_9_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_9_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_9_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_9_4 hp j hj hq
  simp at hm

theorem pair_147_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_10_4 hp j hj hq
  simp at hm

theorem pair_147_11 (p : Nat) (hp : p < (Q2.transData.getD 11 []).length)
    (hrep : (Q2.cosetIsRep.getD 11 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ p (transLenTr ⟨11, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_11 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_11_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_11_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_11_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_11_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_11_4 hp j hj hq
  simp at hm

theorem pair_147_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_12_4 hp j hj hq
  simp at hm

theorem pair_147_13 (p : Nat) (hp : p < (Q2.transData.getD 13 []).length)
    (hrep : (Q2.cosetIsRep.getD 13 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ p (transLenTr ⟨13, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_13 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_13_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_13_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_13_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_13_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_13_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_13_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_13_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_13_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_13_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_13_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_13_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_13_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_13_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_13_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_13_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_13_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_13_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_13_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_13_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_13_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_13_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_13_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_13_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_13_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_13_24 hp j hj hq
  simp at hm

theorem pair_147_14 (p : Nat) (hp : p < (Q2.transData.getD 14 []).length)
    (hrep : (Q2.cosetIsRep.getD 14 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ p (transLenTr ⟨14, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_14 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_14_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_14_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_14_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_14_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_14_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_14_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_14_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_14_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_14_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_14_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_14_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_14_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_14_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_14_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_14_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_14_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_14_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_14_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_14_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_14_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_14_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_14_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_14_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_14_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_14_24 hp j hj hq
  simp at hm

theorem pair_147_15 (p : Nat) (hp : p < (Q2.transData.getD 15 []).length)
    (hrep : (Q2.cosetIsRep.getD 15 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ p (transLenTr ⟨15, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_15 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_15_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_15_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_15_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_15_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_15_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_15_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_15_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_15_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_15_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_15_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_15_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_15_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_15_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_15_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_15_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_15_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_15_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_15_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_15_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_15_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_15_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_15_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_15_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_15_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_15_24 hp j hj hq
  simp at hm

theorem pair_147_16 (p : Nat) (hp : p < (Q2.transData.getD 16 []).length)
    (hrep : (Q2.cosetIsRep.getD 16 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ p (transLenTr ⟨16, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_16 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_16_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_16_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_16_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_16_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_16_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_16_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_16_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_16_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_16_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_16_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_16_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_16_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_16_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_16_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_16_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_16_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_16_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_16_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_16_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_16_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_16_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_16_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_16_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_16_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_16_24 hp j hj hq
  simp at hm

theorem pair_147_17 (p : Nat) (hp : p < (Q2.transData.getD 17 []).length)
    (hrep : (Q2.cosetIsRep.getD 17 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ p (transLenTr ⟨17, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_17 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_17_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_17_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_17_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_17_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_17_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_17_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_17_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_17_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_17_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_17_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_17_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_17_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_17_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_17_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_17_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_17_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_17_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_17_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_17_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_17_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_17_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_17_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_17_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_17_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_17_24 hp j hj hq
  simp at hm

theorem pair_147_18 (p : Nat) (hp : p < (Q2.transData.getD 18 []).length)
    (hrep : (Q2.cosetIsRep.getD 18 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ p (transLenTr ⟨18, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_18 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_18_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_18_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_18_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_18_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_18_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_18_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_18_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_18_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_18_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_18_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_18_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_18_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_18_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_18_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_18_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_18_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_18_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_18_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_18_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_18_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_18_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_18_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_18_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_18_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_18_24 hp j hj hq
  simp at hm

theorem pair_147_19 (p : Nat) (hp : p < (Q2.transData.getD 19 []).length)
    (hrep : (Q2.cosetIsRep.getD 19 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ p (transLenTr ⟨19, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_19 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_19_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_19_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_19_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_19_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_19_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_19_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_19_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_19_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_19_20 hp j hj hq
  simp at hm

theorem pair_147_20 (p : Nat) (hp : p < (Q2.transData.getD 20 []).length)
    (hrep : (Q2.cosetIsRep.getD 20 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ p (transLenTr ⟨20, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_20 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_20_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_20_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_20_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_20_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_20_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_20_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_20_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_20_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_20_20 hp j hj hq
  simp at hm

theorem pair_147_21 (p : Nat) (hp : p < (Q2.transData.getD 21 []).length)
    (hrep : (Q2.cosetIsRep.getD 21 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ p (transLenTr ⟨21, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_21 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_21_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_21_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_21_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_21_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_21_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_21_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_21_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_21_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_21_20 hp j hj hq
  simp at hm

theorem pair_147_22 (p : Nat) (hp : p < (Q2.transData.getD 22 []).length)
    (hrep : (Q2.cosetIsRep.getD 22 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ p (transLenTr ⟨22, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_22 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_22_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_22_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_22_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_22_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_22_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_22_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_22_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_22_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_22_20 hp j hj hq
  simp at hm

theorem pair_147_23 (p : Nat) (hp : p < (Q2.transData.getD 23 []).length)
    (hrep : (Q2.cosetIsRep.getD 23 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ p (transLenTr ⟨23, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_23 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_23_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_23_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_23_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_23_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_23_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_23_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_23_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_23_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_23_20 hp j hj hq
  simp at hm

theorem pair_147_24 (p : Nat) (hp : p < (Q2.transData.getD 24 []).length)
    (hrep : (Q2.cosetIsRep.getD 24 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ p (transLenTr ⟨24, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_24 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_24_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_24_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_24_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_24_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_24_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_24_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_24_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_24_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_24_20 hp j hj hq
  simp at hm

theorem pair_147_25 (p : Nat) (hp : p < (Q2.transData.getD 25 []).length)
    (hrep : (Q2.cosetIsRep.getD 25 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ p (transLenTr ⟨25, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_25 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_25_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_25_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_25_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_25_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_25_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_25_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_25_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_25_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_25_20 hp j hj hq
  simp at hm

theorem pair_147_26 (p : Nat) (hp : p < (Q2.transData.getD 26 []).length)
    (hrep : (Q2.cosetIsRep.getD 26 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ p (transLenTr ⟨26, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_26 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_26_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_26_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_26_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_26_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_26_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_26_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_26_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_26_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_26_20 hp j hj hq
  simp at hm

theorem pair_147_27 (p : Nat) (hp : p < (Q2.transData.getD 27 []).length)
    (hrep : (Q2.cosetIsRep.getD 27 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ p (transLenTr ⟨27, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_27 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_27_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_27_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_27_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_27_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_27_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_27_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_27_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_27_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_27_20 hp j hj hq
  simp at hm

theorem pair_147_28 (p : Nat) (hp : p < (Q2.transData.getD 28 []).length)
    (hrep : (Q2.cosetIsRep.getD 28 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ p (transLenTr ⟨28, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_28 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_28_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_28_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_28_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_28_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_28_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_28_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_28_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_28_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_28_20 hp j hj hq
  simp at hm

theorem pair_147_29 (p : Nat) (hp : p < (Q2.transData.getD 29 []).length)
    (hrep : (Q2.cosetIsRep.getD 29 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ p (transLenTr ⟨29, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_29 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_29_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_29_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_29_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_29_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_29_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_29_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_29_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_29_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_29_20 hp j hj hq
  simp at hm

theorem pair_147_30 (p : Nat) (hp : p < (Q2.transData.getD 30 []).length)
    (hrep : (Q2.cosetIsRep.getD 30 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ p (transLenTr ⟨30, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_30 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_30_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_30_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_30_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_30_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_30_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_30_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_30_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_30_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_30_20 hp j hj hq
  simp at hm

theorem pair_147_31 (p : Nat) (hp : p < (Q2.transData.getD 31 []).length)
    (hrep : (Q2.cosetIsRep.getD 31 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ p (transLenTr ⟨31, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_31 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_31_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_31_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_31_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_31_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_31_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_31_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_31_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_31_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_31_20 hp j hj hq
  simp at hm

theorem pair_147_32 (p : Nat) (hp : p < (Q2.transData.getD 32 []).length)
    (hrep : (Q2.cosetIsRep.getD 32 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ p (transLenTr ⟨32, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_32 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_32_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_32_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_32_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_32_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_32_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_32_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_32_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_32_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_32_20 hp j hj hq
  simp at hm

theorem pair_147_33 (p : Nat) (hp : p < (Q2.transData.getD 33 []).length)
    (hrep : (Q2.cosetIsRep.getD 33 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ p (transLenTr ⟨33, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_33 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_33_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_33_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_33_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_33_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_33_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_33_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_33_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_33_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_33_20 hp j hj hq
  simp at hm

theorem pair_147_34 (p : Nat) (hp : p < (Q2.transData.getD 34 []).length)
    (hrep : (Q2.cosetIsRep.getD 34 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ p (transLenTr ⟨34, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_34 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_34_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_34_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_34_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_34_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_34_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_34_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_34_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_34_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_34_20 hp j hj hq
  simp at hm

theorem pair_147_35 (p : Nat) (hp : p < (Q2.transData.getD 35 []).length)
    (hrep : (Q2.cosetIsRep.getD 35 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ p (transLenTr ⟨35, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_35 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_35_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_35_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_35_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_35_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_35_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_35_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_35_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_35_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_35_20 hp j hj hq
  simp at hm

theorem pair_147_36 (p : Nat) (hp : p < (Q2.transData.getD 36 []).length)
    (hrep : (Q2.cosetIsRep.getD 36 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ p (transLenTr ⟨36, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_36 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_36_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_36_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_36_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_36_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_36_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_36_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_36_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_36_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_36_20 hp j hj hq
  simp at hm

theorem pair_147_37 (p : Nat) (hp : p < (Q2.transData.getD 37 []).length)
    (hrep : (Q2.cosetIsRep.getD 37 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ p (transLenTr ⟨37, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_37 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_37_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_37_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_37_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_37_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_37_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_37_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_37_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_37_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_37_20 hp j hj hq
  simp at hm

theorem pair_147_38 (p : Nat) (hp : p < (Q2.transData.getD 38 []).length)
    (hrep : (Q2.cosetIsRep.getD 38 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ p (transLenTr ⟨38, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_38 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_38_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_38_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_38_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_38_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_38_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_38_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_38_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_38_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_38_20 hp j hj hq
  simp at hm

theorem pair_147_39 (p : Nat) (hp : p < (Q2.transData.getD 39 []).length)
    (hrep : (Q2.cosetIsRep.getD 39 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ p (transLenTr ⟨39, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_39 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_39_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_39_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_39_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_39_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_39_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_39_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_39_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_39_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_39_20 hp j hj hq
  simp at hm

theorem pair_147_40 (p : Nat) (hp : p < (Q2.transData.getD 40 []).length)
    (hrep : (Q2.cosetIsRep.getD 40 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ p (transLenTr ⟨40, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_40 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_40_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_40_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_40_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_40_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_40_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_40_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_40_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_40_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_40_20 hp j hj hq
  simp at hm

theorem pair_147_41 (p : Nat) (hp : p < (Q2.transData.getD 41 []).length)
    (hrep : (Q2.cosetIsRep.getD 41 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ p (transLenTr ⟨41, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_41 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_41_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_41_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_41_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_41_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_41_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_41_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_41_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_41_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_41_20 hp j hj hq
  simp at hm

theorem pair_147_42 (p : Nat) (hp : p < (Q2.transData.getD 42 []).length)
    (hrep : (Q2.cosetIsRep.getD 42 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ p (transLenTr ⟨42, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_42 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_42_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_42_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_42_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_42_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_42_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_42_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_42_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_42_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_42_20 hp j hj hq
  simp at hm

theorem pair_147_43 (p : Nat) (hp : p < (Q2.transData.getD 43 []).length)
    (hrep : (Q2.cosetIsRep.getD 43 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ p (transLenTr ⟨43, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_43 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_43_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_43_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_43_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_43_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_43_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_43_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_43_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_43_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_43_20 hp j hj hq
  simp at hm

theorem pair_147_44 (p : Nat) (hp : p < (Q2.transData.getD 44 []).length)
    (hrep : (Q2.cosetIsRep.getD 44 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ p (transLenTr ⟨44, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_44 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_44_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_44_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_44_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_44_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_44_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_44_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_44_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_44_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_44_20 hp j hj hq
  simp at hm

theorem pair_147_45 (p : Nat) (hp : p < (Q2.transData.getD 45 []).length)
    (hrep : (Q2.cosetIsRep.getD 45 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ p (transLenTr ⟨45, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_45 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_45_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_45_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_45_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_45_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_45_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_45_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_45_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_45_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_45_20 hp j hj hq
  simp at hm

theorem pair_147_46 (p : Nat) (hp : p < (Q2.transData.getD 46 []).length)
    (hrep : (Q2.cosetIsRep.getD 46 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ p (transLenTr ⟨46, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_46 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_46_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_46_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_46_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_46_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_46_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_46_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_46_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_46_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_46_20 hp j hj hq
  simp at hm

theorem pair_147_47 (p : Nat) (hp : p < (Q2.transData.getD 47 []).length)
    (hrep : (Q2.cosetIsRep.getD 47 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ p (transLenTr ⟨47, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_47 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_47_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_47_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_47_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_47_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_47_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_47_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_47_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_47_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_47_20 hp j hj hq
  simp at hm

theorem pair_147_48 (p : Nat) (hp : p < (Q2.transData.getD 48 []).length)
    (hrep : (Q2.cosetIsRep.getD 48 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ p (transLenTr ⟨48, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_48 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_48_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_48_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_48_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_48_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_48_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_48_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_48_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_48_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_48_20 hp j hj hq
  simp at hm

theorem pair_147_49 (p : Nat) (hp : p < (Q2.transData.getD 49 []).length)
    (hrep : (Q2.cosetIsRep.getD 49 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ p (transLenTr ⟨49, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_49 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_49_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_49_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_49_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_49_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_49_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_49_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_49_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_49_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_49_20 hp j hj hq
  simp at hm

theorem pair_147_50 (p : Nat) (hp : p < (Q2.transData.getD 50 []).length)
    (hrep : (Q2.cosetIsRep.getD 50 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ p (transLenTr ⟨50, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_50 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_50_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_50_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_50_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_50_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_50_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_50_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_50_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_50_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_50_20 hp j hj hq
  simp at hm

theorem pair_147_51 (p : Nat) (hp : p < (Q2.transData.getD 51 []).length)
    (hrep : (Q2.cosetIsRep.getD 51 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ p (transLenTr ⟨51, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_51 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_51_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_51_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_51_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_51_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_51_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_51_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_51_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_51_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_51_20 hp j hj hq
  simp at hm

theorem pair_147_52 (p : Nat) (hp : p < (Q2.transData.getD 52 []).length)
    (hrep : (Q2.cosetIsRep.getD 52 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ p (transLenTr ⟨52, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_52 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_52_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_52_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_52_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_52_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_52_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_52_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_52_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_52_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_52_20 hp j hj hq
  simp at hm

theorem pair_147_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_53_20 hp j hj hq
  simp at hm

theorem pair_147_54 (p : Nat) (hp : p < (Q2.transData.getD 54 []).length)
    (hrep : (Q2.cosetIsRep.getD 54 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ p (transLenTr ⟨54, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_54 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_54_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_54_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_54_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_54_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_54_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_54_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_54_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_54_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_54_20 hp j hj hq
  simp at hm

theorem pair_147_55 (p : Nat) (hp : p < (Q2.transData.getD 55 []).length)
    (hrep : (Q2.cosetIsRep.getD 55 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ p (transLenTr ⟨55, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_55 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_55_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_55_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_55_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_55_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_55_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_55_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_55_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_55_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_55_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_55_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_55_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_55_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_55_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_55_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_55_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_55_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_55_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_55_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_55_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_55_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_55_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_55_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_55_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_55_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_55_24 hp j hj hq
  simp at hm

theorem pair_147_56 (p : Nat) (hp : p < (Q2.transData.getD 56 []).length)
    (hrep : (Q2.cosetIsRep.getD 56 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ p (transLenTr ⟨56, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_56 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_56_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_56_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_56_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_56_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_56_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_56_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_56_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_56_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_56_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_56_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_56_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_56_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_56_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_56_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_56_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_56_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_56_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_56_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_56_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_56_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_56_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_56_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_56_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_56_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_56_24 hp j hj hq
  simp at hm

theorem pair_147_57 (p : Nat) (hp : p < (Q2.transData.getD 57 []).length)
    (hrep : (Q2.cosetIsRep.getD 57 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ p (transLenTr ⟨57, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_57 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_57_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_57_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_57_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_57_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_57_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_57_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_57_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_57_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_57_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_57_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_57_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_57_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_57_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_57_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_57_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_57_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_57_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_57_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_57_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_57_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_57_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_57_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_57_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_57_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_57_24 hp j hj hq
  simp at hm

theorem pair_147_58 (p : Nat) (hp : p < (Q2.transData.getD 58 []).length)
    (hrep : (Q2.cosetIsRep.getD 58 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ p (transLenTr ⟨58, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_58 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_58_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_58_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_58_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_58_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_58_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_58_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_58_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_58_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_58_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_58_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_58_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_58_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_58_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_58_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_58_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_58_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_58_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_58_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_58_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_58_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_58_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_58_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_58_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_58_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_58_24 hp j hj hq
  simp at hm

theorem pair_147_59 (p : Nat) (hp : p < (Q2.transData.getD 59 []).length)
    (hrep : (Q2.cosetIsRep.getD 59 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ p (transLenTr ⟨59, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_59 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_59_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_59_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_59_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_59_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_59_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_59_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_59_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_59_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_59_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_59_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_59_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_59_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_59_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_59_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_59_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_59_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_59_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_59_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_59_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_59_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_59_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_59_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_59_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_59_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_59_24 hp j hj hq
  simp at hm

theorem pair_147_60 (p : Nat) (hp : p < (Q2.transData.getD 60 []).length)
    (hrep : (Q2.cosetIsRep.getD 60 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ p (transLenTr ⟨60, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_60 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_60_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_60_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_60_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_60_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_60_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_60_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_60_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_60_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_60_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_60_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_60_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_60_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_60_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_60_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_60_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_60_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_60_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_60_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_60_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_60_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_60_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_60_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_60_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_60_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_60_24 hp j hj hq
  simp at hm

theorem pair_147_61 (p : Nat) (hp : p < (Q2.transData.getD 61 []).length)
    (hrep : (Q2.cosetIsRep.getD 61 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ p (transLenTr ⟨61, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_61 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_61_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_61_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_61_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_61_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_61_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_61_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_61_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_61_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_61_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_61_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_61_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_61_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_61_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_61_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_61_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_61_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_61_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_61_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_61_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_61_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_61_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_61_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_61_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_61_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_61_24 hp j hj hq
  simp at hm

theorem pair_147_62 (p : Nat) (hp : p < (Q2.transData.getD 62 []).length)
    (hrep : (Q2.cosetIsRep.getD 62 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ p (transLenTr ⟨62, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_62 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_62_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_62_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_62_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_62_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_62_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_62_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_62_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_62_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_62_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_62_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_62_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_62_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_62_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_62_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_62_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_62_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_62_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_62_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_62_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_62_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_62_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_62_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_62_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_62_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_62_24 hp j hj hq
  simp at hm

theorem pair_147_63 (p : Nat) (hp : p < (Q2.transData.getD 63 []).length)
    (hrep : (Q2.cosetIsRep.getD 63 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ p (transLenTr ⟨63, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_63 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_63_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_63_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_63_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_63_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_63_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_63_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_63_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_63_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_63_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_63_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_63_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_63_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_63_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_63_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_63_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_63_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_63_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_63_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_63_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_63_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_63_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_63_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_63_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_63_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_63_24 hp j hj hq
  simp at hm

theorem pair_147_64 (p : Nat) (hp : p < (Q2.transData.getD 64 []).length)
    (hrep : (Q2.cosetIsRep.getD 64 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ p (transLenTr ⟨64, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_64 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_24 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_30 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_35 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_40 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_45 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_55 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_60 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_65 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_70 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_80 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_85 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_90 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_95 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_100 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_105 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_110 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_115 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_64_120 hp j hj hq
  simp at hm

theorem pair_147_65 (p : Nat) (hp : p < (Q2.transData.getD 65 []).length)
    (hrep : (Q2.cosetIsRep.getD 65 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ p (transLenTr ⟨65, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_65 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_65_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_65_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_65_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_65_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_65_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_65_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_65_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_65_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_65_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_65_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_65_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_65_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_65_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_65_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_65_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_65_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_65_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_65_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_65_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_65_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_65_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_65_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_65_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_65_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_65_24 hp j hj hq
  simp at hm

theorem pair_147_66 (p : Nat) (hp : p < (Q2.transData.getD 66 []).length)
    (hrep : (Q2.cosetIsRep.getD 66 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ p (transLenTr ⟨66, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_66 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_66_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_66_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_66_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_66_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_66_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_66_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_66_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_66_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_66_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_66_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_66_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_66_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_66_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_66_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_66_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_66_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_66_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_66_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_66_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_66_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_66_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_66_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_66_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_66_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_66_24 hp j hj hq
  simp at hm

theorem pair_147_67 (p : Nat) (hp : p < (Q2.transData.getD 67 []).length)
    (hrep : (Q2.cosetIsRep.getD 67 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ p (transLenTr ⟨67, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_67 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_24 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_30 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_35 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_40 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_45 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_55 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_60 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_65 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_70 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_80 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_85 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_90 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_95 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_100 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_105 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_110 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_115 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_67_120 hp j hj hq
  simp at hm

theorem pair_147_68 (p : Nat) (hp : p < (Q2.transData.getD 68 []).length)
    (hrep : (Q2.cosetIsRep.getD 68 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ p (transLenTr ⟨68, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_68 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_68_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_68_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_68_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_68_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_68_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_68_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_68_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_68_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_68_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_68_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_68_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_68_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_68_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_68_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_68_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_68_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_68_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_68_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_68_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_68_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_68_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_68_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_68_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_68_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_68_24 hp j hj hq
  simp at hm

theorem pair_147_69 (p : Nat) (hp : p < (Q2.transData.getD 69 []).length)
    (hrep : (Q2.cosetIsRep.getD 69 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ p (transLenTr ⟨69, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_69 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_69_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_69_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_69_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_69_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_69_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_69_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_69_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_69_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_69_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_69_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_69_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_69_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_69_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_69_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_69_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_69_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_69_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_69_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_69_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_69_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_69_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_69_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_69_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_69_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_69_24 hp j hj hq
  simp at hm

theorem pair_147_70 (p : Nat) (hp : p < (Q2.transData.getD 70 []).length)
    (hrep : (Q2.cosetIsRep.getD 70 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ p (transLenTr ⟨70, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_70 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_70_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_70_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_70_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_70_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_70_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_70_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_70_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_70_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_70_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_70_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_70_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_70_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_70_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_70_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_70_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_70_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_70_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_70_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_70_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_70_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_70_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_70_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_70_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_70_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_70_24 hp j hj hq
  simp at hm

theorem pair_147_71 (p : Nat) (hp : p < (Q2.transData.getD 71 []).length)
    (hrep : (Q2.cosetIsRep.getD 71 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ p (transLenTr ⟨71, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_71 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_71_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_71_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_71_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_71_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_71_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_71_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_71_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_71_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_71_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_71_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_71_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_71_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_71_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_71_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_71_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_71_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_71_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_71_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_71_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_71_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_71_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_71_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_71_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_71_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_71_24 hp j hj hq
  simp at hm

theorem pair_147_72 (p : Nat) (hp : p < (Q2.transData.getD 72 []).length)
    (hrep : (Q2.cosetIsRep.getD 72 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ p (transLenTr ⟨72, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_72 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_72_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_72_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_72_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_72_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_72_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_72_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_72_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_72_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_72_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_72_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_72_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_72_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_72_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_72_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_72_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_72_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_72_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_72_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_72_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_72_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_72_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_72_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_72_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_72_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_72_24 hp j hj hq
  simp at hm

theorem pair_147_73 (p : Nat) (hp : p < (Q2.transData.getD 73 []).length)
    (hrep : (Q2.cosetIsRep.getD 73 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ p (transLenTr ⟨73, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_73 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_24 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_30 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_35 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_40 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_45 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_55 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_60 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_65 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_70 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_80 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_85 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_90 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_95 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_100 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_105 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_110 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_115 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_73_120 hp j hj hq
  simp at hm

theorem pair_147_74 (p : Nat) (hp : p < (Q2.transData.getD 74 []).length)
    (hrep : (Q2.cosetIsRep.getD 74 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ p (transLenTr ⟨74, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_74 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_74_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_74_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_74_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_74_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_74_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_74_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_74_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_74_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_74_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_74_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_74_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_74_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_74_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_74_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_74_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_74_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_74_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_74_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_74_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_74_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_74_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_74_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_74_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_74_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_74_24 hp j hj hq
  simp at hm

theorem pair_147_75 (p : Nat) (hp : p < (Q2.transData.getD 75 []).length)
    (hrep : (Q2.cosetIsRep.getD 75 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ p (transLenTr ⟨75, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_75 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_75_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_75_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_75_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_75_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_75_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_75_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_75_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_75_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_75_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_75_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_75_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_75_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_75_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_75_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_75_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_75_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_75_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_75_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_75_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_75_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_75_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_75_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_75_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_75_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_75_24 hp j hj hq
  simp at hm

theorem pair_147_76 (p : Nat) (hp : p < (Q2.transData.getD 76 []).length)
    (hrep : (Q2.cosetIsRep.getD 76 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ p (transLenTr ⟨76, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_76 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_24 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_30 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_35 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_40 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_45 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_55 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_60 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_65 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_70 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_80 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_85 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_90 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_95 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_100 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_105 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_110 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_115 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_76_120 hp j hj hq
  simp at hm

theorem pair_147_77 (p : Nat) (hp : p < (Q2.transData.getD 77 []).length)
    (hrep : (Q2.cosetIsRep.getD 77 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ p (transLenTr ⟨77, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_77 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_77_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_77_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_77_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_77_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_77_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_77_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_77_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_77_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_77_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_77_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_77_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_77_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_77_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_77_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_77_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_77_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_77_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_77_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_77_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_77_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_77_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_77_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_77_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_77_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_77_24 hp j hj hq
  simp at hm

theorem pair_147_78 (p : Nat) (hp : p < (Q2.transData.getD 78 []).length)
    (hrep : (Q2.cosetIsRep.getD 78 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ p (transLenTr ⟨78, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_78 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_78_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_78_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_78_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_78_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_78_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_78_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_78_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_78_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_78_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_78_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_78_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_78_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_78_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_78_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_78_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_78_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_78_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_78_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_78_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_78_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_78_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_78_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_78_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_78_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_78_24 hp j hj hq
  simp at hm

theorem pair_147_79 (p : Nat) (hp : p < (Q2.transData.getD 79 []).length)
    (hrep : (Q2.cosetIsRep.getD 79 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ p (transLenTr ⟨79, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_79 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_79_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_79_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_79_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_79_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_79_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_79_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_79_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_79_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_79_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_79_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_79_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_79_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_79_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_79_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_79_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_79_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_79_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_79_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_79_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_79_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_79_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_79_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_79_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_79_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_79_24 hp j hj hq
  simp at hm

theorem pair_147_80 (p : Nat) (hp : p < (Q2.transData.getD 80 []).length)
    (hrep : (Q2.cosetIsRep.getD 80 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ p (transLenTr ⟨80, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_80 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_80_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_80_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_80_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_80_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_80_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_80_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_80_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_80_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_80_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_80_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_80_30 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_80_35 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_80_40 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_80_45 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_80_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_80_55 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_80_60 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_80_65 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_80_70 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_80_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_80_80 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_80_85 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_80_90 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_80_95 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_80_100 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_80_105 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_80_110 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_80_115 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_80_120 hp j hj hq
  simp at hm

theorem pair_147_81 (p : Nat) (hp : p < (Q2.transData.getD 81 []).length)
    (hrep : (Q2.cosetIsRep.getD 81 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ p (transLenTr ⟨81, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_81 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_81_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_81_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_81_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_81_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_81_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_81_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_81_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_81_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_81_20 hp j hj hq
  simp at hm

theorem pair_147_82 (p : Nat) (hp : p < (Q2.transData.getD 82 []).length)
    (hrep : (Q2.cosetIsRep.getD 82 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ p (transLenTr ⟨82, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_82 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_82_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_82_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_82_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_82_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_82_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_82_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_82_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_82_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_82_20 hp j hj hq
  simp at hm

theorem pair_147_83 (p : Nat) (hp : p < (Q2.transData.getD 83 []).length)
    (hrep : (Q2.cosetIsRep.getD 83 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ p (transLenTr ⟨83, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_83 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_83_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_83_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_83_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_83_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_83_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_83_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_83_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_83_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_83_20 hp j hj hq
  simp at hm

theorem pair_147_84 (p : Nat) (hp : p < (Q2.transData.getD 84 []).length)
    (hrep : (Q2.cosetIsRep.getD 84 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ p (transLenTr ⟨84, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_84 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_84_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_84_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_84_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_84_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_84_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_84_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_84_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_84_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_84_20 hp j hj hq
  simp at hm

theorem pair_147_85 (p : Nat) (hp : p < (Q2.transData.getD 85 []).length)
    (hrep : (Q2.cosetIsRep.getD 85 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ p (transLenTr ⟨85, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_85 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_24 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_30 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_35 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_40 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_45 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_55 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_60 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_65 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_70 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_80 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_85 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_90 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_95 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_100 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_105 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_110 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_115 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_85_120 hp j hj hq
  simp at hm

theorem pair_147_86 (p : Nat) (hp : p < (Q2.transData.getD 86 []).length)
    (hrep : (Q2.cosetIsRep.getD 86 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ p (transLenTr ⟨86, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_86 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_86_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_86_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_86_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_86_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_86_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_86_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_86_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_86_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_86_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_86_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_86_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_86_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_86_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_86_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_86_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_86_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_86_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_86_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_86_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_86_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_86_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_86_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_86_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_86_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_86_24 hp j hj hq
  simp at hm

theorem pair_147_87 (p : Nat) (hp : p < (Q2.transData.getD 87 []).length)
    (hrep : (Q2.cosetIsRep.getD 87 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ p (transLenTr ⟨87, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_87 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_87_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_87_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_87_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_87_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_87_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_87_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_87_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_87_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_87_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_87_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_87_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_87_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_87_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_87_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_87_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_87_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_87_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_87_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_87_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_87_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_87_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_87_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_87_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_87_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_87_24 hp j hj hq
  simp at hm

theorem pair_147_88 (p : Nat) (hp : p < (Q2.transData.getD 88 []).length)
    (hrep : (Q2.cosetIsRep.getD 88 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ p (transLenTr ⟨88, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_88 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_88_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_88_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_88_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_88_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_88_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_88_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_88_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_88_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_88_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_88_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_88_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_88_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_88_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_88_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_88_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_88_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_88_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_88_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_88_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_88_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_88_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_88_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_88_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_88_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_88_24 hp j hj hq
  simp at hm

theorem pair_147_89 (p : Nat) (hp : p < (Q2.transData.getD 89 []).length)
    (hrep : (Q2.cosetIsRep.getD 89 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ p (transLenTr ⟨89, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_89 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_89_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_89_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_89_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_89_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_89_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_89_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_89_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_89_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_89_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_89_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_89_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_89_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_89_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_89_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_89_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_89_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_89_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_89_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_89_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_89_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_89_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_89_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_89_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_89_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_89_24 hp j hj hq
  simp at hm

theorem pair_147_90 (p : Nat) (hp : p < (Q2.transData.getD 90 []).length)
    (hrep : (Q2.cosetIsRep.getD 90 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ p (transLenTr ⟨90, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_90 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_90_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_90_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_90_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_90_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_90_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_90_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_90_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_90_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_90_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_90_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_90_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_90_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_90_100 hp j hj hq
  simp at hm

theorem pair_147_91 (p : Nat) (hp : p < (Q2.transData.getD 91 []).length)
    (hrep : (Q2.cosetIsRep.getD 91 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ p (transLenTr ⟨91, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_91 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_91_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_91_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_91_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_91_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_91_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_91_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_91_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_91_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_91_20 hp j hj hq
  simp at hm

theorem pair_147_92 (p : Nat) (hp : p < (Q2.transData.getD 92 []).length)
    (hrep : (Q2.cosetIsRep.getD 92 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ p (transLenTr ⟨92, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_92 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_92_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_92_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_92_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_92_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_92_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_92_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_92_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_92_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_92_20 hp j hj hq
  simp at hm

end LeanDring.P5Presentation
