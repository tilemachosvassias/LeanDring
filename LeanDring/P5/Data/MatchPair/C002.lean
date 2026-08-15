/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.MatchLeaf.C004
import LeanDring.P5.Data.MatchLeaf.C005
import LeanDring.P5.Data.MatchLeaf.C006
import LeanDring.P5.Data.MatchLeaf.C007
import LeanDring.P5.Data.MatchLeaf.C008

/-! # Stage-5 per-pair theorems, chunk 1 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem pair_47_47 (p : Nat) (hp : p < (Q2.transData.getD 47 []).length)
    (hrep : (Q2.cosetIsRep.getD 47 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 47 []).length)
    (hq : (normIsRep.getD 47 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ p hp)
        (rowE2 (⟨47, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ p (transLenTr ⟨47, by decide⟩ p hp))
        (rowE1 (⟨47, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_47 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_47_47_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_47_47_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_47_47_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_47_47_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_47_47_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_47_47_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_47_47_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_47_47_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_47_47_20 hp j hj hq
  simp at hm

theorem pair_48_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 48 []).length)
    (hq : (normIsRep.getD 48 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨48, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨48, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_48_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_48_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_48_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_48_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_48_12_4 hp j hj hq
  simp at hm

theorem pair_48_48 (p : Nat) (hp : p < (Q2.transData.getD 48 []).length)
    (hrep : (Q2.cosetIsRep.getD 48 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 48 []).length)
    (hq : (normIsRep.getD 48 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ p hp)
        (rowE2 (⟨48, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ p (transLenTr ⟨48, by decide⟩ p hp))
        (rowE1 (⟨48, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_48 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_48_48_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_48_48_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_48_48_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_48_48_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_48_48_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_48_48_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_48_48_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_48_48_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_48_48_20 hp j hj hq
  simp at hm

theorem pair_49_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 49 []).length)
    (hq : (normIsRep.getD 49 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨49, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨49, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_49_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_49_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_49_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_49_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_49_12_4 hp j hj hq
  simp at hm

theorem pair_49_49 (p : Nat) (hp : p < (Q2.transData.getD 49 []).length)
    (hrep : (Q2.cosetIsRep.getD 49 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 49 []).length)
    (hq : (normIsRep.getD 49 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ p hp)
        (rowE2 (⟨49, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ p (transLenTr ⟨49, by decide⟩ p hp))
        (rowE1 (⟨49, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_49 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_49_49_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_49_49_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_49_49_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_49_49_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_49_49_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_49_49_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_49_49_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_49_49_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_49_49_20 hp j hj hq
  simp at hm

theorem pair_50_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 50 []).length)
    (hq : (normIsRep.getD 50 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨50, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨50, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_50_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_50_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_50_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_50_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_50_12_4 hp j hj hq
  simp at hm

theorem pair_50_50 (p : Nat) (hp : p < (Q2.transData.getD 50 []).length)
    (hrep : (Q2.cosetIsRep.getD 50 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 50 []).length)
    (hq : (normIsRep.getD 50 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ p hp)
        (rowE2 (⟨50, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ p (transLenTr ⟨50, by decide⟩ p hp))
        (rowE1 (⟨50, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_50 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_50_50_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_50_50_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_50_50_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_50_50_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_50_50_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_50_50_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_50_50_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_50_50_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_50_50_20 hp j hj hq
  simp at hm

theorem pair_51_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 51 []).length)
    (hq : (normIsRep.getD 51 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨51, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨51, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_51_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_51_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_51_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_51_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_51_12_4 hp j hj hq
  simp at hm

theorem pair_51_51 (p : Nat) (hp : p < (Q2.transData.getD 51 []).length)
    (hrep : (Q2.cosetIsRep.getD 51 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 51 []).length)
    (hq : (normIsRep.getD 51 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ p hp)
        (rowE2 (⟨51, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ p (transLenTr ⟨51, by decide⟩ p hp))
        (rowE1 (⟨51, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_51 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_51_51_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_51_51_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_51_51_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_51_51_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_51_51_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_51_51_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_51_51_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_51_51_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_51_51_20 hp j hj hq
  simp at hm

theorem pair_52_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 52 []).length)
    (hq : (normIsRep.getD 52 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨52, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨52, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_52_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_52_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_52_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_52_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_52_12_4 hp j hj hq
  simp at hm

theorem pair_52_52 (p : Nat) (hp : p < (Q2.transData.getD 52 []).length)
    (hrep : (Q2.cosetIsRep.getD 52 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 52 []).length)
    (hq : (normIsRep.getD 52 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ p hp)
        (rowE2 (⟨52, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ p (transLenTr ⟨52, by decide⟩ p hp))
        (rowE1 (⟨52, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_52 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_52_52_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_52_52_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_52_52_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_52_52_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_52_52_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_52_52_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_52_52_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_52_52_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_52_52_20 hp j hj hq
  simp at hm

theorem pair_53_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 53 []).length)
    (hq : (normIsRep.getD 53 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨53, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨53, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_53_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_53_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_53_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_53_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_53_10_4 hp j hj hq
  simp at hm

theorem pair_53_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 53 []).length)
    (hq : (normIsRep.getD 53 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨53, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨53, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_53_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_53_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_53_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_53_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_53_12_4 hp j hj hq
  simp at hm

theorem pair_53_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 53 []).length)
    (hq : (normIsRep.getD 53 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨53, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨53, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_53_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_53_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_53_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_53_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_53_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_53_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_53_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_53_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_53_53_20 hp j hj hq
  simp at hm

theorem pair_54_11 (p : Nat) (hp : p < (Q2.transData.getD 11 []).length)
    (hrep : (Q2.cosetIsRep.getD 11 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 54 []).length)
    (hq : (normIsRep.getD 54 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ p hp)
        (rowE2 (⟨54, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ p (transLenTr ⟨11, by decide⟩ p hp))
        (rowE1 (⟨54, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_11 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_54_11_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_54_11_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_54_11_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_54_11_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_54_11_4 hp j hj hq
  simp at hm

theorem pair_54_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 54 []).length)
    (hq : (normIsRep.getD 54 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨54, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨54, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_54_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_54_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_54_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_54_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_54_12_4 hp j hj hq
  simp at hm

theorem pair_54_54 (p : Nat) (hp : p < (Q2.transData.getD 54 []).length)
    (hrep : (Q2.cosetIsRep.getD 54 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 54 []).length)
    (hq : (normIsRep.getD 54 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ p hp)
        (rowE2 (⟨54, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ p (transLenTr ⟨54, by decide⟩ p hp))
        (rowE1 (⟨54, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_54 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_54_54_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_54_54_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_54_54_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_54_54_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_54_54_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_54_54_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_54_54_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_54_54_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_54_54_20 hp j hj hq
  simp at hm

theorem pair_55_9 (p : Nat) (hp : p < (Q2.transData.getD 9 []).length)
    (hrep : (Q2.cosetIsRep.getD 9 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ p hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ p (transLenTr ⟨9, by decide⟩ p hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_9 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_9_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_9_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_9_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_9_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_9_4 hp j hj hq
  simp at hm

theorem pair_55_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_12_4 hp j hj hq
  simp at hm

theorem pair_55_27 (p : Nat) (hp : p < (Q2.transData.getD 27 []).length)
    (hrep : (Q2.cosetIsRep.getD 27 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ p hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ p (transLenTr ⟨27, by decide⟩ p hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_27 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_27_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_27_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_27_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_27_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_27_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_27_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_27_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_27_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_27_20 hp j hj hq
  simp at hm

theorem pair_55_28 (p : Nat) (hp : p < (Q2.transData.getD 28 []).length)
    (hrep : (Q2.cosetIsRep.getD 28 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ p hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ p (transLenTr ⟨28, by decide⟩ p hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_28 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_28_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_28_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_28_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_28_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_28_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_28_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_28_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_28_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_28_20 hp j hj hq
  simp at hm

theorem pair_55_33 (p : Nat) (hp : p < (Q2.transData.getD 33 []).length)
    (hrep : (Q2.cosetIsRep.getD 33 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ p hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ p (transLenTr ⟨33, by decide⟩ p hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_33 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_33_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_33_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_33_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_33_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_33_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_33_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_33_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_33_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_33_20 hp j hj hq
  simp at hm

theorem pair_55_38 (p : Nat) (hp : p < (Q2.transData.getD 38 []).length)
    (hrep : (Q2.cosetIsRep.getD 38 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ p hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ p (transLenTr ⟨38, by decide⟩ p hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_38 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_38_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_38_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_38_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_38_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_38_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_38_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_38_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_38_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_38_20 hp j hj hq
  simp at hm

theorem pair_55_43 (p : Nat) (hp : p < (Q2.transData.getD 43 []).length)
    (hrep : (Q2.cosetIsRep.getD 43 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ p hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ p (transLenTr ⟨43, by decide⟩ p hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_43 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_43_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_43_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_43_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_43_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_43_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_43_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_43_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_43_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_43_20 hp j hj hq
  simp at hm

theorem pair_55_48 (p : Nat) (hp : p < (Q2.transData.getD 48 []).length)
    (hrep : (Q2.cosetIsRep.getD 48 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ p hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ p (transLenTr ⟨48, by decide⟩ p hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_48 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_48_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_48_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_48_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_48_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_48_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_48_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_48_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_48_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_48_20 hp j hj hq
  simp at hm

theorem pair_55_55 (p : Nat) (hp : p < (Q2.transData.getD 55 []).length)
    (hrep : (Q2.cosetIsRep.getD 55 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ p hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ p (transLenTr ⟨55, by decide⟩ p hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_55 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_55_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_55_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_55_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_55_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_55_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_55_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_55_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_55_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_55_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_55_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_55_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_55_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_55_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_55_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_55_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_55_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_55_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_55_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_55_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_55_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_55_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_55_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_55_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_55_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_55_55_24 hp j hj hq
  simp at hm

theorem pair_56_1 (p : Nat) (hp : p < (Q2.transData.getD 1 []).length)
    (hrep : (Q2.cosetIsRep.getD 1 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ p hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ p (transLenTr ⟨1, by decide⟩ p hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_1 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_1_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_1_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_1_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_1_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_1_4 hp j hj hq
  simp at hm

theorem pair_56_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_12_4 hp j hj hq
  simp at hm

theorem pair_56_19 (p : Nat) (hp : p < (Q2.transData.getD 19 []).length)
    (hrep : (Q2.cosetIsRep.getD 19 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ p hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ p (transLenTr ⟨19, by decide⟩ p hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_19 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_19_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_19_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_19_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_19_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_19_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_19_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_19_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_19_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_19_20 hp j hj hq
  simp at hm

theorem pair_56_28 (p : Nat) (hp : p < (Q2.transData.getD 28 []).length)
    (hrep : (Q2.cosetIsRep.getD 28 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ p hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ p (transLenTr ⟨28, by decide⟩ p hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_28 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_28_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_28_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_28_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_28_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_28_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_28_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_28_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_28_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_28_20 hp j hj hq
  simp at hm

theorem pair_56_33 (p : Nat) (hp : p < (Q2.transData.getD 33 []).length)
    (hrep : (Q2.cosetIsRep.getD 33 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ p hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ p (transLenTr ⟨33, by decide⟩ p hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_33 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_33_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_33_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_33_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_33_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_33_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_33_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_33_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_33_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_33_20 hp j hj hq
  simp at hm

theorem pair_56_38 (p : Nat) (hp : p < (Q2.transData.getD 38 []).length)
    (hrep : (Q2.cosetIsRep.getD 38 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ p hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ p (transLenTr ⟨38, by decide⟩ p hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_38 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_38_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_38_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_38_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_38_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_38_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_38_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_38_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_38_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_38_20 hp j hj hq
  simp at hm

theorem pair_56_43 (p : Nat) (hp : p < (Q2.transData.getD 43 []).length)
    (hrep : (Q2.cosetIsRep.getD 43 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ p hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ p (transLenTr ⟨43, by decide⟩ p hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_43 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_43_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_43_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_43_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_43_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_43_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_43_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_43_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_43_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_43_20 hp j hj hq
  simp at hm

theorem pair_56_48 (p : Nat) (hp : p < (Q2.transData.getD 48 []).length)
    (hrep : (Q2.cosetIsRep.getD 48 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ p hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ p (transLenTr ⟨48, by decide⟩ p hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_48 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_48_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_48_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_48_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_48_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_48_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_48_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_48_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_48_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_48_20 hp j hj hq
  simp at hm

theorem pair_56_56 (p : Nat) (hp : p < (Q2.transData.getD 56 []).length)
    (hrep : (Q2.cosetIsRep.getD 56 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ p hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ p (transLenTr ⟨56, by decide⟩ p hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_56 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_56_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_56_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_56_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_56_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_56_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_56_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_56_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_56_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_56_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_56_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_56_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_56_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_56_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_56_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_56_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_56_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_56_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_56_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_56_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_56_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_56_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_56_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_56_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_56_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_56_56_24 hp j hj hq
  simp at hm

theorem pair_57_7 (p : Nat) (hp : p < (Q2.transData.getD 7 []).length)
    (hrep : (Q2.cosetIsRep.getD 7 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ p hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ p (transLenTr ⟨7, by decide⟩ p hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_7 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_7_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_7_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_7_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_7_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_7_4 hp j hj hq
  simp at hm

theorem pair_57_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_12_4 hp j hj hq
  simp at hm

theorem pair_57_25 (p : Nat) (hp : p < (Q2.transData.getD 25 []).length)
    (hrep : (Q2.cosetIsRep.getD 25 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ p hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ p (transLenTr ⟨25, by decide⟩ p hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_25 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_25_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_25_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_25_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_25_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_25_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_25_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_25_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_25_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_25_20 hp j hj hq
  simp at hm

theorem pair_57_28 (p : Nat) (hp : p < (Q2.transData.getD 28 []).length)
    (hrep : (Q2.cosetIsRep.getD 28 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ p hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ p (transLenTr ⟨28, by decide⟩ p hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_28 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_28_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_28_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_28_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_28_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_28_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_28_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_28_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_28_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_28_20 hp j hj hq
  simp at hm

theorem pair_57_33 (p : Nat) (hp : p < (Q2.transData.getD 33 []).length)
    (hrep : (Q2.cosetIsRep.getD 33 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ p hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ p (transLenTr ⟨33, by decide⟩ p hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_33 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_33_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_33_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_33_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_33_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_33_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_33_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_33_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_33_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_33_20 hp j hj hq
  simp at hm

theorem pair_57_38 (p : Nat) (hp : p < (Q2.transData.getD 38 []).length)
    (hrep : (Q2.cosetIsRep.getD 38 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ p hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ p (transLenTr ⟨38, by decide⟩ p hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_38 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_38_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_38_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_38_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_38_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_38_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_38_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_38_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_38_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_38_20 hp j hj hq
  simp at hm

theorem pair_57_43 (p : Nat) (hp : p < (Q2.transData.getD 43 []).length)
    (hrep : (Q2.cosetIsRep.getD 43 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ p hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ p (transLenTr ⟨43, by decide⟩ p hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_43 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_43_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_43_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_43_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_43_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_43_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_43_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_43_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_43_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_43_20 hp j hj hq
  simp at hm

theorem pair_57_48 (p : Nat) (hp : p < (Q2.transData.getD 48 []).length)
    (hrep : (Q2.cosetIsRep.getD 48 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ p hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ p (transLenTr ⟨48, by decide⟩ p hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_48 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_48_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_48_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_48_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_48_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_48_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_48_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_48_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_48_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_48_20 hp j hj hq
  simp at hm

theorem pair_57_57 (p : Nat) (hp : p < (Q2.transData.getD 57 []).length)
    (hrep : (Q2.cosetIsRep.getD 57 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ p hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ p (transLenTr ⟨57, by decide⟩ p hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_57 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_57_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_57_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_57_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_57_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_57_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_57_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_57_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_57_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_57_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_57_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_57_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_57_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_57_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_57_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_57_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_57_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_57_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_57_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_57_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_57_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_57_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_57_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_57_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_57_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_57_57_24 hp j hj hq
  simp at hm

theorem pair_58_6 (p : Nat) (hp : p < (Q2.transData.getD 6 []).length)
    (hrep : (Q2.cosetIsRep.getD 6 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ p hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ p (transLenTr ⟨6, by decide⟩ p hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_6 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_6_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_6_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_6_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_6_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_6_4 hp j hj hq
  simp at hm

theorem pair_58_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_12_4 hp j hj hq
  simp at hm

theorem pair_58_24 (p : Nat) (hp : p < (Q2.transData.getD 24 []).length)
    (hrep : (Q2.cosetIsRep.getD 24 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ p hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ p (transLenTr ⟨24, by decide⟩ p hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_24 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_24_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_24_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_24_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_24_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_24_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_24_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_24_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_24_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_24_20 hp j hj hq
  simp at hm

theorem pair_58_28 (p : Nat) (hp : p < (Q2.transData.getD 28 []).length)
    (hrep : (Q2.cosetIsRep.getD 28 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ p hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ p (transLenTr ⟨28, by decide⟩ p hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_28 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_28_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_28_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_28_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_28_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_28_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_28_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_28_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_28_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_28_20 hp j hj hq
  simp at hm

theorem pair_58_33 (p : Nat) (hp : p < (Q2.transData.getD 33 []).length)
    (hrep : (Q2.cosetIsRep.getD 33 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ p hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ p (transLenTr ⟨33, by decide⟩ p hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_33 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_33_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_33_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_33_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_33_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_33_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_33_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_33_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_33_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_33_20 hp j hj hq
  simp at hm

theorem pair_58_38 (p : Nat) (hp : p < (Q2.transData.getD 38 []).length)
    (hrep : (Q2.cosetIsRep.getD 38 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ p hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ p (transLenTr ⟨38, by decide⟩ p hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_38 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_38_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_38_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_38_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_38_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_38_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_38_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_38_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_38_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_38_20 hp j hj hq
  simp at hm

theorem pair_58_43 (p : Nat) (hp : p < (Q2.transData.getD 43 []).length)
    (hrep : (Q2.cosetIsRep.getD 43 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ p hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ p (transLenTr ⟨43, by decide⟩ p hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_43 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_43_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_43_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_43_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_43_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_43_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_43_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_43_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_43_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_43_20 hp j hj hq
  simp at hm

theorem pair_58_48 (p : Nat) (hp : p < (Q2.transData.getD 48 []).length)
    (hrep : (Q2.cosetIsRep.getD 48 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ p hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ p (transLenTr ⟨48, by decide⟩ p hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_48 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_48_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_48_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_48_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_48_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_48_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_48_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_48_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_48_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_48_20 hp j hj hq
  simp at hm

theorem pair_58_58 (p : Nat) (hp : p < (Q2.transData.getD 58 []).length)
    (hrep : (Q2.cosetIsRep.getD 58 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ p hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ p (transLenTr ⟨58, by decide⟩ p hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_58 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_58_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_58_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_58_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_58_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_58_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_58_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_58_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_58_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_58_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_58_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_58_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_58_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_58_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_58_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_58_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_58_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_58_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_58_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_58_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_58_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_58_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_58_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_58_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_58_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_58_58_24 hp j hj hq
  simp at hm

theorem pair_59_8 (p : Nat) (hp : p < (Q2.transData.getD 8 []).length)
    (hrep : (Q2.cosetIsRep.getD 8 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ p hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ p (transLenTr ⟨8, by decide⟩ p hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_8 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_8_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_8_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_8_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_8_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_8_4 hp j hj hq
  simp at hm

theorem pair_59_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_12_4 hp j hj hq
  simp at hm

theorem pair_59_26 (p : Nat) (hp : p < (Q2.transData.getD 26 []).length)
    (hrep : (Q2.cosetIsRep.getD 26 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ p hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ p (transLenTr ⟨26, by decide⟩ p hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_26 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_26_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_26_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_26_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_26_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_26_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_26_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_26_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_26_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_26_20 hp j hj hq
  simp at hm

theorem pair_59_28 (p : Nat) (hp : p < (Q2.transData.getD 28 []).length)
    (hrep : (Q2.cosetIsRep.getD 28 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ p hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ p (transLenTr ⟨28, by decide⟩ p hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_28 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_28_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_28_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_28_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_28_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_28_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_28_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_28_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_28_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_28_20 hp j hj hq
  simp at hm

theorem pair_59_33 (p : Nat) (hp : p < (Q2.transData.getD 33 []).length)
    (hrep : (Q2.cosetIsRep.getD 33 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ p hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ p (transLenTr ⟨33, by decide⟩ p hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_33 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_33_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_33_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_33_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_33_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_33_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_33_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_33_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_33_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_33_20 hp j hj hq
  simp at hm

theorem pair_59_38 (p : Nat) (hp : p < (Q2.transData.getD 38 []).length)
    (hrep : (Q2.cosetIsRep.getD 38 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ p hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ p (transLenTr ⟨38, by decide⟩ p hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_38 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_38_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_38_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_38_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_38_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_38_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_38_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_38_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_38_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_38_20 hp j hj hq
  simp at hm

theorem pair_59_43 (p : Nat) (hp : p < (Q2.transData.getD 43 []).length)
    (hrep : (Q2.cosetIsRep.getD 43 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ p hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ p (transLenTr ⟨43, by decide⟩ p hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_43 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_43_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_43_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_43_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_43_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_43_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_43_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_43_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_43_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_43_20 hp j hj hq
  simp at hm

theorem pair_59_48 (p : Nat) (hp : p < (Q2.transData.getD 48 []).length)
    (hrep : (Q2.cosetIsRep.getD 48 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ p hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ p (transLenTr ⟨48, by decide⟩ p hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_48 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_48_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_48_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_48_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_48_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_48_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_48_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_48_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_48_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_48_20 hp j hj hq
  simp at hm

theorem pair_59_59 (p : Nat) (hp : p < (Q2.transData.getD 59 []).length)
    (hrep : (Q2.cosetIsRep.getD 59 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ p hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ p (transLenTr ⟨59, by decide⟩ p hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_59 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_59_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_59_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_59_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_59_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_59_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_59_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_59_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_59_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_59_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_59_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_59_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_59_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_59_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_59_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_59_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_59_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_59_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_59_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_59_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_59_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_59_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_59_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_59_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_59_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_59_59_24 hp j hj hq
  simp at hm

theorem pair_60_9 (p : Nat) (hp : p < (Q2.transData.getD 9 []).length)
    (hrep : (Q2.cosetIsRep.getD 9 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ p hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ p (transLenTr ⟨9, by decide⟩ p hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_9 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_9_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_9_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_9_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_9_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_9_4 hp j hj hq
  simp at hm

theorem pair_60_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_12_4 hp j hj hq
  simp at hm

theorem pair_60_27 (p : Nat) (hp : p < (Q2.transData.getD 27 []).length)
    (hrep : (Q2.cosetIsRep.getD 27 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ p hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ p (transLenTr ⟨27, by decide⟩ p hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_27 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_27_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_27_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_27_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_27_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_27_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_27_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_27_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_27_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_27_20 hp j hj hq
  simp at hm

theorem pair_60_29 (p : Nat) (hp : p < (Q2.transData.getD 29 []).length)
    (hrep : (Q2.cosetIsRep.getD 29 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ p hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ p (transLenTr ⟨29, by decide⟩ p hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_29 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_29_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_29_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_29_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_29_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_29_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_29_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_29_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_29_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_29_20 hp j hj hq
  simp at hm

theorem pair_60_34 (p : Nat) (hp : p < (Q2.transData.getD 34 []).length)
    (hrep : (Q2.cosetIsRep.getD 34 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ p hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ p (transLenTr ⟨34, by decide⟩ p hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_34 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_34_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_34_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_34_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_34_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_34_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_34_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_34_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_34_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_34_20 hp j hj hq
  simp at hm

theorem pair_60_39 (p : Nat) (hp : p < (Q2.transData.getD 39 []).length)
    (hrep : (Q2.cosetIsRep.getD 39 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ p hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ p (transLenTr ⟨39, by decide⟩ p hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_39 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_39_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_39_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_39_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_39_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_39_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_39_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_39_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_39_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_39_20 hp j hj hq
  simp at hm

theorem pair_60_44 (p : Nat) (hp : p < (Q2.transData.getD 44 []).length)
    (hrep : (Q2.cosetIsRep.getD 44 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ p hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ p (transLenTr ⟨44, by decide⟩ p hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_44 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_44_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_44_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_44_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_44_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_44_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_44_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_44_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_44_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_44_20 hp j hj hq
  simp at hm

theorem pair_60_49 (p : Nat) (hp : p < (Q2.transData.getD 49 []).length)
    (hrep : (Q2.cosetIsRep.getD 49 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ p hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ p (transLenTr ⟨49, by decide⟩ p hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_49 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_49_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_49_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_49_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_49_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_49_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_49_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_49_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_49_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_49_20 hp j hj hq
  simp at hm

theorem pair_60_60 (p : Nat) (hp : p < (Q2.transData.getD 60 []).length)
    (hrep : (Q2.cosetIsRep.getD 60 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ p hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ p (transLenTr ⟨60, by decide⟩ p hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_60 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_60_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_60_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_60_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_60_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_60_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_60_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_60_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_60_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_60_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_60_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_60_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_60_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_60_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_60_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_60_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_60_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_60_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_60_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_60_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_60_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_60_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_60_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_60_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_60_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_60_60_24 hp j hj hq
  simp at hm

theorem pair_61_1 (p : Nat) (hp : p < (Q2.transData.getD 1 []).length)
    (hrep : (Q2.cosetIsRep.getD 1 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ p hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ p (transLenTr ⟨1, by decide⟩ p hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_1 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_1_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_1_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_1_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_1_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_1_4 hp j hj hq
  simp at hm

theorem pair_61_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_12_4 hp j hj hq
  simp at hm

theorem pair_61_19 (p : Nat) (hp : p < (Q2.transData.getD 19 []).length)
    (hrep : (Q2.cosetIsRep.getD 19 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ p hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ p (transLenTr ⟨19, by decide⟩ p hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_19 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_19_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_19_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_19_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_19_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_19_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_19_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_19_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_19_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_19_20 hp j hj hq
  simp at hm

theorem pair_61_29 (p : Nat) (hp : p < (Q2.transData.getD 29 []).length)
    (hrep : (Q2.cosetIsRep.getD 29 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ p hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ p (transLenTr ⟨29, by decide⟩ p hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_29 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_29_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_29_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_29_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_29_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_29_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_29_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_29_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_29_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_29_20 hp j hj hq
  simp at hm

theorem pair_61_34 (p : Nat) (hp : p < (Q2.transData.getD 34 []).length)
    (hrep : (Q2.cosetIsRep.getD 34 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ p hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ p (transLenTr ⟨34, by decide⟩ p hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_34 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_34_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_34_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_34_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_34_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_34_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_34_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_34_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_34_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_34_20 hp j hj hq
  simp at hm

theorem pair_61_39 (p : Nat) (hp : p < (Q2.transData.getD 39 []).length)
    (hrep : (Q2.cosetIsRep.getD 39 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ p hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ p (transLenTr ⟨39, by decide⟩ p hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_39 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_39_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_39_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_39_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_39_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_39_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_39_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_39_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_39_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_39_20 hp j hj hq
  simp at hm

theorem pair_61_44 (p : Nat) (hp : p < (Q2.transData.getD 44 []).length)
    (hrep : (Q2.cosetIsRep.getD 44 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ p hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ p (transLenTr ⟨44, by decide⟩ p hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_44 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_44_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_44_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_44_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_44_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_44_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_44_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_44_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_44_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_44_20 hp j hj hq
  simp at hm

theorem pair_61_49 (p : Nat) (hp : p < (Q2.transData.getD 49 []).length)
    (hrep : (Q2.cosetIsRep.getD 49 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ p hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ p (transLenTr ⟨49, by decide⟩ p hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_49 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_49_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_49_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_49_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_49_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_49_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_49_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_49_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_49_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_49_20 hp j hj hq
  simp at hm

theorem pair_61_61 (p : Nat) (hp : p < (Q2.transData.getD 61 []).length)
    (hrep : (Q2.cosetIsRep.getD 61 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ p hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ p (transLenTr ⟨61, by decide⟩ p hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_61 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_61_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_61_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_61_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_61_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_61_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_61_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_61_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_61_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_61_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_61_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_61_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_61_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_61_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_61_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_61_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_61_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_61_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_61_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_61_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_61_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_61_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_61_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_61_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_61_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_61_61_24 hp j hj hq
  simp at hm

theorem pair_62_7 (p : Nat) (hp : p < (Q2.transData.getD 7 []).length)
    (hrep : (Q2.cosetIsRep.getD 7 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ p hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ p (transLenTr ⟨7, by decide⟩ p hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_7 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_7_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_7_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_7_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_7_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_7_4 hp j hj hq
  simp at hm

theorem pair_62_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_12_4 hp j hj hq
  simp at hm

theorem pair_62_25 (p : Nat) (hp : p < (Q2.transData.getD 25 []).length)
    (hrep : (Q2.cosetIsRep.getD 25 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ p hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ p (transLenTr ⟨25, by decide⟩ p hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_25 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_25_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_25_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_25_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_25_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_25_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_25_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_25_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_25_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_25_20 hp j hj hq
  simp at hm

theorem pair_62_29 (p : Nat) (hp : p < (Q2.transData.getD 29 []).length)
    (hrep : (Q2.cosetIsRep.getD 29 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ p hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ p (transLenTr ⟨29, by decide⟩ p hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_29 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_29_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_29_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_29_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_29_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_29_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_29_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_29_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_29_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_29_20 hp j hj hq
  simp at hm

theorem pair_62_34 (p : Nat) (hp : p < (Q2.transData.getD 34 []).length)
    (hrep : (Q2.cosetIsRep.getD 34 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ p hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ p (transLenTr ⟨34, by decide⟩ p hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_34 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_34_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_34_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_34_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_34_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_34_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_34_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_34_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_34_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_34_20 hp j hj hq
  simp at hm

theorem pair_62_39 (p : Nat) (hp : p < (Q2.transData.getD 39 []).length)
    (hrep : (Q2.cosetIsRep.getD 39 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ p hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ p (transLenTr ⟨39, by decide⟩ p hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_39 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_39_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_39_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_39_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_39_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_39_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_39_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_39_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_39_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_39_20 hp j hj hq
  simp at hm

theorem pair_62_44 (p : Nat) (hp : p < (Q2.transData.getD 44 []).length)
    (hrep : (Q2.cosetIsRep.getD 44 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ p hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ p (transLenTr ⟨44, by decide⟩ p hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_44 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_44_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_44_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_44_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_44_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_44_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_44_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_44_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_44_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_44_20 hp j hj hq
  simp at hm

theorem pair_62_49 (p : Nat) (hp : p < (Q2.transData.getD 49 []).length)
    (hrep : (Q2.cosetIsRep.getD 49 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ p hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ p (transLenTr ⟨49, by decide⟩ p hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_49 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_49_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_49_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_49_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_49_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_49_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_49_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_49_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_49_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_49_20 hp j hj hq
  simp at hm

theorem pair_62_62 (p : Nat) (hp : p < (Q2.transData.getD 62 []).length)
    (hrep : (Q2.cosetIsRep.getD 62 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ p hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ p (transLenTr ⟨62, by decide⟩ p hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_62 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_62_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_62_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_62_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_62_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_62_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_62_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_62_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_62_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_62_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_62_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_62_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_62_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_62_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_62_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_62_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_62_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_62_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_62_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_62_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_62_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_62_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_62_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_62_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_62_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_62_62_24 hp j hj hq
  simp at hm

theorem pair_63_6 (p : Nat) (hp : p < (Q2.transData.getD 6 []).length)
    (hrep : (Q2.cosetIsRep.getD 6 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ p hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ p (transLenTr ⟨6, by decide⟩ p hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_6 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_6_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_6_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_6_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_6_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_6_4 hp j hj hq
  simp at hm

theorem pair_63_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_12_4 hp j hj hq
  simp at hm

theorem pair_63_24 (p : Nat) (hp : p < (Q2.transData.getD 24 []).length)
    (hrep : (Q2.cosetIsRep.getD 24 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ p hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ p (transLenTr ⟨24, by decide⟩ p hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_24 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_24_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_24_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_24_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_24_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_24_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_24_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_24_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_24_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_24_20 hp j hj hq
  simp at hm

theorem pair_63_29 (p : Nat) (hp : p < (Q2.transData.getD 29 []).length)
    (hrep : (Q2.cosetIsRep.getD 29 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ p hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ p (transLenTr ⟨29, by decide⟩ p hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_29 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_29_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_29_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_29_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_29_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_29_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_29_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_29_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_29_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_29_20 hp j hj hq
  simp at hm

theorem pair_63_34 (p : Nat) (hp : p < (Q2.transData.getD 34 []).length)
    (hrep : (Q2.cosetIsRep.getD 34 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ p hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ p (transLenTr ⟨34, by decide⟩ p hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_34 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_34_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_34_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_34_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_34_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_34_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_34_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_34_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_34_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_34_20 hp j hj hq
  simp at hm

theorem pair_63_39 (p : Nat) (hp : p < (Q2.transData.getD 39 []).length)
    (hrep : (Q2.cosetIsRep.getD 39 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ p hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ p (transLenTr ⟨39, by decide⟩ p hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_39 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_39_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_39_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_39_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_39_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_39_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_39_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_39_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_39_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_39_20 hp j hj hq
  simp at hm

theorem pair_63_44 (p : Nat) (hp : p < (Q2.transData.getD 44 []).length)
    (hrep : (Q2.cosetIsRep.getD 44 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ p hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ p (transLenTr ⟨44, by decide⟩ p hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_44 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_44_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_44_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_44_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_44_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_44_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_44_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_44_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_44_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_44_20 hp j hj hq
  simp at hm

theorem pair_63_49 (p : Nat) (hp : p < (Q2.transData.getD 49 []).length)
    (hrep : (Q2.cosetIsRep.getD 49 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ p hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ p (transLenTr ⟨49, by decide⟩ p hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_49 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_49_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_49_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_49_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_49_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_49_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_49_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_49_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_49_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_49_20 hp j hj hq
  simp at hm

theorem pair_63_63 (p : Nat) (hp : p < (Q2.transData.getD 63 []).length)
    (hrep : (Q2.cosetIsRep.getD 63 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ p hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ p (transLenTr ⟨63, by decide⟩ p hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_63 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_63_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_63_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_63_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_63_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_63_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_63_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_63_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_63_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_63_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_63_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_63_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_63_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_63_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_63_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_63_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_63_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_63_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_63_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_63_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_63_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_63_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_63_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_63_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_63_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_63_63_24 hp j hj hq
  simp at hm

theorem pair_64_8 (p : Nat) (hp : p < (Q2.transData.getD 8 []).length)
    (hrep : (Q2.cosetIsRep.getD 8 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ p hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ p (transLenTr ⟨8, by decide⟩ p hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_8 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_8_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_8_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_8_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_8_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_8_4 hp j hj hq
  simp at hm

theorem pair_64_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_12_4 hp j hj hq
  simp at hm

theorem pair_64_26 (p : Nat) (hp : p < (Q2.transData.getD 26 []).length)
    (hrep : (Q2.cosetIsRep.getD 26 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ p hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ p (transLenTr ⟨26, by decide⟩ p hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_26 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_26_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_26_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_26_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_26_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_26_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_26_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_26_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_26_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_26_20 hp j hj hq
  simp at hm

theorem pair_64_29 (p : Nat) (hp : p < (Q2.transData.getD 29 []).length)
    (hrep : (Q2.cosetIsRep.getD 29 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ p hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ p (transLenTr ⟨29, by decide⟩ p hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_29 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_29_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_29_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_29_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_29_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_29_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_29_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_29_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_29_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_29_20 hp j hj hq
  simp at hm

theorem pair_64_34 (p : Nat) (hp : p < (Q2.transData.getD 34 []).length)
    (hrep : (Q2.cosetIsRep.getD 34 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ p hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ p (transLenTr ⟨34, by decide⟩ p hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_34 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_34_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_34_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_34_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_34_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_34_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_34_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_34_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_34_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_34_20 hp j hj hq
  simp at hm

theorem pair_64_39 (p : Nat) (hp : p < (Q2.transData.getD 39 []).length)
    (hrep : (Q2.cosetIsRep.getD 39 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ p hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ p (transLenTr ⟨39, by decide⟩ p hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_39 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_39_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_39_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_39_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_39_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_39_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_39_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_39_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_39_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_39_20 hp j hj hq
  simp at hm

theorem pair_64_44 (p : Nat) (hp : p < (Q2.transData.getD 44 []).length)
    (hrep : (Q2.cosetIsRep.getD 44 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ p hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ p (transLenTr ⟨44, by decide⟩ p hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_44 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_44_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_44_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_44_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_44_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_44_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_44_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_44_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_44_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_44_20 hp j hj hq
  simp at hm

theorem pair_64_49 (p : Nat) (hp : p < (Q2.transData.getD 49 []).length)
    (hrep : (Q2.cosetIsRep.getD 49 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ p hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ p (transLenTr ⟨49, by decide⟩ p hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_49 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_49_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_49_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_49_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_49_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_49_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_49_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_49_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_49_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_49_20 hp j hj hq
  simp at hm

theorem pair_64_64 (p : Nat) (hp : p < (Q2.transData.getD 64 []).length)
    (hrep : (Q2.cosetIsRep.getD 64 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ p hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ p (transLenTr ⟨64, by decide⟩ p hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_64 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_24 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_30 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_35 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_40 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_45 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_55 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_60 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_65 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_70 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_80 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_85 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_90 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_95 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_100 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_105 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_110 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_115 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_64_64_120 hp j hj hq
  simp at hm

theorem pair_65_9 (p : Nat) (hp : p < (Q2.transData.getD 9 []).length)
    (hrep : (Q2.cosetIsRep.getD 9 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ p hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ p (transLenTr ⟨9, by decide⟩ p hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_9 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_9_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_9_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_9_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_9_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_9_4 hp j hj hq
  simp at hm

theorem pair_65_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_12_4 hp j hj hq
  simp at hm

theorem pair_65_27 (p : Nat) (hp : p < (Q2.transData.getD 27 []).length)
    (hrep : (Q2.cosetIsRep.getD 27 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ p hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ p (transLenTr ⟨27, by decide⟩ p hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_27 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_27_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_27_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_27_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_27_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_27_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_27_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_27_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_27_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_27_20 hp j hj hq
  simp at hm

theorem pair_65_30 (p : Nat) (hp : p < (Q2.transData.getD 30 []).length)
    (hrep : (Q2.cosetIsRep.getD 30 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ p hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ p (transLenTr ⟨30, by decide⟩ p hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_30 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_30_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_30_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_30_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_30_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_30_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_30_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_30_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_30_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_30_20 hp j hj hq
  simp at hm

theorem pair_65_35 (p : Nat) (hp : p < (Q2.transData.getD 35 []).length)
    (hrep : (Q2.cosetIsRep.getD 35 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ p hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ p (transLenTr ⟨35, by decide⟩ p hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_35 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_35_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_35_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_35_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_35_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_35_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_35_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_35_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_35_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_35_20 hp j hj hq
  simp at hm

theorem pair_65_40 (p : Nat) (hp : p < (Q2.transData.getD 40 []).length)
    (hrep : (Q2.cosetIsRep.getD 40 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ p hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ p (transLenTr ⟨40, by decide⟩ p hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_40 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_40_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_40_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_40_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_40_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_40_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_40_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_40_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_40_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_40_20 hp j hj hq
  simp at hm

theorem pair_65_45 (p : Nat) (hp : p < (Q2.transData.getD 45 []).length)
    (hrep : (Q2.cosetIsRep.getD 45 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ p hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ p (transLenTr ⟨45, by decide⟩ p hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_45 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_45_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_45_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_45_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_45_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_45_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_45_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_45_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_45_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_45_20 hp j hj hq
  simp at hm

theorem pair_65_50 (p : Nat) (hp : p < (Q2.transData.getD 50 []).length)
    (hrep : (Q2.cosetIsRep.getD 50 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ p hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ p (transLenTr ⟨50, by decide⟩ p hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_50 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_50_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_50_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_50_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_50_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_50_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_50_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_50_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_50_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_50_20 hp j hj hq
  simp at hm

theorem pair_65_65 (p : Nat) (hp : p < (Q2.transData.getD 65 []).length)
    (hrep : (Q2.cosetIsRep.getD 65 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ p hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ p (transLenTr ⟨65, by decide⟩ p hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_65 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_65_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_65_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_65_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_65_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_65_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_65_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_65_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_65_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_65_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_65_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_65_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_65_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_65_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_65_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_65_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_65_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_65_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_65_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_65_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_65_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_65_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_65_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_65_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_65_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_65_65_24 hp j hj hq
  simp at hm

theorem pair_66_1 (p : Nat) (hp : p < (Q2.transData.getD 1 []).length)
    (hrep : (Q2.cosetIsRep.getD 1 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ p hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ p (transLenTr ⟨1, by decide⟩ p hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_1 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_1_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_1_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_1_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_1_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_1_4 hp j hj hq
  simp at hm

theorem pair_66_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_12_4 hp j hj hq
  simp at hm

theorem pair_66_19 (p : Nat) (hp : p < (Q2.transData.getD 19 []).length)
    (hrep : (Q2.cosetIsRep.getD 19 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ p hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ p (transLenTr ⟨19, by decide⟩ p hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_19 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_19_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_19_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_19_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_19_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_19_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_19_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_19_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_19_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_19_20 hp j hj hq
  simp at hm

theorem pair_66_30 (p : Nat) (hp : p < (Q2.transData.getD 30 []).length)
    (hrep : (Q2.cosetIsRep.getD 30 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ p hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ p (transLenTr ⟨30, by decide⟩ p hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_30 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_30_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_30_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_30_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_30_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_30_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_30_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_30_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_30_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_30_20 hp j hj hq
  simp at hm

end LeanDring.P5Presentation
