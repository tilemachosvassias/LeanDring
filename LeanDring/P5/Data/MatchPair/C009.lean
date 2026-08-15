/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.MatchLeaf.C037
import LeanDring.P5.Data.MatchLeaf.C038
import LeanDring.P5.Data.MatchLeaf.C039
import LeanDring.P5.Data.MatchLeaf.C040
import LeanDring.P5.Data.MatchLeaf.C041
import LeanDring.P5.Data.MatchLeaf.C042

/-! # Stage-5 per-pair theorems, chunk 8 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem pair_132_93 (p : Nat) (hp : p < (Q2.transData.getD 93 []).length)
    (hrep : (Q2.cosetIsRep.getD 93 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ p hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ p (transLenTr ⟨93, by decide⟩ p hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_93 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_93_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_93_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_93_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_93_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_93_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_93_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_93_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_93_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_93_20 hp j hj hq
  simp at hm

theorem pair_132_97 (p : Nat) (hp : p < (Q2.transData.getD 97 []).length)
    (hrep : (Q2.cosetIsRep.getD 97 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ p hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ p (transLenTr ⟨97, by decide⟩ p hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_97 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_97_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_97_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_97_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_97_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_97_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_97_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_97_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_97_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_97_20 hp j hj hq
  simp at hm

theorem pair_132_100 (p : Nat) (hp : p < (Q2.transData.getD 100 []).length)
    (hrep : (Q2.cosetIsRep.getD 100 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ p hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ p (transLenTr ⟨100, by decide⟩ p hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_100 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_100_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_100_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_100_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_100_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_100_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_100_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_100_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_100_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_100_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_100_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_100_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_100_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_100_100 hp j hj hq
  simp at hm

theorem pair_132_109 (p : Nat) (hp : p < (Q2.transData.getD 109 []).length)
    (hrep : (Q2.cosetIsRep.getD 109 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ p hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ p (transLenTr ⟨109, by decide⟩ p hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_109 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_109_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_109_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_109_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_109_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_109_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_109_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_109_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_109_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_109_20 hp j hj hq
  simp at hm

theorem pair_132_111 (p : Nat) (hp : p < (Q2.transData.getD 111 []).length)
    (hrep : (Q2.cosetIsRep.getD 111 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ p hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ p (transLenTr ⟨111, by decide⟩ p hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_111 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_111_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_111_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_111_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_111_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_111_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_111_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_111_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_111_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_111_20 hp j hj hq
  simp at hm

theorem pair_132_132 (p : Nat) (hp : p < (Q2.transData.getD 132 []).length)
    (hrep : (Q2.cosetIsRep.getD 132 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ p hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ p (transLenTr ⟨132, by decide⟩ p hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_132 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_132_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_132_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_132_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_132_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_132_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_132_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_132_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_132_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_132_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_132_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_132_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_132_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_132_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_132_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_132_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_132_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_132_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_132_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_132_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_132_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_132_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_132_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_132_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_132_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_132_24 hp j hj hq
  simp at hm

theorem pair_133_4 (p : Nat) (hp : p < (Q2.transData.getD 4 []).length)
    (hrep : (Q2.cosetIsRep.getD 4 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ p hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ p (transLenTr ⟨4, by decide⟩ p hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_4 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_4_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_4_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_4_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_4_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_4_4 hp j hj hq
  simp at hm

theorem pair_133_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_10_4 hp j hj hq
  simp at hm

theorem pair_133_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_12_4 hp j hj hq
  simp at hm

theorem pair_133_22 (p : Nat) (hp : p < (Q2.transData.getD 22 []).length)
    (hrep : (Q2.cosetIsRep.getD 22 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ p hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ p (transLenTr ⟨22, by decide⟩ p hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_22 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_22_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_22_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_22_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_22_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_22_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_22_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_22_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_22_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_22_20 hp j hj hq
  simp at hm

theorem pair_133_32 (p : Nat) (hp : p < (Q2.transData.getD 32 []).length)
    (hrep : (Q2.cosetIsRep.getD 32 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ p hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ p (transLenTr ⟨32, by decide⟩ p hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_32 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_32_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_32_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_32_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_32_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_32_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_32_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_32_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_32_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_32_20 hp j hj hq
  simp at hm

theorem pair_133_36 (p : Nat) (hp : p < (Q2.transData.getD 36 []).length)
    (hrep : (Q2.cosetIsRep.getD 36 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ p hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ p (transLenTr ⟨36, by decide⟩ p hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_36 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_36_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_36_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_36_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_36_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_36_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_36_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_36_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_36_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_36_20 hp j hj hq
  simp at hm

theorem pair_133_39 (p : Nat) (hp : p < (Q2.transData.getD 39 []).length)
    (hrep : (Q2.cosetIsRep.getD 39 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ p hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ p (transLenTr ⟨39, by decide⟩ p hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_39 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_39_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_39_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_39_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_39_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_39_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_39_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_39_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_39_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_39_20 hp j hj hq
  simp at hm

theorem pair_133_43 (p : Nat) (hp : p < (Q2.transData.getD 43 []).length)
    (hrep : (Q2.cosetIsRep.getD 43 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ p hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ p (transLenTr ⟨43, by decide⟩ p hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_43 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_43_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_43_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_43_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_43_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_43_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_43_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_43_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_43_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_43_20 hp j hj hq
  simp at hm

theorem pair_133_50 (p : Nat) (hp : p < (Q2.transData.getD 50 []).length)
    (hrep : (Q2.cosetIsRep.getD 50 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ p hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ p (transLenTr ⟨50, by decide⟩ p hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_50 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_50_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_50_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_50_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_50_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_50_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_50_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_50_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_50_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_50_20 hp j hj hq
  simp at hm

theorem pair_133_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_53_20 hp j hj hq
  simp at hm

theorem pair_133_83 (p : Nat) (hp : p < (Q2.transData.getD 83 []).length)
    (hrep : (Q2.cosetIsRep.getD 83 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ p hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ p (transLenTr ⟨83, by decide⟩ p hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_83 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_83_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_83_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_83_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_83_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_83_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_83_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_83_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_83_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_83_20 hp j hj hq
  simp at hm

theorem pair_133_94 (p : Nat) (hp : p < (Q2.transData.getD 94 []).length)
    (hrep : (Q2.cosetIsRep.getD 94 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ p hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ p (transLenTr ⟨94, by decide⟩ p hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_94 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_94_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_94_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_94_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_94_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_94_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_94_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_94_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_94_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_94_20 hp j hj hq
  simp at hm

theorem pair_133_98 (p : Nat) (hp : p < (Q2.transData.getD 98 []).length)
    (hrep : (Q2.cosetIsRep.getD 98 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ p hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ p (transLenTr ⟨98, by decide⟩ p hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_98 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_98_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_98_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_98_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_98_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_98_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_98_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_98_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_98_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_98_20 hp j hj hq
  simp at hm

theorem pair_133_101 (p : Nat) (hp : p < (Q2.transData.getD 101 []).length)
    (hrep : (Q2.cosetIsRep.getD 101 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ p hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ p (transLenTr ⟨101, by decide⟩ p hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_101 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_101_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_101_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_101_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_101_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_101_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_101_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_101_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_101_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_101_20 hp j hj hq
  simp at hm

theorem pair_133_105 (p : Nat) (hp : p < (Q2.transData.getD 105 []).length)
    (hrep : (Q2.cosetIsRep.getD 105 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ p hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ p (transLenTr ⟨105, by decide⟩ p hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_105 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_105_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_105_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_105_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_105_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_105_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_105_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_105_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_105_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_105_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_105_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_105_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_105_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_105_100 hp j hj hq
  simp at hm

theorem pair_133_112 (p : Nat) (hp : p < (Q2.transData.getD 112 []).length)
    (hrep : (Q2.cosetIsRep.getD 112 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ p hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ p (transLenTr ⟨112, by decide⟩ p hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_112 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_112_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_112_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_112_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_112_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_112_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_112_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_112_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_112_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_112_20 hp j hj hq
  simp at hm

theorem pair_133_133 (p : Nat) (hp : p < (Q2.transData.getD 133 []).length)
    (hrep : (Q2.cosetIsRep.getD 133 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ p hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ p (transLenTr ⟨133, by decide⟩ p hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_133 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_133_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_133_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_133_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_133_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_133_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_133_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_133_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_133_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_133_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_133_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_133_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_133_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_133_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_133_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_133_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_133_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_133_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_133_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_133_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_133_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_133_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_133_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_133_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_133_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_133_133_24 hp j hj hq
  simp at hm

theorem pair_134_4 (p : Nat) (hp : p < (Q2.transData.getD 4 []).length)
    (hrep : (Q2.cosetIsRep.getD 4 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ p hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ p (transLenTr ⟨4, by decide⟩ p hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_4 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_4_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_4_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_4_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_4_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_4_4 hp j hj hq
  simp at hm

theorem pair_134_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_10_4 hp j hj hq
  simp at hm

theorem pair_134_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_12_4 hp j hj hq
  simp at hm

theorem pair_134_22 (p : Nat) (hp : p < (Q2.transData.getD 22 []).length)
    (hrep : (Q2.cosetIsRep.getD 22 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ p hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ p (transLenTr ⟨22, by decide⟩ p hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_22 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_22_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_22_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_22_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_22_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_22_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_22_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_22_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_22_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_22_20 hp j hj hq
  simp at hm

theorem pair_134_28 (p : Nat) (hp : p < (Q2.transData.getD 28 []).length)
    (hrep : (Q2.cosetIsRep.getD 28 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ p hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ p (transLenTr ⟨28, by decide⟩ p hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_28 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_28_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_28_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_28_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_28_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_28_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_28_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_28_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_28_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_28_20 hp j hj hq
  simp at hm

theorem pair_134_37 (p : Nat) (hp : p < (Q2.transData.getD 37 []).length)
    (hrep : (Q2.cosetIsRep.getD 37 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ p hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ p (transLenTr ⟨37, by decide⟩ p hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_37 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_37_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_37_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_37_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_37_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_37_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_37_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_37_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_37_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_37_20 hp j hj hq
  simp at hm

theorem pair_134_40 (p : Nat) (hp : p < (Q2.transData.getD 40 []).length)
    (hrep : (Q2.cosetIsRep.getD 40 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ p hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ p (transLenTr ⟨40, by decide⟩ p hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_40 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_40_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_40_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_40_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_40_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_40_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_40_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_40_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_40_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_40_20 hp j hj hq
  simp at hm

theorem pair_134_44 (p : Nat) (hp : p < (Q2.transData.getD 44 []).length)
    (hrep : (Q2.cosetIsRep.getD 44 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ p hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ p (transLenTr ⟨44, by decide⟩ p hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_44 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_44_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_44_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_44_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_44_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_44_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_44_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_44_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_44_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_44_20 hp j hj hq
  simp at hm

theorem pair_134_51 (p : Nat) (hp : p < (Q2.transData.getD 51 []).length)
    (hrep : (Q2.cosetIsRep.getD 51 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ p hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ p (transLenTr ⟨51, by decide⟩ p hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_51 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_51_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_51_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_51_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_51_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_51_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_51_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_51_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_51_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_51_20 hp j hj hq
  simp at hm

theorem pair_134_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_53_20 hp j hj hq
  simp at hm

theorem pair_134_83 (p : Nat) (hp : p < (Q2.transData.getD 83 []).length)
    (hrep : (Q2.cosetIsRep.getD 83 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ p hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ p (transLenTr ⟨83, by decide⟩ p hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_83 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_83_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_83_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_83_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_83_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_83_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_83_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_83_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_83_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_83_20 hp j hj hq
  simp at hm

theorem pair_134_90 (p : Nat) (hp : p < (Q2.transData.getD 90 []).length)
    (hrep : (Q2.cosetIsRep.getD 90 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ p hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ p (transLenTr ⟨90, by decide⟩ p hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_90 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_90_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_90_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_90_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_90_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_90_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_90_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_90_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_90_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_90_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_90_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_90_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_90_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_90_100 hp j hj hq
  simp at hm

theorem pair_134_99 (p : Nat) (hp : p < (Q2.transData.getD 99 []).length)
    (hrep : (Q2.cosetIsRep.getD 99 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ p hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ p (transLenTr ⟨99, by decide⟩ p hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_99 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_99_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_99_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_99_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_99_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_99_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_99_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_99_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_99_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_99_20 hp j hj hq
  simp at hm

theorem pair_134_102 (p : Nat) (hp : p < (Q2.transData.getD 102 []).length)
    (hrep : (Q2.cosetIsRep.getD 102 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ p hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ p (transLenTr ⟨102, by decide⟩ p hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_102 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_102_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_102_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_102_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_102_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_102_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_102_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_102_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_102_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_102_20 hp j hj hq
  simp at hm

theorem pair_134_106 (p : Nat) (hp : p < (Q2.transData.getD 106 []).length)
    (hrep : (Q2.cosetIsRep.getD 106 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ p hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ p (transLenTr ⟨106, by decide⟩ p hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_106 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_106_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_106_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_106_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_106_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_106_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_106_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_106_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_106_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_106_20 hp j hj hq
  simp at hm

theorem pair_134_113 (p : Nat) (hp : p < (Q2.transData.getD 113 []).length)
    (hrep : (Q2.cosetIsRep.getD 113 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ p hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ p (transLenTr ⟨113, by decide⟩ p hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_113 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_113_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_113_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_113_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_113_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_113_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_113_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_113_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_113_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_113_20 hp j hj hq
  simp at hm

theorem pair_134_134 (p : Nat) (hp : p < (Q2.transData.getD 134 []).length)
    (hrep : (Q2.cosetIsRep.getD 134 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ p hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ p (transLenTr ⟨134, by decide⟩ p hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_134 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_134_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_134_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_134_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_134_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_134_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_134_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_134_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_134_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_134_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_134_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_134_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_134_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_134_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_134_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_134_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_134_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_134_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_134_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_134_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_134_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_134_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_134_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_134_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_134_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_134_134_24 hp j hj hq
  simp at hm

theorem pair_135_4 (p : Nat) (hp : p < (Q2.transData.getD 4 []).length)
    (hrep : (Q2.cosetIsRep.getD 4 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ p hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ p (transLenTr ⟨4, by decide⟩ p hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_4 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_4_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_4_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_4_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_4_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_4_4 hp j hj hq
  simp at hm

theorem pair_135_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_10_4 hp j hj hq
  simp at hm

theorem pair_135_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_12_4 hp j hj hq
  simp at hm

theorem pair_135_22 (p : Nat) (hp : p < (Q2.transData.getD 22 []).length)
    (hrep : (Q2.cosetIsRep.getD 22 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ p hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ p (transLenTr ⟨22, by decide⟩ p hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_22 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_22_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_22_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_22_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_22_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_22_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_22_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_22_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_22_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_22_20 hp j hj hq
  simp at hm

theorem pair_135_29 (p : Nat) (hp : p < (Q2.transData.getD 29 []).length)
    (hrep : (Q2.cosetIsRep.getD 29 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ p hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ p (transLenTr ⟨29, by decide⟩ p hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_29 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_29_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_29_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_29_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_29_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_29_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_29_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_29_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_29_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_29_20 hp j hj hq
  simp at hm

theorem pair_135_33 (p : Nat) (hp : p < (Q2.transData.getD 33 []).length)
    (hrep : (Q2.cosetIsRep.getD 33 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ p hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ p (transLenTr ⟨33, by decide⟩ p hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_33 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_33_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_33_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_33_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_33_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_33_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_33_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_33_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_33_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_33_20 hp j hj hq
  simp at hm

theorem pair_135_41 (p : Nat) (hp : p < (Q2.transData.getD 41 []).length)
    (hrep : (Q2.cosetIsRep.getD 41 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ p hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ p (transLenTr ⟨41, by decide⟩ p hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_41 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_41_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_41_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_41_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_41_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_41_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_41_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_41_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_41_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_41_20 hp j hj hq
  simp at hm

theorem pair_135_45 (p : Nat) (hp : p < (Q2.transData.getD 45 []).length)
    (hrep : (Q2.cosetIsRep.getD 45 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ p hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ p (transLenTr ⟨45, by decide⟩ p hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_45 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_45_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_45_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_45_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_45_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_45_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_45_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_45_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_45_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_45_20 hp j hj hq
  simp at hm

theorem pair_135_52 (p : Nat) (hp : p < (Q2.transData.getD 52 []).length)
    (hrep : (Q2.cosetIsRep.getD 52 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ p hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ p (transLenTr ⟨52, by decide⟩ p hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_52 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_52_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_52_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_52_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_52_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_52_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_52_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_52_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_52_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_52_20 hp j hj hq
  simp at hm

theorem pair_135_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_53_20 hp j hj hq
  simp at hm

theorem pair_135_83 (p : Nat) (hp : p < (Q2.transData.getD 83 []).length)
    (hrep : (Q2.cosetIsRep.getD 83 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ p hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ p (transLenTr ⟨83, by decide⟩ p hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_83 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_83_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_83_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_83_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_83_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_83_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_83_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_83_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_83_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_83_20 hp j hj hq
  simp at hm

theorem pair_135_91 (p : Nat) (hp : p < (Q2.transData.getD 91 []).length)
    (hrep : (Q2.cosetIsRep.getD 91 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ p hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ p (transLenTr ⟨91, by decide⟩ p hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_91 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_91_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_91_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_91_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_91_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_91_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_91_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_91_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_91_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_91_20 hp j hj hq
  simp at hm

theorem pair_135_95 (p : Nat) (hp : p < (Q2.transData.getD 95 []).length)
    (hrep : (Q2.cosetIsRep.getD 95 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ p hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ p (transLenTr ⟨95, by decide⟩ p hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_95 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_95_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_95_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_95_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_95_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_95_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_95_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_95_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_95_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_95_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_95_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_95_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_95_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_95_100 hp j hj hq
  simp at hm

theorem pair_135_103 (p : Nat) (hp : p < (Q2.transData.getD 103 []).length)
    (hrep : (Q2.cosetIsRep.getD 103 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ p hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ p (transLenTr ⟨103, by decide⟩ p hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_103 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_103_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_103_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_103_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_103_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_103_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_103_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_103_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_103_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_103_20 hp j hj hq
  simp at hm

theorem pair_135_107 (p : Nat) (hp : p < (Q2.transData.getD 107 []).length)
    (hrep : (Q2.cosetIsRep.getD 107 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ p hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ p (transLenTr ⟨107, by decide⟩ p hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_107 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_107_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_107_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_107_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_107_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_107_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_107_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_107_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_107_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_107_20 hp j hj hq
  simp at hm

theorem pair_135_114 (p : Nat) (hp : p < (Q2.transData.getD 114 []).length)
    (hrep : (Q2.cosetIsRep.getD 114 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ p hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ p (transLenTr ⟨114, by decide⟩ p hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_114 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_114_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_114_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_114_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_114_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_114_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_114_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_114_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_114_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_114_20 hp j hj hq
  simp at hm

theorem pair_135_135 (p : Nat) (hp : p < (Q2.transData.getD 135 []).length)
    (hrep : (Q2.cosetIsRep.getD 135 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ p hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ p (transLenTr ⟨135, by decide⟩ p hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_135 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_135_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_135_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_135_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_135_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_135_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_135_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_135_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_135_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_135_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_135_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_135_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_135_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_135_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_135_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_135_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_135_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_135_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_135_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_135_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_135_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_135_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_135_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_135_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_135_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_135_135_24 hp j hj hq
  simp at hm

theorem pair_136_5 (p : Nat) (hp : p < (Q2.transData.getD 5 []).length)
    (hrep : (Q2.cosetIsRep.getD 5 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ p hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ p (transLenTr ⟨5, by decide⟩ p hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_5 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_5_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_5_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_5_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_5_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_5_4 hp j hj hq
  simp at hm

theorem pair_136_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_10_4 hp j hj hq
  simp at hm

theorem pair_136_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_12_4 hp j hj hq
  simp at hm

theorem pair_136_23 (p : Nat) (hp : p < (Q2.transData.getD 23 []).length)
    (hrep : (Q2.cosetIsRep.getD 23 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ p hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ p (transLenTr ⟨23, by decide⟩ p hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_23 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_23_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_23_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_23_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_23_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_23_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_23_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_23_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_23_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_23_20 hp j hj hq
  simp at hm

theorem pair_136_29 (p : Nat) (hp : p < (Q2.transData.getD 29 []).length)
    (hrep : (Q2.cosetIsRep.getD 29 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ p hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ p (transLenTr ⟨29, by decide⟩ p hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_29 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_29_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_29_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_29_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_29_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_29_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_29_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_29_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_29_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_29_20 hp j hj hq
  simp at hm

theorem pair_136_36 (p : Nat) (hp : p < (Q2.transData.getD 36 []).length)
    (hrep : (Q2.cosetIsRep.getD 36 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ p hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ p (transLenTr ⟨36, by decide⟩ p hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_36 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_36_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_36_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_36_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_36_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_36_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_36_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_36_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_36_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_36_20 hp j hj hq
  simp at hm

theorem pair_136_40 (p : Nat) (hp : p < (Q2.transData.getD 40 []).length)
    (hrep : (Q2.cosetIsRep.getD 40 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ p hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ p (transLenTr ⟨40, by decide⟩ p hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_40 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_40_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_40_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_40_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_40_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_40_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_40_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_40_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_40_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_40_20 hp j hj hq
  simp at hm

theorem pair_136_47 (p : Nat) (hp : p < (Q2.transData.getD 47 []).length)
    (hrep : (Q2.cosetIsRep.getD 47 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ p hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ p (transLenTr ⟨47, by decide⟩ p hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_47 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_47_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_47_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_47_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_47_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_47_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_47_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_47_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_47_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_47_20 hp j hj hq
  simp at hm

theorem pair_136_48 (p : Nat) (hp : p < (Q2.transData.getD 48 []).length)
    (hrep : (Q2.cosetIsRep.getD 48 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ p hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ p (transLenTr ⟨48, by decide⟩ p hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_48 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_48_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_48_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_48_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_48_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_48_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_48_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_48_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_48_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_48_20 hp j hj hq
  simp at hm

theorem pair_136_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_53_20 hp j hj hq
  simp at hm

theorem pair_136_84 (p : Nat) (hp : p < (Q2.transData.getD 84 []).length)
    (hrep : (Q2.cosetIsRep.getD 84 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ p hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ p (transLenTr ⟨84, by decide⟩ p hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_84 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_84_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_84_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_84_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_84_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_84_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_84_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_84_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_84_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_84_20 hp j hj hq
  simp at hm

theorem pair_136_91 (p : Nat) (hp : p < (Q2.transData.getD 91 []).length)
    (hrep : (Q2.cosetIsRep.getD 91 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ p hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ p (transLenTr ⟨91, by decide⟩ p hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_91 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_91_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_91_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_91_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_91_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_91_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_91_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_91_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_91_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_91_20 hp j hj hq
  simp at hm

theorem pair_136_98 (p : Nat) (hp : p < (Q2.transData.getD 98 []).length)
    (hrep : (Q2.cosetIsRep.getD 98 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ p hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ p (transLenTr ⟨98, by decide⟩ p hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_98 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_98_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_98_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_98_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_98_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_98_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_98_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_98_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_98_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_98_20 hp j hj hq
  simp at hm

theorem pair_136_102 (p : Nat) (hp : p < (Q2.transData.getD 102 []).length)
    (hrep : (Q2.cosetIsRep.getD 102 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ p hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ p (transLenTr ⟨102, by decide⟩ p hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_102 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_102_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_102_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_102_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_102_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_102_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_102_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_102_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_102_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_102_20 hp j hj hq
  simp at hm

theorem pair_136_109 (p : Nat) (hp : p < (Q2.transData.getD 109 []).length)
    (hrep : (Q2.cosetIsRep.getD 109 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ p hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ p (transLenTr ⟨109, by decide⟩ p hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_109 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_109_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_109_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_109_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_109_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_109_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_109_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_109_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_109_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_109_20 hp j hj hq
  simp at hm

theorem pair_136_110 (p : Nat) (hp : p < (Q2.transData.getD 110 []).length)
    (hrep : (Q2.cosetIsRep.getD 110 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ p hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ p (transLenTr ⟨110, by decide⟩ p hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_110 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_110_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_110_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_110_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_110_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_110_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_110_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_110_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_110_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_110_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_110_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_110_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_110_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_110_100 hp j hj hq
  simp at hm

theorem pair_136_136 (p : Nat) (hp : p < (Q2.transData.getD 136 []).length)
    (hrep : (Q2.cosetIsRep.getD 136 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ p hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ p (transLenTr ⟨136, by decide⟩ p hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_136 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_136_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_136_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_136_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_136_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_136_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_136_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_136_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_136_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_136_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_136_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_136_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_136_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_136_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_136_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_136_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_136_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_136_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_136_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_136_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_136_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_136_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_136_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_136_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_136_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_136_136_24 hp j hj hq
  simp at hm

theorem pair_137_5 (p : Nat) (hp : p < (Q2.transData.getD 5 []).length)
    (hrep : (Q2.cosetIsRep.getD 5 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ p hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ p (transLenTr ⟨5, by decide⟩ p hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_5 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_5_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_5_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_5_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_5_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_5_4 hp j hj hq
  simp at hm

theorem pair_137_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_10_4 hp j hj hq
  simp at hm

theorem pair_137_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_12_4 hp j hj hq
  simp at hm

theorem pair_137_23 (p : Nat) (hp : p < (Q2.transData.getD 23 []).length)
    (hrep : (Q2.cosetIsRep.getD 23 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ p hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ p (transLenTr ⟨23, by decide⟩ p hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_23 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_23_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_23_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_23_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_23_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_23_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_23_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_23_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_23_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_23_20 hp j hj hq
  simp at hm

theorem pair_137_30 (p : Nat) (hp : p < (Q2.transData.getD 30 []).length)
    (hrep : (Q2.cosetIsRep.getD 30 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ p hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ p (transLenTr ⟨30, by decide⟩ p hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_30 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_30_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_30_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_30_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_30_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_30_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_30_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_30_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_30_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_30_20 hp j hj hq
  simp at hm

theorem pair_137_37 (p : Nat) (hp : p < (Q2.transData.getD 37 []).length)
    (hrep : (Q2.cosetIsRep.getD 37 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ p hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ p (transLenTr ⟨37, by decide⟩ p hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_37 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_37_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_37_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_37_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_37_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_37_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_37_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_37_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_37_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_37_20 hp j hj hq
  simp at hm

theorem pair_137_41 (p : Nat) (hp : p < (Q2.transData.getD 41 []).length)
    (hrep : (Q2.cosetIsRep.getD 41 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ p hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ p (transLenTr ⟨41, by decide⟩ p hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_41 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_41_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_41_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_41_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_41_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_41_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_41_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_41_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_41_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_41_20 hp j hj hq
  simp at hm

theorem pair_137_43 (p : Nat) (hp : p < (Q2.transData.getD 43 []).length)
    (hrep : (Q2.cosetIsRep.getD 43 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ p hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ p (transLenTr ⟨43, by decide⟩ p hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_43 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_43_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_43_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_43_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_43_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_43_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_43_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_43_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_43_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_43_20 hp j hj hq
  simp at hm

theorem pair_137_49 (p : Nat) (hp : p < (Q2.transData.getD 49 []).length)
    (hrep : (Q2.cosetIsRep.getD 49 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ p hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ p (transLenTr ⟨49, by decide⟩ p hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_49 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_49_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_49_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_49_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_49_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_49_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_49_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_49_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_49_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_49_20 hp j hj hq
  simp at hm

theorem pair_137_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_53_20 hp j hj hq
  simp at hm

theorem pair_137_84 (p : Nat) (hp : p < (Q2.transData.getD 84 []).length)
    (hrep : (Q2.cosetIsRep.getD 84 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ p hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ p (transLenTr ⟨84, by decide⟩ p hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_84 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_84_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_84_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_84_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_84_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_84_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_84_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_84_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_84_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_84_20 hp j hj hq
  simp at hm

theorem pair_137_92 (p : Nat) (hp : p < (Q2.transData.getD 92 []).length)
    (hrep : (Q2.cosetIsRep.getD 92 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ p hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ p (transLenTr ⟨92, by decide⟩ p hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_92 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_92_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_92_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_92_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_92_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_92_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_92_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_92_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_92_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_92_20 hp j hj hq
  simp at hm

theorem pair_137_99 (p : Nat) (hp : p < (Q2.transData.getD 99 []).length)
    (hrep : (Q2.cosetIsRep.getD 99 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ p hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ p (transLenTr ⟨99, by decide⟩ p hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_99 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_99_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_99_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_99_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_99_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_99_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_99_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_99_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_99_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_99_20 hp j hj hq
  simp at hm

theorem pair_137_103 (p : Nat) (hp : p < (Q2.transData.getD 103 []).length)
    (hrep : (Q2.cosetIsRep.getD 103 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ p hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ p (transLenTr ⟨103, by decide⟩ p hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_103 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_103_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_103_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_103_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_103_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_103_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_103_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_103_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_103_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_103_20 hp j hj hq
  simp at hm

theorem pair_137_105 (p : Nat) (hp : p < (Q2.transData.getD 105 []).length)
    (hrep : (Q2.cosetIsRep.getD 105 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ p hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ p (transLenTr ⟨105, by decide⟩ p hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_105 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_105_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_105_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_105_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_105_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_105_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_105_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_105_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_105_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_105_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_105_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_105_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_105_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_105_100 hp j hj hq
  simp at hm

theorem pair_137_111 (p : Nat) (hp : p < (Q2.transData.getD 111 []).length)
    (hrep : (Q2.cosetIsRep.getD 111 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ p hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ p (transLenTr ⟨111, by decide⟩ p hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_111 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_111_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_111_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_111_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_111_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_111_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_111_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_111_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_111_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_111_20 hp j hj hq
  simp at hm

theorem pair_137_137 (p : Nat) (hp : p < (Q2.transData.getD 137 []).length)
    (hrep : (Q2.cosetIsRep.getD 137 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ p hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ p (transLenTr ⟨137, by decide⟩ p hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_137 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_137_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_137_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_137_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_137_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_137_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_137_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_137_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_137_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_137_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_137_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_137_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_137_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_137_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_137_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_137_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_137_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_137_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_137_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_137_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_137_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_137_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_137_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_137_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_137_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_137_137_24 hp j hj hq
  simp at hm

theorem pair_138_5 (p : Nat) (hp : p < (Q2.transData.getD 5 []).length)
    (hrep : (Q2.cosetIsRep.getD 5 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ p hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ p (transLenTr ⟨5, by decide⟩ p hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_5 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_5_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_5_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_5_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_5_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_5_4 hp j hj hq
  simp at hm

theorem pair_138_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_10_4 hp j hj hq
  simp at hm

theorem pair_138_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_12_4 hp j hj hq
  simp at hm

theorem pair_138_23 (p : Nat) (hp : p < (Q2.transData.getD 23 []).length)
    (hrep : (Q2.cosetIsRep.getD 23 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ p hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ p (transLenTr ⟨23, by decide⟩ p hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_23 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_23_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_23_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_23_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_23_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_23_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_23_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_23_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_23_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_23_20 hp j hj hq
  simp at hm

theorem pair_138_31 (p : Nat) (hp : p < (Q2.transData.getD 31 []).length)
    (hrep : (Q2.cosetIsRep.getD 31 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ p hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ p (transLenTr ⟨31, by decide⟩ p hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_31 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_31_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_31_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_31_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_31_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_31_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_31_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_31_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_31_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_31_20 hp j hj hq
  simp at hm

theorem pair_138_33 (p : Nat) (hp : p < (Q2.transData.getD 33 []).length)
    (hrep : (Q2.cosetIsRep.getD 33 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ p hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ p (transLenTr ⟨33, by decide⟩ p hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_33 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_33_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_33_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_33_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_33_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_33_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_33_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_33_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_33_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_33_20 hp j hj hq
  simp at hm

theorem pair_138_42 (p : Nat) (hp : p < (Q2.transData.getD 42 []).length)
    (hrep : (Q2.cosetIsRep.getD 42 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ p hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ p (transLenTr ⟨42, by decide⟩ p hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_42 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_42_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_42_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_42_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_42_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_42_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_42_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_42_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_42_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_42_20 hp j hj hq
  simp at hm

theorem pair_138_44 (p : Nat) (hp : p < (Q2.transData.getD 44 []).length)
    (hrep : (Q2.cosetIsRep.getD 44 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ p hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ p (transLenTr ⟨44, by decide⟩ p hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_44 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_44_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_44_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_44_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_44_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_44_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_44_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_44_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_44_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_44_20 hp j hj hq
  simp at hm

theorem pair_138_50 (p : Nat) (hp : p < (Q2.transData.getD 50 []).length)
    (hrep : (Q2.cosetIsRep.getD 50 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ p hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ p (transLenTr ⟨50, by decide⟩ p hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_50 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_50_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_50_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_50_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_50_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_50_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_50_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_50_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_50_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_50_20 hp j hj hq
  simp at hm

theorem pair_138_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_53_20 hp j hj hq
  simp at hm

theorem pair_138_84 (p : Nat) (hp : p < (Q2.transData.getD 84 []).length)
    (hrep : (Q2.cosetIsRep.getD 84 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ p hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ p (transLenTr ⟨84, by decide⟩ p hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_84 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_84_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_84_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_84_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_84_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_84_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_84_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_84_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_84_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_84_20 hp j hj hq
  simp at hm

theorem pair_138_93 (p : Nat) (hp : p < (Q2.transData.getD 93 []).length)
    (hrep : (Q2.cosetIsRep.getD 93 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ p hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ p (transLenTr ⟨93, by decide⟩ p hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_93 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_93_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_93_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_93_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_93_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_93_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_93_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_93_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_93_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_93_20 hp j hj hq
  simp at hm

theorem pair_138_95 (p : Nat) (hp : p < (Q2.transData.getD 95 []).length)
    (hrep : (Q2.cosetIsRep.getD 95 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ p hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ p (transLenTr ⟨95, by decide⟩ p hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_95 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_95_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_95_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_95_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_95_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_95_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_95_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_95_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_95_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_95_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_95_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_95_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_95_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_95_100 hp j hj hq
  simp at hm

theorem pair_138_104 (p : Nat) (hp : p < (Q2.transData.getD 104 []).length)
    (hrep : (Q2.cosetIsRep.getD 104 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ p hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ p (transLenTr ⟨104, by decide⟩ p hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_104 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_104_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_104_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_104_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_104_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_104_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_104_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_104_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_104_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_104_20 hp j hj hq
  simp at hm

theorem pair_138_106 (p : Nat) (hp : p < (Q2.transData.getD 106 []).length)
    (hrep : (Q2.cosetIsRep.getD 106 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ p hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ p (transLenTr ⟨106, by decide⟩ p hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_106 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_106_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_106_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_106_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_106_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_106_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_106_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_106_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_106_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_106_20 hp j hj hq
  simp at hm

theorem pair_138_112 (p : Nat) (hp : p < (Q2.transData.getD 112 []).length)
    (hrep : (Q2.cosetIsRep.getD 112 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ p hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ p (transLenTr ⟨112, by decide⟩ p hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_112 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_112_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_112_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_112_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_112_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_112_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_112_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_112_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_112_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_112_20 hp j hj hq
  simp at hm

theorem pair_138_138 (p : Nat) (hp : p < (Q2.transData.getD 138 []).length)
    (hrep : (Q2.cosetIsRep.getD 138 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ p hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ p (transLenTr ⟨138, by decide⟩ p hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_138 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_138_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_138_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_138_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_138_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_138_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_138_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_138_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_138_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_138_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_138_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_138_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_138_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_138_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_138_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_138_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_138_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_138_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_138_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_138_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_138_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_138_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_138_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_138_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_138_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_138_138_24 hp j hj hq
  simp at hm

theorem pair_139_5 (p : Nat) (hp : p < (Q2.transData.getD 5 []).length)
    (hrep : (Q2.cosetIsRep.getD 5 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ p hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ p (transLenTr ⟨5, by decide⟩ p hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_5 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_5_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_5_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_5_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_5_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_5_4 hp j hj hq
  simp at hm

theorem pair_139_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_10_4 hp j hj hq
  simp at hm

theorem pair_139_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_12_4 hp j hj hq
  simp at hm

theorem pair_139_23 (p : Nat) (hp : p < (Q2.transData.getD 23 []).length)
    (hrep : (Q2.cosetIsRep.getD 23 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ p hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ p (transLenTr ⟨23, by decide⟩ p hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_23 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_23_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_23_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_23_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_23_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_23_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_23_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_23_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_23_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_23_20 hp j hj hq
  simp at hm

theorem pair_139_32 (p : Nat) (hp : p < (Q2.transData.getD 32 []).length)
    (hrep : (Q2.cosetIsRep.getD 32 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ p hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ p (transLenTr ⟨32, by decide⟩ p hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_32 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_32_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_32_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_32_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_32_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_32_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_32_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_32_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_32_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_32_20 hp j hj hq
  simp at hm

theorem pair_139_34 (p : Nat) (hp : p < (Q2.transData.getD 34 []).length)
    (hrep : (Q2.cosetIsRep.getD 34 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ p hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ p (transLenTr ⟨34, by decide⟩ p hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_34 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_34_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_34_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_34_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_34_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_34_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_34_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_34_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_34_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_34_20 hp j hj hq
  simp at hm

theorem pair_139_38 (p : Nat) (hp : p < (Q2.transData.getD 38 []).length)
    (hrep : (Q2.cosetIsRep.getD 38 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ p hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ p (transLenTr ⟨38, by decide⟩ p hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_38 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_38_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_38_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_38_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_38_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_38_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_38_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_38_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_38_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_38_20 hp j hj hq
  simp at hm

theorem pair_139_45 (p : Nat) (hp : p < (Q2.transData.getD 45 []).length)
    (hrep : (Q2.cosetIsRep.getD 45 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ p hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ p (transLenTr ⟨45, by decide⟩ p hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_45 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_45_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_45_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_45_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_45_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_45_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_45_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_45_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_45_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_45_20 hp j hj hq
  simp at hm

theorem pair_139_51 (p : Nat) (hp : p < (Q2.transData.getD 51 []).length)
    (hrep : (Q2.cosetIsRep.getD 51 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ p hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ p (transLenTr ⟨51, by decide⟩ p hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_51 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_51_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_51_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_51_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_51_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_51_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_51_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_51_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_51_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_51_20 hp j hj hq
  simp at hm

theorem pair_139_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_53_20 hp j hj hq
  simp at hm

theorem pair_139_84 (p : Nat) (hp : p < (Q2.transData.getD 84 []).length)
    (hrep : (Q2.cosetIsRep.getD 84 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ p hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ p (transLenTr ⟨84, by decide⟩ p hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_84 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_84_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_84_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_84_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_84_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_84_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_84_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_84_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_84_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_84_20 hp j hj hq
  simp at hm

theorem pair_139_94 (p : Nat) (hp : p < (Q2.transData.getD 94 []).length)
    (hrep : (Q2.cosetIsRep.getD 94 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ p hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ p (transLenTr ⟨94, by decide⟩ p hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_94 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_94_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_94_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_94_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_94_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_94_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_94_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_94_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_94_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_94_20 hp j hj hq
  simp at hm

end LeanDring.P5Presentation
